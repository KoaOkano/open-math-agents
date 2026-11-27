"""Check upstream receipts for every proof added on the research branch."""

import json
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path
from urllib.error import HTTPError, URLError
from urllib.parse import urlencode
from urllib.request import Request, urlopen


ROOT = Path(__file__).resolve().parents[1]
BASE = "318d3bcb19bb6f9ae811f7c2f8870ba5418449e1"
OWNER = "KoaOkano"
REPO = "GuillaumeBAUD-coder/open-math-agents"
UPSTREAM = f"https://github.com/{REPO}"


def git(*args):
    return subprocess.check_output(["git", "-C", ROOT, *args], text=True).splitlines()


def api(path, **params):
    endpoint = path + ("?" + urlencode(params) if params else "")
    gh = shutil.which("gh")
    if gh:
        response = subprocess.run([gh, "api", endpoint], capture_output=True)
        if response.returncode == 0:
            return json.loads(response.stdout)
    data = subprocess.check_output(["curl", "--fail", "--silent", "--show-error",
                                    "--max-time", "30", "https://api.github.com" + endpoint])
    return json.loads(data)


def receipt_rows():
    for line in (ROOT / "research/README.md").read_text(encoding="utf-8").splitlines():
        match = re.fullmatch(r"\| (A\d{6}) \| ([^|]*) \| ([^|]*) \|", line)
        if match:
            yield "oeis-" + match[1].lower(), match[2], match[3]


def pr_number(cell):
    link = re.search(re.escape(f"{UPSTREAM}/pull/") + r"(\d+)\)", cell)
    return int(link[1]) if link else None


def receipts():
    return {problem: [pr_number(statement), pr_number(proof)]
            for problem, statement, proof in receipt_rows()}


def certificate_credit(problem, number, ledger_status):
    url = f"https://lefttosolve.com/c/{problem}/{OWNER}"
    result = {"problem": problem, "pr": number, "url": url, "ledgerStatus": ledger_status}
    query = urlencode({"problem": problem, "handle": OWNER})
    request = Request(f"https://lefttosolve.com/api/certificate?{query}",
                      headers={"Accept": "application/json", "User-Agent": "open-math-research"})
    try:
        with urlopen(request, timeout=20) as response:
            envelope = json.load(response)
    except HTTPError as error:
        status = "pending" if error.code == 404 else "unavailable"
        return {**result, "status": status, "httpStatus": error.code}
    except (URLError, TimeoutError, OSError, ValueError):
        return {**result, "status": "unavailable"}

    cert = envelope.get("certificate") if isinstance(envelope, dict) else None
    if not isinstance(cert, dict) or cert.get("type") != "left-to-solve/contribution-certificate":
        return {**result, "status": "unavailable"}
    holder = cert.get("holder") or {}
    handle = holder.get("handle") or ""
    polarity = cert.get("result")
    proof_url = f"{UPSTREAM}/pull/{number}"
    matching_role = any(r.get("role") == "proof" and r.get("item") == problem and r.get("pr") == proof_url
                        for r in holder.get("roles", []) if isinstance(r, dict))
    if (handle.casefold() != OWNER.casefold() or (cert.get("problem") or {}).get("id") != problem
            or polarity not in ("proof", "disproof") or not matching_role):
        return {**result, "status": "mismatch"}
    return {**result, "status": "recorded", "handle": handle, "polarity": polarity,
            "certificateId": envelope.get("id")}


def proof_credit(problem, number):
    """Verify the problem, GitHub author, PR number and polarity on a public site receipt."""
    if not re.fullmatch(r"oeis-a[0-9]{6}", problem) or number < 1:
        raise ValueError("Expected an OEIS identifier and a positive PR number")
    url = f"https://lefttosolve.com/api/ledger?pr={number}"
    result = {"problem": problem, "pr": number, "url": url}
    request = Request(url, headers={"Accept": "application/json", "User-Agent": "open-math-research"})
    try:
        with urlopen(request, timeout=20) as response:
            payload = json.load(response)
    except HTTPError as error:
        missing = error.code == 404 and error.headers.get_content_type() == "application/json"
        status = "pending" if missing else "unavailable"
        return certificate_credit(problem, number, status)
    except (URLError, TimeoutError, OSError, ValueError):
        return certificate_credit(problem, number, "unavailable")
    if not isinstance(payload, dict) or not isinstance(payload.get("entry"), dict):
        return certificate_credit(problem, number, "unavailable")
    entry = payload["entry"]
    if (payload.get("pr") != number or entry.get("pr") != number or entry.get("id") != problem
            or str(entry.get("handle") or "").casefold() != OWNER.casefold() or entry.get("kind") != "proof"
            or entry.get("polarity") not in ("proof", "disproof")):
        return {**result, "status": "mismatch"}
    return {**result, "status": "recorded", "handle": entry["handle"], "polarity": entry["polarity"]}


def desk_followups():
    """GitHub receipts whose submission still needs linking on the problem desk."""
    return [{"id": problem, "proofPR": pr_number(proof)}
            for problem, _, proof in receipt_rows()
            if "Desk follow-up pending" in proof and pr_number(proof)]


def statement_desk_followups():
    """Statement PRs for which the first-party assignment service was unavailable."""
    return [{"id": problem, "statementPR": pr_number(statement)}
            for problem, statement, _ in receipt_rows()
            if "Statement desk follow-up pending" in statement and pr_number(statement)]


def fetch_main():
    remote = UPSTREAM + ".git"
    tip = git("ls-remote", "--exit-code", remote, "refs/heads/main")[0].split()[0]
    attempts = 8
    for attempt in range(attempts):
        present = subprocess.run(["git", "-C", ROOT, "cat-file", "-e", f"{tip}^{{commit}}"],
                                 stderr=subprocess.DEVNULL)
        if present.returncode == 0:
            return tip
        fetched = subprocess.run(["git", "-C", ROOT, "fetch", "--quiet", "--depth=1", "--no-tags",
                                  "--no-write-fetch-head", remote, tip], capture_output=True, text=True)
        if fetched.returncode == 0:
            return tip
        contention = ".lock" in fetched.stderr or "shallow file has changed" in fetched.stderr
        if attempt + 1 == attempts or not contention:
            raise RuntimeError(fetched.stderr.strip() or "Unable to fetch upstream main")
        time.sleep(min(5, attempt + 1))


def proof_queue(tip):
    """List locally prepared proofs whose statement has arrived on upstream main."""
    blobs = {}
    for entry in git("ls-tree", "-r", tip, "--", "statements", "proofs"):
        header, path = entry.split("\t", 1)
        blobs[path] = header.split()[2]
    ready, completed, recheck = [], [], []
    for problem, (statement_pr, proof_pr) in receipts().items():
        statement = f"statements/{problem}.lean"
        proof = f"proofs/{problem}.lean"
        if proof in blobs:
            completed.append(problem)
            continue
        if proof_pr or not statement_pr or statement not in blobs:
            continue
        if not (ROOT / proof).is_file() or not (ROOT / statement).is_file():
            recheck.append(problem)
            continue
        local = git("hash-object", f"--path={statement}", statement)[0]
        change = git("status", "--porcelain", "--", statement, proof)
        if local != blobs[statement] or change:
            recheck.append(problem)
            continue
        commit = git("log", "-1", "--format=%H", "--", proof)[0]
        source = (ROOT / proof).read_text(encoding="utf-8")
        theorem = re.findall(r"^theorem OMA\.(solution|disproof)\s*:", source, re.MULTILINE)
        if len(theorem) != 1:
            recheck.append(problem)
            continue
        ready.append({"id": problem, "statement": statement_pr, "commit": commit,
                      "polarity": "disproof" if theorem[0] == "disproof" else "proof"})
    return {"tip": tip, "ready": ready, "completed": completed, "recheck": recheck}


def proof_files(problem, tip):
    """Identify the merged statement that the checked proof actually imports."""
    if not re.fullmatch(r"oeis-a[0-9]{6}", problem):
        raise ValueError("Expected an OEIS problem ID")
    statement = f"statements/{problem}.lean"
    proof = f"proofs/{problem}.lean"
    result = {"eligible": False, "main": tip}
    if git("ls-tree", tip, "--", proof):
        return {**result, "reason": "A proof is already on upstream main"}
    entry = git("ls-tree", tip, "--", statement)
    if not entry:
        return {**result, "reason": "Waiting for the statement to merge into upstream main"}
    if not (ROOT / statement).is_file() or not (ROOT / proof).is_file():
        return {**result, "reason": "The local statement or proof is missing"}
    if git("hash-object", f"--path={statement}", statement)[0] != entry[0].split()[2]:
        return {**result, "reason": "Recheck the proof against the merged statement revision"}
    return {**result, "filesMatch": True}


def proof_readiness(problem, tip, statement_pr):
    result = proof_files(problem, tip)
    if not result.get("filesMatch"):
        return result
    statement = f"statements/{problem}.lean"
    repo_path = f"/repos/{REPO}"
    reviewed = api(f"{repo_path}/pulls/{statement_pr}") if statement_pr else {}
    if not reviewed.get("merged_at") or reviewed["base"]["ref"] != "main":
        commits = api(f"{repo_path}/commits", sha=tip, path=statement, per_page=1)
        associated = api(f"{repo_path}/commits/{commits[0]['sha']}/pulls") if commits else []
        reviewed = next((pr for pr in associated
                         if pr.get("merged_at") and pr["base"]["ref"] == "main"), {})
    if not reviewed:
        return {**result, "reason": "Waiting for a merged statement review on upstream main"}
    files = api(f"{repo_path}/pulls/{reviewed['number']}/files", per_page=100)
    if not any(file["filename"] == statement for file in files):
        return {**result, "reason": "The recorded review did not merge this statement file"}
    return {**result, "eligible": True, "statementPR": reviewed["number"],
            "mergedAt": reviewed["merged_at"]}


def review_status(pr, stage):
    if pr.get("comments"):
        comments = api(f"/repos/{REPO}/issues/{pr['number']}/comments", per_page=100)
        for comment in reversed(comments):
            if comment["user"]["login"] not in ("github-actions[bot]", "GuillaumeBAUD-coder"):
                continue
            body = comment["body"]
            if "GitHub refused the merge" in body:
                return f"{stage} accepted by checker, upstream merge pending  {comment['html_url']}", False
            verdict = re.search(r"\b(ACCEPTED|REJECTED|FAULT)\b", body)
            if verdict:
                return f"{stage} checker reported {verdict[1]}  {comment['html_url']}", verdict[1] == "REJECTED"
    return f"{stage} under review", False


def audit():
    tip = fetch_main()
    merged_paths = set(git("ls-tree", "-r", "--name-only", tip, "--", "proofs", "statements"))
    research_files = set(git("diff", "--name-only", "--diff-filter=A", BASE, "--", "proofs"))
    research_files.update(git("ls-files", "--others", "--exclude-standard", "--", "proofs"))
    register = receipts()
    issue_path = f"/repos/{REPO}/issues"
    pull_path = f"/repos/{REPO}/pulls"
    recent = api("/search/issues", q=f"repo:{REPO} author:{OWNER} is:pr", sort="created",
                 order="desc", per_page=100)
    issues = {pr["number"]: pr for pr in recent["items"]}
    needs_action = False

    for file in sorted(research_files):
        if not file.endswith(".lean"):
            continue
        problem = Path(file).stem
        state_pr, proof_pr = register.get(problem, (None, None))
        state_merged = f"statements/{problem}.lean" in merged_paths
        if not proof_pr and (state_merged or file in merged_paths):
            existing = api(pull_path, state="all", head=f"{OWNER}:codex/proof-{problem}", base="main")
            if existing:
                proof_pr = existing[0]["number"]
                print(f"{problem}  RECORD PROOF RECEIPT  {UPSTREAM}/pull/{proof_pr}")
                needs_action = True

        if proof_pr:
            pr = issues.get(proof_pr) or api(f"{issue_path}/{proof_pr}")
            files = api(f"{pull_path}/{proof_pr}/files", per_page=2)
            valid = (pr.get("user", {}).get("login") == OWNER and "pull_request" in pr
                     and len(files) == 1 and files[0]["filename"] == file)
            if not valid:
                message = "FIX PROOF RECEIPT"
                needs_action = True
            elif not state_merged:
                message = "HOLD PROOF: statement missing on upstream main"
                needs_action = True
            elif pr["pull_request"].get("merged_at") and file in merged_paths:
                credit = proof_credit(problem, proof_pr)
                if credit["status"] == "recorded":
                    message = f"accepted upstream, {credit['polarity']} credited to {credit['handle']}"
                else:
                    message = f"accepted upstream, site credit {credit['status']}"
                    needs_action |= credit["status"] == "mismatch"
            elif file in merged_paths:
                message = "resolved upstream; verify solver credit"
            elif pr["state"] == "closed":
                message = "REVIEW CLOSED PROOF"
                needs_action = True
            else:
                message, rejected = review_status(pr, "proof")
                needs_action |= rejected
            print(f"{problem}  {message}  {UPSTREAM}/pull/{proof_pr}")
        elif file in merged_paths:
            print(f"{problem}  resolved upstream by a separate submission")
        elif state_merged:
            readiness = proof_readiness(problem, tip, state_pr)
            message = "SUBMIT PROOF" if readiness["eligible"] else readiness["reason"]
            print(f"{problem}  {message}  {file}")
            needs_action = True
        elif state_pr:
            pr = issues.get(state_pr) or api(f"{issue_path}/{state_pr}")
            if pr["state"] == "open":
                message, rejected = review_status(pr, "statement")
                needs_action |= rejected
                print(f"{problem}  {message}  {UPSTREAM}/pull/{state_pr}")
            else:
                print(f"{problem}  REVIEW CLOSED STATEMENT  {UPSTREAM}/pull/{state_pr}")
                needs_action = True
        else:
            print(f"{problem}  SUBMIT OR RECORD STATEMENT  {file}")
            needs_action = True
    return int(needs_action)


if __name__ == "__main__":
    try:
        if sys.argv[1:] == ["--main"]:
            print(fetch_main())
        elif sys.argv[1:] == ["--proof-queue"]:
            print(json.dumps(proof_queue(fetch_main())))
        elif sys.argv[1:] == ["--desk-followups"]:
            print(json.dumps(desk_followups()))
        elif sys.argv[1:] == ["--statement-desk-followups"]:
            print(json.dumps(statement_desk_followups()))
        elif len(sys.argv) == 4 and sys.argv[1] == "--proof-credit":
            print(json.dumps(proof_credit(sys.argv[2], int(sys.argv[3]))))
        elif len(sys.argv) == 3 and sys.argv[1] == "--proof-files":
            problem = sys.argv[2]
            result = proof_files(problem, fetch_main())
            result["registeredStatement"] = receipts().get(problem, (None, None))[0]
            print(json.dumps(result))
        elif len(sys.argv) == 3 and sys.argv[1] == "--ready-for-proof":
            problem = sys.argv[2]
            statement_pr = receipts().get(problem, (None, None))[0]
            print(json.dumps(proof_readiness(problem, fetch_main(), statement_pr)))
        elif len(sys.argv) == 1:
            sys.exit(audit())
        else:
            sys.exit("Usage: check_submissions.py [--main | --proof-queue | --desk-followups | "
                     "--statement-desk-followups | --proof-files oeis-aNNNNNN | "
                     "--ready-for-proof oeis-aNNNNNN | --proof-credit oeis-aNNNNNN PR]")
    except (OSError, ValueError, KeyError, RuntimeError, subprocess.CalledProcessError) as error:
        sys.exit(f"Unable to verify upstream submissions: {error}")
