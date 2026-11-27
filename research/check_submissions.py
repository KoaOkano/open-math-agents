"""Check upstream receipts for every proof added on the research branch."""

import json
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path
from urllib.parse import urlencode


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


def receipts():
    rows = {}
    for line in (ROOT / "research/README.md").read_text(encoding="utf-8").splitlines():
        match = re.fullmatch(r"\| (A\d{6}) \| ([^|]*) \| ([^|]*) \|", line)
        if match:
            numbers = []
            for cell in match.groups()[1:]:
                link = re.search(re.escape(f"{UPSTREAM}/pull/") + r"(\d+)\)", cell)
                numbers.append(int(link[1]) if link else None)
            rows["oeis-" + match[1].lower()] = numbers
    return rows


def fetch_main():
    remote = UPSTREAM + ".git"
    tip = git("ls-remote", "--exit-code", remote, "refs/heads/main")[0].split()[0]
    for attempt in range(3):
        present = subprocess.run(["git", "-C", ROOT, "cat-file", "-e", f"{tip}^{{commit}}"],
                                 stderr=subprocess.DEVNULL)
        if present.returncode == 0:
            return tip
        fetched = subprocess.run(["git", "-C", ROOT, "fetch", "--quiet", "--depth=1", "--no-tags",
                                  "--no-write-fetch-head", remote, tip], capture_output=True, text=True)
        if fetched.returncode == 0:
            return tip
        if attempt == 2 or not ("shallow" in fetched.stderr or "lock" in fetched.stderr):
            raise RuntimeError(fetched.stderr.strip() or "Unable to fetch upstream main")
        time.sleep(attempt + 1)


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
                message = "accepted upstream"
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
            sys.exit("Usage: check_submissions.py [--ready-for-proof oeis-aNNNNNN]")
    except (OSError, ValueError, KeyError, RuntimeError, subprocess.CalledProcessError) as error:
        sys.exit(f"Unable to verify upstream submissions: {error}")
