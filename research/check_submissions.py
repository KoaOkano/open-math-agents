"""Check upstream receipts for every proof added on the research branch."""

import json
import re
import subprocess
import sys
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
    url = "https://api.github.com" + path + "?" + urlencode(params)
    data = subprocess.check_output(["curl", "--fail", "--silent", "--show-error",
                                    "--max-time", "30", url])
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
    git("fetch", "--quiet", "--no-tags", "--depth=1", UPSTREAM + ".git", "refs/heads/main")
    merged_paths = set(git("ls-tree", "-r", "--name-only", "FETCH_HEAD", "--", "proofs", "statements"))
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
        elif state_merged or not (ROOT / "statements" / f"{problem}.lean").exists():
            print(f"{problem}  SUBMIT PROOF  {file}")
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
        sys.exit(audit())
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        sys.exit(f"Unable to verify upstream submissions: {error}")
