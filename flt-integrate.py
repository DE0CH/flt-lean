#!/usr/bin/env python3
"""Integrate an agent branch: merge, and free its slot ONLY if the merge stuck.

WHY THIS EXISTS (2026-07-25). The orchestrator freed a worktree whose branch was
not an ancestor of main THREE times in one session:

  * once for ten "orphan" worktrees that all had live uncommitted work,
  * once for flt-lean-26, whose Stage B proof was still unmerged,
  * once for flt-lean-92, whose merge had just CONFLICTED and been aborted.

Each time the pool hook caught it by hard-crashing on the next dispatch, which is
the design working -- but a freed slot with unmerged work is a lost proof if the
crash is ever "fixed" by retrying. The failure mode is always the same shape: the
free step is written as an unconditional follow-on to the merge step, so a
conflict, a bad shell quoting, or a pipeline that swallows git's exit status all
leave the branch behind while the slot is handed to someone else.

    if git merge ... | head -3; then ...   # tests head, NOT git

So: freeing is now GATED on `git merge-base --is-ancestor <branch> main`, checked
after the merge, in the same process. No ancestry, no free. That is the whole
point of the file.

    python3 flt-integrate.py flt-lean-92 "Merge flt-lean-92 -- <subject>

    <body>"

Exits nonzero and leaves the pool untouched on conflict, so the caller sees it.
"""

import json
import os
import subprocess
import sys

ROOT = "/home/chend/flt-lean"
POOL = os.path.expanduser("~/.flt-worktree-pool")
INFLIGHT = os.path.expanduser("~/.flt-inflight.jsonl")


def git(*args, check=True):
    return subprocess.run(["git", "-C", ROOT, *args], capture_output=True, text=True,
                          check=check)


def is_ancestor(branch):
    return subprocess.run(["git", "-C", ROOT, "merge-base", "--is-ancestor", branch, "main"],
                          capture_output=True).returncode == 0


def free_slot(branch):
    lines = open(POOL).read().splitlines()
    out, changed = [], False
    for line in lines:
        f = line.split()
        if f and f[0] == branch and len(f) > 1 and f[1] == "claimed":
            line, changed = f"{branch} free", True
        out.append(line)
    open(POOL, "w").write("\n".join(out) + "\n")
    recs = [json.loads(x) for x in open(INFLIGHT) if x.strip()]
    keep = [x for x in recs if x.get("worktree") != branch]
    open(INFLIGHT, "w").write("".join(json.dumps(x) + "\n" for x in keep))
    return changed, len(recs) - len(keep)


def main():
    if len(sys.argv) < 3:
        print("usage: flt-integrate.py <branch> <commit-message>", file=sys.stderr)
        return 2
    branch, message = sys.argv[1], sys.argv[2]

    ahead = int(git("rev-list", "--count", f"main..{branch}").stdout.strip())
    if ahead == 0 and is_ancestor(branch):
        print(f"{branch}: nothing to merge, already an ancestor")
    else:
        r = git("merge", "--no-ff", "-q", "-m", message, branch, check=False)
        if r.returncode != 0:
            git("merge", "--abort", check=False)
            print(f"{branch}: CONFLICT ({ahead} ahead) -- merge aborted, POOL UNTOUCHED",
                  file=sys.stderr)
            print((r.stdout + r.stderr).strip()[:600], file=sys.stderr)
            return 1
        print(f"{branch}: merged ({ahead} commits)")

    # GATE 1: no conflict markers anywhere. This catches the HAND-RESOLVE path,
    # where the merge conflicted, I resolved it by editing, and committed --
    # 2026-07-25 I committed a stray '<<<<<<< HEAD' inside a module docstring
    # because I checked the marker count after staging and read "1" as success.
    # It survived only because it sat inside a comment block. A printed number is
    # not a check; this is.
    markers = subprocess.run(
        ["git", "-C", ROOT, "grep", "-lE", r"^(<<<<<<< |>>>>>>> |=======$)", "--", "Fermat"],
        capture_output=True, text=True)
    if markers.stdout.strip():
        print(f"{branch}: CONFLICT MARKERS still present -- refusing to free:\n"
              + markers.stdout.strip(), file=sys.stderr)
        return 1

    # GATE 2. Nothing below runs unless the branch really is in main now.
    if not is_ancestor(branch):
        print(f"{branch}: NOT an ancestor of main after merge -- refusing to free",
              file=sys.stderr)
        return 1

    changed, dropped = free_slot(branch)
    print(f"{branch}: ancestor confirmed; slot {'freed' if changed else 'was not claimed'}, "
          f"{dropped} inflight record(s) dropped")
    return 0


if __name__ == "__main__":
    sys.exit(main())
