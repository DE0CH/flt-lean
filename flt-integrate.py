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

import importlib.util
import json
import pathlib
import re
import os
import subprocess
import sys

ROOT = "/home/chend/flt-lean"
# Branches merge into STAGING, not main (Deyao, 2026-07-25). main is the last
# commit known to BUILD; staging is the integration queue. The staging worker
# builds staging, fixes what is red, and promotes to main only on a green build.
# The orchestrator never builds -- a full cone build costs hours and would make
# integration the fleet's bottleneck.
TARGET_BRANCH = "staging"
POOL = os.path.expanduser("~/.flt-worktree-pool")
INFLIGHT = os.path.expanduser("~/.flt-inflight.jsonl")


def git(*args, check=True):
    return subprocess.run(["git", "-C", ROOT, *args], capture_output=True, text=True,
                          check=check)


def is_ancestor(branch, onto=None):
    onto = onto or TARGET_BRANCH
    return subprocess.run(["git", "-C", ROOT, "merge-base", "--is-ancestor", branch, onto],
                          capture_output=True).returncode == 0


DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|class)\s+"
    r"([^\s:{\[(]+)")
NS_OPEN = re.compile(r"^namespace\s+(\S+)")
SECTION = re.compile(r"^section\b")
NS_END = re.compile(r"^end(?:\s+(\S+))?\s*$")

# Comment/string stripping is shared with flt-frontier.py rather than
# reimplemented: the first draft of this gate skipped it and immediately produced
# a false positive, reporting `GaloisRepresentation.map` twice because a
# DOCSTRING line happened to begin "structure map -- impossible in the nontrivial
# k". A gate that cries wolf gets switched off, so it must see only code.
_frontier_spec = importlib.util.spec_from_file_location(
    "flt_frontier", os.path.join(ROOT, "flt-frontier.py"))
_frontier = importlib.util.module_from_spec(_frontier_spec)
_frontier_spec.loader.exec_module(_frontier)
strip_noncode = _frontier.strip_noncode


def sorry_set():
    """{name: path} for every DIRECT sorry in the working tree right now."""
    out = {}
    for path in sorted((pathlib.Path(ROOT) / "Fermat").rglob("*.lean")):
        for name, _ in _frontier.scan(path):
            out[name] = str(path.relative_to(ROOT))
    return out


def touched_lean_files(branch):
    """.lean files this branch changed relative to the merge base."""
    base = subprocess.run(["git", "-C", ROOT, "merge-base", TARGET_BRANCH, branch],
                          capture_output=True, text=True).stdout.strip()
    if not base:
        return []
    out = git("diff", "--name-only", base, branch, check=False).stdout
    return [p for p in out.splitlines() if p.endswith(".lean")]


def duplicate_decls(paths):
    """[(path, fullname, [lines])] for names declared more than once in one file.

    Namespaces are tracked so that `A.foo` and `B.foo` are distinct -- otherwise
    this gate would fire constantly on a codebase that reuses short lemma names
    across namespaces, and a gate that cries wolf gets removed. Only an exact
    full-name collision inside ONE file is reported, which is exactly what Lean
    rejects with "has already been declared". `instance` is deliberately absent
    from DECL: instances are routinely anonymous, and Lean generates fresh names
    for those, so they cannot collide this way."""
    found = []
    for rel in paths:
        full = os.path.join(ROOT, rel)
        if not os.path.exists(full):
            continue
        text = strip_noncode(
            open(full, encoding="utf-8", errors="replace").read())
        seen = {}
        # `section` is pushed as well as `namespace`, with an empty name. Both
        # are closed by `end`, so tracking only namespaces made a section's `end`
        # pop the enclosing namespace and mislabel every declaration after it.
        stack = []
        for lineno, line in enumerate(text.splitlines(), 1):
            m = NS_OPEN.match(line)
            if m:
                stack.append(m.group(1))
                continue
            if SECTION.match(line):
                stack.append("")
                continue
            if NS_END.match(line):
                if stack:
                    stack.pop()
                continue
            m = DECL.match(line)
            if m:
                name = ".".join([s for s in stack if s] + [m.group(1)])
                seen.setdefault(name, []).append(lineno)
        for name, lines in seen.items():
            if len(lines) > 1:
                found.append((rel, name, lines))
    return found


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

    on = git("rev-parse", "--abbrev-ref", "HEAD").stdout.strip()
    if on != TARGET_BRANCH:
        print(f"refusing to integrate: {ROOT} is checked out on '{on}', not "
              f"'{TARGET_BRANCH}'. Merging into the wrong branch is the one "
              f"mistake this script cannot undo for you.", file=sys.stderr)
        return 2

    before = sorry_set()
    ahead = int(git("rev-list", "--count", f"{TARGET_BRANCH}..{branch}").stdout.strip())
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

    # SORRY-SET DELTA. Reported, not gated -- a leaf legitimately disappears every
    # time a branch proves one, so this cannot be a pass/fail test. It is printed
    # because a CLEAN `git merge` EXIT IS NOT EVIDENCE OF A CORRECT MERGE: on
    # 2026-07-26 an auto-merge of MazurTorsion.lean reported no conflict and exit 0
    # while producing a stale mixture -- 27 sorries against main's 28, having
    # silently DROPPED three leaves main had and RESURRECTED two the branch had
    # already retired. Nothing else we run would have caught it; the agent found it
    # only by diffing the sorry set by hand. So: read this delta against what the
    # branch actually claimed. Disappearances it did not claim to prove, and
    # reappearances of names you remember closing, are the signature.
    after = sorry_set()
    gone = sorted(set(before) - set(after))
    new = sorted(set(after) - set(before))
    print(f"{branch}: direct sorries {len(before)} -> {len(after)}")
    for n in gone:
        print(f"    -{n}")
    for n in new:
        print(f"    +{n}  ({after[n]})")

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

    # GATE 1b: no declaration declared twice in a file this merge touched.
    #
    # This is THE most common way main goes red (three independent reports on
    # 2026-07-25 alone, for one lemma). Two owners prove the same lemma with
    # byte-identical statements in disjoint regions of a 10k-line file; git sees
    # non-overlapping hunks and merges both cleanly; Lean rejects the file with
    # "has already been declared". Every contributing worktree was green.
    #
    # It is invisible to every other check we have: no `sorry` token, no
    # `declaration uses 'sorry'` warning, so neither the direct-sorry scan nor
    # the census sees it -- yet the module produces no olean and silently blocks
    # its whole downstream cone. Only a build finds it, and a build costs hours.
    # This costs milliseconds and catches it at the merge that creates it.
    dupes = duplicate_decls(touched_lean_files(branch))
    if dupes:
        print(f"{branch}: DUPLICATE DECLARATIONS after merge -- refusing to free:",
              file=sys.stderr)
        for path, name, lines in dupes:
            print(f"  {path}: `{name}` declared at lines "
                  + ", ".join(str(n) for n in lines), file=sys.stderr)
        print("  (Lean will reject these files. Delete the redundant copy -- keep "
              "the one declared FIRST, since later uses may already resolve to it "
              "-- then re-run.)", file=sys.stderr)
        return 1

    # GATE 2. Nothing below runs unless the branch really is in main now.
    if not is_ancestor(branch):
        print(f"{branch}: NOT an ancestor of {TARGET_BRANCH} after merge -- refusing to free",
              file=sys.stderr)
        return 1

    changed, dropped = free_slot(branch)
    print(f"{branch}: ancestor confirmed; slot {'freed' if changed else 'was not claimed'}, "
          f"{dropped} inflight record(s) dropped")

    # PUSH (Deyao, 2026-07-24; re-issued 2026-07-25 because the orchestrator
    # drifted off it again). A reminder in the merge hook was not enough -- the
    # only reliable push is one nobody has to remember. An unpushed merge lives
    # on exactly one disk, and since every worktree fast-forwards from main at
    # dispatch, it is also invisible to the next agent allocated.
    #
    # NON-FATAL: the merge already succeeded and the slot is already freed. A
    # failed push must be loud but must not make the caller think integration
    # failed and retry it.
    push = git("push", "origin", TARGET_BRANCH, check=False)
    if push.returncode != 0:
        print(f"{branch}: PUSH FAILED (merge stands, slot freed) -- push by hand:\n"
              + (push.stdout + push.stderr).strip()[:400], file=sys.stderr)
    else:
        print(f"{branch}: pushed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
