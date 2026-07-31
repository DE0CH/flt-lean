#!/usr/bin/env python3
"""Resolve a conflicted NON-Lean text file (CLAUDE.md, memory/*.md, MEMORY.md)
by taking the UNION of both sides of every conflict hunk.

These files are append-mostly prose: CLAUDE.md gains sections, MEMORY.md gains
index lines, memory/*.md are whole new files.  Both sides' additions are wanted
in every case observed so far, and neither can make the Lean build red -- so the
union is the cheap correct resolution and there is nothing to judge.

Usage: resolve_text.py <file>...
Prints one line per file with the number of hunks unioned.
"""
import sys

def resolve(path):
    with open(path, encoding="utf-8") as fh:
        lines = fh.readlines()
    out, ours, theirs = [], [], []
    # state: 0 = normal, 1 = inside <<<<<<< (ours), 2 = inside ======= (theirs)
    state, hunks = 0, 0
    for ln in lines:
        if state == 0:
            if ln.startswith("<<<<<<<"):
                state, ours, theirs = 1, [], []
            else:
                out.append(ln)
        elif state == 1:
            if ln.startswith("|||||||"):
                state = 3            # diff3 base section: discard it
            elif ln.startswith("======="):
                state = 2
            else:
                ours.append(ln)
        elif state == 3:
            if ln.startswith("======="):
                state = 2
        elif state == 2:
            if ln.startswith(">>>>>>>"):
                out.extend(ours)
                # only append theirs' lines that ours does not already carry,
                # so a hunk where both sides made the SAME edit is not doubled
                ourset = set(x.rstrip("\n") for x in ours)
                extra = [x for x in theirs if x.rstrip("\n") not in ourset]
                out.extend(extra)
                hunks += 1
                state = 0
            else:
                theirs.append(ln)
    if state != 0:
        print(f"  {path}: UNTERMINATED conflict, left alone", file=sys.stderr)
        return -1
    with open(path, "w", encoding="utf-8") as fh:
        fh.writelines(out)
    return hunks

if __name__ == "__main__":
    for p in sys.argv[1:]:
        n = resolve(p)
        print(f"  union {p}: {n} hunk(s)")
