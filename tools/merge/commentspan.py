#!/usr/bin/env python3
"""Find SWALLOWED CODE: block comments that contain top-level declarations.

`flt-comment-balance.py` and `tools/merge/scopecheck.py` catch the two loud
shapes of merge damage to comments — a file whose nesting depth ends non-zero
(an unterminated opener) and a stray `-/` at depth zero.  Both are blind to the
shape that costs the most, because it CANCELS:

    /--  <- orphaned opener left by a merge (a truncated docstring header)
    ...  thousands of lines of real declarations ...
    ... -/   <- the closer of some LATER declaration's docstring

Lean block comments NEST, so every well-formed docstring in between raises and
lowers the depth again and the file still balances to zero.  Lean reports no
`unterminated comment`; it reports nothing at all.  The declarations in between
simply do not exist, and the only symptom is `unknown identifier` at their use
sites — often in a DIFFERENT module, thousands of lines away.

THE DETECTOR: a legitimate docstring, however long this project writes them,
never contains a line that begins a TOP-LEVEL DECLARATION at column 0.  A block
comment that does is a swallow.  This separates the two cases exactly, where
span length alone does not: measured on this tree at 2026-07-31, thresholding on
span > 400 lines gives 21 reports of which most are honest 400–800 line module
essays, while thresholding on "contains declarations" gives the wounds and
nothing else.

Usage:
    python3 tools/merge/commentspan.py                    # whole tree
    python3 tools/merge/commentspan.py Fermat/FLT/X.lean  # one file
    python3 tools/merge/commentspan.py --list             # name the swallowed decls

Exit status is 1 if anything is reported, 0 otherwise.
"""

import argparse
import os
import re
import sys

SKIP = {"Fermat/SorryGate.lean"}  # comment tokens inside string literals

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+|partial\s+|unsafe\s+)*"
    r"(theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+\S"
)


def spans(text):
    """Return ([(open_line, close_line, depth)], [unclosed_open_lines])."""
    stack = []
    out = []
    i = 0
    line = 1
    n = len(text)
    while i < n:
        if text[i] == "\n":
            line += 1
            i += 1
            continue
        if text[i : i + 2] == "/-":
            stack.append(line)
            i += 2
            continue
        if text[i : i + 2] == "-/":
            if stack:
                out.append((stack.pop(), line, len(stack) + 1))
            i += 2
            continue
        if not stack and text[i : i + 2] == "--":
            j = text.find("\n", i)
            i = j if j >= 0 else n
            continue
        i += 1
    return out, stack


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("paths", nargs="*", help="files to scan (default: all of Fermat/)")
    ap.add_argument("--list", action="store_true",
                    help="print the swallowed declaration lines")
    args = ap.parse_args()

    paths = args.paths
    if not paths:
        paths = []
        for root, _, files in os.walk("Fermat"):
            for f in files:
                if f.endswith(".lean"):
                    p = os.path.join(root, f)
                    if p not in SKIP:
                        paths.append(p)
        paths.sort()

    bad = 0
    for p in paths:
        try:
            text = open(p, encoding="utf-8").read()
        except OSError as e:
            print(f"{p}: CANNOT READ: {e}")
            bad += 1
            continue
        lines = text.split("\n")
        found, unclosed = spans(text)
        # only report the OUTERMOST offending comment of each nest
        for op, cl, depth in sorted(found):
            if depth != 1:
                continue
            swallowed = [(i + 1, lines[i]) for i in range(op, cl - 1)
                         if DECL.match(lines[i])]
            if swallowed:
                print(f"{p}:{op}: SWALLOW — block comment closing at :{cl} "
                      f"({cl - op} lines) contains {len(swallowed)} top-level "
                      f"declaration(s), the first at :{swallowed[0][0]}")
                bad += 1
                if args.list:
                    for ln, src in swallowed:
                        print(f"    :{ln}  {src[:96]}")
        for op in unclosed:
            print(f"{p}:{op}: UNTERMINATED block comment (never closed)")
            bad += 1

    if bad:
        print(f"\n{bad} report(s). Open the reported line: the tell for merge damage "
              f"is a docstring header that stops mid-sentence with another `/-`, `/-!` "
              f"or `/--` immediately below it. Repair by DELETING the stranded opener "
              f"(the real docstring usually survives further down) — and then look for "
              f"the mirror half, a `-/` that has just become stray.")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
