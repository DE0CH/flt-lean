#!/usr/bin/env python3
"""Find Lean block comments that are IMPLAUSIBLY LONG, and stray terminators.

WHY THIS EXISTS (2026-07-31, `flt-lean-361`, release 27).  `flt-comment-balance.py`
finds a comment that never closes — `depth > 0` at EOF, which Lean reports as
`unterminated comment`.  It cannot find the defect that actually blocked release
27, because that one BALANCES:

    a merge spliced a duplicated `/-- …` docstring header into the middle of
    another docstring.  The extra OPENER ran the comment 1214 lines past its
    intended end, swallowing **45 top-level declarations**; a later stray `-/`
    (itself the residue of a different orphaned block) closed it again, so the
    file's total depth was 0 and every existing check was silent.

Symptoms, none of which name a comment: a shower of `Unknown identifier` and
`Function expected at` for names that are visibly present in the source, plus
`(kernel) declaration has metavariables` and `Ambiguous term` downstream.  A
reader chases a rename, a merge-side removal, or a missing import, and none of
those is the cause.  See CLAUDE.md, "AN ORPHANED OPENER CAN SCORE ZERO".

The signal is blunt and it works: **a 1200-line comment in a Lean file is never
intentional**, and unlike the depth check it points straight at its own opener.

    python3 tools/merge/longcomment.py [ROOT] [--min N] [--damage-only]

`ROOT` defaults to `Fermat` (a single file also works); `--min` defaults to 400
lines.  Each long block is reported with the number of DOC-COMMENT OPENERS at
column 0 found inside it, and that count is the damage signal.

Reading the output:

*   `DAMAGE: n nested doc-opener(s)` means a merge spliced a header into the
    middle of a comment.  Find it (it usually duplicates a header appearing
    elsewhere in the file — grep its first line) and DELETE the duplicate.  Do
    not close it with a terminator; that leaves the declarations commented out.
*   A long block with no nested opener is a genuine docstring.  `X0.lean` has one
    of 1147 lines (`exists_gamma0Rigidification_of_rigidifiedModuli_motive`), so
    a plain run needs one eyeball per hit; `--damage-only` suppresses them.
*   STRAY TERMINATORS (a `-/` seen at depth 0) are reported separately.  Each one
    is the end of an ORPHANED PROSE block whose opener a merge dropped, i.e.
    English being parsed as Lean.  Repair by reopening the block as a PLAIN `/-`
    comment, not as a docstring — the text usually documents a declaration other
    than the one that follows it, and reuniting them is an author's call.

TRAP, and it cost a round: do not write a literal comment delimiter inside a
comment when you annotate one of these repairs.  It closes the comment and
recreates the defect.  Say "terminator" / "delimiter" in prose instead.
"""

import os
import re
import sys

# A doc-comment opener at column 0 INSIDE another comment.  This, not a count of
# declaration-looking lines, is the reliable damage signal: it is what a merge
# leaves behind when it splices a duplicated header into an existing docstring,
# and it was present in both instances found so far (X0.lean:81078,
# Interface.lean:39953).  Counting `^theorem`-looking lines instead gives false
# positives on every long docstring in this tree, because the prose quotes Lean
# constantly and sentences begin "theorem …", "lemma …", "class …" at column 0.
NESTED_DOC = re.compile(r"^/-[-!]")


def scan(path, minlen):
    """Return ([(open_line, close_line, n_nested_doc_openers)], [stray lines])."""
    with open(path, encoding="utf-8") as f:
        lines = f.read().split("\n")
    depth, opens, longs, strays = 0, [], [], []
    for n, line in enumerate(lines, 1):
        i = 0
        while i < len(line):
            # Outside a block comment, a string literal shadows `/-` and `-/`.
            # Skipping it is not optional: `Interface.lean` contains string
            # literals holding comment delimiters, and without this the scanner
            # pairs a real docstring with a terminator 41 000 lines away and
            # reports 644 phantom swallowed declarations in a module that builds.
            if depth == 0 and line[i] == '"':
                i += 1
                while i < len(line) and line[i] != '"':
                    i += 2 if line[i] == "\\" else 1
                i += 1
                continue
            if line.startswith("/-", i):
                depth += 1
                opens.append(n)
                i += 2
            elif line.startswith("-/", i):
                if depth > 0:
                    depth -= 1
                    start = opens.pop()
                    if n - start >= minlen:
                        nested = sum(
                            1 for l in lines[start:n - 1] if NESTED_DOC.match(l)
                        )
                        longs.append((start, n, nested))
                else:
                    strays.append(n)
                i += 2
            elif depth == 0 and line.startswith("--", i):
                break
            else:
                i += 1
    return longs, strays


def main():
    args = [a for a in sys.argv[1:]]
    minlen = 400
    quiet = "--damage-only" in args
    if "--min" in args:
        k = args.index("--min")
        minlen = int(args[k + 1])
        del args[k:k + 2]
    args = [a for a in args if not a.startswith("--")]
    root = args[0] if args else "Fermat"

    paths = []
    if os.path.isfile(root):
        paths = [root]
    else:
        for dirpath, _, filenames in os.walk(root):
            for name in sorted(filenames):
                if name.endswith(".lean"):
                    paths.append(os.path.join(dirpath, name))

    hits = 0
    for path in paths:
        longs, strays = scan(path, minlen)
        for start, end, nested in longs:
            if quiet and not nested:
                continue
            hits += 1
            flag = f"  <-- DAMAGE: {nested} nested doc-opener(s)" if nested else ""
            print(f"{path} comment {start}-{end} ({end - start} lines){flag}")
        for line in strays:
            hits += 1
            print(f"{path} STRAY TERMINATOR at {line} (orphaned prose block ends here)")
    if hits == 0:
        print(f"{root}: no long comments (>= {minlen} lines) and no stray terminators")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
