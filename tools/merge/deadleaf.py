#!/usr/bin/env python3
"""deadleaf.py — list the OPEN leaves that NOTHING CONSUMES.

WHY THIS EXISTS (2026-08-01, flt-lean-400).

Every frontier instrument in this project answers "is this leaf OPEN?".  None of
them answers "is it REACHABLE?", and the two come apart constantly:

  * a hoist puts a leaf DOWNSTREAM of the consumer it was cut for, so the
    consumer can never cite it (this is how `flt-lean-400` was dispatched at
    `exists_localInertia_subgroup_relIndex_dvd_twelve_of_padicValRat_j_nonneg`,
    which had ZERO consumers anywhere while its consumer sat upstream, still
    open, in a module the leaf's own file `public import`s);
  * a rival cut lands beside the winner and its residue is orphaned;
  * a `DELETE x REFACTOR` merge removes the only consumer.

In all three the leaf compiles, emits `declaration uses 'sorry'`, is counted by
`flt-frontier.py` and by the census, and passes every ownership check — and
closing it moves the count and not the project.  Measured on `main` at
2026-08-01: **36 of 378 open leaves, ~10%, have no consumer at all.**

USAGE

    python3 tools/merge/deadleaf.py                 # from the repo root
    python3 tools/merge/deadleaf.py --root DIR      # or point it somewhere else

TWO THINGS IT GETS RIGHT THAT A HAND-ROLLED SCAN GETS WRONG

1.  **DOT NOTATION.**  The obvious use-site regex excludes a preceding `.` so
    that `Foo.bar` is not counted as a use of `bar`.  In this project the
    commonest call shape is exactly `E.some_theorem h₁ h₂`, so that exclusion
    hides most real consumers.  The first run of this scan reported
    `det_galoisRep_five_eq_one_of_mem_localInertiaGroup` as consumerless while
    it is used, as `E.det_galoisRep_five_eq_one_of_mem_localInertiaGroup`, 400
    lines below its own declaration.  Match the SHORT name with no
    lookbehind on `.`.

2.  **COMMENTS.**  This tree's docstrings name other declarations constantly, so
    an unstripped grep reports almost nothing as dead.  Block comments nest.

WHAT IT DOES NOT DO, AND YOU MUST NOT READ THE OUTPUT AS COMPLETE

  * It is ONE HOP.  A leaf whose only consumer is itself consumerless is dead
    too and will not appear here — see the standing rule that a consumer scan
    must be a FIXPOINT.  So the count is a LOWER BOUND.
  * It says nothing about the root cone: a leaf with consumers can still be
    free-floating.  `ProgressCensus.lean` answers that and this does not.
  * A hit is a HYPOTHESIS.  Before acting, read the leaf's docstring for the
    consumer it names and check the import direction:

        grep -n 'import Fermat.FLT.<consumer module>' <the leaf's module>

    A hit there means the consumer is UPSTREAM, the leaf is stranded rather than
    garbage, and the repair is a HOIST of the leaf to just above its consumer —
    NOT the deletion the dead-leaf rule otherwise prescribes.
"""

import argparse
import os
import re
import sys

DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+)*"
    r"(?:theorem|lemma)\s+([^\s({\[:]+)"
)
SORRY = re.compile(r"(?<![A-Za-z_])sorry(?![A-Za-z_0-9])")


def strip_comments(s: str) -> str:
    """Blank out `--` line comments and NESTING `/- -/` blocks, keeping newlines."""
    out = []
    i = 0
    depth = 0
    while i < len(s):
        if depth == 0 and s.startswith("--", i) and not s.startswith("-/", i):
            j = s.find("\n", i)
            if j < 0:
                break
            i = j
            continue
        if s.startswith("/-", i):
            depth += 1
            i += 2
            out.append("  ")
            continue
        if s.startswith("-/", i):
            if depth > 0:
                depth -= 1
            i += 2
            out.append("  ")
            continue
        out.append(" " if (depth > 0 and s[i] != "\n") else s[i])
        i += 1
    return "".join(out)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=None,
                    help="repository root (default: the repo this script lives in)")
    ap.add_argument("--quiet", action="store_true", help="print only the hits")
    args = ap.parse_args()

    root = args.root or os.path.dirname(
        os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    src = os.path.join(root, "Fermat")
    if not os.path.isdir(src):
        print(f"deadleaf: no {src}", file=sys.stderr)
        return 2

    files = []
    for dp, _, fns in os.walk(src):
        for fn in fns:
            if fn.endswith(".lean"):
                files.append(os.path.join(dp, fn))

    # `SorryGate.lean` carries the token inside a STRING LITERAL in its `elab`.
    stripped = {f: strip_comments(open(f, encoding="utf-8").read()) for f in files}

    leaves = []
    seen = set()
    for f, text in stripped.items():
        if os.path.basename(f) == "SorryGate.lean":
            continue
        cur = None
        for i, line in enumerate(text.split("\n")):
            m = DECL.match(line)
            if m:
                cur = (m.group(1), i + 1)
            if cur and SORRY.search(line) and (f, cur[0]) not in seen:
                seen.add((f, cur[0]))
                leaves.append((f, cur[0], cur[1]))

    dead = []
    for f, name, line in leaves:
        short = name.split(".")[-1]
        if not short:
            continue
        pat = re.compile(r"(?<![A-Za-z0-9_])" + re.escape(short) + r"(?![A-Za-z0-9_'])")
        uses = 0
        for g, text in stripped.items():
            n = len(pat.findall(text))
            if g == f:
                n -= 1                      # its own declaration
            uses += max(n, 0)
        if uses <= 0:
            dead.append((f, name, line))

    if not args.quiet:
        print(f"open leaves scanned : {len(leaves)}")
        print(f"CONSUMERLESS (1 hop): {len(dead)}   [LOWER BOUND — not a fixpoint]")
    for f, name, line in sorted(dead):
        print(f"{os.path.relpath(f, root)}:{line}\t{name}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
