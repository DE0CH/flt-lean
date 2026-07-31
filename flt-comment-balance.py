#!/usr/bin/env python3
"""Find Lean files whose block comments do not balance.

WHY THIS EXISTS (2026-07-31, flt-lean-105, release 24/25).  A merge that
resolves a conflict inside a comment BLOCK can keep the first line of one
side's `/-- …` or `/-! …` header and the body of the other side's, dropping
the first header's `-/`.  The orphaned opener then swallows every declaration
after it, and `lake build` reports exactly one error:

    error: <file>:<EOF>:0: unterminated comment

with no indication of where the comment started.  Downstream modules then fail
on names that "do not exist".  Four files were damaged this way in one release
(`IsogenyTrace`, `MordellWeil19`, `EllipticScheme`, `AmpleSheaf`), and because
the build stops at the first failing module in dependency order, each one costs
a whole release-build round to discover.  This script finds all of them at once,
in seconds, without building.

    python3 flt-comment-balance.py [ROOT]        # default ROOT = Fermat

Output: one line per suspicious file, `<path> depth=<d> unclosed_at=<lines>`.

READ THE OUTPUT AS FOLLOWS.

*   `depth > 0` is the real signal, and `unclosed_at` names the opener Lean
    will choke on.  Every instance found so far had the same repair: the
    orphaned header line is a RENAMED-AND-MOVED copy of a block that still
    exists elsewhere in the file (grep its title), so DELETE the stranded line
    rather than closing it with `-/`.
*   `depth < 0` is NOISE, not a finding.  The scanner is a two-character
    matcher and Lean's lexer is not: a `-/` occurring inside prose, or a `/-`
    the scanner counts and Lean does not, desynchronises it.  A file Lean
    accepts can score negative here.  Do not "fix" a negative; confirm with
    `lake env lean` first.

So: `depth > 0` is worth acting on before a build, `depth < 0` is worth
ignoring.  The check costs nothing and belongs in a release preflight.
"""

import os
import sys


def scan(path):
    """Return (final_depth, [line numbers of unclosed openers])."""
    with open(path, encoding="utf-8") as f:
        src = f.read()
    i, n, depth, line = 0, len(src), 0, 1
    starts = []
    while i < n:
        c = src[i]
        if c == "\n":
            line += 1
        if depth == 0:
            # String literals and `--` line comments only shadow `/-` outside
            # a block comment; inside one, Lean treats neither specially.
            if c == '"':
                i += 1
                while i < n and src[i] != '"':
                    if src[i] == "\\":
                        i += 1
                    if i < n and src[i] == "\n":
                        line += 1
                    i += 1
                i += 1
                continue
            if src.startswith("--", i):
                while i < n and src[i] != "\n":
                    i += 1
                continue
        if src.startswith("/-", i):
            depth += 1
            starts.append(line)
            i += 2
            continue
        if src.startswith("-/", i):
            depth -= 1
            if starts:
                starts.pop()
            i += 2
            continue
        i += 1
    return depth, starts


def main():
    root = sys.argv[1] if len(sys.argv) > 1 else "Fermat"
    hits = 0
    for dirpath, _, filenames in os.walk(root):
        for name in sorted(filenames):
            if not name.endswith(".lean"):
                continue
            path = os.path.join(dirpath, name)
            depth, starts = scan(path)
            if depth != 0:
                hits += 1
                print(f"{path} depth={depth} unclosed_at={starts}")
    if hits == 0:
        print(f"{root}: all block comments balance")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
