#!/usr/bin/env python3
"""Apply several PURE BLOCK MOVES to one file, atomically, in ORIGINAL coordinates.

    blockmove.py <file> START:END:DEST [START:END:DEST ...]

All line numbers are 1-indexed, inclusive, and refer to the file AS IT IS ON DISK
before any move -- so the moves do not have to be ordered and cannot invalidate
each other's indices.  Each block is removed from its position and re-inserted
immediately BEFORE the original line DEST.

A pure move is a PERMUTATION of the file's lines, so the receipt is exact:
the sorted multiset of lines must be unchanged.  This script checks that itself
and refuses to write if it is not.  (CLAUDE.md: "verify a BLOCK MOVE inside a
file: sort both versions and diff".)
"""
import sys
from collections import Counter

def main():
    path = sys.argv[1]
    specs = []
    for a in sys.argv[2:]:
        s, e, d = (int(x) for x in a.split(':'))
        assert s <= e, a
        assert not (s <= d <= e + 1), f"{a}: destination inside (or adjacent to) its own block"
        specs.append((s, e, d))
    src = open(path, encoding='utf-8').read().split('\n')
    n = len(src)
    for s, e, d in specs:
        assert 1 <= s <= e <= n and 1 <= d <= n + 1, (s, e, d, n)
    # overlapping blocks are a bug, not a feature
    covered = set()
    for s, e, _ in specs:
        rng = set(range(s, e + 1))
        assert not (rng & covered), "overlapping blocks"
        covered |= rng
    ins = {}
    for s, e, d in specs:
        ins.setdefault(d, []).extend(src[s - 1:e])
    out = []
    for i in range(1, n + 1):
        out.extend(ins.get(i, []))
        if i not in covered:
            out.append(src[i - 1])
    out.extend(ins.get(n + 1, []))
    assert Counter(out) == Counter(src), "NOT A PERMUTATION -- refusing to write"
    assert len(out) == n
    open(path, 'w', encoding='utf-8').write('\n'.join(out))
    print(f"{path}: {len(specs)} block(s) moved, {n} lines, permutation verified")

main()
