#!/usr/bin/env python3
"""Carry a NEWER downstream declaration body up to its duplicated upstream copy.

    transplant.py <downstream.lean> <upstream.lean> <qualified-name> [...] [--apply]

When a hoist lands the upstream copies but not its own deletions, later branches
go on improving the DOWNSTREAM copy -- which is the one their call sites see --
so by the time anyone notices, the upstream copy is a stale snapshot and the
downstream one carries the proof.  Deleting the downstream copy to clear the
`has already been declared` error would then silently revert that proof to the
upstream `sorry`.

This moves the newer body up first, so the subsequent deletion is lossless.  It
is only safe when the newer body is self-contained upstream -- every constant it
names must be declared in the upstream file BEFORE the copy, or in that file's
import cone -- which is a per-declaration judgement, so the names are given
explicitly rather than inferred.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import blocks


def index(path):
    lines, bs = blocks.blocks(path)
    out = {}
    for (n, q, a, b, d) in bs:
        if q:
            out.setdefault(q, (a, b, d))
    return lines, out


def main(argv):
    apply = '--apply' in argv
    argv = [a for a in argv if a != '--apply']
    down, up, names = argv[0], argv[1], argv[2:]
    dlines, didx = index(down)
    ulines, uidx = index(up)

    edits = []
    for q in names:
        if q not in didx:
            sys.exit('not declared in %s: %s' % (down, q))
        if q not in uidx:
            sys.exit('not declared in %s: %s' % (up, q))
        da, db, dd = didx[q]
        ua, ub, ud = uidx[q]
        edits.append((ua, ub, dlines[da:db], q))
        print('%s\n    %s:%d..%d (%d lines)  ->  %s:%d..%d (%d lines)'
              % (q, os.path.basename(down), da + 1, db, db - da,
                 os.path.basename(up), ua + 1, ub, ub - ua))

    if not apply:
        return
    out = list(ulines)
    for (ua, ub, text, q) in sorted(edits, reverse=True):
        out[ua:ub] = text
    open(up, 'w', encoding='utf-8').write('\n'.join(out))
    print('APPLIED: %s %d -> %d lines' % (os.path.basename(up), len(ulines), len(out)))


main(sys.argv[1:])
