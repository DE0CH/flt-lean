#!/usr/bin/env python3
"""Remove the DOWNSTREAM copies of cross-file duplicate declarations.

    dedup_cross.py <downstream.lean> <upstream.lean> [<upstream.lean> ...] [--apply]

A hoist that adds the upstream copies but never lands its own deletions leaves
every hoisted name declared TWICE inside one import cone -- `has already been
declared`, and no per-file check sees it (`xdup.py` is the one that does).  The
repair is to delete the copy in the module that does the IMPORTING.

Only blocks whose bodies AGREE are deleted.  Whitespace and comments are
normalised away before comparing, so reflowed docstrings and re-indented proofs
still count as agreement; anything else is reported for a decision and left in
place, because a downstream copy that was IMPROVED after the hoist is real work
and deleting it silently reverts it.
"""
import sys, os, collections
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
    argv = [a for a in argv if a not in ('--apply', '--all')]
    down, ups = argv[0], argv[1:]
    dlines, didx = index(down)
    uidx = {}
    for u in ups:
        ulines, ui = index(u)
        for q, v in ui.items():
            uidx.setdefault(q, (u, ulines, v))

    same, diff = [], []
    for q, (a, b, d) in sorted(didx.items(), key=lambda kv: kv[1][0]):
        if q not in uidx:
            continue
        umod, ulines, (ua, ub, ud) = uidx[q]
        dn = blocks.norm(dlines, a, b)
        un = blocks.norm(ulines, ua, ub)
        (same if dn == un else diff).append((q, a, b, d, umod, ua, ub, ud, dn, un))

    print('duplicated names present in both: %d' % (len(same) + len(diff)))
    print('  identical bodies : %d' % len(same))
    print('  DIFFERING bodies : %d' % len(diff))
    for (q, a, b, d, umod, ua, ub, ud, dn, un) in diff:
        print('    DIFF %-70s %s:%d  vs  %s:%d  (%d vs %d norm chars)'
              % (q, os.path.basename(down), d + 1, os.path.basename(umod), ud + 1,
                 len(dn), len(un)))

    if os.environ.get('DEDUP_DUMP'):
        import subprocess, tempfile
        for (q, a, b, d, umod, ua, ub, ud, dn, un) in diff:
            f1 = tempfile.NamedTemporaryFile('w', suffix='.down', delete=False)
            f2 = tempfile.NamedTemporaryFile('w', suffix='.up', delete=False)
            f1.write('\n'.join(dlines[a:b]) + '\n'); f1.close()
            uls = uidx[q][1]
            f2.write('\n'.join(uls[ua:ub]) + '\n'); f2.close()
            print('\n' + '=' * 78 + '\n=== %s   %s:%d  vs  %s:%d'
                  % (q, os.path.basename(down), d + 1, os.path.basename(umod), ud + 1))
            sys.stdout.flush()
            subprocess.run(['diff', '-u', '--label', 'DOWNSTREAM/' + os.path.basename(down),
                            '--label', 'UPSTREAM/' + os.path.basename(umod), f1.name, f2.name])
            os.unlink(f1.name); os.unlink(f2.name)

    if not apply:
        return
    take = same + (diff if '--all' in sys.argv else [])
    kill = set()
    for (q, a, b, d, *_rest) in take:
        kill.update(range(a, b))

    # An `attribute [instance] Foo.bar` command applying to a declaration that
    # has just moved upstream is not scaffolding this file still needs: the
    # upstream module already carries the same command, and re-marking a
    # declaration that is already an instance is an error, not a no-op.
    gone = {q.split('.')[-1] for (q, *_r) in take}
    upattr = set()
    for u in ups:
        for ln in open(u, encoding='utf-8', errors='replace'):
            if ln.startswith('attribute'):
                upattr.add(' '.join(ln.split()))
    for i, ln in enumerate(dlines):
        if i in kill or not ln.startswith('attribute'):
            continue
        if ' '.join(ln.split()) in upattr:
            kill.add(i)
            print('  also removing duplicated command: %s' % ln.strip())

    out = [ln for i, ln in enumerate(dlines) if i not in kill]
    # collapse the runs of blank lines a removal leaves behind
    sq = []
    for ln in out:
        if not ln.strip() and sq and not sq[-1].strip():
            continue
        sq.append(ln)
    open(down, 'w', encoding='utf-8').write('\n'.join(sq))
    print('APPLIED: removed %d declaration blocks, %d lines (%d -> %d)'
          % (len(same), len(dlines) - len(sq), len(dlines), len(sq)))


main(sys.argv[1:])
