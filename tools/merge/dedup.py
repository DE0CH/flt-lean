#!/usr/bin/env python3
"""Delete the DOWNSTREAM copy of a cross-file duplicate declaration.

    dedup.py plan   <repo-root>          -> write /tmp/dedup-plan.txt, report body diffs
    dedup.py apply  <repo-root>          -> perform the deletions in the plan

WHY THIS EXISTS.  `semmerge.py` propagates a branch's ADDITIONS and never its
DELETIONS, so a branch that HOISTS declarations from a downstream module up into
an upstream one lands the upstream copies while the downstream originals
survive.  Each surviving pair is a hard `has already been declared`, and because
the downstream module is usually behind a red one in the import graph, NOTHING
sees them -- not `lake build`, not the sorry-warning set, not any frontier scan.
Release 28 inherited 249 of them in `FreyCurve/MazurTorsion.lean` that had been
invisible for three releases.

WHICH COPY GOES.  `xdup.py` prints the UPSTREAM location first and the
DOWNSTREAM location second (it reports exactly when `a` is in `b`'s import
cone).  The downstream copy is the stale original of the hoist, and deleting it
lets every consumer resolve upward to the survivor.  Deleting the UPSTREAM copy
instead would strand every consumer that sits between the two positions.

THE TRAP THIS TOOL EXISTS TO AVOID.  A declaration BLOCK, as `semmerge.py`
splits it, runs to the start of the NEXT block -- so it swallows any
`namespace` / `section` / `end` / `variable` glue that follows the declaration
body.  Deleting a block naively therefore deletes scope lines, which is the
single most expensive merge wound this project has had: a lost `end` reports at
the END OF THE FILE, thousands of lines from the damage, and an unclosed
`section` silently adds a `variable` binder to every later declaration.  So
every scope-significant line inside a deleted block is KEPT.
"""
import re, sys, os, subprocess, collections

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from semmerge import split_blocks, comment_mask

PLAN = '/tmp/dedup-plan.txt'

# Lines that must survive the deletion of the block that happens to contain them.
SCOPE = re.compile(r'^\s*(namespace\b|section\b|end\b|variable\b|universe\b|open\b|'
                   r'attribute\b|noncomputable\s+section\b|set_option\b|/-!)')


def norm(lines):
    """Whitespace-normalised body, for deciding whether two copies agree."""
    return re.sub(r'\s+', ' ', ' '.join(lines)).strip()


def xdup_pairs(root):
    """-> [(name, upstream_mod, dn_mod)] from xdup.py's QUALIFIED pass."""
    out = subprocess.run([sys.executable, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'xdup.py'), root],
                         capture_output=True, text=True).stdout
    pairs = []
    for ln in out.split('\n'):
        if not ln.startswith('XDUP '):
            continue
        m = re.match(r'XDUP (\S+) : (\S+):(\d+)\s+and\s+(\S+):(\d+)', ln)
        if m:
            pairs.append((m.group(1), m.group(2), m.group(4)))
    return pairs


def mod_path(root, mod):
    return os.path.join(root, mod.replace('.', '/') + '.lean')


def plan(root):
    pairs = xdup_pairs(root)
    print('%d qualified duplicate pair(s)' % len(pairs))
    by_dn = collections.defaultdict(list)
    for name, up, dn in pairs:
        by_dn[dn].append((name, up))
    lines_out, ndiff, nsame = [], 0, 0
    for dn, items in sorted(by_dn.items()):
        dnp = mod_path(root, dn)
        dn_items, dn_names = split_blocks(open(dnp, encoding='utf-8').read())
        for name, up in sorted(items):
            upp = mod_path(root, up)
            up_items, up_names = split_blocks(open(upp, encoding='utf-8').read())
            if name not in dn_names or name not in up_names:
                print('  SKIP (not a block): %s in %s' % (name, dn))
                continue
            # `split_blocks` maps a name to a LIST of blocks (a name can occur
            # more than once in one file), so compare the first of each.
            same = norm(dn_names[name][0]) == norm(up_names[name][0])
            if same:
                nsame += 1
            else:
                ndiff += 1
                print('  BODIES DIFFER: %s   (%s vs %s)' % (name, up, dn))
            lines_out.append('%s\t%s\t%s\t%s' % (dn, name, up, 'same' if same else 'DIFFER'))
    open(PLAN, 'w').write('\n'.join(lines_out) + '\n')
    print('plan: %d deletions (%d identical bodies, %d differing) -> %s'
          % (len(lines_out), nsame, ndiff, PLAN))


def apply(root):
    todo = collections.defaultdict(set)
    for ln in open(PLAN):
        ln = ln.rstrip('\n')
        if not ln:
            continue
        dn, name, up, kind = ln.split('\t')
        todo[dn].add(name)
    total, kept_scope = 0, 0
    for dn, names in sorted(todo.items()):
        p = mod_path(root, dn)
        text = open(p, encoding='utf-8').read()
        items, _ = split_blocks(text)
        out = []
        for kind, q, ls in items:
            if kind == 'decl' and q in names:
                # keep any scope-significant glue that the block swallowed
                mask = comment_mask(ls)
                keep = [l for i, l in enumerate(ls) if not mask[i] and SCOPE.match(l)]
                if keep:
                    kept_scope += len(keep)
                    out.extend(keep)
                total += 1
                continue
            out.extend(ls)
        open(p, 'w', encoding='utf-8').write('\n'.join(out))
        print('  %s: removed %d' % (dn, len([n for n in names])))
    print('removed %d declaration block(s); preserved %d scope line(s)' % (total, kept_scope))


if __name__ == '__main__':
    cmd = sys.argv[1]
    root = sys.argv[2] if len(sys.argv) > 2 else '.'
    (plan if cmd == 'plan' else apply)(root)
