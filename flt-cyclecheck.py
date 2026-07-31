#!/usr/bin/env python3
"""Would hoisting a block into module DEST create an import cycle?  Which one?

WHY THIS EXISTS.  `flt-hoistcheck.py` answers the WITHIN-file question — does a
block use anything in the region it would jump over.  The other half of a hoist
decision is CROSS-file and nothing answered it:

    if I move this block into DEST, does it still reach declarations that live
    in modules which (transitively) IMPORT DEST?

Every such declaration is a cycle.  The verdict matters because it is usually
recorded as prose and then believed for ever: `flt-hoist-genusone.py` restricted
itself to the genus-one branch because `_thirtySeven` and `_classNumberOne` were
said to reach `NeronModel.lean`, which imports `X0.lean` — "a genuine import
cycle, with no sorried link to cut it at".  That was true of the tree it was
measured on.  Ten of the eighteen leaves under it closed within a day, the proofs
that landed did not take that route, and the cycle was gone.  Nobody re-measured,
because re-measuring meant writing this.

**An open leaf's body contributes no dependencies**, so a cycle traced through a
sorried declaration is a claim about its INTENDED proof.  Run this against the
branch where the proofs EXIST, not the one where the leaves are open:

    git show merger:Fermat/FLT/FreyCurve/MazurTorsion.lean > /tmp/mt.lean

and pass `--block /tmp/mt.lean LO HI`.  The `--dest` side is read from the
worktree, so point the worktree at the same branch when it matters.

WHAT IT REPORTS.

  1. the transitive within-file closure of the block — everything that must
     travel with it, and how much of that lies OUTSIDE the block;
  2. every module that transitively imports DEST, together with the declarations
     of that module the closure references.  That list IS the cycle set: empty
     means the hoist is legal, non-empty names exactly what has to move first.
  3. for each offending module, the within-file closure of the offending
     declarations — i.e. the price of moving them upstream instead.

USAGE
    ./flt-cyclecheck.py --block Fermat/FLT/FreyCurve/MazurTorsion.lean 50383 57658 \
                        --dest Fermat/FLT/ModularCurve/X0.lean

WHAT IT CANNOT SEE, and it is the same short list every scanner here has:
anonymous `instance`s (no name to scan for), `simp`-set membership, and
notation.  It matches on the SHORT name, which OVER-approximates references —
the safe direction for a "would this be a cycle" question, since a false cycle
costs a read and a missed one costs a build.
"""

import argparse
import os
import re
import sys

DECL = re.compile(
    r'^(?:@\[[^\]]*\]\s*)?'
    r'(?:private\s+|protected\s+|noncomputable\s+|public\s+|partial\s+|unsafe\s+|scoped\s+)*'
    r'(theorem|lemma|def|instance|abbrev|structure|inductive|class|opaque|axiom)\s+(\S+)?')

# Lean identifier characters.  Deliberately NOT a regex class: a `À-￿` range
# contains `⟨⟩←▸`, so a naive class swallows every name inside an anonymous
# constructor and the scan silently misses it.  Two dependency scans in this
# project have already agreed with each other and both been wrong that way.
TOKCH = set("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
            "0123456789_'.!?₀₁₂₃₄₅₆₇₈₉ℓ")

IMPORT = re.compile(r'^\s*(?:public\s+|private\s+|meta\s+)*import\s+(\S+)')


def strip_comments(src):
    """Blank out `--` line comments and nested `/- -/` blocks, preserving line
    count and column positions."""
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        if depth == 0 and src.startswith('--', i):
            j = src.find('\n', i)
            j = n if j < 0 else j
            out.append(' ' * (j - i))
            i = j
        elif src.startswith('/-', i):
            depth += 1
            out.append('  ')
            i += 2
        elif depth > 0 and src.startswith('-/', i):
            depth -= 1
            out.append('  ')
            i += 2
        elif depth > 0:
            out.append('\n' if src[i] == '\n' else ' ')
            i += 1
        else:
            out.append(src[i])
            i += 1
    return ''.join(out)


def tokens(s):
    out, cur = set(), []
    for ch in s:
        if ch in TOKCH:
            cur.append(ch)
        else:
            if cur:
                out.add(''.join(cur))
                cur = []
    if cur:
        out.add(''.join(cur))
    return out | {p for t in out for p in t.split('.') if p}


def parse(path):
    """-> [(line1, short, full)] for top-level declarations, plus stripped lines."""
    st = strip_comments(open(path, encoding='utf-8').read()).split('\n')
    ns, out = [], []
    for i, l in enumerate(st):
        s = l.strip()
        m = re.match(r'^namespace\s+(\S+)', s)
        if m:
            ns.append(m.group(1))
            continue
        m = re.match(r'^end\s+(\S+)\s*$', s)
        if m:
            if ns and ns[-1] == m.group(1):
                ns.pop()
            continue
        m = DECL.match(l)
        if m and m.group(2):
            out.append((i + 1, m.group(2),
                        '.'.join(ns + [m.group(2)]) if ns else m.group(2)))
    return out, st


def index(path):
    """-> (bodies, tok, byshort) keyed by fully qualified name."""
    decls, st = parse(path)
    bodies, tok, byshort = {}, {}, {}
    for k, (l1, short, full) in enumerate(decls):
        end = decls[k + 1][0] - 1 if k + 1 < len(decls) else len(st)
        bodies[full] = (l1, end, short)
        tok[full] = tokens('\n'.join(st[l1 - 1:end]))
        byshort.setdefault(short, []).append(full)
    return bodies, tok, byshort


def closure(bodies, tok, byshort, seed):
    """Transitive within-file dependency closure of `seed`."""
    def deps(f):
        out = set()
        for t in tok[f]:
            if len(t) < 4:
                continue
            for g in byshort.get(t, ()):
                if g != f and len(bodies[g][2]) >= 4:
                    out.add(g)
        return out

    clo, fr = set(seed), list(seed)
    while fr:
        for g in deps(fr.pop()):
            if g not in clo:
                clo.add(g)
                fr.append(g)
    return clo


def module_of(path):
    return os.path.splitext(path)[0].replace('/', '.')


def importers_of(dest, root='Fermat'):
    """Modules that TRANSITIVELY import `dest`.  These are exactly the modules a
    block moved into `dest` may no longer reference."""
    paths = [os.path.join(d, f)
             for d, _, fs in os.walk(root) for f in fs if f.endswith('.lean')]
    imports = {}
    for p in paths:
        with open(p, encoding='utf-8', errors='replace') as fh:
            head = []
            for line in fh:
                head.append(line)
                if len(head) > 400:
                    break
        imports[module_of(p)] = {m.group(1) for m in
                                 (IMPORT.match(l) for l in head) if m}
    target, changed = {module_of(dest)}, True
    while changed:
        changed = False
        for mod, imps in imports.items():
            if mod not in target and imps & target:
                target.add(mod)
                changed = True
    target.discard(module_of(dest))
    return {m: m.replace('.', '/') + '.lean' for m in sorted(target)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--block', nargs=3, metavar=('FILE', 'LO', 'HI'), required=True)
    ap.add_argument('--dest', required=True)
    ap.add_argument('--root', default='Fermat')
    a = ap.parse_args()
    src, lo, hi = a.block[0], int(a.block[1]), int(a.block[2])

    bodies, tok, byshort = index(src)
    seed = {f for f, (l1, _, _) in bodies.items() if lo <= l1 <= hi}
    if not seed:
        sys.exit(f'no declarations in {src} lines {lo}-{hi}')
    clo = closure(bodies, tok, byshort, seed)
    outside = sorted((bodies[f][0], f) for f in clo if not (lo <= bodies[f][0] <= hi))

    print(f'BLOCK  {src}:{lo}-{hi}')
    print(f'  {len(seed)} declarations in the block, {len(clo)} in its closure, '
          f'{len(outside)} of them OUTSIDE the block and travelling with it')
    for ln, f in outside:
        print(f'    {ln:7d}  {f}')

    ctok = set()
    for f in clo:
        ctok |= tok[f]

    mods = importers_of(a.dest, a.root)
    print(f'\nDEST   {a.dest}  ({len(mods)} modules transitively import it)')
    cycles = 0
    for mod, path in mods.items():
        if not os.path.exists(path) or os.path.abspath(path) == os.path.abspath(src):
            continue
        mb, mt, mbs = index(path)
        hit = sorted((mb[f][0], f) for s, v in mbs.items()
                     if s in ctok and len(s) >= 4 for f in v)
        if not hit:
            continue
        cycles += len(hit)
        price = closure(mb, mt, mbs, {f for _, f in hit})
        print(f'\n  CYCLE via {mod}  — {len(hit)} referenced, '
              f'{len(price)} declarations to relocate if moved upstream')
        for ln, f in hit:
            print(f'    {ln:7d}  {f}')
    if cycles == 0:
        print('\n  NO CYCLE: the closure references nothing declared in any module '
              'that imports the destination.')
    return 0


if __name__ == '__main__':
    sys.exit(main())
