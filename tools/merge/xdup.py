#!/usr/bin/env python3
"""Cross-FILE duplicate declaration scan, restricted to import-cone pairs.

    xdup.py <repo-root>

A name declared in BOTH a module and a module that (transitively) imports it is
`has already been declared`, and NO per-file check sees it.  This is the shape a
HOIST merges into: `semmerge.py` propagates a branch's ADDITIONS but not its
DELETIONS, so a branch that moves declarations from a downstream module up into
an upstream one lands the upstream copies while the downstream copies survive.
Release 27 hit it with flt-lean-86's ~80-declaration Gamma0Cusp/Sturm hoist out
of MazurTorsion.lean into X0.lean.

TWO passes, because neither alone is trustworthy on this tree:

  QUALIFIED -- exact namespace-qualified names.  Sound, but this tree's giant
    modules contain bare `end`s that a stack model mis-attributes, so from some
    point in X0.lean onwards every name loses its `Fermat.` prefix and the
    qualified pass silently reports NOTHING.  That is exactly how the release-27
    duplicates were missed on the first run.

  SIBLINGS -- a pair is reported when SOME SINGLE MODULE can see both, not only
    when one of the two imports the other.  Until 2026-07-31 the test was
    `a in cone[b]`, which is structurally blind to two files that do not import
    each other while a third imports both -- and Lean rejects exactly that, with
    `import M failed, environment already contains 'X' from M'`.  It cost a
    release: `AlgebraicGeometry.divDegree_eq_zero` was declared in BOTH
    `CurveDivisorDegree` (a `sorry` leaf) and `PrincipalDivisorDegree` (PROVEN),
    neither importing the other, `X0.lean` importing both, and this scan printed
    `zero qualified duplicates` on the tree that would not build.  Each pair is
    now tagged ANCESTOR or SIBLING, and a SIBLING names a module that sees both.

  LAST-COMPONENT -- match on the final component only.  Over-reports (this tree
    has many legitimate same-last-component pairs in different namespaces), so it
    is a REVIEW list, not an error list.  Difference it against pre-merge `main`
    and read only the new entries.
"""
import re, sys, os, collections

DECL = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|public\s+|local\s+|scoped\s+)*'
    r'(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom)\s+'
    r"([A-Za-z_À-ɏͰ-Ͽᴀ-ᶿ℀-⅏][A-Za-z0-9_À-ɏͰ-Ͽᴀ-ᶿ₀-ₜ⁰-ⁿ℀-⅏.'!?]*)")
NS = re.compile(r'^\s*namespace\s+(\S+)')
ENDNS = re.compile(r'^\s*end\s*(\S*)\s*$')
IMP = re.compile(r'^\s*(?:public\s+)?import\s+(Fermat[A-Za-z0-9_.]*)\s*$')


def strip_comments(lines):
    out, depth = [], 0
    for ln in lines:
        s = ln.strip()
        if depth == 0:
            if s.startswith('/-'):
                depth += 1
                if '-/' in ln[ln.index('/-') + 2:]: depth -= 1
                out.append(''); continue
            if s.startswith('--'): out.append(''); continue
            out.append(ln)
        else:
            if '-/' in ln: depth -= 1
            out.append('')
    return out


def decls(path):
    code = strip_comments(open(path, encoding='utf-8', errors='replace').read().split('\n'))
    stack, res = [], {}
    for i, ln in enumerate(code, 1):
        m = NS.match(ln)
        if m: stack.append(m.group(1)); continue
        m = ENDNS.match(ln)
        if m:
            if stack and (not m.group(1) or m.group(1) == stack[-1]): stack.pop()
            continue
        m = DECL.match(ln)
        if m: res.setdefault('.'.join(stack + [m.group(1)]), i)
    return res


def imports(path):
    out = []
    for ln in open(path, encoding='utf-8', errors='replace'):
        m = IMP.match(ln)
        if m: out.append(m.group(1))
        if ln.strip().startswith(('theorem ', 'def ', 'namespace ')): break
    return out


def main(root):
    mod = {}
    for d, _, fs in os.walk(os.path.join(root, 'Fermat')):
        for f in fs:
            if f.endswith('.lean'):
                p = os.path.join(d, f)
                mod[os.path.relpath(p, root)[:-5].replace('/', '.')] = p
    imp = {m: imports(p) for m, p in mod.items()}
    cone, busy = {}, set()
    def cl(m):
        if m in cone: return cone[m]
        if m in busy: return set()
        busy.add(m)
        acc = set()
        for i in imp.get(m, []):
            if i in mod:
                acc.add(i); acc |= cl(i)
        cone[m] = acc; busy.discard(m)
        return acc
    for m in mod: cl(m)
    dmap = {m: decls(p) for m, p in mod.items()}

    # Modules that can SEE module x, i.e. x itself plus everything importing it
    # transitively.  Two declarations of one name collide as soon as some single
    # module sees both -- the two need NOT be in an import relation with each
    # other.  See the SIBLING note in the header.
    seers = collections.defaultdict(set)
    for m in mod:
        seers[m].add(m)
        for x in cone.get(m, ()): seers[x].add(m)

    def report(key, label):
        by = collections.defaultdict(list)
        for m, d in dmap.items():
            for q, ln in d.items(): by[key(q)].append((m, ln, q))
        n = 0
        for k, locs in sorted(by.items()):
            if len(locs) < 2: continue
            for i, a in enumerate(locs):
                for b in locs[i + 1:]:
                    if a[0] == b[0]: continue
                    if a[0] in cone.get(b[0], ()):
                        rel = 'ANCESTOR'
                    elif b[0] in cone.get(a[0], ()):
                        rel = 'ANCESTOR'
                    else:
                        common = seers[a[0]] & seers[b[0]]
                        if not common: continue
                        # name the MOST SPECIFIC witness -- the module with the
                        # smallest import cone that still sees both.  Picking the
                        # alphabetically first names `Fermat.Basic` every time,
                        # which is true and useless for locating the clash.
                        rel = 'SIBLING via ' + min(
                            common, key=lambda w: (len(cone.get(w, ())), w))
                    print('%s %s : %s:%d  and  %s:%d  [%s]'
                          % (label, k, a[0], a[1], b[0], b[1], rel))
                    n += 1
        print('%s: %d pair(s)' % (label, n))

    report(lambda q: q, 'XDUP')
    report(lambda q: q.split('.')[-1], 'XDUP-LAST')


main(sys.argv[1] if len(sys.argv) > 1 else '.')
