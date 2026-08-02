#!/usr/bin/env python3
"""Replay the p = 37 hoist: MazurTorsion.lean -> X0.lean.  Sibling of
`flt-hoist-genusone.py`, which did the genus-one branch on 2026-07-30.

WHY THIS EXISTS.  Same reason as its sibling: the edit moves ~3 100 lines between
two files of ~70 000 and ~119 000 lines with a dozen concurrent editors, and a diff
that size does not merge (`flt-lean-123`/`cbedf0b4` was correct and was declined at
release 22 purely on conflict volume).  Do not merge the diff -- RE-RUN THE
TRANSFORM on whatever base is current.  Every anchor is matched by CONTENT and
asserted unique, and the declaration set is RECOMPUTED from source each run, so it
picks up work that landed inside the moved blocks meanwhile.

WHY ONLY p = 37, AND WHY THAT IS NOT THE OLD REASON.  `flt-hoist-genusone.py` says
`_thirtySeven` and `_classNumberOne` both reach `NeronModel.lean`, "a genuine import
cycle".  Re-measured 2026-07-31 (flt-lean-247): that cycle is GONE -- the closure
reaches nothing declared in any of the 20 modules importing `X0.lean`.  The two
nodes are nevertheless not alike:

* `_classNumberOne` is blocked by a cycle through THE TARGET ITSELF, seven call
  sites long, ending at `exists_endMinpoly_of_stable_cyclic_isolatedJ`
  (MazurTorsion.lean:41417) which CONSUMES
  `Fermat.mem_isolatedJInvariants_of_stable_classNumberOne`.  No relocation, module
  split or import edit repairs that; it would survive merging the two files.  See
  that leaf's docstring, and `flt-cyclecheck.py --at` section 4.
* `_thirtySeven` is free.  Its only tie to the class-number-one chain is that
  `card_le_of_isogenyPrimeHigherGenus` is stated uniformly over
  `higherGenusCountTable`, so it calls `card_y0Le_classNumberOne` even at 37.  The
  `37` branch itself (MazurTorsion.lean:45909) calls only `card_y0Le_thirtySeven`.
  SPLITTING THAT THEOREM BY LEVEL is the whole of the repair, and this script does
  it by leaving the general theorem where it is and emitting a level-37 counterpart
  next to the hoisted material.

WHAT IT DOES.

  1. Moves four contiguous runs of `namespace MazurIsogenyPrimeJ` -- the
     `higherGenusCountTable`..`card_y0Le_thirtySeven` block, the
     `numRationalCusps_of_prime`..`exists_isogenyCurve_thirtySeven` block,
     `exists_x0ThirtySevenPoints`, and `exists_jMap_thirtySeven` -- out of
     `FreyCurve/MazurTorsion.lean` and into the existing
     `section MazurIsogenyPrimeJHoist` at the end of `ModularCurve/X0.lean`, at the
     SAME namespace, so every reference from `MazurTorsion.lean` still resolves
     unqualified through its `public import`.
  2. Emits `card_le_of_isogenyPrimeThirtySeven` (the `37` branch of
     `card_le_of_isogenyPrimeHigherGenus`, whose proof is transcribed from it) and
     re-points the moved `exists_jMap_thirtySeven` at it.  The general theorem stays
     in `MazurTorsion.lean` and keeps working: everything it calls is either hoisted
     (hence visible) or local.
  3. Rewrites `Fermat.mem_isolatedJInvariants_of_stable_thirtySeven` from `sorry`
     to three lines over the hoisted material, in the shape
     `flt-hoist-genusone.py` used for its genus-one counterpart.

ASSERTED, not assumed: the four runs are gap-free (every declaration inside each
range is in the closure), the closure has NO declaration outside the higher-genus
tail, and it makes NO forward reference into `X0.lean`.  The script recomputes all
three and refuses to write if any fails.

USAGE:  python3 flt-hoist-thirtyseven.py [--check]
Then:   lake build Fermat.FLT.ModularCurve.X0 Fermat.FLT.FreyCurve.MazurTorsion
Expect: X0 sorried +3 (-1 target, +4 hoisted leaves), MazurTorsion -4, no errors.
"""

import re
import sys

X0 = 'Fermat/FLT/ModularCurve/X0.lean'
MZ = 'Fermat/FLT/FreyCurve/MazurTorsion.lean'

# The four runs, by the NAME of their first and last declaration.
RUNS = [('higherGenusCountTable', 'card_y0Le_thirtySeven'),
        ('numRationalCusps_of_prime', 'exists_isogenyCurve_thirtySeven'),
        ('exists_x0ThirtySevenPoints', 'exists_x0ThirtySevenPoints'),
        ('exists_jMap_thirtySeven', 'exists_jMap_thirtySeven')]

DECL = re.compile(
    r'^(?:@\[[^\]]*\]\s*)?'
    r'(?:private\s+|protected\s+|noncomputable\s+|public\s+|partial\s+|unsafe\s+|scoped\s+)*'
    r'(theorem|lemma|def|instance|abbrev|structure|inductive|class|opaque|axiom)\s+(\S+)?')

# NOT a regex class: `À-￿` contains `⟨⟩←▸` and swallows names inside anonymous
# constructors.  Two scans in this project have agreed with each other and both
# been wrong that way.
TOKCH = set("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
            "0123456789_'.!?₀₁₂₃₄₅₆₇₈₉ℓ")

MODIFIER = re.compile(r'^(open|set_option|attribute|omit|include)\b.*\bin\s*$')


def strip_comments(src):
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
    src = open(path, encoding='utf-8').read()
    raw = src.split('\n')
    st = strip_comments(src).split('\n')
    assert len(raw) == len(st), 'comment stripper lost lines'
    ns, decls = [], []
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
            decls.append((i + 1, m.group(2),
                          '.'.join(ns + [m.group(2)]) if ns else m.group(2)))
    return raw, st, decls


def index(decls, st):
    bodies, tok, byshort = {}, {}, {}
    for k, (l1, short, full) in enumerate(decls):
        end = decls[k + 1][0] - 1 if k + 1 < len(decls) else len(st)
        bodies[full] = (l1, end, short, k)
        tok[full] = tokens('\n'.join(st[l1 - 1:end]))
        byshort.setdefault(short, []).append(full)
    return bodies, tok, byshort


def only(bodies, short, tag):
    hits = [f for f in bodies if bodies[f][2] == short]
    if len(hits) != 1:
        sys.exit(f'ANCHOR {tag!r}: expected exactly 1 declaration named {short!r}, '
                 f'got {len(hits)}: {hits[:6]}\n  The file has moved in a way this '
                 f'script cannot follow.  Fix the anchor by hand rather than guessing.')
    return hits[0]


def main(check_only=False):
    raw, st, decls = parse(MZ)
    bodies, tok, byshort = index(decls, st)

    # ---- the closure, with the level split modelled ------------------------
    HG = only(bodies, 'card_le_of_isogenyPrimeHigherGenus', 'general count theorem')
    CN = only(bodies, 'card_y0Le_classNumberOne', 'class-number-one count')

    def deps(f):
        out = set()
        for t in tok[f]:
            if len(t) < 4:
                continue
            for g in byshort.get(t, ()):
                if g != f and len(bodies[g][2]) >= 4:
                    out.add(g)
        # THE LEVEL SPLIT: the `37` branch of the general count theorem does not
        # call the class-number-one one (MazurTorsion.lean:45909 vs :45910-45912).
        return out - ({CN} if f == HG else set())

    seed = only(bodies, 'exists_jMap_thirtySeven', 'target')
    clo, fr = {seed}, [seed]
    while fr:
        for g in deps(fr.pop()):
            if g not in clo:
                clo.add(g)
                fr.append(g)
    clo.discard(HG)      # replaced by the emitted level-37 counterpart

    # ---- the four runs, docstrings and modifier lines included --------------
    def doc_start(h):
        i = h - 1
        while i >= 1 and raw[i - 1].strip() == '':
            i -= 1
        if i >= 1 and raw[i - 1].rstrip().endswith('-/'):
            j = i
            while j >= 1:
                s = raw[j - 1].lstrip()
                if s.startswith('/--'):
                    i = j
                    break
                if s.startswith('/-'):     # a `/-!` note: not this declaration's
                    return h
                j -= 1
            else:
                return h
        # carry `open … in` / `set_option … in` modifiers, which sit ABOVE the
        # docstring (putting them between it and the theorem is a parse error)
        while i >= 2 and MODIFIER.match(raw[i - 2].strip()):
            i -= 1
        return i

    def code_end(full):
        k = bodies[full][3]
        lo = bodies[full][0]
        hi = decls[k + 1][0] - 1 if k + 1 < len(decls) else len(raw)
        last = lo
        for i in range(lo + 1, hi + 1):
            s = st[i - 1]
            if not s.strip():
                continue
            if s[0] not in ' \t' and re.match(
                    r'^(namespace|end|section|open|variable|set_option|attribute|@\[)',
                    s.strip()):
                break
            last = i
        return last

    runs = []
    for a, b in RUNS:
        fa, fb = only(bodies, a, a), only(bodies, b, b)
        runs.append((doc_start(bodies[fa][0]), code_end(fb), a, b))
    runs.sort()

    # ---- the three assertions that make this a legal move ------------------
    tail_lo = min(bodies[f][0] for f in clo)
    covered = set()
    for lo, hi, a, b in runs:
        for f in bodies:
            if lo <= bodies[f][0] <= hi:
                if f not in clo:
                    sys.exit(f'REFUSING: run {a}..{b} ({lo}-{hi}) is not gap-free — '
                             f'{f} at {bodies[f][0]} is inside it but not in the '
                             f'closure.  Moving it would drag work nobody asked for.')
                covered.add(f)
    missing = clo - covered
    if missing:
        sys.exit('REFUSING: the four runs do not cover the closure; missing '
                 + ', '.join(f'{bodies[f][0]}:{f}' for f in sorted(missing,
                                                                   key=lambda g: bodies[g][0])))
    for lo, hi, a, b in runs:
        for i in range(lo, hi + 1):
            s = st[i - 1]
            if s.strip() and s[0] not in ' \t' and re.match(
                    r'^(namespace|end|section|variable)\b', s.strip()):
                sys.exit(f'REFUSING: run {a}..{b} swallowed a structural line at '
                         f'{i}: {raw[i-1]!r}')

    # forward references into X0 below the landing point
    xraw, xst, xdecls = parse(X0)
    xb, xt, xbs = index(xdecls, xst)
    land = [i + 1 for i, l in enumerate(xst)
            if re.match(r'^end MazurIsogenyPrimeJ\s*$', l)]
    if len(land) != 1:
        sys.exit(f'ANCHOR: expected exactly one `end MazurIsogenyPrimeJ` in {X0}, '
                 f'got {land}')
    land = land[0]
    ctok = set()
    for f in clo:
        ctok |= tok[f]
    fwd = sorted((xb[f][0], f) for s, v in xbs.items() if len(s) >= 4 for f in v
                 if xb[f][0] >= land and s in ctok
                 and (not f.endswith('.' + s)
                      or f[: -(len(s) + 1)].split('.')[-1] in ctok))
    if fwd:
        sys.exit('REFUSING: the closure forward-references ' + ', '.join(
            f'{ln}:{f}' for ln, f in fwd) + f' in {X0}, declared at or below the '
            'landing point.  That is the cycle that blocks the class-number-one '
            'node; it must not appear for p = 37.')

    tgt = only(xb, 'mem_isolatedJInvariants_of_stable_thirtySeven', 'X0 target')

    if check_only:
        print(f'{MZ}: closure = {len(clo)} declarations, '
              f'{sum(hi - lo + 1 for lo, hi, _, _ in runs)} lines in {len(runs)} runs')
        for lo, hi, a, b in runs:
            print(f'    {lo:6d}-{hi:6d}  {a} .. {b}')
        print(f'{X0}: landing before `end MazurIsogenyPrimeJ` at line {land}; '
              f'target {tgt} at {xb[tgt][0]}')
        print('assertions: runs gap-free, closure covered, no structural line '
              'swallowed, no forward reference')
        return

    # ---- rewrite MazurTorsion ---------------------------------------------
    cut = {i for lo, hi, _, _ in runs for i in range(lo, hi + 1)}
    first = runs[0][0]
    out = []
    for i in range(1, len(raw) + 1):
        if i in cut:
            if i == first:
                out.append(POINTER)
            continue
        out.append(raw[i - 1])
    open(MZ, 'w').write('\n'.join(out))

    # ---- rewrite X0 --------------------------------------------------------
    blocks = []
    for lo, hi, a, b in runs:
        txt = '\n'.join(raw[lo - 1:hi])
        if a == 'exists_jMap_thirtySeven':
            new = txt.replace('card_le_of_isogenyPrimeHigherGenus 37 4 (by decide) hX',
                              'card_le_of_isogenyPrimeThirtySeven hX')
            if new == txt:
                sys.exit('REFUSING: could not re-point `exists_jMap_thirtySeven` at '
                         'the level-37 count theorem; its call site has changed.')
            blocks.append(NEW_COUNT)
            txt = new
        blocks.append(txt)
    body = HOIST_NOTE + '\n\n' + '\n\n'.join(blocks)

    doc_hi = xb[tgt][0] - 1
    while doc_hi >= 1 and xraw[doc_hi - 1].strip() == '':
        doc_hi -= 1
    if not xraw[doc_hi - 1].rstrip().endswith('-/'):
        sys.exit('REFUSING: target docstring does not end in a doc terminator')
    tk = xb[tgt][3]
    tgt_hi = xdecls[tk + 1][0] - 1 if tk + 1 < len(xdecls) else len(xraw)
    while tgt_hi > xb[tgt][0] and xraw[tgt_hi - 1].strip() == '':
        tgt_hi -= 1

    imp = [i + 1 for i, l in enumerate(xraw)
           if re.match(r'^public import Fermat\.FLT\.EllipticCurve\.'
                       r'GenusOneKernelPolynomials\s*$', l)]
    if len(imp) != 1:
        sys.exit(f'ANCHOR: expected one GenusOneKernelPolynomials import, got {imp}')

    out = []
    for i in range(1, len(xraw) + 1):
        if xb[tgt][0] <= i <= tgt_hi:
            if i == xb[tgt][0]:
                out.append(NEW_PROOF)
            continue
        if i == doc_hi:
            out.append(xraw[i - 1].rstrip()[:-2].rstrip() + '\n' + DOC_UPDATE)
            continue
        if i == land:
            out.append(body)
            out.append('')
        out.append(xraw[i - 1])
        if i == imp[0]:
            out.append(NEW_IMPORT)
    open(X0, 'w').write('\n'.join(out))

    print(f'moved {sum(hi - lo + 1 for lo, hi, _, _ in runs)} lines '
          f'({len(clo)} declarations) out of {MZ}')
    print('now run: lake build Fermat.FLT.ModularCurve.X0 Fermat.FLT.FreyCurve.MazurTorsion')


NEW_IMPORT = ("-- Added with the p = 37 half of `section MazurIsogenyPrimeJHoist`: the two\n"
              "-- explicit `37`-isogenous curves and their kernel polynomials, which\n"
              "-- `exists_isogenyCurve_thirtySeven` consumes.  It does not import this module.\n"
              "public import Fermat.FLT.EllipticCurve.ThirtySevenKernelPolynomials")

HOIST_NOTE = """/-! ### The level `37` half of the higher-genus block, hoisted (2026-07-31)

Moved VERBATIM out of `Fermat/FLT/FreyCurve/MazurTorsion.lean` at the same namespace,
so that `Fermat.mem_isolatedJInvariants_of_stable_thirtySeven` -- stated below and
consumed by `Fermat.mem_isolatedJInvariants_of_stable` -- can CITE it rather than
restate it.  That module `public import`s this one, so the duplicate was forced by
import direction, not chosen; and everything moved here is still visible there,
unqualified, through that import.

**ONLY the `37` half could travel, and the reason is NOT the one the genus-one hoist
recorded.**  That note blamed an import cycle ending at `NeronModel.lean`; re-measured
2026-07-31 that cycle is gone -- the closure reaches nothing declared in any module
that imports this one.  What blocks `43, 67, 163` is a cycle through
`Fermat.mem_isolatedJInvariants_of_stable_classNumberOne` ITSELF, seven call sites
long; see that leaf's docstring.  It is unfixable by relocation.

`37` escapes it because `card_le_of_isogenyPrimeHigherGenus` is stated uniformly over
`higherGenusCountTable` and so calls `card_y0Le_classNumberOne` even at `37`, while
its `37` BRANCH calls only `card_y0Le_thirtySeven`.  Splitting that theorem by level
is the whole repair: the general theorem stays in `MazurTorsion.lean` (where it still
works, since everything it calls is either hoisted or local) and
`card_le_of_isogenyPrimeThirtySeven` below is its `37` branch, transcribed.

Regenerated by `flt-hoist-thirtyseven.py`; re-run that rather than merging its diff. -/"""

NEW_COUNT = """/-- **`#X_0(37)(ℚ) ≤ 4`** -- the `37` branch of
`card_le_of_isogenyPrimeHigherGenus`, split off so that it does not consume
`card_y0Le_classNumberOne`.

That is the entire content of the split, and it is what makes the `37` node
hoistable while its two siblings are not: the general theorem is stated uniformly
over `higherGenusCountTable`, so it calls the class-number-one count at every level
including this one, and that count is proven THROUGH
`Fermat.mem_isolatedJInvariants_of_stable_classNumberOne` -- so a hoist of the
uniform theorem would carry a cycle through a leaf of this file.  The `37` branch
calls only `card_y0Le_thirtySeven`, whose closure touches no leaf here.

The proof is transcribed from the uniform one's `key`, specialised to `p = 37`,
`c = 2`, `k = 2`. -/
theorem card_le_of_isogenyPrimeThirtySeven {X Y : Scheme.{0}}
    {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {jY : Y ⟶ X}
    (hX : IsX0Compactification 37 strX strY jY)
    (s : Finset (RelPoint strX (𝟙 SpecQ))) : s.card ≤ 4 := by
  classical
  have hc : numRationalCusps 37 = 2 := numRationalCusps_of_prime (by norm_num)
  have h : s.card ≤ 2 + 2 :=
    card_le_of_cuspBound_of_y0Bound hX
      (fun t ht => hc ▸ card_le_numRationalCusps_of_isCusp (by decide) hX t ht)
      (card_y0Le_thirtySeven hX.coarse) s
  exact h"""

DOC_UPDATE = """
**THIS NODE IS NOW PROVEN (2026-07-31, flt-lean-247)**, by the `p = 37` hoist in
`section MazurIsogenyPrimeJHoist` at the end of this file: it is
`MazurIsogenyPrimeJ.exists_jMap_thirtySeven` carried onto the curve by
`MazurIsogenyPrimeJ.jInvariant_mem_of_exists_jMap`, then the table translation
`(37, E.j) ∈ thirtySevenJTable → E.j ∈ isolatedJInvariants 37`.  The paragraph above
is kept because its account of WHY the uniform hoist fails is still correct for the
sibling below; what it got wrong is that splitting
`card_le_of_isogenyPrimeHigherGenus` by level, which it calls "necessary but NOT
sufficient", is in fact sufficient at `37`. -/"""

NEW_PROOF = """theorem mem_isolatedJInvariants_of_stable_thirtySeven
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (g : (E⁄(AlgebraicClosure ℚ)).Point)
    (hg : addOrderOf g = 37)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ AddSubgroup.zmultiples g,
      WeierstrassCurve.Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
        AddSubgroup.zmultiples g) :
    E.j ∈ isolatedJInvariants 37 := by
  have h := MazurIsogenyPrimeJ.jInvariant_mem_of_exists_jMap
    MazurIsogenyPrimeJ.exists_jMap_thirtySeven E g hg hstable
  simp only [MazurIsogenyPrimeJ.thirtySevenJTable, List.mem_cons, List.not_mem_nil,
    Prod.mk.injEq, or_false] at h
  norm_num at h
  simp only [isolatedJInvariants]
  norm_num
  tauto"""

POINTER = """/-! #### The level `37` half of this block HAS BEEN HOISTED into `ModularCurve/X0.lean`

(2026-07-31, flt-lean-247.)  `higherGenusCountTable`, the counting assembly
`forall_jm_mem_of_pointBound`, the cusp/affine splitting, the whole
`thirtySevenB`/`sexticThirtySeven` plane-model development down to
`card_y0Le_thirtySeven`, `numRationalCusps_of_prime`, `exists_jm_eq_of_isogenyCurve`,
`exists_isogenyCurve_thirtySeven`, `exists_x0ThirtySevenPoints` and
`exists_jMap_thirtySeven` now live in `section MazurIsogenyPrimeJHoist` at the END of
`Fermat/FLT/ModularCurve/X0.lean`, in the SAME namespace, so the class-number-one
material below still cites them unqualified through the `public import`.

**Why only `37`.**  `Fermat.mem_isolatedJInvariants_of_stable_thirtySeven` was a
forced duplicate of `exists_jMap_thirtySeven`, uncitable because this module imports
that one; hoisting closed it.  The class-number-one levels cannot follow: their chain
runs through `card_y0Le_classNumberOne`, whose proof reaches
`exists_endMinpoly_of_stable_cyclic_isolatedJ` below, which CONSUMES
`Fermat.mem_isolatedJInvariants_of_stable_classNumberOne` -- so hoisting them would
need that leaf both above and below itself.  Recorded in full on that leaf.

`card_le_of_isogenyPrimeHigherGenus` STAYS here and is unchanged: everything it calls
is either hoisted (hence still visible) or local.  Its `37` branch is duplicated
upstream as `card_le_of_isogenyPrimeThirtySeven`, which is what let `37` travel.
-/"""


if __name__ == '__main__':
    main(check_only='--check' in sys.argv)
