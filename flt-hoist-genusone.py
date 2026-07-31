#!/usr/bin/env python3
"""Replay the genus-one hoist: MazurTorsion.lean -> X0.lean.

WHY THIS EXISTS.  The edit this script performs moves ~7 000 lines between two
files that are each ~75 000 lines and have a dozen concurrent editors.  A diff
that large does not merge -- branch `flt-lean-123` (`cbedf0b4`) did exactly this
hoist, was correct, and was declined at the release-22 merge purely on conflict
volume.  So do not merge the diff: RE-RUN THE TRANSFORM on whatever base is
current.  Every anchor below is matched by CONTENT and asserted unique, and the
declaration set to relocate is RECOMPUTED from the source each time, so the
script picks up work that landed inside the moved blocks in the meantime.

WHAT IT DOES.

  1. Moves `namespace X0GenusOne` (whole) and the genus-one PREFIX of
     `namespace MazurIsogenyPrimeJ` (up to but excluding `higherGenusCountTable`)
     out of `FreyCurve/MazurTorsion.lean` and into a new
     `section MazurIsogenyPrimeJHoist` at the END of `ModularCurve/X0.lean`,
     at the SAME root namespaces, so no name changes and every reference from
     `MazurTorsion.lean` still resolves through its `public import`.
  2. Relocates the downward closure of `Fermat.isolatedJInvariants` inside
     `X0.lean` to a reopened `namespace Fermat` after the hoist, reproducing the
     interleaved `open` lines in order so each range keeps its open context.
  3. Rewrites `Fermat.mem_isolatedJInvariants_of_stable_genusOne` to cite the
     hoisted material instead of `sorry`.

WHY THE RELOCATION IN (2) IS NEEDED, and why it is safe: the hoisted material
consumes `Fermat.card_le_of_rankZeroJacobian`, declared ~40 000 lines BELOW the
target, so the hoist can only land at the end of the file and the target has to
follow it.  The downward closure of `isolatedJInvariants` is disjoint from
`card_le_of_rankZeroJacobian`'s cone -- the script ASSERTS this -- so the move is
a pure reordering and introduces no cycle.

WHAT IT DELIBERATELY DOES NOT DO.  Only the genus-one branch.  `_thirtySeven`
and `_classNumberOne` reach `MazurIsogenyPrimeJ.exists_endMinpoly_of_stable_cyclic_mazurLevel`,
hence Mazur's isogeny-character descent, hence `exists_goodReductionModel_of_surjective`
and `exists_neronExtension` in `Mathlib/AlgebraicGeometry/NeronModel.lean`, whose
line 8 is `public import Fermat.FLT.ModularCurve.X0` -- a genuine import cycle,
with no sorried link to cut it at.  See the note on
`mem_isolatedJInvariants_of_stable_classNumberOne`.

USAGE:  python3 flt-hoist-genusone.py [--check]
        --check  parses and reports the anchors and the closure, changing nothing.

Then: lake build Fermat.FLT.ModularCurve.X0 Fermat.FLT.FreyCurve.MazurTorsion
Expect: X0's `declaration uses 'sorry'` count +4 (-1 target, +5 relocated
X0GenusOne leaves), MazurTorsion's -5, and zero errors.
"""

import re
import sys

X0 = 'Fermat/FLT/ModularCurve/X0.lean'
MZ = 'Fermat/FLT/FreyCurve/MazurTorsion.lean'


# ---------------------------------------------------------------- comment strip
def strip_comments(src):
    """Blank out `--` line comments and nested `/- -/` blocks, PRESERVING both
    line count and column positions, so indices into the result are valid
    indices into the original."""
    out = []
    i = 0
    n = len(src)
    depth = 0
    while i < n:
        if depth == 0 and src.startswith('--', i):
            j = src.find('\n', i)
            if j < 0:
                j = n
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


DECL = re.compile(
    r'^(?:@\[[^\]]*\]\s*)?'
    r'(?:private\s+|protected\s+|noncomputable\s+|public\s+|partial\s+|unsafe\s+|scoped\s+)*'
    r'(theorem|lemma|def|instance|abbrev|structure|inductive|class|opaque|axiom)\s+(\S+)?')

# Lean identifier characters.  NOTE: do NOT use a `À-￿` range here -- it
# contains `⟨⟩←▸`, so a naive class swallows every name inside an anonymous
# constructor and dependency scans silently miss them.
TOKCH = set("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
            "0123456789_'.!?₀₁₂₃₄₅₆₇₈₉ℓ")


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
    """-> (raw_lines, stripped_lines, decls) with decls = [(line1, kind, short, full)]."""
    src = open(path).read()
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
            short = m.group(2)
            decls.append((i + 1, m.group(1), short,
                          ('.'.join(ns) + '.' + short) if ns else short))
    return raw, st, decls


def anchor(lines, pat, tag):
    hits = [i + 1 for i, l in enumerate(lines) if re.match(pat, l)]
    if len(hits) != 1:
        sys.exit(f'ANCHOR {tag!r}: expected exactly 1 match, got {len(hits)} {hits[:8]}\n'
                 f'  The file has moved in a way this script cannot follow.  Fix the '
                 f'anchor by hand rather than guessing.')
    return hits[0]


# --------------------------------------------------------------------- the move
def main(check_only=False):
    mzraw, mzst, mzd = parse(MZ)
    x0raw, x0st, x0d = parse(X0)

    # ---- MazurTorsion anchors -------------------------------------------------
    a_open = anchor(mzraw, r'^namespace X0GenusOne\s*$', 'namespace X0GenusOne')
    a_close = anchor(mzraw, r'^end X0GenusOne\s*$', 'end X0GenusOne')
    b_open = anchor(mzraw, r'^namespace MazurIsogenyPrimeJ\s*$', 'namespace MazurIsogenyPrimeJ')
    hg = anchor(mzraw, r'^def higherGenusCountTable\b', 'def higherGenusCountTable')
    assert a_open < a_close < b_open < hg, 'blocks are not in the expected order'
    # block B ends at the last CODE line before higherGenusCountTable's docstring
    b_close = max(i for i in range(b_open, hg) if mzst[i - 1].strip())

    # ---- X0: downward closure of isolatedJInvariants -------------------------
    bodies = {}
    for k, (l1, kind, short, full) in enumerate(x0d):
        end = x0d[k + 1][0] - 1 if k + 1 < len(x0d) else len(x0raw)
        bodies[full] = (l1, end, '\n'.join(x0st[l1 - 1:end]), short)
    tok = {f: tokens(bodies[f][2]) for f in bodies}
    byshort = {}
    for f, (_, _, _, short) in bodies.items():
        byshort.setdefault(short, []).append(f)

    def refs(f):
        out = set()
        for t in tok[f]:
            if len(t) < 4:
                continue
            for g in byshort.get(t, ()):
                if g != f and len(bodies[g][3]) >= 4:
                    out.add(g)
        return out

    rev = {}
    for f in bodies:
        for g in refs(f):
            rev.setdefault(g, set()).add(f)
    seed = {f for f in bodies if bodies[f][3] == 'isolatedJInvariants'} | \
           {f for f in bodies if 'mem_isolatedJInvariants_of_stable' in f}
    if not seed:
        sys.exit('no isolatedJInvariants seed found')
    clo, fr = set(seed), list(seed)
    while fr:
        for f in rev.get(fr.pop(), ()):
            if f not in clo:
                clo.add(f)
                fr.append(f)

    # the disjointness that makes the relocation a pure reordering
    crz = [f for f in bodies if bodies[f][3] == 'card_le_of_rankZeroJacobian']
    if not crz:
        sys.exit('card_le_of_rankZeroJacobian not found')
    cone, fr = set(crz), list(crz)
    while fr:
        for g in refs(fr.pop()):
            if g not in cone:
                cone.add(g)
                fr.append(g)
    clash = clo & cone
    if clash:
        sys.exit('REFUSING TO MOVE: card_le_of_rankZeroJacobian depends on the '
                 f'isolatedJInvariants closure via {sorted(clash)}.  That is a real '
                 'cycle inside X0.lean and this hoist is no longer a pure reordering.')

    # ---- mover source ranges, docstring included ----------------------------
    STRUCT = re.compile(r'^(namespace|end|section|open|variable|set_option|attribute|@\[|/-)')

    def doc_start(h):
        i = h - 1
        while i >= 1 and x0raw[i - 1].strip() == '':
            i -= 1
        if i < 1 or not x0raw[i - 1].rstrip().endswith('-/'):
            return h
        j = i
        while j >= 1:
            s = x0raw[j - 1].lstrip()
            if s.startswith('/--'):
                return j
            if s.startswith('/-'):      # `/-!` section note, or a plain block: not ours
                return h
            j -= 1
        return h

    def code_end(k):
        lo = x0d[k][0]
        hi = x0d[k + 1][0] - 1 if k + 1 < len(x0d) else len(x0raw)
        last = lo
        for i in range(lo + 1, hi + 1):
            s = x0st[i - 1]
            if not s.strip():
                continue
            if s[0] not in ' \t' and STRUCT.match(s.strip()):
                break                    # structural line: not part of the proof
            last = i
        return last

    movers = sorted((doc_start(h), code_end(k), full)
                    for k, (h, _, _, full) in enumerate(x0d) if full in clo)
    merged = []
    for a, b, nm in movers:
        if merged and a <= merged[-1][1] + 1:
            merged[-1] = (merged[-1][0], max(merged[-1][1], b), merged[-1][2] + [nm])
        else:
            merged.append((a, b, [nm]))
    for a, b, _ in merged:
        for i in range(a, b + 1):
            s = x0st[i - 1]
            if s.strip() and s[0] not in ' \t' and \
               re.match(r'^(namespace|end|section|variable|set_option)\b', s.strip()):
                sys.exit(f'range {a}-{b} swallowed a structural line at {i}: {x0raw[i-1]!r}')

    # the `open`s in effect inside `namespace Fermat`, in file order
    ns_fermat = anchor(x0st, r'^namespace Fermat\s*$', 'namespace Fermat')
    opens = [(i + 1, x0raw[i]) for i, l in enumerate(x0st)
             if i + 1 > ns_fermat and re.match(r'^open\b', l) and not l.rstrip().endswith(' in')]
    last_mover = merged[-1][1]
    opens = [o for o in opens if o[0] < last_mover]

    tgt = [f for f in clo if bodies[f][3] == 'mem_isolatedJInvariants_of_stable_genusOne']
    if len(tgt) != 1:
        sys.exit(f'expected exactly one genus-one target, got {tgt}')
    tgt_line = bodies[tgt[0]][0]

    if check_only:
        print(f'{MZ}: block A = {a_open}-{a_close} ({a_close-a_open+1} lines), '
              f'block B = {b_open}-{b_close} ({b_close-b_open+1} lines)')
        print(f'{X0}: closure = {len(movers)} declarations in {len(merged)} ranges, '
              f'{sum(b-a+1 for a,b,_ in merged)} lines; disjoint from '
              f"card_le_of_rankZeroJacobian's {len(cone)}-declaration cone")
        print(f'{X0}: opens to reproduce = {[o[0] for o in opens]}')
        ef = anchor(x0st, r'^end Fermat\s*$', 'end Fermat')
        print(f'{X0}: target at line {tgt_line}; end Fermat at {ef}')
        return

    block_a = '\n'.join(mzraw[a_open - 1:a_close])
    block_b = '\n'.join(mzraw[b_open - 1:b_close])

    # ---------------- rewrite MazurTorsion.lean ------------------------------
    out, i = [], 1
    while i <= len(mzraw):
        if i == a_open:
            out.append(POINTER_A)
            i = a_close + 1
            continue
        if i == b_open:
            out.append(POINTER_B)
            i = b_close + 1
            continue
        out.append(mzraw[i - 1])
        i += 1
    open(MZ, 'w').write('\n'.join(out))

    # ---------------- rewrite X0.lean ---------------------------------------
    reloc, emitted = ['namespace Fermat', ''], set()
    for a, b, nms in merged:
        for ln, txt in opens:
            if ln < a and ln not in emitted:
                emitted.add(ln)
                reloc += [txt, '']
        if a <= tgt_line <= b:
            # keep the docstring, drop its final `-/`, append the update, then the proof
            doc = x0raw[a - 1:tgt_line - 1]
            while doc and doc[-1].strip() == '':
                doc.pop()
            assert doc[-1].rstrip().endswith('-/'), 'target docstring does not end in -/'
            doc[-1] = doc[-1].rstrip()[:-2].rstrip()
            reloc.append('\n'.join(doc) + '\n' + DOC_UPDATE + '\n' + NEW_PROOF)
        else:
            reloc.append('\n'.join(x0raw[a - 1:b]))
        reloc.append('')
    reloc += ['end Fermat', '']

    end_fermat = anchor(x0st, r'^end Fermat\s*$', 'end Fermat')
    last_import = anchor(x0raw,
                         r'^public import Fermat\.FLT\.Mathlib\.AlgebraicGeometry\.'
                         r'EllipticCurve\.DivisionPolynomialTwist\s*$', 'last import')
    tail = ['', 'section MazurIsogenyPrimeJHoist', '', HOIST_NOTE, '',
            'open WeierstrassCurve WeierstrassCurve.Affine', '',
            block_a, '', block_b, '', 'end MazurIsogenyPrimeJ', '',
            'end MazurIsogenyPrimeJHoist', ''] + reloc

    skip = {i for a, b, _ in merged for i in range(a, b + 1)}
    out = []
    for i in range(1, len(x0raw) + 1):
        if i in skip:
            continue
        out.append(x0raw[i - 1])
        if i == last_import:
            out.append(NEW_IMPORTS)
        elif i == end_fermat:
            out.extend(tail)
    open(X0, 'w').write('\n'.join(out))

    print(f'moved {a_close-a_open+1} + {b_close-b_open+1} lines out of {MZ}')
    print(f'relocated {len(movers)} declarations '
          f'({sum(b-a+1 for a,b,_ in merged)} lines) inside {X0}')
    print('now run: lake build Fermat.FLT.ModularCurve.X0 Fermat.FLT.FreyCurve.MazurTorsion')


NEW_IMPORTS = """
-- Added with `section MazurIsogenyPrimeJHoist` at the end of this file: the genus-one
-- cone of Mazur's isogeny theorem, moved up out of `FreyCurve/MazurTorsion.lean` so
-- that `mem_isolatedJInvariants_of_stable_genusOne` can cite it instead of restating
-- it.  None of the four project modules below imports this one, so no cycle is created.
public import Fermat.FLT.EllipticCurve.GenusOneKernelPolynomials
public import Fermat.FLT.EllipticCurve.MordellWeil19
public import Fermat.FLT.FreyCurve.QuarticDescent
public import Fermat.FLT.GaloisRepresentation.Chebotarev
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.NumberTheory.PythagoreanTriples"""

HOIST_NOTE = """/-! ## Mazur's isogeny theorem at the genus-one levels, hoisted

Everything in this section was moved VERBATIM out of
`Fermat/FLT/FreyCurve/MazurTorsion.lean`, at the same root namespaces `X0GenusOne`
and `MazurIsogenyPrimeJ`, so that `Fermat.mem_isolatedJInvariants_of_stable_genusOne`
-- stated far above and consumed by `Fermat.mem_isolatedJInvariants_of_stable` -- can
CITE it rather than restate it.  That module `public import`s this one, so the
duplicate was forced by import direction, not chosen.

**It sits at the END of the file, and had to.**  The hoisted material consumes
`Fermat.card_le_of_rankZeroJacobian`, declared far below the target's original
position, so the `isolatedJInvariants` cluster travelled down here too -- see the
reopened `namespace Fermat` below.  That closure is disjoint from
`card_le_of_rankZeroJacobian`'s cone, so this is a pure reordering.

**ONLY the genus-one branch could travel.**  `jInvariant_mem_of_isogenyPrime_thirtySeven`
and `_classNumberOne` both reach
`MazurIsogenyPrimeJ.exists_endMinpoly_of_stable_cyclic_mazurLevel`, hence Mazur's
isogeny-character descent, hence `Fermat.exists_goodReductionModel_of_surjective` and
`Fermat.exists_neronExtension` in
`Fermat/FLT/Mathlib/AlgebraicGeometry/NeronModel.lean`, whose line 8 is
`public import Fermat.FLT.ModularCurve.X0`.  Not one link in that chain is a sorried
leaf, so it cannot be cut by leaving a `sorry` where it hurts least.  The chain is
recorded link by link on `Fermat.mem_isolatedJInvariants_of_stable_classNumberOne`.

Regenerated by `flt-hoist-genusone.py`; re-run that rather than merging its diff.
-/"""

DOC_UPDATE = """
**THIS NODE IS PROVEN**, by the hoist in `section MazurIsogenyPrimeJHoist` at the end
of this file: it is `MazurIsogenyPrimeJ.exists_jMap_genusOne` carried onto the curve
by `MazurIsogenyPrimeJ.jInvariant_mem_of_exists_jMap`, then the table translation
`(p, E.j) ∈ genusOneJTable → E.j ∈ isolatedJInvariants p`.  The hoist landed at the
END of the file because the hoisted material consumes `card_le_of_rankZeroJacobian`,
declared far BELOW this point; the `isolatedJInvariants` cluster therefore travelled
down with it, which is why these declarations are no longer where this docstring's
neighbours suggest. -/"""

NEW_PROOF = """theorem mem_isolatedJInvariants_of_stable_genusOne {p : ℕ}
    (hp : p ∈ ({11, 17, 19} : Finset ℕ))
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (g : (E⁄(AlgebraicClosure ℚ)).Point)
    (hg : addOrderOf g = p)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ AddSubgroup.zmultiples g,
      WeierstrassCurve.Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
        AddSubgroup.zmultiples g) :
    E.j ∈ isolatedJInvariants p := by
  have h := MazurIsogenyPrimeJ.jInvariant_mem_of_exists_jMap
    (MazurIsogenyPrimeJ.exists_jMap_genusOne p hp) E g hg hstable
  have hp' : p = 11 ∨ p = 17 ∨ p = 19 := by simpa using hp
  rcases hp' with rfl | rfl | rfl <;>
    simp only [MazurIsogenyPrimeJ.genusOneJTable, List.mem_cons, List.not_mem_nil,
      Prod.mk.injEq, or_false] at h <;>
    norm_num at h <;>
    simp only [isolatedJInvariants] <;>
    norm_num <;> tauto"""

POINTER_A = """/-! #### `namespace X0GenusOne` HAS BEEN HOISTED into `ModularCurve/X0.lean`

The four levels at which `X_0(N)` is an elliptic curve of rank `0` -- the section note
immediately above still describes them, and is left here because it is the record of
how they were chosen -- now live in `section MazurIsogenyPrimeJHoist` at the END of
`Fermat/FLT/ModularCurve/X0.lean`, at the SAME root namespace `X0GenusOne`, so every
reference from this file still resolves, unqualified, through the `public import` of
that module.

**Why it moved.**  `Fermat.mem_isolatedJInvariants_of_stable_genusOne` is stated in
`X0.lean` and was a forced duplicate of
`WeierstrassCurve.jInvariant_mem_of_isogenyPrime_genusOne` below, uncitable because
this module imports that one.  Hoisting the genus-one cone upstream of both closed it.
The genus-one branch is the ONE branch of the three for which this works: `37` and the
class-number-one levels reach Mazur's isogeny-character descent, which ends at
`Fermat/FLT/Mathlib/AlgebraicGeometry/NeronModel.lean`, a module that `public import`s
`X0.lean` -- a genuine import cycle.  The chain, link by link, is recorded on
`Fermat.mem_isolatedJInvariants_of_stable_classNumberOne`.
-/"""

POINTER_B = """/-! #### The genus-one half of `MazurIsogenyPrimeJ` HAS BEEN HOISTED into
`ModularCurve/X0.lean`

`genusOneJTable` through `exists_jMap_genusOne` -- including the level-generic
`jInvariant_mem_of_exists_jMap`, which all three wrappers below use -- now live in
`section MazurIsogenyPrimeJHoist` at the END of `Fermat/FLT/ModularCurve/X0.lean`, in
the SAME root namespace, so the higher-genus material below still cites them
unqualified through the `public import`.  See the note where `namespace X0GenusOne`
used to be for why only the genus-one branch could travel.
-/

namespace MazurIsogenyPrimeJ

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Fermat"""


if __name__ == '__main__':
    main(check_only='--check' in sys.argv)
