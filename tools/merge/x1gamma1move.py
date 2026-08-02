#!/usr/bin/env python3
"""ONE-SHOT: relocate the `IsBaseChangeOfGamma1` cluster X1.lean -> X0.lean.

Kept in the tree (rather than run and thrown away) for the reason
`flt-hoist-genusone.py` records: a relocation that must survive a rebase is
better shipped as a TRANSFORM than as a diff.  Every anchor below is matched by
CONTENT and asserted unique, so re-running it on a moved tree either works or
fails loudly; it never silently cuts the wrong lines.

WHAT MOVES, and why exactly this set.  `flt-cyclecheck.py --block <the
MazurIsogenyPrimeJ tail> --dest X0.lean` reports the closure of the three names
`Fermat.IsBaseChangeOfGamma1.{refl, comp, along_injective}` inside X1.lean as
seven declarations in two contiguous runs:

    the four structures   RelPoint.ofSection, PointOfExactOrder,
                          Gamma1Datum, IsBaseChangeOfGamma1
    the namespace block   refl, comp, cancelMap, cancelMap_fst, cancelMap_snd,
                          cancel, along_injective

`cancelMap*`/`cancel` are NOT in the closure; they travel anyway because they
are inside the same `namespace IsBaseChangeOfGamma1 … end` and splitting a
namespace across two modules buys nothing.  Their own closure adds nothing new
(checked: it is the same four structures).

WHERE IT LANDS.  Immediately after `RelPoint.along_val` in X0.lean, which is the
LAST X0 declaration the moved text references (`RelPoint.transport{,_val,_zero,
_add}` and `along_val` are what `refl` runs on; everything else it uses —
`AbelianSchemeStruct` and its `zero_val_congr`/`add_val_congr`/`addCommGroup`,
`RelPoint`, `RelPoint.along`, `SmoothOfRelativeDimension` — is far above).  That
puts the `Γ₁` base-change calculus directly beside the `Γ₀` one it mirrors.

SCOPE, which no scanner sees and which is the half that bites:
  * source and destination are both plain `namespace Fermat`, no enclosing
    `section`, no `variable` in scope at either site (X0's `namespace
    IsBaseChangeOf` closes at `end IsBaseChangeOf` well above the anchor);
  * both files carry the same file-level `universe u` and
    `open CategoryTheory AlgebraicGeometry`;
  * no `open … in` / `set_option … in` binds any moved declaration;
  * the moved block's own `variable {N : ℕ}` is inside the moved namespace and
    travels with it;
  * no anonymous `instance` and no `@[simp]` in the moved text (`@[reassoc]` on
    `cancelMap_fst`/`cancelMap_snd` travels unchanged).
"""

import re
import sys

X0 = 'Fermat/FLT/ModularCurve/X0.lean'
X1 = 'Fermat/FLT/ModularCurve/X1.lean'

# --- the two source runs -----------------------------------------------------
# Each is (opening anchor, closing anchor, offset-from-open, offset-from-close),
# where the offsets say how far the run's real boundary sits from the anchor.
# `namespace IsBaseChangeOfGamma1` / `end IsBaseChangeOfGamma1` are NOT usable as
# anchors: X1.lean reopens that namespace three times (the other two blocks stay
# put), so both strings occur three times.  The unique anchors are the last line
# of `exists_gamma1Datum_baseChange` just above the block, and the last line of
# `along_injective` just inside its end.
RUNS = [
    (r'^/-! ### Sections, and the `Γ₁\(N\)`-level structure -/$', 0,
     r'^  map_sec : d\'\.pt\.sec ≫ map = h ≫ d\.pt\.sec$', 0),
    (r'^  ⟨Gamma1BaseChange\.datumBC h d, ⟨Gamma1BaseChange\.isBaseChangeBC h d⟩⟩$', 2,
     r'^  Subtype\.ext \(bc\.isPullback\.hom_ext \(by rw \[a\.2, b\.2\]\) hab\)$', 2),
]

# what the derived boundaries MUST be, checked before anything is written
RUN_BOUNDS = [
    ('/-! ### Sections, and the `Γ₁(N)`-level structure -/',
     "  map_sec : d'.pt.sec ≫ map = h ≫ d.pt.sec"),
    ('namespace IsBaseChangeOfGamma1', 'end IsBaseChangeOfGamma1'),
]

# --- the destination anchor: insert AFTER this line -------------------------
DEST_AFTER = r'^    \(RelPoint\.along map hw x\)\.1 = x\.1 ≫ map := rfl$'

HEADER = """/-! #### The `Γ₁(N)`-level structure and its base-change calculus

**RELOCATED HERE FROM `ModularCurve/X1.lean` on 2026-07-31**, verbatim and at the
same root namespace `Fermat`, so that every name below resolves unchanged at both
its old and its new call sites; `X1.lean` `public import`s this module, so nothing
in it had to be edited beyond deleting these lines.

WHY.  `X1.lean` imports `X0.lean`, so anything hoisted INTO `X0.lean` that reaches
`Fermat.IsBaseChangeOfGamma1.{refl, comp, along_injective}` is an import cycle.
`flt-cyclecheck.py` named exactly those three as the only `X1`-side obstruction to
hoisting the `MazurIsogenyPrimeJ` tail of `FreyCurve/MazurTorsion.lean` up here —
the hoist that would let `mem_isolatedJInvariants_of_stable_thirtySeven` and
`_classNumberOne` cite `exists_jMap_thirtySeven` / `_classNumberOne` instead of
restating them, exactly as `flt-hoist-genusone.py` already did for the genus-one
branch.  Moving them removes that obstruction permanently and costs nothing: it is
a pure reordering, and the `Γ₁` base-change calculus is a mirror of the `Γ₀` one
declared immediately above it.

**READ THIS BEFORE COSTING ANY WORK OFF THAT CYCLE REPORT.**  Re-measured on
2026-07-31 against `main` at `fe5131ca`, the `X1` cycle it reports is a FALSE
POSITIVE, and so is the second one it reports via `Modularity/Interface.lean`.
`flt-cyclecheck.py` matches on the SHORT name — its own docstring says so, and
says the over-approximation is the safe direction for a "would this be a cycle"
question.  Here it over-approximated on four of the most common short names in
the library:

* `refl`   — the block's only hit is `Equiv.refl` in `exists_hopfAlgebra_fixedLocus`;
* `comp`   — eight hits, every one of them `RingHom.comp` / `Function.comp` /
             `Category.id_comp` / `CommRingCat.hom_comp`;
* `along_injective` — the block's own `MazurIsogenyPrimeJ.IsEllipticIsoOf.along_injective`;
* `val_neg` (the `Interface.lean` report) — `Units.val_neg`.

The decisive check is one command and needs no build:
`grep -c 'IsBaseChangeOfGamma1\\|Gamma1Datum\\|PointOfExactOrder' Fermat/FLT/FreyCurve/MazurTorsion.lean`
returns **0** — the whole 70 000-line module never mentions the `Γ₁` moduli layer.
So the tail's hoist was ALREADY unblocked before this relocation, and the
`NeronModel.lean` cycle that `flt-hoist-genusone.py`'s docstring names as the
blocker is likewise gone (it was traced through leaves that have since been proven
by other routes — an open leaf's body contributes no dependencies).  This move is
therefore worth its cost only for what it prevents: the next agent to run
`flt-cyclecheck.py` will not read `CYCLE via …X1` and conclude, for a second time,
that a hoist is blocked when it is not.

The generalisable lesson is recorded in `CLAUDE.md`: a short-name cycle report is
a HYPOTHESIS, and the refuting check is a `grep` for the qualified name in the
source module, not another run of the scanner. -/

"""

POINTER_A = """/-! ### Sections, and the `Γ₁(N)`-level structure — RELOCATED

`RelPoint.ofSection`, `PointOfExactOrder`, `Gamma1Datum` and
`IsBaseChangeOfGamma1` were moved VERBATIM into `Fermat/FLT/ModularCurve/X0.lean`
on 2026-07-31, at the same root namespace `Fermat`, so every reference in this
file still resolves through the `public import` at the top.  They sit there
immediately after `RelPoint.along_val`, beside the `Γ₀` base-change calculus they
mirror; the reason for the move, and the false-positive cycle report that
prompted it, are recorded in full on the section header there. -/

"""

POINTER_B = """/-! #### `namespace IsBaseChangeOfGamma1` — RELOCATED

`refl`, `comp`, `cancelMap`, `cancelMap_fst`, `cancelMap_snd`, `cancel` and
`along_injective` were moved VERBATIM into `Fermat/FLT/ModularCurve/X0.lean` on
2026-07-31, together with the four structures above, at the same root namespace.
`exists_descendClassifyGamma1` and `nonempty_gamma1RigidifiedModuli_of_iso` below
consume `cancel` and `along_injective` unchanged. -/

"""


def anchor(lines, pat, tag, lo=0):
    rx = re.compile(pat)
    hit = [i for i, l in enumerate(lines) if i >= lo and rx.match(l.rstrip('\n'))]
    if len(hit) != 1:
        sys.exit(f'anchor {tag!r}: expected exactly 1 match at/after line {lo + 1}, '
                 f'got {len(hit)} ({[h + 1 for h in hit]}).  Re-derive it by hand '
                 f'rather than guessing.')
    return hit[0]


def main():
    x1 = open(X1).read().splitlines(keepends=True)
    x0 = open(X0).read().splitlines(keepends=True)

    # ---- locate the two runs in X1 -----------------------------------------
    spans = []
    for (first, doff, last, coff), (wfirst, wlast) in zip(RUNS, RUN_BOUNDS):
        a = anchor(x1, first, first) + doff
        b = anchor(x1, last, last, lo=a) + coff
        for idx, want in ((a, wfirst), (b, wlast)):
            got = x1[idx].rstrip('\n')
            if got != want:
                sys.exit(f'derived boundary line {idx + 1} is {got!r}, '
                         f'expected {want!r}; refusing')
        # take the trailing blank line with the run, so the seam stays tidy
        end = b + 1
        if end < len(x1) and x1[end].strip() == '':
            end += 1
        spans.append((a, end))
    (a0, b0), (a1, b1) = spans
    if not (b0 <= a1):
        sys.exit('the two runs overlap; refusing')

    moved = x1[a0:b0] + x1[a1:b1]

    # ---- rewrite X1: delete high span first so indices stay valid -----------
    new_x1 = x1[:a1] + [POINTER_B] + x1[b1:]
    new_x1 = new_x1[:a0] + [POINTER_A] + new_x1[b0:]

    # ---- rewrite X0 --------------------------------------------------------
    d = anchor(x0, DEST_AFTER, DEST_AFTER) + 1
    if x0[d].strip() != '':
        sys.exit(f'destination line {d + 1} is not blank; refusing')
    d += 1
    new_x0 = x0[:d] + [HEADER] + moved + x0[d:]

    open(X1, 'w').write(''.join(new_x1))
    open(X0, 'w').write(''.join(new_x0))

    # ---- receipt: the moved lines are a PERMUTATION, nothing else changed ---
    from collections import Counter
    before = Counter(x1) + Counter(x0)
    after = Counter(new_x1) + Counter(new_x0)
    added = after - before
    removed = before - after
    print(f'moved {len(moved)} lines '
          f'(X1 {a0 + 1}-{b0} and {a1 + 1}-{b1}) into X0 after line {d}')
    print(f'added   (must be exactly the 3 pointer/header blocks): {sum(added.values())}')
    for k in added:
        print(f'    + {k[:70]!r}')
    print(f'removed (must be 0): {sum(removed.values())}')
    for k in removed:
        print(f'    - {k[:70]!r}')
    return 0 if not removed else 1


if __name__ == '__main__':
    sys.exit(main())
