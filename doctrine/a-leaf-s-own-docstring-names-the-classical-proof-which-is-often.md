## A LEAF'S OWN DOCSTRING NAMES THE CLASSICAL PROOF — WHICH IS OFTEN THE WRONG CUT

(2026-07-31, `flt-lean-370`, `HyperellipticJacobian.lean`, immediately after the two
lessons above and in the same cluster.) `placeAct_transitive` — Galois is transitive on the
geometric places above a place of `F` — carried a docstring giving the textbook argument:
the places above `v` are the `ℚ`-embeddings of the residue field `κ(v)`, and `Gal(ℚ̄/ℚ)` is
transitive on those. Correct mathematics, and a **dead end in this file**: it needs the
residue field of an ARBITRARY place, and the file has residue fields only at the NAMED
points (`finrank_residue_pt_eq_one`, and the whole `exists_localDenom_*` machinery under it).
Following the docstring means first building general residue theory.

The cut that worked ran the other way. The leaf lives over `ℚ̄`, and over an algebraically
closed field **every place IS a named point** — so the general-position tool is not needed,
because base change made the general case special. `placeAct_transitive` then became a proof
about the COORDINATES of two rational points (ordinary field theory: extend `a ↦ a'`, fix the
sign of `b` with the other root of `X² − f(a')`), over one new leaf that contains no Galois
group at all. Same leaf count, and the residue theory is no longer on the path.

Generalise: **when a leaf's stated classical proof needs a tool the file only has in special
position, look for a change of base that puts you in special position.** The docstring is
evidence about the mathematics, not about the cheapest route through *this* development —
and it was written before anyone tried.

Two corollaries worth having separately.

**A hypothesis can be discovered by the recut, and threading it is cheap if you check the
call sites first.** The new leaf is FALSE without separability of the sextic (with a double
root the plane model is singular and TWO places sit over one rational point, so `pt` is not
surjective), so `placeAct_transitive` and `geomPic_descent` both had to gain `hsep`. That
looked like the class-7 interface-split hazard until the call sites were counted: exactly
ONE, and it already had the hypothesis. Count them before you decide a hypothesis is too
expensive to add.

**A mathlib instance can fail to apply because a DIFFERENT, equal instance won synthesis.**
In this file `Algebra ℚ (AlgebraicClosure ℚ)` resolves to `DivisionRing.toRatAlgebra`, not to
`AlgebraicClosure.instAlgebra` — so `Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ)` does NOT
synthesise, and neither does `IsIntegral`, any `minpoly` argument, or `algHom_bijective`. The
symptom is a bare "failed to synthesize" for a fact mathlib obviously has, and `#synth` on the
*carrier* instance is what diagnoses it. The repair is three lines and belongs in the file
once, as a declared instance:

    have h : (DivisionRing.toRatAlgebra : Algebra ℚ K) = AlgebraicClosure.instAlgebra ℚ :=
      Subsingleton.elim _ _
    have hb := AlgebraicClosure.isAlgebraic (k := ℚ)
    rw [← h] at hb

Minor but it cost a compile cycle: `open Polynomial` at the top of this file is NOT in scope
at line 7000 — intervening `end`s closed it — so `aeval`, `X` and `ℚ[X]` are unknown there.
Wrap a new block in `section ... open Polynomial ... end` rather than opening it globally,
which would change name resolution for the 1500 lines below.

