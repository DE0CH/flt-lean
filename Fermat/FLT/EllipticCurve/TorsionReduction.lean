module

/-
TorsionReduction.lean — own work for the Fermat project.

# Torsion injects into the reduction, and the finite-field point count

This module supplies the *reduction brick*: the classical statement that the
torsion of an elliptic curve over `ℚ` injects into the group of points of its
reduction at a suitable prime, packaged in the two forms this development
actually consumes, together with the elementary point-counting facts over a
finite field that turn such an injection into an arithmetic contradiction.

## Why this module exists

Two open leaves in this tree are the *same* piece of mathematics seen twice:

* `WeierstrassCurve.curve14a4_points` (`Fermat/FLT/EllipticCurve/MordellWeil.lean`)
  — the affine rational points of `14a4` are exactly the five listed ones.
  Reduction at the good prime `3` embeds the torsion of `14a4(ℚ)` into
  `14a4(𝔽₃)`, which has `6` elements; `14a4(ℚ)` is torsion (rank `0`), so it has
  at most `6` elements, and six are exhibited. The same injection supplies
  `curve14a4_finite`, which is why the Mordell–Weil leaf `curve14a4_fg` could be
  DELETED rather than left in front of level `14`.
* `WeierstrassCurve.no_rational_point_of_isogenyPrime_jInvariant`
  (`Fermat/FLT/FreyCurve/MazurTorsion.lean`) — none of the five `(p, j)` pairs
  of the `X₀` table at `p ∈ {37, 43, 67, 163}` carries a rational point of order
  `p`. Reduction at `5` sends such a point to a point of order `p` on an
  elliptic curve over `𝔽₅`, whose group has at most `5·5 + 1 = 26` elements,
  and `26 < 37 ≤ p`.

The second of these **supersedes Olson's theorem entirely**, which is why this
brick was worth building. The route recorded in `MazurTorsion.lean`'s section
note — twist to a fixed model and hunt for a rational root of a degree-`81`
isogeny-kernel factor — is not needed, and neither is the CM packaging of
Olson's argument: a single auxiliary prime kills all five entries at once,
because *any* elliptic curve over `𝔽₅` has fewer than `37` points.

## The two bricks

`exists_injective_torsion_toReduction` (good reduction) and
`exists_goodReductionHom_of_jIntegral` (potentially good reduction) are the two
open leaves of this module.

UPDATED 2026-07-26: the second brick used to be
`exists_reduction_dvd_addOrderOf_of_jIntegral` itself. That declaration is now
PROVEN, and the reduction-theoretic content it rested on was factored out into
`exists_goodReductionHom_of_jIntegral` — "there is a group homomorphism
`E(ℚ) → W(𝔽_ℓ)` onto an elliptic curve over `𝔽_ℓ` that does not kill
prime-to-`ℓ` torsion". Everything downstream of that (Lagrange, and the passage
from a point of order `p` to `p ∣ #W(𝔽_ℓ)`) is elementary and is proven. So the
open frontier of this module is smaller than it was, but not easier: the two
leaves below are the same missing theory in its good and potentially-good forms.

Both are Silverman *AEC* VII; see their
docstrings for the precise citation, the proof route, and an AUDIT of what this
tree already has towards them. In short: `PointReduction.lean` has the
reduction homomorphism on points and its kernel, sorry-free, and
`GoodReduction.lean` has the Lutz–Nagell integrality of torsion coordinates —
but the latter assumes `ℓ ∤ n`, so the `ℓ`-primary half of the injection (the
formal-group content, `e < ℓ − 1`) is present in neither this tree nor mathlib.
Do not start these expecting a short composition.

## What is PROVEN here

The finite-field counting, which is elementary and is what converts an
injection into a contradiction:

* `natCard_affine_point_eq` — `#W(K) = #{(x,y) : W.Nonsingular x y} + 1`,
  by transport along mathlib's `Affine.nonsingularPointEquiv`.
* `natCard_affine_point_le` — `#W(K) ≤ (#K)² + 1` over a finite base.
  This is deliberately the *trivial* bound (the affine points sit inside
  `K × K`) rather than Hasse's `|a| ≤ 2√q`: at the one place it is used, the
  base is `𝔽₅` and `26 < 37`, so the sharp bound would buy nothing and Hasse
  is not in mathlib.
* `natCard_affine_point_pos` — the group is nonempty, so its order is positive.
  Needed because `Nat.card` is `0` on infinite types, and `p ∣ 0` is vacuous.
-/

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Data.ZMod.Basic
-- `Field (ZMod ℓ)` from `[Fact ℓ.Prime]`, which is what puts the `AddCommGroup`
-- structure on `W.toAffine.Point` for `W` over `ZMod ℓ`: mathlib's group law on
-- `Affine.Point` is stated for a field. `Data.ZMod.Basic` alone does not supply it.
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

open scoped WeierstrassCurve.Affine

namespace WeierstrassCurve

/-! ### Counting the points of a Weierstrass curve -/

variable {R : Type*} [CommRing R]

/-- The affine part of `W(R)` is finite as soon as `W(R)` is. Transport along
mathlib's `Affine.nonsingularPointEquiv : W.Point ≃ WithZero {xy // Nonsingular xy}`
and use that `WithZero X = Option X` has `X` as a retract. -/
theorem finite_nonsingular_subtype_of_finite_point (W : WeierstrassCurve R)
    (h : Finite W.toAffine.Point) :
    Finite {xy : R × R // W.toAffine.Nonsingular xy.fst xy.snd} := by
  haveI := h
  haveI : Finite (WithZero {xy : R × R // W.toAffine.Nonsingular xy.fst xy.snd}) :=
    Finite.of_equiv _ W.toAffine.nonsingularPointEquiv
  exact Finite.of_injective (fun s => (WithZero.coe s : WithZero _))
    (fun a b hab => by simpa using hab)

/-- **`#W(R) = #{affine points} + 1`** — the point at infinity is the `+ 1`.
Immediate from `Affine.nonsingularPointEquiv` and `Finite.card_option`. -/
theorem natCard_affine_point_eq (W : WeierstrassCurve R) (h : Finite W.toAffine.Point) :
    Nat.card W.toAffine.Point
      = Nat.card {xy : R × R // W.toAffine.Nonsingular xy.fst xy.snd} + 1 := by
  haveI := h
  haveI := W.finite_nonsingular_subtype_of_finite_point h
  rw [Nat.card_congr W.toAffine.nonsingularPointEquiv]
  exact Finite.card_option

/-- Over a finite base ring the point group is finite. Not registered as an
`instance`: this module is imported by `MazurTorsion.lean`, and a new global
`Finite` instance on `Affine.Point` would be attempted on every `Finite` goal
there for no gain. -/
theorem finite_affine_point_of_finite [Finite R] (W : WeierstrassCurve R) :
    Finite W.toAffine.Point := by
  haveI : Finite (WithZero {xy : R × R // W.toAffine.Nonsingular xy.fst xy.snd}) :=
    inferInstanceAs (Finite (Option _))
  exact Finite.of_equiv _ W.toAffine.nonsingularPointEquiv.symm

/-- **`#W(K) ≤ (#K)² + 1`** over a finite base: the affine points sit inside
`K × K`, and there is one point at infinity.

This is the crude bound, not Hasse's `#W(𝔽_q) = q + 1 − a` with `|a| ≤ 2√q`
(which mathlib does not have). It is enough wherever it is used here: at
`K = 𝔽₅` it gives `26`, and the primes to be excluded are `≥ 37`. A sharper
`≤ 2·#K + 1` is available at the cost of counting roots of the quadratic in
`y` fibrewise; it was not needed. -/
theorem natCard_affine_point_le [Finite R] (W : WeierstrassCurve R) :
    Nat.card W.toAffine.Point ≤ Nat.card R * Nat.card R + 1 := by
  rw [natCard_affine_point_eq W (W.finite_affine_point_of_finite)]
  have h2 : Nat.card {xy : R × R // W.toAffine.Nonsingular xy.fst xy.snd}
      ≤ Nat.card (R × R) := Finite.card_subtype_le _
  simpa [Nat.card_prod] using h2

/-- `#W(K) > 0` over a finite base — the point at infinity is there. Needed
because `Nat.card` returns the junk value `0` on an infinite type, which would
make a divisibility conclusion `p ∣ #W(K)` vacuous. -/
theorem natCard_affine_point_pos [Finite R] (W : WeierstrassCurve R) :
    0 < Nat.card W.toAffine.Point := by
  haveI := W.finite_affine_point_of_finite
  exact Nat.card_pos

/-! ### The reduction brick, in its two consumed forms -/

/-- **Torsion injects into the reduction at an odd prime of good reduction**
(sorry leaf, opened 2026-07-26): if the integral Weierstrass model `W` has good
reduction at an odd prime `ℓ` (i.e. `ℓ ∤ Δ(W)`), the torsion subgroup of `W(ℚ)`
injects into `W(𝔽_ℓ)`.

STATED AS A BARE INJECTION, not as `#W(ℚ) ≤ #W(𝔽_ℓ)`, and the difference is
load-bearing rather than stylistic. A cardinality form would have to assume
`W(ℚ)` finite — `Nat.card` is `0` on infinite types — and that assumption is
precisely the Mordell–Weil input this brick is meant to *remove*. In the
injection form, "`W(ℚ)` is torsion" alone (rank `0`, one leaf) yields finiteness
and the count together, which is what let `curve14a4_fg` be deleted rather than
merely bypassed. It is also why the domain is the torsion subtype rather than
`W(ℚ)` itself: on the full group the statement is simply false whenever the rank
is positive.

CLASSICAL STATEMENT. Silverman *AEC* VII.3.1 together with VII.3.4: for
`E/K` over a local field with residue characteristic `ℓ`, the kernel `E₁(K)`
of reduction is the group of points of the formal group `Ê(𝔪)`, hence a
**pro-`ℓ` group**; so reduction is injective on prime-to-`ℓ` torsion always,
and injective on *all* torsion as soon as `e < ℓ − 1`, which for `K = ℚ_ℓ`
(`e = 1`) says exactly `ℓ ≠ 2`. Over `ℚ` with `ℓ ∤ Δ` the model is already
minimal at `ℓ`, so `E(ℚ) ⊆ E(ℚ_ℓ)` and the reduction is the coefficientwise
one.

`ℓ ≠ 2` IS NECESSARY, not defensive: at `ℓ = 2` the condition `e < ℓ − 1`
reads `1 < 1` and the `2`-torsion of `E(ℚ)` can lie in the kernel of
reduction, so the injection fails.

WHAT THIS TREE ALREADY HAS TOWARDS IT, so the next owner does not rebuild it.
`Fermat/FLT/KnownIn1980s/EllipticCurves/PointReduction.lean` (878 lines, no
sorries) constructs the reduction map on points for a `ValuationSubring` and
any local ring hom to a field: `WeierstrassCurve.IsReductionAlong`,
`redFun`, **`redHom : W.toAffine.Point →+ Wred.toAffine.Point`**, and
crucially `redFun_eq_zero_iff`, which identifies the kernel as the locus where
the abscissa is not integral. `Fermat/FLT/KnownIn1980s/EllipticCurves/GoodReduction.lean`
(1080 lines, no sorries) supplies the other half as a Lutz–Nagell integrality
statement: `WeierstrassCurve.torsion_abscissa_mem` and `torsion_ordinate_mem`
show, by Cassels' division-polynomial argument, that a torsion point of order
`n` with `n` a unit in the residue field has *integral* coordinates. Those two
compose to injectivity — a torsion point in the kernel would have non-integral
abscissa and integral abscissa at once, so it is `0`.

**BUT THAT COMPOSITION IS NOT THE WHOLE PROOF, AND THE GAP IS REAL** (audited
2026-07-26, correcting an earlier and over-optimistic version of this note that
called the remainder "bookkeeping"). Three obstacles, in increasing order of
seriousness:

1. `redHom` wants `A : ValuationSubring ℚ` at `ℓ` together with a local ring
   hom `A →+* ZMod ℓ`, and `IsReductionAlong A ρ (W⁄ℚ) (W.map (Int.castRingHom
   (ZMod ℓ)))`. Nothing in the tree builds the `ℓ`-adic valuation subring of
   `ℚ` in that form; `MazurTorsion.lean`'s good-reduction reductions go through
   `AlgebraicClosure (adicCompletion ℚ v)` and land in `𝔽̄_ℓ`, whose infinite
   residue field is useless for a cardinality bound. This part really is
   bookkeeping, but it is a few hundred lines of it.
2. `torsion_abscissa_mem` is stated over a SEPARABLE CLOSURE (`[IsSepClosure k
   ksep]`, with `𝒪 : ValuationSubring ksep` and a compatibility hypothesis
   `h𝒪`) and assumes mathlib's `[E.HasGoodReduction R]` for a DVR `R` with
   `Frac R = k`. That class extends `IsMinimal`, and deriving it from the
   elementary `ℓ ∤ Δ` of an integral model is itself unproven here.
3. **The decisive one.** `torsion_abscissa_mem` carries `[NeZero (n :
   ResidueField R)]`, i.e. `ℓ ∤ n`. So it yields injectivity only on the
   **prime-to-`ℓ`** torsion, and the `ℓ`-primary part — exactly where the
   hypothesis `ℓ ≠ 2` does its work, via `e < ℓ − 1` — is NOT covered by
   anything in this repository. That is the genuine formal-group content of
   Silverman VII.3.4 and it is missing from mathlib too (the only
   `FormalGroup` file, `Mathlib/RingTheory/FormalGroup/Basic.lean`, has no
   `neg`, no elliptic-curve attachment and no torsion-freeness).

Obstacle 3 is not academic for the consumer: `14a4(ℚ) ≅ ℤ/6` really does have
`3`-torsion, and the injection is applied there at `ℓ = 3`. A prime-to-`ℓ`
version of this leaf would therefore NOT close `curve14a4_points` at a single
prime; it would need a two-prime argument (`#14a4(𝔽₃) = #14a4(𝔽₅) = 6`) whose
group theory is messier than the statement above. The leaf is stated in the
full-torsion form because that is the standard theorem and the clean consumer
interface — not because the remainder is short. -/
theorem exists_injective_torsion_toReduction
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (W : WeierstrassCurve ℤ)
    (hΔ : ¬ ((ℓ : ℤ) ∣ W.Δ)) :
    ∃ f : {P : (W.map (Int.castRingHom ℚ)).toAffine.Point // IsOfFinAddOrder P} →
        (W.map (Int.castRingHom (ZMod ℓ))).toAffine.Point, Function.Injective f :=
  sorry

/-- **Potentially good reduction at a tame prime, packaged as a reduction
homomorphism injective on prime-to-`ℓ` torsion** (sorry leaf, opened 2026-07-26
as the cut of `exists_reduction_dvd_addOrderOf_of_jIntegral`): if `ℓ ≥ 5` and
`j(E)` is `ℓ`-integral, then there is an elliptic curve `W` over `𝔽_ℓ` and a
group homomorphism `f : E(ℚ) → W(𝔽_ℓ)` such that a point killed by an integer
prime to `ℓ` and lying in `ker f` is already `0`.

THIS IS THE WHOLE REDUCTION-THEORETIC CONTENT of
`exists_reduction_dvd_addOrderOf_of_jIntegral`; that theorem is now PROVEN over
this leaf by Lagrange, and it is the only consumer. The cut was chosen here
because everything downstream of "the reduction map exists and does not kill
prime-to-`ℓ` torsion" is elementary group theory, while everything upstream is
Silverman *AEC* VII and is a theory this repository does not have.

WHY THE KERNEL CONDITION IS PHRASED WITH AN ARBITRARY `n` rather than as
`Function.Injective f`. Injectivity on the nose is FALSE: `E(ℚ)` may have
positive rank, and the kernel of reduction is an infinite pro-`ℓ` group, so `f`
kills plenty. Injectivity holds exactly on the prime-to-`ℓ` torsion, and
`∀ P n, ¬ ℓ ∣ n → n • P = 0 → f P = 0 → P = 0` is that statement written
without having to name a torsion subgroup. Note `¬ ℓ ∣ n` already forces
`n ≠ 0`, since `ℓ ∣ 0`, so no separate nondegeneracy hypothesis is needed.
The `ℓ`-primary torsion really is NOT covered, and must not be: at a prime of
good ordinary reduction the `ℓ`-torsion of the kernel is where the formal group
lives.

CLASSICAL STATEMENT AND ROUTE. Silverman *AEC* VII.5.5 plus VII.3.1, in four
steps, of which the first three are the missing theory:

1. `¬ ℓ ∣ E.j.den` says `v_ℓ(j) ≥ 0`, so `E/ℚ_ℓ` has POTENTIALLY GOOD REDUCTION
   (*AEC* VII.5.5). This is an iff, and only this direction is needed.
2. Because `ℓ ≥ 5` the ramification is TAME, and good reduction is attained over
   a TOTALLY RAMIFIED extension `L/ℚ_ℓ` of degree `e = 12 / gcd(v_ℓ(Δ_min), 12)`,
   so `e ∈ {1, 2, 3, 4, 6, 12}` and `gcd(e, ℓ) = 1`. Concretely, choosing
   `u ∈ L` with `v_L(u) = v_ℓ(Δ_min) · e / 12` — an integer by the choice of
   `e` — the variable change `(x, y) ↦ (u²x, u³y)` scales `Δ` by `u^{-12}` and
   lands `v_L(Δ') = 0`.
   TOTALLY RAMIFIED IS THE LOAD-BEARING WORD: it makes the residue field of `L`
   equal to `𝔽_ℓ` rather than an extension of it, which is what keeps the
   resulting point count inside the `(#𝔽_ℓ)² + 1` bound the consumers use. An
   unramified or mixed extension would make this leaf true but useless.
3. Reduction `W(L) → W(𝔽_ℓ)` on the good model is a group homomorphism whose
   kernel is `E₁(L)`, the group of points of the formal group `Ê(𝔪_L)`, hence a
   PRO-`ℓ` group (*AEC* VII.3.1 with VII.2.2): an element killed by an integer
   prime to `ℓ` is therefore `0`. Composing with `E(ℚ) ⊆ E(ℚ_ℓ) ⊆ E(L) ≅ W(L)`
   gives `f`.
4. `W.IsElliptic` is exactly `v_L(Δ') = 0` read in the residue field.

WHAT THIS TREE HAS, AND THE THREE GAPS. Identical audit to
`exists_injective_torsion_toReduction` above, and the two leaves should be
attacked together by whoever builds the theory — they are the same machinery in
the good and the potentially-good case, and neither is a short composition:

* `Fermat/FLT/KnownIn1980s/EllipticCurves/PointReduction.lean` (sorry-free) has
  the reduction homomorphism on points, `redHom`, for a `ValuationSubring` and a
  local ring hom to a field, plus `redFun_eq_zero_iff` identifying the kernel by
  non-integrality of the abscissa. That is step 3's SHAPE but not its content.
* `Fermat/FLT/KnownIn1980s/EllipticCurves/GoodReduction.lean` (sorry-free) has
  Lutz–Nagell integrality, `torsion_abscissa_mem` and `torsion_ordinate_mem` —
  but under `[NeZero (n : ResidueField R)]`, i.e. only for prime-to-`ℓ` torsion.
  THAT IS EXACTLY THE RANGE THIS LEAF ASKS FOR, which is why this leaf is the
  more reachable of the two: unlike its sibling it does NOT need the
  formal-group `e < ℓ − 1` argument, only the pro-`ℓ` statement restricted to
  the prime-to-`ℓ` part, which is formal.
* GAP A (bookkeeping, a few hundred lines): nothing builds the `ℓ`-adic
  valuation subring of `ℚ`, or of a totally ramified `L/ℚ_ℓ`, in the form
  `redHom` wants. `MazurTorsion.lean`'s reductions go through
  `AlgebraicClosure (adicCompletion ℚ v)` and land in `𝔽̄_ℓ`, whose infinite
  residue field is useless for a cardinality bound — hence step 2's insistence
  on a totally ramified `L`.
* GAP B (real): step 1, the criterion `v(j) ≥ 0 ⟹ potentially good reduction`,
  is in neither this tree nor mathlib.
* GAP C (real): step 2, the tame totally-ramified model, needs minimal models
  and `v(Δ_min)`, which mathlib's `EllipticCurve/Reduction.lean` does not
  supply beyond `IsMinimal`.

NOT VACUOUS. The hypotheses are satisfiable — `ℓ = 5`, `E = 14a4`, whose `j` is
an integer — and there the conclusion is a genuine assertion, since `14a4(ℚ)`
has a point of order `7`. Nor is the conclusion satisfiable by junk: the zero
homomorphism does not work, because it would force every prime-to-`ℓ` torsion
point of `E(ℚ)` to vanish. -/
theorem exists_goodReductionHom_of_jIntegral
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ5 : 5 ≤ ℓ) (hj : ¬ (ℓ ∣ E.j.den)) :
    ∃ (W : WeierstrassCurve (ZMod ℓ)) (f : (E⁄ℚ).Point →+ W.toAffine.Point),
      W.IsElliptic ∧
        ∀ (P : (E⁄ℚ).Point) (n : ℕ), ¬ (ℓ ∣ n) → n • P = 0 → f P = 0 → P = 0 :=
  sorry

/-- **A rational point of prime order `p` survives reduction at any prime `ℓ ≥ 5`
of potentially good reduction** (PROVEN 2026-07-26 over the leaf
`exists_goodReductionHom_of_jIntegral` above): if `j(E)` is
`ℓ`-integral and `E/ℚ` carries a rational point of exact order `p ≠ ℓ`, then some
elliptic curve over `𝔽_ℓ` has `p` dividing its number of points.

WHY THE `∃` OVER CURVES OVER `𝔽_ℓ`. `E` itself need not have good reduction at
`ℓ`; it need only have *potentially* good reduction, and the curve that appears
downstream is the reduction of a good model over a ramified extension. Naming
that model would drag minimal models and quadratic twists into the statement
for no gain, since every consumer only ever uses the *bound* on `#W(𝔽_ℓ)`.
So the existential is the honest and the usable form.

CLASSICAL STATEMENT AND PROOF ROUTE. Silverman *AEC* VII.5.5 (the criterion
`v(j) ≥ 0 ⟺ potentially good reduction`) plus VII.3.1 (the kernel of reduction
is pro-`ℓ`). Explicitly: `v_ℓ(j(E)) ≥ 0` gives `E/ℚ_ℓ` potentially good. For
`ℓ ≥ 5` the ramification is tame and one may take the good-reduction field to be
the **totally ramified** extension `L = ℚ_ℓ(π^{1/e})` with
`e = 12 / gcd(v_ℓ(Δ_min), 12) ∈ {1,2,3,4,6,12}`: the variable change
`(x, y) ↦ (u²x, u³y)` with `v_L(u) = 1` scales `Δ` by `u^{-12}`, so `e` chosen
that way makes `v_L(Δ) = 0`. Totally ramified is the load-bearing word — the
residue field of `L` is then `𝔽_ℓ` itself and not an extension of it, which is
exactly what keeps the point count bounded by `(#𝔽_ℓ)² + 1`. Now `E(ℚ) ⊆ E(L)`,
the kernel `E₁(L)` of reduction is a pro-`ℓ` group, and `p ≠ ℓ`, so the given
point of order `p` maps to a point of order `p` on the reduction `W/𝔽_ℓ`;
hence `p ∣ #W(𝔽_ℓ)` by Lagrange.

The `ℓ ≥ 5` hypothesis is what makes the ramification tame and `e ∣ 12`; at
`ℓ = 2, 3` wild ramification allows `e ∣ 24` and the totally-ramified statement
needs more care. It costs nothing here — every consumer uses `ℓ = 5`.

NOT VACUOUS. The conclusion is a genuine assertion about `𝔽_ℓ`-curves; it is
the consumers that combine it with `#W(𝔽_ℓ) ≤ (#𝔽_ℓ)² + 1` to reach a
contradiction. In particular the hypotheses are jointly satisfiable for small
`p` — e.g. `p = 7`, `ℓ = 5`, `E = 14a4` — where the conclusion is true and
non-trivial.

DECOMPOSED 2026-07-26, and this declaration is now PROVEN. All of the
reduction-theoretic content was factored out into the single leaf
`exists_goodReductionHom_of_jIntegral` below; what remains here — the passage
from "a homomorphism injective on prime-to-`ℓ` torsion" to the divisibility
`p ∣ #W(𝔽_ℓ)` — is Lagrange plus `addOrderOf_map_dvd`, and is proven. See that
leaf's docstring for the route and the audit. -/
theorem exists_reduction_dvd_addOrderOf_of_jIntegral
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {ℓ p : ℕ} [Fact ℓ.Prime]
    (hℓ5 : 5 ≤ ℓ) (hp : p.Prime) (hpℓ : p ≠ ℓ) (hj : ¬ (ℓ ∣ E.j.den))
    (Q : (E⁄ℚ).Point) (hQ : addOrderOf Q = p) :
    ∃ W : WeierstrassCurve (ZMod ℓ), W.IsElliptic ∧ p ∣ Nat.card W.toAffine.Point := by
  obtain ⟨W, f, hW, hker⟩ := E.exists_goodReductionHom_of_jIntegral hℓ5 hj
  refine ⟨W, hW, ?_⟩
  -- `ℓ ∤ p`: two distinct primes.
  have hℓp : ¬ (ℓ ∣ p) := fun h => hpℓ ((Nat.prime_dvd_prime_iff_eq Fact.out hp).mp h).symm
  -- `Q` is killed by `p`, which is prime to `ℓ`, so `Q` is not in the kernel of `f`.
  have hpQ : p • Q = 0 := hQ ▸ addOrderOf_nsmul_eq_zero Q
  have hfQ0 : f Q ≠ 0 := by
    intro h
    have hQ0 : Q = 0 := hker Q p hℓp hpQ h
    rw [hQ0, addOrderOf_zero] at hQ
    exact hp.one_lt.ne hQ
  -- Its image therefore has order exactly `p`.
  have hdvd : addOrderOf (f Q) ∣ p := hQ ▸ addOrderOf_map_dvd f Q
  have hfQ : addOrderOf (f Q) = p := by
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp _ hdvd) with h1 | hpp
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h1) hfQ0
    · exact hpp
  -- Lagrange in the finite group `W(𝔽_ℓ)`.
  exact hfQ ▸ addOrderOf_dvd_natCard (f Q)

end WeierstrassCurve
