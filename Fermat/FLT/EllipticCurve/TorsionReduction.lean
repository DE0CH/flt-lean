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
  `curve14a4_finite`.

  **NOT WIRED UP — this bullet is a PLAN, not a description of the tree**
  (integrator, 2026-07-27). This module arrived on a branch that also rewrote
  `MordellWeil.lean` to run `14a4` through the reduction route above. That rival
  route was measured to need MORE leaves than the released one and was NOT
  taken, so `MordellWeil.lean` neither imports this module nor uses any of it,
  and `curve14a4_points` is still closed the released way. Nothing here is
  consumed at level `14` today. A future owner who wants the reduction route
  should add `public import Fermat.FLT.EllipticCurve.TorsionReduction` there —
  the brick is general in the curve and the prime, so it needs no new
  mathematics — rather than build a second copy. (`curve14a4_fg` is already
  gone from `MordellWeil.lean` on the released route, for its own reasons; it
  is not waiting on this module.)
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
`exists_reduction_dvd_addOrderOf_of_jIntegral` (potentially good reduction) are
the module's two bricks. Both are Silverman *AEC* VII; see their docstrings for
the precise citation, the proof route, and an AUDIT of what this tree already
has towards them.

**Brick 1 is PROVEN (2026-07-26)**, over two smaller leaves it was decomposed
into on the same day, and the reduction bookkeeping underneath it is proven
outright:

* `RatAdic.valuationSubring` / `RatAdic.res` / `isReductionAlong_ratAdic` /
  `map_zmod_Δ_ne_zero` — the `ℓ`-adic reduction datum over `ℚ`, feeding
  `PointReduction.lean`'s `redHom`. PROVEN.
* `redHom_eq_zero_iff_of_isOfFinAddOrder` — the group theory reducing "the
  kernel meets the torsion trivially" to the case of PRIME order. PROVEN.
* `redHom_ne_zero_of_prime_order_ne` — the prime-to-`ℓ` (Lutz–Nagell) half.
  OPEN; `GoodReduction.lean`'s `torsion_abscissa_mem` is the right theorem and
  the leaf's docstring lists the three obligations to instantiate it.
* `redHom_ne_zero_of_addOrderOf_eq` — the `ℓ`-primary half, where `ℓ ≠ 2` does
  its work via `e < ℓ − 1`. OPEN, and it is the one piece that is genuinely
  missing mathematics: the formal group of a Weierstrass curve and its
  torsion-freeness exist in neither this tree nor mathlib.

Do not start the two open ones expecting a short composition.

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
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Fermat.FLT.KnownIn1980s.EllipticCurves.PointReduction

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

/-! ### The `ℓ`-adic reduction datum over `ℚ`

Everything in this section is PROVEN (2026-07-26). It is what the previous
version of the brick-1 docstring called "obstacle 1 — a few hundred lines of
bookkeeping": the `ℓ`-adic valuation subring of `ℚ`, the residue map to `𝔽_ℓ`,
its locality, and the `IsReductionAlong` datum that feeds
`WeierstrassCurve.IsReductionAlong.redHom` from `PointReduction.lean`. It came
to about seventy lines rather than a few hundred, because mathlib's
`IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime` already packages
the localization of a Dedekind domain at a height-one prime as a
`ValuationSubring` of the fraction field, *and* registers the
`IsLocalization` instance that makes the residue map a one-liner
(`IsLocalization.lift`). The audit that estimated "a few hundred lines" did not
know that declaration existed. -/

namespace RatAdic

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

/-- The height-one spectrum point of `ℤ` at the prime `ℓ`. -/
def spec : IsDedekindDomain.HeightOneSpectrum ℤ where
  asIdeal := Ideal.span {(ℓ : ℤ)}
  isPrime := (Ideal.span_singleton_prime (by exact_mod_cast hℓ.out.ne_zero)).mpr
    (Int.prime_iff_natAbs_prime.mpr (by simpa using hℓ.out))
  ne_bot := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hℓ.out.ne_zero

/-- **`ℤ_(ℓ) ⊆ ℚ`**, the `ℓ`-adic valuation subring of `ℚ`: the localization of
`ℤ` at `(ℓ)`, viewed inside `ℚ`. -/
noncomputable abbrev valuationSubring : ValuationSubring ℚ :=
  IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ℚ (spec ℓ)

theorem mem_primeCompl_iff (y : ℤ) :
    y ∈ (spec ℓ).asIdeal.primeCompl ↔ ¬ ((ℓ : ℤ) ∣ y) := by
  simp [spec, Ideal.primeCompl, Ideal.mem_span_singleton]

theorem isUnit_intCast_of_mem_primeCompl (y : (spec ℓ).asIdeal.primeCompl) :
    IsUnit ((Int.castRingHom (ZMod ℓ)) (y : ℤ)) := by
  have h := (mem_primeCompl_iff ℓ (y : ℤ)).mp y.2
  rw [isUnit_iff_ne_zero]
  simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using h

/-- **The residue map `ℤ_(ℓ) →+* 𝔽_ℓ`**, obtained from the universal property of
the localization: every element of `(ℓ)ᶜ` is invertible in `ZMod ℓ`. -/
noncomputable def res : valuationSubring ℓ →+* ZMod ℓ :=
  IsLocalization.lift (isUnit_intCast_of_mem_primeCompl ℓ)

theorem intCast_mem_valuationSubring (n : ℤ) : (n : ℚ) ∈ valuationSubring ℓ := intCast_mem _ n

theorem coe_algebraMap_int (n : ℤ) :
    ((algebraMap ℤ (valuationSubring ℓ) n : valuationSubring ℓ) : ℚ) = (n : ℚ) := Rat.ext rfl rfl

@[simp]
theorem res_intCast (n : ℤ) (h : (n : ℚ) ∈ valuationSubring ℓ) :
    res ℓ ⟨(n : ℚ), h⟩ = (n : ZMod ℓ) := by
  have he : (⟨(n : ℚ), h⟩ : valuationSubring ℓ) = algebraMap ℤ (valuationSubring ℓ) n :=
    Subtype.ext (coe_algebraMap_int ℓ n).symm
  rw [he, res, IsLocalization.lift_eq]
  rfl

/-- `res ℓ` is a local ring hom, as `PointReduction.lean`'s API requires. An
element of `ℤ_(ℓ)` is `IsLocalization.mk' n d`; its residue is nonzero exactly
when `ℓ ∤ n`, which is exactly when `n` too lies in `(ℓ)ᶜ` and the element is a
unit. -/
instance : IsLocalHom (res ℓ) where
  map_nonunit a ha := by
    obtain ⟨⟨n, d⟩, rfl⟩ := IsLocalization.mk'_surjective ((spec ℓ).asIdeal.primeCompl) a
    rw [res, IsLocalization.lift_mk'] at ha
    have hn : n ∈ (spec ℓ).asIdeal.primeCompl := by
      rw [mem_primeCompl_iff]
      intro hdvd
      rw [isUnit_iff_ne_zero] at ha
      refine ha ?_
      have h0 : ((Int.castRingHom (ZMod ℓ)) n) = 0 := by
        simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hdvd
      rw [h0, zero_mul]
    exact isUnit_iff_exists_inv.mpr ⟨_, IsLocalization.mk'_mul_mk'_eq_one ⟨n, hn⟩ d⟩

end RatAdic

/-- **The reduction datum of an integral model at `ℓ`**: the coefficients of
`W⁄ℚ` are integers, hence lie in `ℤ_(ℓ)`, and their residues are the
coefficients of `W⁄𝔽_ℓ`. This is the hypothesis of
`WeierstrassCurve.IsReductionAlong.redHom`. -/
theorem isReductionAlong_ratAdic (ℓ : ℕ) [Fact ℓ.Prime] (W : WeierstrassCurve ℤ) :
    IsReductionAlong (RatAdic.valuationSubring ℓ) (RatAdic.res ℓ)
      (W.map (Int.castRingHom ℚ)) (W.map (Int.castRingHom (ZMod ℓ))) where
  a₁_mem := by rw [map_a₁]; exact RatAdic.intCast_mem_valuationSubring ℓ _
  a₂_mem := by rw [map_a₂]; exact RatAdic.intCast_mem_valuationSubring ℓ _
  a₃_mem := by rw [map_a₃]; exact RatAdic.intCast_mem_valuationSubring ℓ _
  a₄_mem := by rw [map_a₄]; exact RatAdic.intCast_mem_valuationSubring ℓ _
  a₆_mem := by rw [map_a₆]; exact RatAdic.intCast_mem_valuationSubring ℓ _
  a₁_eq := (RatAdic.res_intCast ℓ W.a₁ _).symm
  a₂_eq := (RatAdic.res_intCast ℓ W.a₂ _).symm
  a₃_eq := (RatAdic.res_intCast ℓ W.a₃ _).symm
  a₄_eq := (RatAdic.res_intCast ℓ W.a₄ _).symm
  a₆_eq := (RatAdic.res_intCast ℓ W.a₆ _).symm

/-- **`ℓ ∤ Δ` makes the reduced curve nonsingular**, which is the side condition
every `redFun`/`redHom` statement carries. -/
theorem map_zmod_Δ_ne_zero {ℓ : ℕ} [Fact ℓ.Prime] (W : WeierstrassCurve ℤ)
    (hΔ : ¬ ((ℓ : ℤ) ∣ W.Δ)) : (W.map (Int.castRingHom (ZMod ℓ))).Δ ≠ 0 := by
  rw [map_Δ]
  simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hΔ

/-! ### The reduction brick, in its two consumed forms

Brick 1 (`exists_injective_torsion_toReduction`) is PROVEN below, over the two
sorried leaves `redHom_ne_zero_of_prime_order_ne` and
`redHom_ne_zero_of_addOrderOf_eq` stated first. That cut is the point of the
2026-07-26 decomposition: the old single leaf mixed three unrelated difficulties
(the valuation-subring bookkeeping, the prime-to-`ℓ` Lutz–Nagell theorem, and
the `ℓ`-primary formal-group theorem), and only the last of the three is
genuinely missing from mathematics-as-formalised-here. The bookkeeping is now
done, and the two theorems are separated so they can be owned independently. -/

/-- **No point of prime order `q ≠ ℓ` lies in the kernel of reduction** (sorry
leaf, opened 2026-07-26 by decomposing `exists_injective_torsion_toReduction`).

This is the PRIME-TO-`ℓ` half, i.e. Lutz–Nagell. By
`WeierstrassCurve.IsReductionAlong.redFun_eq_zero_iff` the conclusion is
equivalent to saying the abscissa of `P` is `ℓ`-integral, so this is exactly the
classical statement "torsion of order prime to `ℓ` has integral coordinates".
Silverman *AEC* VII.3.1: the kernel of reduction is the group of points of the
formal group `Ê(𝔪)`, which is pro-`ℓ`, so it contains no element of order prime
to `ℓ`. `hℓ2` is deliberately ABSENT from this statement — the odd-prime
hypothesis does no work in the prime-to-`ℓ` regime, and including it would
misrepresent the mathematics.

ROUTE THROUGH THIS TREE, with the three obligations it still costs.
`Fermat/FLT/KnownIn1980s/EllipticCurves/GoodReduction.lean` proves
`WeierstrassCurve.torsion_abscissa_mem` (Cassels' division-polynomial argument),
whose `[NeZero (n : IsLocalRing.ResidueField R)]` is precisely `q ≠ ℓ`, so it is
the right theorem. Instantiating it at `R = ℤ_(ℓ)` (= `RatAdic.valuationSubring
ℓ`, which is a DVR with `IsFractionRing ℤ_(ℓ) ℚ`) needs:

1. `[E.HasGoodReduction R]` for `E = W⁄ℚ` from the elementary `ℓ ∤ Δ(W)`. That
   class extends `IsMinimal`, so this is "an integral model with unit
   discriminant at `ℓ` is minimal at `ℓ` and has good reduction there".
2. A separable closure `ℚˢᵉᵖ` together with a valuation subring `𝒪` above
   `ℤ_(ℓ)` satisfying `torsion_abscissa_mem`'s compatibility hypothesis
   `(𝒪.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range` — i.e. an
   extension of the `ℓ`-adic valuation to `ℚˢᵉᵖ` restricting back exactly.
3. Descent of the conclusion `x ∈ 𝒪` along `ℚ → ℚˢᵉᵖ` to `x ∈ ℤ_(ℓ)`, which is
   immediate from the compatibility in 2.

None of the three is deep; together they are a real task, which is why this is a
leaf and not an inlined `have`. THE CHECK THAT WOULD REFUTE THIS ROUTE: grep for
an instance producing `HasGoodReduction` from a discriminant hypothesis, and for
a mathlib extension theorem for valuation subrings along a separable closure — if
either exists the route shortens accordingly. -/
theorem redHom_ne_zero_of_prime_order_ne {ℓ : ℕ} [Fact ℓ.Prime] (W : WeierstrassCurve ℤ)
    (hΔ : ¬ ((ℓ : ℤ) ∣ W.Δ)) {q : ℕ} (hq : q.Prime) (hqℓ : q ≠ ℓ)
    {P : (W.map (Int.castRingHom ℚ)).toAffine.Point} (hP : addOrderOf P = q) :
    (isReductionAlong_ratAdic ℓ W).redHom (map_zmod_Δ_ne_zero W hΔ) P ≠ 0 :=
  sorry

/-- **No point of order `ℓ` lies in the kernel of reduction, for `ℓ` odd** (sorry
leaf, opened 2026-07-26 by decomposing `exists_injective_torsion_toReduction`).

THIS IS THE GENUINELY MISSING MATHEMATICS, and it is the reason brick 1 is not a
short composition of the two theorems this tree already has. Silverman *AEC*
VII.3.4 / IV.6.1: the kernel of reduction is `Ê(𝔪)` for the formal group `Ê` of
`E` over `ℤ_ℓ`, and `Ê(𝔪)` is TORSION-FREE as soon as `e < ℓ − 1`, where `e` is
the absolute ramification index. Over `ℚ_ℓ` we have `e = 1`, so `e < ℓ − 1` reads
`ℓ > 2` — which is exactly `hℓ2`, and `hℓ2` is therefore load-bearing here and
nowhere else in the brick. At `ℓ = 2` the statement is FALSE in general: the
`2`-torsion can lie in the kernel of reduction.

WHAT WOULD HAVE TO BE BUILT, none of which exists in this tree or in mathlib
(verified 2026-07-26 by reading `Mathlib/RingTheory/FormalGroup/Basic.lean` in
full — it has `FormalGroup`, `𝔾ₐ`, `𝔾ₘ`, `map`, and an `AddCommMonoid` on
`F.Point`, and that is ALL: no `neg`, no elliptic-curve attachment, no
logarithm, no torsion statement):

* the formal group law `Ê` attached to a Weierstrass curve — the power series
  `w(z₁, z₂)` and the addition law `F(z₁, z₂) ∈ R⟦z₁, z₂⟧` (Silverman IV.1);
* its formal logarithm and exponential, with the convergence estimate that makes
  `log : Ê(𝔪) ≃ 𝔾ₐ(𝔪)` an isomorphism when `e < ℓ − 1` (Silverman IV.6.4);
* the identification of `ker(reduction)` with `Ê(𝔪)` via the parameter
  `z = −x/y` (Silverman VII.2.2).

An alternative avoiding the logarithm is the filtration `E_n = {P : v(x(P)) ≤
−2n}` with `E_n/E_{n+1} ↪ (𝔽_ℓ, +)`, but it still needs the power-series
expansion of the group law to get the valuation estimate on `[ℓ]`, so it is not
a cheaper route — only a differently packaged one.

NOT VACUOUS, and the consumer proves it: `14a4(ℚ) ≅ ℤ/6` has a point of order
`3` and `MordellWeil.lean` applies brick 1 at `ℓ = 3`. So this leaf is exercised
at `q = ℓ = 3`; a prime-to-`ℓ` brick would not close that consumer. -/
theorem redHom_ne_zero_of_addOrderOf_eq {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    (W : WeierstrassCurve ℤ) (hΔ : ¬ ((ℓ : ℤ) ∣ W.Δ))
    {P : (W.map (Int.castRingHom ℚ)).toAffine.Point} (hP : addOrderOf P = ℓ) :
    (isReductionAlong_ratAdic ℓ W).redHom (map_zmod_Δ_ne_zero W hΔ) P ≠ 0 :=
  sorry

/-- **The kernel of reduction meets the torsion trivially** (PROVEN 2026-07-26
over the two leaves above).

The reduction step is pure group theory and is what makes the two leaves above
suffice: a nonzero point `P` of finite order `m` has `m ≠ 1`, so `q := m.minFac`
is prime and `(m / q) • P` has order exactly `q`; the kernel is a subgroup, so
that multiple is still in it; and `q` is either `ℓ` or not. -/
theorem redHom_eq_zero_iff_of_isOfFinAddOrder {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    (W : WeierstrassCurve ℤ) (hΔ : ¬ ((ℓ : ℤ) ∣ W.Δ))
    {P : (W.map (Int.castRingHom ℚ)).toAffine.Point} (hP : IsOfFinAddOrder P) :
    (isReductionAlong_ratAdic ℓ W).redHom (map_zmod_Δ_ne_zero W hΔ) P = 0 ↔ P = 0 := by
  refine ⟨fun hker => ?_, fun h => by rw [h, map_zero]⟩
  by_contra hP0
  set m := addOrderOf P
  have hm0 : m ≠ 0 := hP.addOrderOf_pos.ne'
  have hm1 : m ≠ 1 := fun h => hP0 (AddMonoid.addOrderOf_eq_one_iff.mp h)
  have hqp : (m.minFac).Prime := Nat.minFac_prime hm1
  have hord : addOrderOf ((m / m.minFac) • P) = m.minFac :=
    addOrderOf_nsmul_addOrderOf_sub hm0 (Nat.minFac_dvd m)
  have hkerQ : (isReductionAlong_ratAdic ℓ W).redHom (map_zmod_Δ_ne_zero W hΔ)
      ((m / m.minFac) • P) = 0 := by rw [map_nsmul, hker, smul_zero]
  by_cases hqℓ : m.minFac = ℓ
  · exact redHom_ne_zero_of_addOrderOf_eq hℓ2 W hΔ (hqℓ ▸ hord) hkerQ
  · exact redHom_ne_zero_of_prime_order_ne W hΔ hqp hqℓ hord hkerQ

/-- **Torsion injects into the reduction at an odd prime of good reduction**
(PROVEN 2026-07-26 over `redHom_ne_zero_of_prime_order_ne` and
`redHom_ne_zero_of_addOrderOf_eq`): if the integral Weierstrass model `W` has
good reduction at an odd prime `ℓ` (i.e. `ℓ ∤ Δ(W)`), the torsion subgroup of
`W(ℚ)` injects into `W(𝔽_ℓ)`.

THE INJECTION IS THE REDUCTION MAP, not merely some abstract injection: the
witness produced is `(isReductionAlong_ratAdic ℓ W).redHom` restricted to the
torsion subtype. That matters, because the existential form of the statement
would also be satisfied by any counting argument, and a consumer that later
needs compatibility with the group law would be stuck with a useless witness.

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

**WHERE THE THREE-OBSTACLE AUDIT OF 2026-07-26 STANDS NOW** (updated the same
day, by the owner who carried it out). The audit listed three obstacles; the
first is DISCHARGED and the other two are now the two named sorry leaves above,
so this docstring's job is only to say which is which.

1. *(DISCHARGED, and it was over-estimated.)* "Nothing in the tree builds the
   `ℓ`-adic valuation subring of `ℚ` … a few hundred lines of bookkeeping." It
   is built, in the `RatAdic` section above, in about seventy lines. The audit
   did not know about mathlib's
   `IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime`, which supplies
   the subring together with the `IsLocalization` instance that reduces the
   residue map to one `IsLocalization.lift` and its locality to one
   `mk'`-computation. The audit's remark that `MazurTorsion.lean`'s reductions
   land in `𝔽̄_ℓ` and are useless here remains correct and is why a fresh
   construction was the right move.
2. *(Now `redHom_ne_zero_of_prime_order_ne`.)* `torsion_abscissa_mem` is stated
   over a separable closure and assumes `[E.HasGoodReduction R]`. Still true;
   see that leaf's docstring for the three residual obligations.
3. *(Now `redHom_ne_zero_of_addOrderOf_eq`.)* The `ℓ`-primary half, the genuine
   formal-group content of Silverman VII.3.4, absent from this tree and from
   mathlib. Still true; see that leaf's docstring for what would have to be
   built.

Obstacle 3 is not academic for the consumer: `14a4(ℚ) ≅ ℤ/6` really does have
`3`-torsion, and the injection is applied there at `ℓ = 3`. A prime-to-`ℓ`
version of this brick would therefore NOT close `curve14a4_points` at a single
prime; it would need a two-prime argument (`#14a4(𝔽₃) = #14a4(𝔽₅) = 6`) whose
group theory is messier than the statement above. The brick is stated in the
full-torsion form because that is the standard theorem and the clean consumer
interface — not because the remainder is short. -/
theorem exists_injective_torsion_toReduction
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (W : WeierstrassCurve ℤ)
    (hΔ : ¬ ((ℓ : ℤ) ∣ W.Δ)) :
    ∃ f : {P : (W.map (Int.castRingHom ℚ)).toAffine.Point // IsOfFinAddOrder P} →
        (W.map (Int.castRingHom (ZMod ℓ))).toAffine.Point, Function.Injective f := by
  refine ⟨fun P => (isReductionAlong_ratAdic ℓ W).redHom (map_zmod_Δ_ne_zero W hΔ) P.val, ?_⟩
  rintro ⟨P, hP⟩ ⟨Q, hQ⟩ hPQ
  simp only at hPQ
  rw [Subtype.mk.injEq]
  have htor : IsOfFinAddOrder (P - Q) :=
    (AddCommGroup.mem_torsion _).mp (AddSubgroup.sub_mem (AddCommGroup.torsion _)
      ((AddCommGroup.mem_torsion P).mpr hP) ((AddCommGroup.mem_torsion Q).mpr hQ))
  have hzero : (isReductionAlong_ratAdic ℓ W).redHom (map_zmod_Δ_ne_zero W hΔ) (P - Q) = 0 := by
    rw [map_sub, hPQ, sub_self]
  exact sub_eq_zero.mp ((redHom_eq_zero_iff_of_isOfFinAddOrder hℓ2 W hΔ htor).mp hzero)

/-- **A rational point of prime order `p` survives reduction at any prime `ℓ ≥ 5`
of potentially good reduction** (sorry leaf, opened 2026-07-26): if `j(E)` is
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
non-trivial. -/
theorem exists_reduction_dvd_addOrderOf_of_jIntegral
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {ℓ p : ℕ} [Fact ℓ.Prime]
    (hℓ5 : 5 ≤ ℓ) (hp : p.Prime) (hpℓ : p ≠ ℓ) (hj : ¬ (ℓ ∣ E.j.den))
    (Q : (E⁄ℚ).Point) (hQ : addOrderOf Q = p) :
    ∃ W : WeierstrassCurve (ZMod ℓ), W.IsElliptic ∧ p ∣ Nat.card W.toAffine.Point :=
  sorry

end WeierstrassCurve
