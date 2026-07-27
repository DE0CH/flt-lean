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

This module has exactly ONE consumer, and it is the reason the module exists:

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

## The brick

`exists_reduction_dvd_addOrderOf_of_jIntegral` (potentially good reduction) is
the module's brick. It is Silverman *AEC* VII; see its docstring for the precise
citation, the proof route, and an AUDIT of what this tree already has towards it.
**It is now PROVEN**, over its own smaller leaves; what follows is the state of
those leaves.

**A SECOND BRICK WAS DELETED HERE ON 2026-07-27 — DO NOT RECREATE IT WITHOUT A
CONSUMER.** `exists_injective_torsion_toReduction` ("the torsion of `W(ℚ)`
injects into `W(𝔽_ℓ)` at an odd prime `ℓ ∤ Δ`"), together with
`redHom_eq_zero_iff_of_isOfFinAddOrder` and its two leaves
`redHom_ne_zero_of_prime_order_ne` and `redHom_ne_zero_of_addOrderOf_eq`, was
removed as free-floating: it had **zero** consumers anywhere in the tree. It was
built for a rewrite of `MordellWeil.lean` that would have run `14a4` through the
reduction route, and that rewrite was measured to need MORE leaves than the
released route and was not taken — `main` derives `curve14a4_points`,
`curve14a4_finite` and `curve14a4_isTorsion` unconditionally from the single
plane-Diophantine leaf `curve14a4_rational_T`, with no reduction step at all.

The check that would refute this and justify restoring it:
`grep -rn 'exists_injective_torsion_toReduction' Fermat/` finding a use in a
proof body, or `grep -rn 'public import Fermat.FLT.EllipticCurve.TorsionReduction' Fermat/`
naming a module other than `FreyCurve/MazurTorsion.lean`. Recover the text with
`git show <this commit>^:Fermat/FLT/EllipticCurve/TorsionReduction.lean`. Note
that little is lost: `redHom_eq_zero_of_nsmul_eq_zero` below SUBSUMES
`redHom_ne_zero_of_prime_order_ne`, and the surviving `RatAdic` block is exactly
the bookkeeping that brick needed.

**The brick, `exists_reduction_dvd_addOrderOf_of_jIntegral`, is PROVEN
(2026-07-26)** over the single reduction leaf
`exists_goodReductionHom_of_jIntegral` — "there is a group homomorphism
`E(ℚ) → W(𝔽_ℓ)` onto an elliptic curve over `𝔽_ℓ` that does not kill
prime-to-`ℓ` torsion". Everything downstream of that (Lagrange, and the passage
from a point of order `p` to `p ∣ #W(𝔽_ℓ)`) is elementary and is proven.

That leaf was in turn DECOMPOSED on 2026-07-27 and is now PROVEN, over

* `exists_tameGoodModel_of_jIntegral` — the arithmetic: `E` acquires good
  reduction over an extension in which `ℓ` is TOTALLY RAMIFIED. **DECOMPOSED AND
  PROVEN 2026-07-27**, over the `TameBase` interface, which separates the
  number theory from the curve theory. What remains open under it is:
  * `nonempty_tameBase` — the field `ℚ(ℓ^{1/12})` with `ℓ` totally ramified and
    residue field `𝔽_ℓ`. Independent of `E` and of `Δ`: ONE field serves every
    curve and every `ℓ`. OPEN, and the only genuinely missing theory left in the
    potentially-good chain.
  * `padicValRat_Δ_le_of_jIntegral` — `v_ℓ(j) ≥ 0 ⟹ 3v(A) ≥ v(Δ)` and
    `2v(B) ≥ v(Δ)`, a statement about three rational numbers. OPEN, elementary.
  The scaling itself (`exists_tameGoodModel_of_isShortNF`) is PROVEN, and so is
  the reduction to short Weierstrass form. One of the four obligations the
  pre-decomposition docstring listed — a `VariableChange`-induced map on
  `Affine.Point` — turned out to exist already in `Fermat/FLT/Mathlib/`.
* `redHom_eq_zero_of_nsmul_eq_zero` — Lutz–Nagell: the kernel of reduction
  contains no point killed by an integer prime to `ℓ`. **PROVEN 2026-07-27**,
  directly from Cassels' division-polynomial argument at the stated generality
  (an arbitrary valuation subring with residue field `𝔽_ℓ`) — no DVR, no
  separable closure, no formal group. It is the general form of the `ℚ`-specific
  twin that was deleted as free-floating on the same day.

The key structural discovery, made while cutting it, is worth repeating here:
**the `RatAdic` bookkeeping generalises verbatim from `ℚ` to any number
field**, because `IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime`
is stated for an arbitrary Dedekind domain. That is what makes the
potentially-good case reachable without `ℚ_ℓ`, formal groups, or Tate's
algorithm: one may work over the number field `ℚ(ℓ^{1/e})`, in which `ℓ` is
TOTALLY RAMIFIED, so the residue field is still `𝔽_ℓ`.

Do not start the open ones expecting a short composition.

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
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Fermat.FLT.KnownIn1980s.EllipticCurves.PointReduction
-- The three imports below are what `redHom_eq_zero_of_nsmul_eq_zero` consumes:
-- `ValuationSubring.mem_of_root_of_inv_leadingCoeff_mem` (GoodReduction), the
-- division-polynomial torsion dictionary `TorsionCard.smul_some_eq_zero_iff`, and
-- the degree/leading-coefficient facts about `ΨSq`. All three are PUBLIC on purpose:
-- `TorsionCard` and `Degree` are already in this module's cone, but only through
-- `PointReduction → Flat`, which imports them PRIVATELY — and a private import
-- upstream makes the names unavailable even in proof bodies. `GoodReduction` is the
-- only module this adds to the cone; its own imports are all present already.
public import Fermat.FLT.KnownIn1980s.EllipticCurves.GoodReduction
public import Fermat.FLT.EllipticCurve.TorsionCard
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
-- And these three are what the decomposition of `exists_tameGoodModel_of_jIntegral`
-- consumes: the short-Weierstrass normal form, `padicValRat`, and — the one that
-- retires a whole obligation the pre-decomposition docstring recorded as missing —
-- this project's own shim `Affine.Point.equivVariableChange`.
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Fermat.FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

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
(which mathlib does not have). It is enough where it is used at `p ≥ 37`: at
`K = 𝔽₅` it gives `26`, and the primes to be excluded there are `≥ 37`.

UPDATE 2026-07-27: the sharper `≤ 2·#K + 1` this docstring used to record as
"available … but not needed" IS needed, and is now proven as
`natCard_affine_point_le_two_mul` below. At `K = 𝔽₅` it gives `11`, which is
what lets the SAME reduction argument reach `p ∈ {17, 19}` — where `26` is
useless — and so retire the explicit plane models of `X_1(17)` and `X_1(19)`
in `MazurTorsion.lean`. Keep this cruder version: it needs no `IsDomain`
hypothesis, and it is what the `p ≥ 37` proof is written against. -/
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

/-! #### The sharper fibrewise bound `#W(K) ≤ 2·#K + 1`

Added 2026-07-27. The crude bound above counts the affine points inside
`K × K`; this one counts them fibrewise over the abscissa, where the
Weierstrass equation is a QUADRATIC in `y` and so has at most two roots. The
gain at `K = 𝔽₅` is `26 ↦ 11`, and that is exactly the difference between
reaching `p ≥ 37` and reaching `p ∈ {17, 19}`.

It is still not Hasse (`#W(𝔽₅) ≤ 10`), and it does not need to be. -/

section Domain

variable {R : Type*} [CommRing R] [IsDomain R]

/-- **Two points of an affine Weierstrass curve over a domain with the same
abscissa have equal or negated ordinates.** Subtracting the two Weierstrass
equations factors as `(y₁ − y₂)(y₁ + y₂ + a₁x + a₃) = 0`, and the second factor
vanishing is exactly `y₁ = negY x y₂`. Being a domain is what makes the product
vanish factorwise; nothing else here uses it.

This is the same computation as `MazurLevel13.y_eq_or_eq_negY` used to run over
`ℚ` in `MazurTorsion.lean`; it is stated here over a general domain because the
consumer is the point count over `𝔽_ℓ`. -/
theorem Affine.eq_or_eq_negY_of_equation {W : Affine R} {x y₁ y₂ : R}
    (h₁ : W.Equation x y₁) (h₂ : W.Equation x y₂) :
    y₁ = y₂ ∨ y₁ = W.negY x y₂ := by
  rw [Affine.equation_iff] at h₁ h₂
  have h : (y₁ - y₂) * (y₁ + y₂ + W.a₁ * x + W.a₃) = 0 := by linear_combination h₁ - h₂
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (by rw [Affine.negY]; linear_combination h)

/-- **`#W(K) ≤ 2·#K + 1`** over a finite domain — the sharper crude bound.

Each fibre of `(x, y) ↦ x` on the affine points has at most two elements, by
`Affine.eq_or_eq_negY_of_equation`: every ordinate over a given abscissa is
either a fixed `y₀` or `negY x y₀`. Summing over the `#K` abscissae gives
`2·#K` affine points, and the point at infinity is the `+ 1`.

At `K = 𝔽₅` this gives `11`, against `26` from `natCard_affine_point_le`. -/
theorem natCard_affine_point_le_two_mul [Finite R] (W : WeierstrassCurve R) :
    Nat.card W.toAffine.Point ≤ 2 * Nat.card R + 1 := by
  classical
  haveI : Fintype R := Fintype.ofFinite R
  rw [natCard_affine_point_eq W (W.finite_affine_point_of_finite)]
  have hcard : Nat.card {xy : R × R // W.toAffine.Nonsingular xy.fst xy.snd}
      ≤ 2 * Nat.card R := by
    have hsub : Nat.card {xy : R × R // W.toAffine.Nonsingular xy.fst xy.snd}
        = (Finset.univ.filter
            (fun xy : R × R => W.toAffine.Nonsingular xy.fst xy.snd)).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hsub, Nat.card_eq_fintype_card, ← Finset.card_univ (α := R)]
    refine Finset.card_le_mul_card_image_of_maps_to
      (f := Prod.fst) (fun a _ => Finset.mem_univ _) 2 ?_
    intro x _
    rcases Finset.eq_empty_or_nonempty
        ((Finset.univ.filter (fun xy : R × R => W.toAffine.Nonsingular xy.fst xy.snd)).filter
          (fun xy : R × R => xy.fst = x)) with he | ⟨⟨x₀, y₀⟩, hmem⟩
    · simp [he]
    · have hmem' := Finset.mem_filter.mp hmem
      have hx₀ : x₀ = x := hmem'.2
      subst hx₀
      have hns : W.toAffine.Nonsingular x₀ y₀ := (Finset.mem_filter.mp hmem'.1).2
      refine le_trans (Finset.card_le_card
        (t := ({(x₀, y₀), (x₀, W.toAffine.negY x₀ y₀)} : Finset (R × R))) ?_) ?_
      · rintro ⟨x', y'⟩ hp
        have hp' := Finset.mem_filter.mp hp
        have hx' : x' = x₀ := hp'.2
        subst hx'
        have hns' : W.toAffine.Nonsingular x' y' := (Finset.mem_filter.mp hp'.1).2
        rcases Affine.eq_or_eq_negY_of_equation hns'.1 hns.1 with h | h <;> simp [h]
      · exact (Finset.card_insert_le _ _).trans (by simp)
  omega

end Domain

/-! ### The `ℓ`-adic reduction datum over `ℚ`

**STATUS, 2026-07-27: PROVEN BUT CURRENTLY UNCONSUMED — RETAINED DELIBERATELY.**
Its only consumer was the torsion-injection brick deleted that day, so nothing
in the tree now uses `isReductionAlong_ratAdic` or `map_zmod_Δ_ne_zero`; the
`RatAdic` internals feed only those two. It is kept, rather than deleted with
the brick, because it is the `ℚ` instance of exactly the construction
`redHom_eq_zero_of_nsmul_eq_zero` (the live brick's open Lutz–Nagell leaf) is
stated over, and because the section note below records that it generalises
verbatim to a number field — which is the route the live brick's other open
leaf, `exists_tameGoodModel_of_jIntegral`, is expected to take. **So it is a
deliberate keep, not an oversight, and it is NOT a proof target: there is
nothing open here.** The check that would settle whether it has become live:
`grep -rn 'isReductionAlong_ratAdic\|map_zmod_Δ_ne_zero' Fermat/` returning a
line that is not one of the two declaration headers.

Everything in this section is PROVEN (2026-07-26). It is what the previous
version of the deleted brick's docstring called "obstacle 1 — a few hundred
lines of bookkeeping": the `ℓ`-adic valuation subring of `ℚ`, the residue map to `𝔽_ℓ`,
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

/-! ### The potentially-good case: a good model over a totally ramified extension

The three declarations below are the 2026-07-27 decomposition of
`exists_goodReductionHom_of_jIntegral`. The cut separates the two difficulties
that leaf mixed, and which have nothing to do with each other:

* **the arithmetic** — produce a field `L ⊇ ℚ` in which `ℓ` is TOTALLY RAMIFIED,
  and a variable change over `L` carrying `E` to a model with good reduction
  there. This is Silverman *AEC* VII.5.5 (potentially good reduction from
  `v_ℓ(j) ≥ 0`) plus the tame totally-ramified model, and is `TameGoodModel` /
  `exists_tameGoodModel_of_jIntegral`.
* **the reduction theory** — on such a model, the kernel of reduction contains no
  point killed by an integer prime to `ℓ`. This is Lutz–Nagell, and is
  `redHom_eq_zero_of_nsmul_eq_zero`.

**THE STRUCTURAL DISCOVERY THAT MAKES THIS CUT WORTH MAKING** (2026-07-27, and it
refutes the "GAP A is a few hundred lines of bookkeeping" note that the
pre-decomposition docstring below carried). `RatAdic` above builds the `ℓ`-adic
valuation subring of `ℚ` and its residue map to `𝔽_ℓ` in about seventy lines,
because `IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime` packages the
localization of a Dedekind domain at a height-one prime as a `ValuationSubring`
of the fraction field. **That declaration is stated for an ARBITRARY Dedekind
domain**, so the same seventy lines run verbatim over `𝓞_L` for a number field
`L` and a prime `𝔭 ∣ ℓ`. The residue field is `𝓞_L/𝔭`, which is `𝔽_ℓ` exactly
when `𝔭` has residue degree `1` — i.e. exactly when `ℓ` is totally ramified.

The consequence is that **`ℚ_ℓ` is not needed anywhere in this cut, and neither
are formal groups or Tate's algorithm**. One may take `L = ℚ(ℓ^{1/12})`, a fixed
degree-`12` number field independent of `E`: `X¹² − ℓ` is Eisenstein at `ℓ`, so
`ℓ` is totally ramified in `L` and the residue field at the prime above it is
`𝔽_ℓ`. Since the ramification index needed is `e = 12 / gcd(v_ℓ(Δ_min), 12)`,
which always DIVIDES `12`, this single `L` works for every `E` at once — and
`ℓ ≥ 5` is what makes `gcd(e, ℓ) = 1`, i.e. the ramification tame.

The scaling arithmetic is elementary and is worth recording so the owner of
`exists_tameGoodModel_of_jIntegral` need not rediscover it. Over a field of
characteristic `≠ 2, 3` put `E` in the form `y² = x³ + Ax + B`, so that
`Δ = −16(4A³ + 27B²)` and `j = 1728 · 4A³/(4A³ + 27B²)`. Write `a = v(A)`,
`b = v(B)`, `d = v(4A³ + 27B²)`. The variable change `(x, y) ↦ (u²x, u³y)` sends
`(A, B) ↦ (u⁴A, u⁶B)` and scales `4A³ + 27B²` by `u¹²`, so a good model needs
`t = v(u)` with

    4t + a ≥ 0,    6t + b ≥ 0,    12t + d = 0,

i.e. `t = −d/12`, which is achievable in `L` precisely because `12t ∈ ℤ` and `ℓ`
is totally ramified of degree `12`. The first condition is `3a ≥ d`, which **is
exactly the hypothesis `v_ℓ(j) ≥ 0`**; and the second, `2b ≥ d`, is then
automatic: `d ≥ min(3a, 2b)` always, so if `3a < 2b` then `d = 3a ≤ 2b`; if
`3a > 2b` then `d = 2b`; and if `3a = 2b` then `d ≤ 3a = 2b` by `3a ≥ d`. So
`v_ℓ(j) ≥ 0` is not merely sufficient for the construction — it is precisely the
one inequality that is not automatic. -/

/-- **A good model of `E` over an extension in which `ℓ` is totally ramified**,
bundled with everything `PointReduction.lean`'s `redHom` needs.

The fields say: `L` is a field extension of `ℚ`; `A ⊆ L` is a valuation subring
whose residue map `res` lands in `𝔽_ℓ` and is LOCAL (so the residue field is
`𝔽_ℓ` itself, which is where "totally ramified" is encoded — an unramified or
mixed extension would give a residue field strictly larger than `𝔽_ℓ` and no
`res` into `ZMod ℓ` at all); `V` is `E` transported to `L` by a variable change
`C`; `red` is its coefficientwise reduction, which is nonsingular; and `emb`
injects the rational points of `E` into `V(L)`.

**WHY `V_eq` IS PRESENT, AND WHY THE STRUCTURE WOULD BE UNFAITHFUL WITHOUT IT.**
Without pinning `V` to a variable change of `E⁄L`, the structure could be
satisfied by an UNRELATED curve `V` with good reduction at `ℓ` together with an
abstract injective homomorphism of abelian groups `E(ℚ) →+ V(L)` — such a
homomorphism can exist for purely group-theoretic reasons (both groups are
finitely generated of the same shape) while carrying none of the reduction
theory this leaf is supposed to supply. `V_eq` forces `V` to be `L`-isomorphic
to `E`, so "V has good reduction at `A`" really does say that `E` has
POTENTIALLY good reduction at `ℓ`, which is the content.

`emb` is left as an abstract injective homomorphism rather than pinned to
`Affine.Point.baseChange` composed with a variable-change isomorphism. The
original reason given was that **mathlib has no map on points induced by a
`VariableChange`**, and that constructing one was "part of what the owner of
`exists_tameGoodModel_of_jIntegral` must build".

**THAT IS CORRECT ABOUT MATHLIB AND WRONG ABOUT THIS PROJECT, AND THE CHECK IT
ITSELF PRESCRIBED IS WHAT FOUND THE ERROR** (2026-07-27, by that owner). The
recorded refutation check was to grep `Affine/Point.lean` for a point-level
`VariableChange` map — but only mathlib's copy was grepped. This repository
carries its own shim tree, and
`Fermat/FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean` already
supplies exactly the missing map, in the better shape the note asked for:

* `Affine.Point.mapVariableChange : (C • W).Point →+ W.Point`,
* `Affine.Point.equivVariableChange : (C • W).Point ≃+ W.Point`, whose inverse
  is given explicitly by `C⁻¹` rather than extracted from bijectivity, so the
  whole thing is computable given `DecidableEq F`,
* `Affine.Point.equivOfEq`, transport along an equality of curves.

So that obligation is RETIRED — nothing had to be built — and `emb` below is
constructed from it composed with mathlib's `Affine.Point.map`. The general
lesson is the one this development keeps relearning: grep `Fermat/`,
`.lake/packages/mathlib/` and `~/cs/FLT` before recording anything as absent,
because material lands in `Fermat/FLT/Mathlib/` precisely when mathlib lacks it.

The field is nevertheless kept ABSTRACT rather than pinned to that composite,
because `emb_injective` is all any consumer uses and pinning it would force
every producer through one particular factorisation. -/
structure TameGoodModel (E : WeierstrassCurve ℚ) (ℓ : ℕ) [Fact ℓ.Prime] where
  /-- The extension of `ℚ` over which `E` acquires good reduction. -/
  L : Type
  [instField : Field L]
  [instDec : DecidableEq L]
  [instAlgebra : Algebra ℚ L]
  /-- The valuation subring of `L` above `ℓ`. -/
  A : ValuationSubring L
  /-- Its residue map. Landing in `ZMod ℓ` rather than an extension of it is
  where TOTAL RAMIFICATION is encoded. -/
  res : A →+* ZMod ℓ
  [instLocal : IsLocalHom res]
  /-- The variable change over `L` producing the good model. -/
  C : VariableChange L
  /-- The good model itself. -/
  V : WeierstrassCurve L
  /-- `V` is genuinely a model of `E` over `L`, not an unrelated curve. -/
  V_eq : V = C • (E.baseChange L)
  /-- The reduction of `V` modulo the maximal ideal of `A`. -/
  red : WeierstrassCurve (ZMod ℓ)
  /-- The reduction datum, in the form `redHom` consumes. -/
  isReduction : IsReductionAlong A res V red
  /-- Good reduction: the reduced curve is nonsingular. -/
  red_Δ_ne_zero : red.Δ ≠ 0
  /-- The rational points of `E` sit inside `V(L)`. -/
  emb : (E⁄ℚ).Point →+ V.toAffine.Point
  /-- and they do so injectively. -/
  emb_injective : Function.Injective emb

attribute [instance] TameGoodModel.instField TameGoodModel.instDec
  TameGoodModel.instAlgebra TameGoodModel.instLocal

/-- **A tamely totally ramified base for `ℓ`** (interface opened 2026-07-27 while
decomposing `exists_tameGoodModel_of_jIntegral`): a field `L ⊇ ℚ` carrying a
valuation with ramification index `12` over the `ℓ`-adic one and residue field
exactly `𝔽_ℓ`. Concretely `L = ℚ(ℓ^{1/12})` and `π = ℓ^{1/12}`, but nothing below
uses that — this structure is the entire interface between the NUMBER THEORY and
the CURVE THEORY, and it is what makes the two halves separately ownable.

WHY THIS IS THE RIGHT CUT. `TameGoodModel` mixes two difficulties that share no
technique: constructing a totally ramified extension with a prescribed residue
field, and scaling a Weierstrass equation until its discriminant is a unit. The
first is Dedekind-domain arithmetic, the second is `VariableChange` bookkeeping.
`TameBase` is exactly the data the second needs from the first.

`mem_iff` IS THE LOAD-BEARING FIELD, and it is stated for a general exponent `m`
because that is what the scaling uses: the scaled coefficients are `π^{-4d}·A`
and `π^{-6d}·B` for `d = v_ℓ(Δ)`, so integrality is decided by comparing `m`
against `12·v_ℓ(q)`. At `m = 0` it degenerates to "the `ℓ`-integral rationals are
exactly `A ∩ ℚ`"; at `q = 1` to "`π` has valuation `1/12` of `ℓ`".

NOT VACUOUS, and `mem_iff` is what prevents it: `q = 1/ℓ, m = 0` gives
`0 ≤ -12`, false, so `A ≠ L`; `q = 1, m = -1` gives `0 ≤ -1`, false, so `π` is a
genuine non-unit; and `π_pow` then forces the ramification index to be `12`
rather than merely divisible by it. A `TameBase` therefore cannot be produced by
any degenerate choice of `A`. -/
structure TameBase (ℓ : ℕ) [Fact ℓ.Prime] where
  /-- The extension of `ℚ`, morally `ℚ(ℓ^{1/12})`. -/
  L : Type
  [instField : Field L]
  [instDec : DecidableEq L]
  [instAlgebra : Algebra ℚ L]
  /-- The valuation subring above `ℓ`. -/
  A : ValuationSubring L
  /-- Its residue map. Landing in `ZMod ℓ` is where residue degree `1` is encoded. -/
  res : A →+* ZMod ℓ
  [instLocal : IsLocalHom res]
  /-- The uniformizer, morally `ℓ^{1/12}`. -/
  π : L
  /-- and it is nonzero, so its integer powers make sense. -/
  π_ne_zero : π ≠ 0
  /-- **Total ramification of index `12`**, in the only form the scaling needs. -/
  π_pow : π ^ (12 : ℕ) = algebraMap ℚ L (ℓ : ℚ)
  /-- **The integrality criterion**: `v(π^m · q) = m + 12 · v_ℓ(q)`, written as a
  membership so that no `ValueGroup` arithmetic is needed downstream. -/
  mem_iff : ∀ (m : ℤ) {q : ℚ}, q ≠ 0 →
    (π ^ m * algebraMap ℚ L q ∈ A ↔ 0 ≤ m + 12 * padicValRat ℓ q)

attribute [instance] TameBase.instField TameBase.instDec TameBase.instAlgebra
  TameBase.instLocal

/-- **`ℚ(ℓ^{1/12})` exists, with `ℓ` totally ramified and residue field `𝔽_ℓ`**
(sorry leaf, opened 2026-07-27 by decomposing
`exists_tameGoodModel_of_jIntegral`). This is the NUMBER-THEORETIC half, and it
is the only place in the potentially-good chain where Dedekind-domain arithmetic
is needed.

INDEPENDENT OF THE CURVE AND OF `E`, and that is the point: `X¹² − ℓ` is
Eisenstein at `ℓ`, so `ℓ` is totally ramified in `L = ℚ[X]/(X¹² − ℓ)` and the
residue field at the prime above it is `𝔽_ℓ`. Since the ramification index the
scaling needs is `e = 12 / gcd(v_ℓ(Δ), 12)`, which always DIVIDES `12`, this
single field works for every `E` and every `ℓ` at once — which is why the leaf
quantifies over `ℓ` alone.

WHAT MUST BE BUILT (checked 2026-07-27 against mathlib and `~/cs/FLT`):

1. Irreducibility of `X¹² − ℓ` over `ℚ`. Mathlib HAS this:
   `Polynomial.IsEisensteinAt.irreducible`.
2. `ℓ` totally ramified in `L`, i.e. `e = 12` and `f = 1` at the unique prime
   `𝔭 ∣ ℓ`. Mathlib does NOT have "Eisenstein implies totally ramified" — only
   three files mention `IsEisensteinAt` at all, and none is about ramification.
   This is the substantial item.
3. `𝓞_L/𝔭 ≃+* ZMod ℓ`, which is what lets `res` land in `ZMod ℓ`.
4. `mem_iff`, i.e. that the normalized valuation of `π` is `1/12` that of `ℓ`.

The subring itself is FREE, and this is the discovery that made the whole
potentially-good route cheap:
`IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime` is stated for an
ARBITRARY Dedekind domain, so the seventy lines of `RatAdic` above run verbatim
over `𝓞_L`. Neither `ℚ_ℓ` nor completion nor Tate's algorithm appears anywhere.

THE CHECK THAT WOULD REFUTE THIS ROUTE: a mathlib declaration producing a totally
ramified extension of prescribed degree over a number field together with an
explicit residue-field identification — grep
`Mathlib/NumberTheory/RamificationInertia/` and
`Mathlib/RingTheory/Polynomial/Eisenstein/` for one. Either would collapse items
2 and 3. A cheaper *alternative* worth trying first: build the DVR
`ℤ_(ℓ)[X]/(X¹² − ℓ)` directly and take `L` to be its fraction field, which avoids
`𝓞_L` and global class-field bookkeeping entirely — an Eisenstein extension of a
DVR is monogenic, so that quotient IS the integral closure. -/
theorem nonempty_tameBase (ℓ : ℕ) [Fact ℓ.Prime] : Nonempty (TameBase ℓ) :=
  sorry

/-- **`v_ℓ(j) ≥ 0` bounds the coefficient valuations against the discriminant's**
(sorry leaf, opened 2026-07-27 by decomposing
`exists_tameGoodModel_of_jIntegral`). This is the whole arithmetic content of the
hypothesis `¬ ℓ ∣ E.j.den`, isolated from every curve-theoretic concern: it is a
statement about three rational numbers.

In the short form `y² = x³ + A x + B` write `a = v_ℓ(A)`, `b = v_ℓ(B)`,
`d = v_ℓ(Δ)`, where `Δ = −16(4A³ + 27B²)` and `v_ℓ(−16) = v_ℓ(4) = v_ℓ(27) = 0`
because `ℓ ≥ 5`. The two conclusions are `3a ≥ d` and `2b ≥ d`, and they are the
exact conditions under which the variable change `u = π^d` lands the scaled
model in `A` — see `exists_tameGoodModel_of_isShortNF`.

**THE FIRST IS THE HYPOTHESIS AND THE SECOND IS FREE.** `j = 1728·4A³/(4A³+27B²)`,
so `v_ℓ(j) ≥ 0` says precisely `3a ≥ d`. Given that, `2b ≥ d` follows by
ultrametricity alone: `d ≥ min(3a, 2b)` always, with EQUALITY when the two
differ. If `3a < 2b` then `d = 3a < 2b`; if `3a > 2b` then `d = 2b`; and if
`3a = 2b` then `d ≥ 3a` combines with `d ≤ 3a` to give `d = 2b`. So the leaf has
one hypothesis doing all the work, which is why it is stated as a conjunction
rather than split in two.

WHY BOTH HALVES CARRY A NONVANISHING SIDE CONDITION, and it is NOT defensive
bookkeeping: `padicValRat ℓ 0 = 0` by convention, so at `A = 0` the unguarded
claim `d ≤ 3·v_ℓ(A)` reads `d ≤ 0` and is FALSE — `y² = x³ + ℓ` has `A = 0`,
`d = 2`, and is perfectly good potentially. The honest reading is `a = ∞` there,
and the consumer discharges that case separately because the scaled coefficient
is literally `0`, which is in `A` for free. The same applies at `B = 0`.

THE CHECK THAT WOULD REFUTE THE "second is free" CLAIM: exhibit rationals with
`3a ≥ d` and `2b < d`. By the trichotomy above that needs `d > min(3a,2b) = 2b`
with the minimum attained uniquely, contradicting ultrametric equality — so any
such witness would instead be a bug in `padicValRat`'s treatment of the
characteristic-`0` cancellations, which `hℓ5` is there to exclude. -/
theorem padicValRat_Δ_le_of_jIntegral (W : WeierstrassCurve ℚ) [W.IsElliptic] [W.IsShortNF]
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) (hj : ¬ (ℓ ∣ W.j.den)) :
    (W.a₄ ≠ 0 → padicValRat ℓ W.Δ ≤ 3 * padicValRat ℓ W.a₄) ∧
      (W.a₆ ≠ 0 → padicValRat ℓ W.Δ ≤ 2 * padicValRat ℓ W.a₆) :=
  sorry

/-- **The tame good model, for a curve already in short Weierstrass form**
(PROVEN 2026-07-27 over `nonempty_tameBase` and `padicValRat_Δ_le_of_jIntegral`).

This is the curve-theoretic half of `exists_tameGoodModel_of_jIntegral`, and the
whole of it: given the base and the two valuation inequalities, the model is the
single variable change `u = π^d` with `d = v_ℓ(Δ)`, `r = s = t = 0`.

The arithmetic, recorded because it is the reason `12` appears everywhere.
Normalize `v` on `L` so that `v(π) = 1`, hence `v(q) = 12·v_ℓ(q)` for rational
`q`. The change `(x, y) ↦ (u²x, u³y)` sends `(A, B, Δ) ↦ (u⁻⁴A, u⁻⁶B, u⁻¹²Δ)`,
so with `v(u) = d`:

    v(V.a₄) = −4d + 12a ≥ 0  ⟺  3a ≥ d      (the `j`-integrality hypothesis)
    v(V.a₆) = −6d + 12b ≥ 0  ⟺  2b ≥ d      (automatic, see the leaf above)
    v(V.Δ)  = −12d + 12d = 0                (always, by the CHOICE of `d`)

The third line is why `d` is defined as `v_ℓ(Δ)` and not as anything subtler:
`12 ∣ 12d` needs no divisibility hypothesis, which is exactly the step that
would have required `v_ℓ(Δ_min)` and a minimal model over `ℚ_ℓ` had the base had
ramification index less than `12`. `v(V.Δ) = 0` on the nose gives BOTH `V.Δ ∈ A`
and `(V.Δ)⁻¹ ∈ A`, i.e. `V.Δ` is a unit of `A`, and hence its residue — which is
`red.Δ` — is a unit of `𝔽_ℓ` and in particular nonzero. That is `red_Δ_ne_zero`,
and note it comes out of the valuation bookkeeping rather than needing a separate
nondegeneracy argument.

`emb` is `Affine.Point.map` into `L` followed by
`Affine.Point.equivVariableChange`'s inverse; both are injective, and both were
already available (see `TameGoodModel`'s docstring on the retired obligation). -/
theorem exists_tameGoodModel_of_isShortNF (W : WeierstrassCurve ℚ) [W.IsElliptic] [W.IsShortNF]
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) (hj : ¬ (ℓ ∣ W.j.den)) :
    Nonempty (TameGoodModel W ℓ) := by
  classical
  obtain ⟨M⟩ := nonempty_tameBase ℓ
  obtain ⟨h4, h6⟩ := padicValRat_Δ_le_of_jIntegral W hℓ5 hj
  have hΔ0 : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
  set d : ℤ := padicValRat ℓ W.Δ with hd
  have hπd : (M.π ^ d) ≠ 0 := zpow_ne_zero _ M.π_ne_zero
  set u : (M.L)ˣ := Units.mk0 (M.π ^ d) hπd with hu
  set C : VariableChange M.L := ⟨u, 0, 0, 0⟩ with hC
  set V : WeierstrassCurve M.L := C • (W.baseChange M.L) with hV
  -- ### the coefficients of the scaled model
  have hui : ∀ k : ℕ, ((u⁻¹ : (M.L)ˣ) : M.L) ^ k = M.π ^ (-(k : ℤ) * d) := by
    intro k
    rw [hu]
    simp only [Units.val_inv_eq_inv_val, Units.val_mk0]
    rw [← zpow_natCast (M.π ^ d)⁻¹ k, ← zpow_neg, ← zpow_mul]
    ring_nf
  have hVa₁ : V.a₁ = 0 := by
    rw [hV, variableChange_a₁, hC]
    simp [baseChange]
  have hVa₂ : V.a₂ = 0 := by
    rw [hV, variableChange_a₂, hC]
    simp [baseChange]
  have hVa₃ : V.a₃ = 0 := by
    rw [hV, variableChange_a₃, hC]
    simp [baseChange]
  have hVa₄ : V.a₄ = M.π ^ (-4 * d) * algebraMap ℚ M.L W.a₄ := by
    rw [hV, variableChange_a₄, hC]
    simp only [baseChange, map_a₁, map_a₂, map_a₃, map_a₄, W.a₁_of_isShortNF,
      W.a₂_of_isShortNF, W.a₃_of_isShortNF, map_zero]
    rw [hui 4]
    push_cast
    ring
  have hVa₆ : V.a₆ = M.π ^ (-6 * d) * algebraMap ℚ M.L W.a₆ := by
    rw [hV, variableChange_a₆, hC]
    simp only [baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, W.a₁_of_isShortNF,
      W.a₂_of_isShortNF, W.a₃_of_isShortNF, map_zero]
    rw [hui 6]
    push_cast
    ring
  have hVΔ : V.Δ = M.π ^ (-12 * d) * algebraMap ℚ M.L W.Δ := by
    rw [hV, variableChange_Δ, hC]
    simp only [baseChange, map_Δ]
    rw [hui 12]
    push_cast
    ring
  -- ### integrality of the scaled coefficients
  have hzero : (0 : M.L) ∈ M.A := zero_mem _
  have ha₁ : V.a₁ ∈ M.A := by rw [hVa₁]; exact hzero
  have ha₂ : V.a₂ ∈ M.A := by rw [hVa₂]; exact hzero
  have ha₃ : V.a₃ ∈ M.A := by rw [hVa₃]; exact hzero
  have ha₄ : V.a₄ ∈ M.A := by
    rcases eq_or_ne W.a₄ 0 with h0 | h0
    · rw [hVa₄, h0, map_zero, mul_zero]; exact hzero
    · rw [hVa₄, M.mem_iff _ h0]; have := h4 h0; omega
  have ha₆ : V.a₆ ∈ M.A := by
    rcases eq_or_ne W.a₆ 0 with h0 | h0
    · rw [hVa₆, h0, map_zero, mul_zero]; exact hzero
    · rw [hVa₆, M.mem_iff _ h0]; have := h6 h0; omega
  have haΔ : V.Δ ∈ M.A := by rw [hVΔ, M.mem_iff _ hΔ0]; omega
  have haΔinv : (V.Δ)⁻¹ ∈ M.A := by
    have hrw : (V.Δ)⁻¹ = M.π ^ (12 * d) * algebraMap ℚ M.L (W.Δ)⁻¹ := by
      rw [hVΔ, mul_inv, ← zpow_neg, map_inv₀]; ring_nf
    rw [hrw, M.mem_iff _ (inv_ne_zero hΔ0), padicValRat.inv]
    omega
  -- ### the integral model over `A` and its reduction
  set ι : M.A →+* M.L := SubringClass.subtype M.A with hι
  set VA : WeierstrassCurve M.A :=
    ⟨⟨V.a₁, ha₁⟩, ⟨V.a₂, ha₂⟩, ⟨V.a₃, ha₃⟩, ⟨V.a₄, ha₄⟩, ⟨V.a₆, ha₆⟩⟩ with hVA
  have hVAmap : VA.map ι = V := rfl
  have hVAΔ : (VA.Δ : M.L) = V.Δ := by rw [← hVAmap, map_Δ]; rfl
  have hVΔne : V.Δ ≠ 0 := by
    rw [hVΔ]
    refine mul_ne_zero (zpow_ne_zero _ M.π_ne_zero) ?_
    simp only [ne_eq, map_eq_zero]
    exact hΔ0
  have hVAΔunit : IsUnit VA.Δ := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨(V.Δ)⁻¹, haΔinv⟩, Subtype.ext ?_⟩
    show (VA.Δ : M.L) * (V.Δ)⁻¹ = 1
    rw [hVAΔ]
    exact mul_inv_cancel₀ hVΔne
  haveI : (W.baseChange M.L).IsElliptic :=
    inferInstanceAs (W.map (algebraMap ℚ M.L)).IsElliptic
  refine ⟨{
    L := M.L
    A := M.A
    res := M.res
    C := C
    V := V
    V_eq := hV
    red := VA.map M.res
    isReduction :=
      { a₁_mem := ha₁, a₂_mem := ha₂, a₃_mem := ha₃, a₄_mem := ha₄, a₆_mem := ha₆
        a₁_eq := rfl, a₂_eq := rfl, a₃_eq := rfl, a₄_eq := rfl, a₆_eq := rfl }
    red_Δ_ne_zero := by
      rw [map_Δ]
      exact (hVAΔunit.map M.res).ne_zero
    emb := (Affine.Point.equivVariableChange (W.baseChange M.L) C).symm.toAddMonoidHom.comp
      (Affine.Point.map (W' := W) (Algebra.ofId ℚ M.L))
    emb_injective := fun P Q h =>
      Affine.Point.map_injective (Algebra.ofId ℚ M.L)
        ((Affine.Point.equivVariableChange (W.baseChange M.L) C).symm.injective h) }⟩

/-- **Potentially good reduction, as the existence of a tame good model**
(opened 2026-07-27 by decomposing `exists_goodReductionHom_of_jIntegral`;
**DECOMPOSED AND PROVEN 2026-07-27** over `exists_tameGoodModel_of_isShortNF`,
hence over `nonempty_tameBase` and `padicValRat_Δ_le_of_jIntegral`).

THIS IS THE ARITHMETIC HALF, and it is where Silverman *AEC* VII.5.5 lives. See
the section note above for the explicit construction: take `L = ℚ(ℓ^{1/12})`,
`A` the valuation subring of `𝓞_L` at the unique prime above `ℓ` (obtained from
`IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime`, exactly as
`RatAdic` does over `ℚ`), and the variable change `u` with `v(u) = −d/12` in the
short Weierstrass form. The hypothesis `¬ ℓ ∣ E.j.den` is used exactly once, to
give `3a ≥ d`, which is the one inequality that is not automatic.

`hℓ5` is load-bearing twice: it makes the ramification TAME (`gcd(12, ℓ) = 1`),
and it puts `E` in short Weierstrass form (`char ≠ 2, 3`).

**WHERE THE FOUR-ITEM "WHAT MUST BE BUILT" LIST STANDS NOW.** The
pre-decomposition version of this docstring listed four items, "none of which
exists in this tree or in mathlib". Two are done, one was never missing, and
only one is genuinely open:

1. *(Open — now `nonempty_tameBase`.)* The number field `ℚ(ℓ^{1/12})` with `ℓ`
   totally ramified. Still absent; see that leaf for the reduced list, and for a
   cheaper alternative route through the DVR `ℤ_(ℓ)[X]/(X¹² − ℓ)`.
2. *(Open — also `nonempty_tameBase`.)* Residue degree `1`, `𝓞_L/𝔭 ≃+* ZMod ℓ`.
   Folded into the same leaf because it is the same construction.
3. *(RETIRED — IT WAS NEVER MISSING.)* "The `VariableChange`-induced map on
   `Affine.Point`, needed for `emb`." True of mathlib, FALSE of this project:
   `Affine.Point.equivVariableChange` is in
   `Fermat/FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`, in
   exactly the general `≃+` shape the note asked someone to write. The audit's
   own refutation check found this — it just had to be run against `Fermat/` and
   not only against `.lake/packages/mathlib`. See `TameGoodModel`'s docstring.
4. *(DONE — `exists_tameGoodModel_of_isShortNF`.)* The valuation bookkeeping of
   the scaling argument, together with the reduction to short Weierstrass form.

So the residue of this leaf is ONE construction, `nonempty_tameBase`, which is
independent of `E` and of every curve-theoretic concern, plus the elementary
`padicValRat` inequality `padicValRat_Δ_le_of_jIntegral`.

THE PROOF BELOW is only the reduction to short form: `E.toShortNF` puts `E` in
the form `y² = x³ + Ax + B` (mathlib's `toShortNF_spec`; `Invertible 2` and
`Invertible 3` hold over `ℚ`, which is the second job of `hℓ5` in the informal
account and is free here since the base is `ℚ`), `variableChange_j` carries the
hypothesis `¬ ℓ ∣ j.den` across, and the resulting `TameGoodModel` is transported
back by composing the two variable changes (`mul_smul` and `map_variableChange`)
and pre-composing `emb` with `Affine.Point.equivVariableChange`.

NOT VACUOUS. `TameGoodModel` is a structure with an `emb_injective` field, so it
cannot be discharged by a zero homomorphism; and `V_eq` forbids substituting an
unrelated curve. See `TameGoodModel`'s docstring for why that field is there. -/
theorem exists_tameGoodModel_of_jIntegral
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ5 : 5 ≤ ℓ) (hj : ¬ (ℓ ∣ E.j.den)) :
    Nonempty (TameGoodModel E ℓ) := by
  classical
  haveI : Invertible (2 : ℚ) := invertibleOfNonzero (by norm_num)
  haveI : Invertible (3 : ℚ) := invertibleOfNonzero (by norm_num)
  have hj' : ¬ (ℓ ∣ (E.toShortNF • E).j.den) := by rwa [variableChange_j]
  obtain ⟨N⟩ := exists_tameGoodModel_of_isShortNF (E.toShortNF • E) hℓ5 hj'
  refine ⟨{
    L := N.L
    A := N.A
    res := N.res
    C := N.C * (E.toShortNF.map (algebraMap ℚ N.L))
    V := N.V
    V_eq := by
      have hmv : (E.toShortNF.map (algebraMap ℚ N.L)) • (E.baseChange N.L)
          = (E.toShortNF • E).baseChange N.L := map_variableChange _ _ _
      rw [N.V_eq, mul_smul, hmv]
    red := N.red
    isReduction := N.isReduction
    red_Δ_ne_zero := N.red_Δ_ne_zero
    emb := N.emb.comp (Affine.Point.equivVariableChange E E.toShortNF).symm.toAddMonoidHom
    emb_injective := fun P Q h =>
      (Affine.Point.equivVariableChange E E.toShortNF).symm.injective (N.emb_injective h) }⟩

/-- **The kernel of reduction contains no point killed by an integer prime to
`ℓ`** (opened 2026-07-27 by decomposing `exists_goodReductionHom_of_jIntegral`;
**PROVEN 2026-07-27**). Lutz–Nagell, in the generality of an arbitrary valuation
subring with residue field `𝔽_ℓ`.

**THE ROUTE THAT WORKED, and it is the one this docstring predicted** — the four
ingredients below compose with no descent and no DVR. The whole proof is: the
`aᵢ` of `V` lie in `A` (that IS `IsReductionAlong`), so `V` is the base change
along `A ↪ L` of a Weierstrass curve `VA` over `A`, and `Wred = VA.map ρ`. That
single observation discharges three obligations at once:

* `V.ΨSqₙ = (VA.ΨSqₙ).map (A ↪ L)` by `map_ΨSq`, so every coefficient is in `A`;
* `Wred.Δ = ρ VA.Δ` by `map_Δ`, so `hΔ` says `ρ VA.Δ ≠ 0`, so `VA.Δ` is a UNIT of
  `A` by `ValuationSubring.isUnit_of_map_ne_zero` — which is where `V.IsElliptic`
  comes from. It is not a hypothesis of this leaf and does not need to be: good
  reduction of `Wred` forces it;
* `ρ (n : A) = (n : 𝔽_ℓ) ≠ 0` exactly when `¬ ℓ ∣ n`, so `(n : A)` is a unit by
  the same lemma — giving both `(n : L) ≠ 0` and `(n : L)⁻¹ ∈ A`, i.e. the
  inverse of the leading coefficient `n²`.

Then `TorsionCard.smul_some_eq_zero_iff` turns `n • P = 0` into "the abscissa is
a root of `ΨSqₙ`", and `ValuationSubring.mem_of_root_of_inv_leadingCoeff_mem`
puts that abscissa in `A` — contradicting `IsReductionAlong.redFun_eq_zero_iff`,
which says the kernel of reduction is exactly the NON-integral locus.

**THE REFUTATION CHECK THIS DOCSTRING ASKED FOR WAS RUN, AND IT PASSED.** It
read: "if `mem_of_root_of_inv_leadingCoeff_mem` or the division-polynomial API
turns out to need a DISCRETE or COMPLETE valuation, the general form is not
available and the leaf must be restated for a DVR." Neither does.
`mem_of_root_of_inv_leadingCoeff_mem` is stated for an arbitrary
`ValuationSubring` of an arbitrary field, and `ΨSq`'s degree and leading
coefficient (`natDegree_ΨSq`, `leadingCoeff_ΨSq`, `ΨSq_ne_zero`, `map_ΨSq`) are
mathlib lemmas over an arbitrary `CommRing`/`NoZeroDivisors`. So the leaf stands
as stated, and the recommended route — "proving it directly from the four
ingredients above may well be shorter" — was the right one: the descent along
`L → Lˢᵉᵖ` and the `HasGoodReduction` instance that `torsion_abscissa_mem` would
have cost are both avoided entirely.

**THIS IS THE ONLY SURVIVING FORM, AND THAT IS DELIBERATE.** A `ℚ`-specific
twin, `redHom_ne_zero_of_prime_order_ne`, was opened on 2026-07-26 while
decomposing the deleted torsion-injection brick, and was DELETED with it on
2026-07-27 as free-floating. It was this statement specialised to `L = ℚ`,
`A = RatAdic.valuationSubring ℓ`, `V = W⁄ℚ` for an integral `W`, and `n = q` a
prime `≠ ℓ` — so nothing was lost by deleting it, and whoever proves this one
gets that case for free. The argument uses nothing special about `ℚ`, which is
why the general form is the one to prove.

WHY THE GENERAL FORM IS NO HARDER. The classical proof is Cassels' division
polynomial argument, and every ingredient it needs is already present at this
generality:

* `ΨSqₙ` has coefficients in `A`, because `IsReductionAlong` says exactly that
  `V`'s coefficients lie in `A`;
* its leading coefficient is `n²`, which is a UNIT of `A` precisely when
  `res n ≠ 0`, i.e. when `¬ ℓ ∣ n` — this is the only place the hypothesis `hn`
  is used, and it is why the `ℓ`-primary case is genuinely excluded rather than
  merely inconvenient;
* `ValuationSubring.mem_of_root_of_inv_leadingCoeff_mem`
  (`GoodReduction.lean:62`) then puts the abscissa of `P` in `A`, and it is
  stated for an ARBITRARY valuation subring already;
* `IsReductionAlong.redFun_eq_zero_iff` (`PointReduction.lean:712`) says the
  kernel of reduction is exactly the non-integral locus, so an integral abscissa
  forces `P = 0`.

Note `hΔ` is needed only so that `redHom` exists at all; the integrality
argument does not use it. Note also that `¬ ℓ ∣ n` already forces `n ≠ 0`.

`GoodReduction.lean`'s `torsion_abscissa_mem` is the same theorem but stated
over a SEPARABLE CLOSURE with a compatibility hypothesis relating `𝒪` back to a
DVR `R`, and under `[E.HasGoodReduction R]`. Deriving this statement from it
therefore costs the descent along `L → Lˢᵉᵖ` and an instance of
`HasGoodReduction`; proving it directly from the four ingredients above may well
be shorter, and is the recommended route.

THE CHECK THAT WOULD REFUTE THE "no harder" CLAIM: if
`mem_of_root_of_inv_leadingCoeff_mem` or the division-polynomial API turns out
to need a DISCRETE or COMPLETE valuation, the general form is not available and
the leaf must be restated for a DVR. Read those signatures before starting. -/
theorem redHom_eq_zero_of_nsmul_eq_zero {ℓ : ℕ} [Fact ℓ.Prime] {L : Type*} [Field L]
    [DecidableEq L] {A : ValuationSubring L} {ρ : A →+* ZMod ℓ} [IsLocalHom ρ]
    {V : WeierstrassCurve L} {Wred : WeierstrassCurve (ZMod ℓ)}
    (hred : IsReductionAlong A ρ V Wred) (hΔ : Wred.Δ ≠ 0)
    {P : V.toAffine.Point} {n : ℕ} (hn : ¬ (ℓ ∣ n)) (hP : n • P = 0)
    (hker : hred.redHom hΔ P = 0) :
    P = 0 := by
  classical
  -- ### The integral model of `V` over `A`
  -- `IsReductionAlong` says exactly that the `aᵢ` lie in `A`, so `V` is the base change
  -- of a Weierstrass curve `VA` over `A`, and `Wred` is its reduction along `ρ`.
  set ι : A →+* L := SubringClass.subtype A with hι
  set VA : WeierstrassCurve A :=
    ⟨⟨V.a₁, hred.a₁_mem⟩, ⟨V.a₂, hred.a₂_mem⟩, ⟨V.a₃, hred.a₃_mem⟩,
      ⟨V.a₄, hred.a₄_mem⟩, ⟨V.a₆, hred.a₆_mem⟩⟩ with hVA
  have hVmap : VA.map ι = V := rfl
  have hWmap : VA.map ρ = Wred :=
    WeierstrassCurve.ext hred.a₁_eq.symm hred.a₂_eq.symm hred.a₃_eq.symm
      hred.a₄_eq.symm hred.a₆_eq.symm
  -- ### `n` is a unit of `A`, hence nonzero in `L` and invertible there
  have hnZMod : ((n : ℕ) : ZMod ℓ) ≠ 0 := by
    rw [show ((n : ℕ) : ZMod ℓ) = ((n : ℤ) : ZMod ℓ) by push_cast; ring, Ne,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast hn
  have hnA : IsUnit (n : A) :=
    ValuationSubring.isUnit_of_map_ne_zero ρ (by rwa [map_natCast])
  have hnL : (n : L) ≠ 0 := by
    have := ValuationSubring.coe_ne_zero_of_isUnit hnA
    rwa [show (((n : A) : L)) = (n : L) from map_natCast ι n] at this
  have hinvmem : ((n : L))⁻¹ ∈ A := by
    obtain ⟨u, hu⟩ := hnA
    have hmul : (n : L) * ((u⁻¹ : Aˣ) : A) = 1 := by
      have h1 : ((n : A)) * ((u⁻¹ : Aˣ) : A) = 1 := by rw [← hu]; exact u.mul_inv
      have := congrArg ι h1
      rwa [map_mul, map_one, show ι (n : A) = (n : L) from map_natCast ι n] at this
    rw [inv_eq_of_mul_eq_one_right hmul]
    exact SetLike.coe_mem _
  -- ### `V` is elliptic: `Δ` is a unit of `A` because its residue `Wred.Δ` is nonzero
  have hΔA : IsUnit VA.Δ :=
    ValuationSubring.isUnit_of_map_ne_zero ρ (by rw [← map_Δ, hWmap]; exact hΔ)
  haveI : V.IsElliptic := ⟨by rw [← hVmap, map_Δ]; exact hΔA.map ι⟩
  -- ### The Cassels division-polynomial argument
  cases P with
  | zero => rfl
  | some x y hns =>
    exfalso
    -- the kernel of reduction is exactly the NON-integral locus
    have hxnot : x ∉ A := (hred.redFun_eq_zero_iff hΔ hns).mp hker
    -- `n ≠ 0`, since `ℓ ∣ 0`
    have hnne : n ≠ 0 := by rintro rfl; exact hn (dvd_zero ℓ)
    have hnZ : (n : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hnne
    have hnL' : (((n : ℤ)) : L) ≠ 0 := by push_cast; exact hnL
    -- the division-polynomial torsion dictionary
    have hΨ0 : (V.ΨSq (n : ℤ)).eval x = 0 :=
      (TorsionCard.smul_some_eq_zero_iff V hnZ hns).mp (by rw [natCast_zsmul]; exact hP)
    -- its coefficients are integral, because `V` is the base change of `VA`
    have hcoeff : ∀ i, (V.ΨSq (n : ℤ)).coeff i ∈ A := by
      intro i
      rw [← hVmap, map_ΨSq, Polynomial.coeff_map]
      exact SetLike.coe_mem _
    -- its leading coefficient is `n²`, whose inverse is integral
    have hlc : (V.ΨSq (n : ℤ)).leadingCoeff = ((n : L)) ^ 2 := by
      rw [V.leadingCoeff_ΨSq hnL']; push_cast; ring
    have hlcinv : ((V.ΨSq (n : ℤ)).leadingCoeff)⁻¹ ∈ A := by
      rw [hlc, ← inv_pow]
      exact pow_mem hinvmem 2
    exact hxnot (A.mem_of_root_of_inv_leadingCoeff_mem (V.ΨSq_ne_zero hnL') hcoeff hlcinv hΨ0)

/-- **Potentially good reduction at a tame prime, packaged as a reduction
homomorphism injective on prime-to-`ℓ` torsion** (PROVEN 2026-07-27 over
`exists_tameGoodModel_of_jIntegral` and `redHom_eq_zero_of_nsmul_eq_zero`;
opened 2026-07-26
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

WHAT THIS TREE HAS, AND THE THREE GAPS. This audit was originally shared with
the good-reduction brick `exists_injective_torsion_toReduction`, deleted as
free-floating on 2026-07-27; the same machinery serves the good and the
potentially-good case, and this is not a short composition:

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
* GAP A — **RETIRED 2026-07-27, and the "few hundred lines" estimate was wrong.**
  It read: "nothing builds the `ℓ`-adic valuation subring of `ℚ`, or of a totally
  ramified `L/ℚ_ℓ`, in the form `redHom` wants". `RatAdic` above now does exactly
  that over `ℚ`, in about seventy lines, via
  `IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime`; and because that
  mathlib declaration is stated for an arbitrary Dedekind domain, the same
  seventy lines run over `𝓞_L`. See the section note above
  `TameGoodModel`. What survives of GAP A is only the residue-degree-`1`
  identification `𝓞_L/𝔭 ≃+* 𝔽_ℓ`, and it is now part of
  `exists_tameGoodModel_of_jIntegral`.
* GAP B (real) and GAP C (real): step 1, the criterion
  `v(j) ≥ 0 ⟹ potentially good reduction`, and step 2, the tame
  totally-ramified model, are in neither this tree nor mathlib. **Both are now
  exactly `exists_tameGoodModel_of_jIntegral`**, and the section note above
  gives the explicit elementary construction that discharges them together —
  notably, without `ℚ_ℓ`, minimal models, or `v(Δ_min)`: the short Weierstrass
  form and the single inequality `3v(A) ≥ v(4A³ + 27B²)` suffice.

Step 3 is `redHom_eq_zero_of_nsmul_eq_zero`, and note it does NOT need the
formal group: in the prime-to-`ℓ` range Cassels' division-polynomial argument
gives it. That is what makes this brick reachable at all — the deleted
good-reduction brick needed the `ℓ`-primary case, hence the formal group, and
this one never does.

NOT VACUOUS. The hypotheses are satisfiable — `ℓ = 5`, `E = 14a4`, whose `j` is
an integer — and there the conclusion is a genuine assertion, since `14a4(ℚ)`
has a point of order `7`. Nor is the conclusion satisfiable by junk: the zero
homomorphism does not work, because it would force every prime-to-`ℓ` torsion
point of `E(ℚ)` to vanish.

DECOMPOSED AND PROVEN 2026-07-27. The proof below is the whole of what this leaf
contributed beyond its two parts: take the good model, reduce along it, and
transport the kernel condition back through the injection. -/
theorem exists_goodReductionHom_of_jIntegral
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ5 : 5 ≤ ℓ) (hj : ¬ (ℓ ∣ E.j.den)) :
    ∃ (W : WeierstrassCurve (ZMod ℓ)) (f : (E⁄ℚ).Point →+ W.toAffine.Point),
      W.IsElliptic ∧
        ∀ (P : (E⁄ℚ).Point) (n : ℕ), ¬ (ℓ ∣ n) → n • P = 0 → f P = 0 → P = 0 := by
  obtain ⟨M⟩ := E.exists_tameGoodModel_of_jIntegral hℓ5 hj
  refine ⟨M.red, (M.isReduction.redHom M.red_Δ_ne_zero).comp M.emb, ?_, ?_⟩
  · -- Over a field `IsElliptic` is just `Δ ≠ 0`.
    exact ⟨isUnit_iff_ne_zero.mpr M.red_Δ_ne_zero⟩
  · intro P n hn hnP hker
    -- `emb` is additive, so `P` being killed by `n` is inherited by its image.
    have hnι : n • M.emb P = 0 := by rw [← map_nsmul, hnP, map_zero]
    -- The image lies in the kernel of reduction, so it vanishes.
    have himg : M.emb P = 0 :=
      redHom_eq_zero_of_nsmul_eq_zero M.isReduction M.red_Δ_ne_zero hn hnι hker
    exact M.emb_injective (by rw [himg, map_zero])

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
