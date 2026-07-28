/-
StableLineFactor.lean — own work for the Fermat project (not vendored).

**The converse of the kernel-polynomial criterion.**  Two distinct
Galois-stable lines of odd prime order `p` on an elliptic curve `E / F`
multiply into a monic *rational* factor of the `p`-division polynomial
`preΨ'ₚ`, of degree `p − 1`.

Cut out of the sorry leaf `exists_monic_dvd_preΨ_of_twoStableLines` in
`Fermat/FLT/ModularCurve/X0.lean` (cut 2026-07-28 out of
`not_twoStableLines_of_mem_isolatedNonCMJInvariants`).  It is placed in its own
module rather than inside `X0.lean` for two reasons: the mathematics is about
elliptic curves and not about modular curves, and `mem_range_of_fixed` — the
descent step `X0.lean` already carries — sits *below* the leaf in that file, so
an in-file proof would have forced a hoist through another owner's region.

## What this file does

`Fermat/FLT/EllipticCurve/KernelPolynomial.lean` proves
`WeierstrassCurve.exists_point_of_isKernelPolynomial`: a polynomial certificate
over `F` produces a Galois-stable line over `F̄`.  This file runs that
implication backwards, twice, and multiplies:

* `WeierstrassCurve.lineAbscissae g p` is the finset of abscissae `x(Q)` of the
  nonzero points `Q` of the cyclic group `⟨g⟩`.
* `two_mul_card_lineAbscissae`: it has exactly `(p − 1)/2` elements, because
  the abscissa map is exactly `2`-to-`1` on `⟨g⟩ ∖ 0` (`x(Q) = x(Q')` iff
  `Q' = ±Q`, and `Q ≠ −Q` because `p` is odd).
* `eval_preΨ'_eq_zero_of_mem_lineAbscissae`: each such abscissa is a root of
  `preΨ'ₚ`, since `ΨSqₚ = preΨ'ₚ²` for odd `p`.
* `lineAbscissae_image_eq_self`: `Γ_F` permutes the abscissa set, because it
  permutes `⟨g⟩ ∖ 0`.
* `disjoint_lineAbscissae`: two lines with distinct spans have disjoint
  abscissa sets, since a shared abscissa would put a nonzero point in
  `⟨g₁⟩ ∩ ⟨g₂⟩`, and a nonzero element of a group of prime order generates it.

The product `∏_{α ∈ X₁ ∪ X₂} (X − α)` is then monic of degree `p − 1`, divides
`preΨ'ₚ` over `F̄` (distinct linear factors are pairwise coprime, so
`Finset.prod_dvd_of_coprime` applies — no separability of `preΨ'ₚ` is needed),
and has `Γ_F`-invariant coefficients, hence descends to `F[X]`
(`InfiniteGalois.mem_range_algebraMap_iff_fixed` plus
`Polynomial.lifts_and_degree_eq_and_monic`).  Divisibility descends because
`f` is monic and `algebraMap F F̄` is injective (`Polynomial.map_dvd_map`).

## Why the product rather than the pair

The consumer in `X0.lean` is a statement about factor DEGREES of `Ψₚ`, and the
disjointness step is what licenses multiplying the two kernel polynomials
before it is applied.  Exposing `f₁`, `f₂` and `IsCoprime f₁ f₂` separately
would push that step across the cut for no gain.

## Not vacuous

With `⟨g₁⟩ = ⟨g₂⟩` the honest conclusion is a factor of degree `(p − 1)/2`, and
`hne` is exactly what doubles it; `MazurIsogenyPrimeJ`'s explicit kernel
polynomials in `FreyCurve/MazurTorsion.lean` exhibit the degree-`(p − 1)/2`
factors, so the hypothesis is not decorative.
-/
module

public import Fermat.FLT.EllipticCurve.KernelPolynomial
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Algebra.Polynomial.BigOperators

@[expose] public section

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace WeierstrassCurve

universe u v

/-- **Base change of an elliptic curve to a field extension is elliptic.**

`WeierstrassCurve.baseChange` is `map` along `algebraMap`, and mathlib registers
`(W.map f).IsElliptic`; but instance search does not see through `baseChange`, so
the bridge has to be supplied by hand.  `local` for the same reason `X0.lean`
keeps its copy local: a global instance on `(E⁄Ω)` would fire inside every
statement mentioning a base-changed curve. -/
local instance isElliptic_baseChange {K : Type*} [Field K] {E : WeierstrassCurve K}
    [E.IsElliptic] {Ω : Type*} [Field Ω] [Algebra K Ω] : (E⁄Ω).IsElliptic :=
  inferInstanceAs (E.map (algebraMap K Ω)).IsElliptic

section Line

variable {F : Type u} [Field F] {K : Type v} [Field K] [Algebra F K] [DecidableEq K]
  {E : WeierstrassCurve F} [E.IsElliptic] {p : ℕ} {g : (E⁄K).Point}

/-- **The abscissa set of a cyclic line**: the abscissae of the nonzero points
of `⟨g⟩`, indexed by `k ∈ [1, p)`. -/
noncomputable def lineAbscissae (g : (E⁄K).Point) (p : ℕ) : Finset K :=
  (Finset.Ico 1 p).image fun k : ℕ => pointAbscissa ((k : ℤ) • g)

omit [E.IsElliptic] in
theorem mem_lineAbscissae_iff {a : K} :
    a ∈ lineAbscissae g p ↔ ∃ k ∈ Finset.Ico 1 p, pointAbscissa ((k : ℤ) • g) = a := by
  simp only [lineAbscissae, Finset.mem_image]

omit [E.IsElliptic] in
/-- **The order relation**: `n • g = 0` exactly when `p ∣ n`. -/
theorem zsmul_line_eq_zero_iff (hg : addOrderOf g = p) (n : ℤ) :
    n • g = 0 ↔ (p : ℤ) ∣ n := by
  rw [← addOrderOf_dvd_iff_zsmul_eq_zero, hg]

omit [E.IsElliptic] in
/-- Indices in `[1, p)` give nonzero points of `⟨g⟩`. -/
theorem zsmul_line_ne_zero (hg : addOrderOf g = p) {k : ℕ}
    (hk : k ∈ Finset.Ico 1 p) : ((k : ℤ)) • g ≠ 0 := by
  intro hc
  rw [Finset.mem_Ico] at hk
  have hd : p ∣ k := by exact_mod_cast (zsmul_line_eq_zero_iff hg (k : ℤ)).mp hc
  have := Nat.le_of_dvd (by omega) hd
  omega

omit [DecidableEq K] [E.IsElliptic] in
/-- Every nonzero point is affine. -/
theorem exists_some_of_ne_zero {Q : (E⁄K).Point} (hQ : Q ≠ 0) :
    ∃ (x y : K) (h : (E⁄K).toAffine.Nonsingular x y), Q = Affine.Point.some x y h := by
  rcases Q with _ | ⟨x, y, h⟩
  · exact absurd rfl hQ
  · exact ⟨x, y, h, rfl⟩

omit [DecidableEq K] [E.IsElliptic] in
/-- The abscissa is insensitive to negation. -/
theorem pointAbscissa_neg (Q : (E⁄K).Point) : pointAbscissa (-Q) = pointAbscissa Q := by
  rcases Q with _ | ⟨x, y, h⟩
  · rfl
  · rw [Affine.Point.neg_some]; rfl

omit [E.IsElliptic] in
/-- **Each abscissa fibre has at least two indices**: `k` and `p − k`, which are
distinct because `p` is odd. -/
theorem two_le_card_fibre (hodd : Odd p) (hg : addOrderOf g = p) {a : K}
    (ha : a ∈ lineAbscissae g p) :
    2 ≤ ((Finset.Ico 1 p).filter fun k : ℕ => pointAbscissa ((k : ℤ) • g) = a).card := by
  obtain ⟨k, hk, rfl⟩ := mem_lineAbscissae_iff.mp ha
  rw [Finset.mem_Ico] at hk
  have hpg : ((p : ℤ)) • g = 0 := (zsmul_line_eq_zero_iff hg _).mpr dvd_rfl
  have hkne : k ≠ p - k := by rcases hodd with ⟨t, ht⟩; omega
  have habs : pointAbscissa (((p - k : ℕ) : ℤ) • g) = pointAbscissa ((k : ℤ) • g) := by
    have hcast : ((p - k : ℕ) : ℤ) = (p : ℤ) - (k : ℤ) := by omega
    have h1 : (((p - k : ℕ) : ℤ)) • g = -((k : ℤ) • g) := by
      rw [hcast, sub_zsmul, hpg]; abel
    rw [h1, pointAbscissa_neg]
  have hsub : ({k, p - k} : Finset ℕ) ⊆
      (Finset.Ico 1 p).filter fun j : ℕ => pointAbscissa ((j : ℤ) • g) =
        pointAbscissa ((k : ℤ) • g) := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rw [Finset.mem_filter, Finset.mem_Ico]
    rcases hj with rfl | rfl
    · exact ⟨⟨hk.1, hk.2⟩, rfl⟩
    · exact ⟨⟨by omega, by omega⟩, habs⟩
  calc 2 = ({k, p - k} : Finset ℕ).card := (Finset.card_pair hkne).symm
    _ ≤ _ := Finset.card_le_card hsub

omit [E.IsElliptic] in
/-- **Each abscissa fibre has at most two indices**, by the `x`-collision
dichotomy: `x(Q) = x(Q')` forces `Q' = ±Q`.  This is the same degree count that
drives `exists_point_of_isKernelPolynomial`, run in the same direction. -/
theorem card_fibre_le_two (hg : addOrderOf g = p) {a : K} :
    ((Finset.Ico 1 p).filter fun k : ℕ => pointAbscissa ((k : ℤ) • g) = a).card ≤ 2 := by
  classical
  rcases Finset.eq_empty_or_nonempty
      ((Finset.Ico 1 p).filter fun k : ℕ => pointAbscissa ((k : ℤ) • g) = a) with
    he | ⟨k₀, hk₀⟩
  · rw [he]; simp
  rw [Finset.mem_filter] at hk₀
  refine le_trans (Finset.card_le_card (?_ : _ ⊆ ({k₀, p - k₀} : Finset ℕ)))
    ((Finset.card_insert_le _ _).trans (by simp))
  intro k hk
  rw [Finset.mem_filter] at hk
  obtain ⟨x₁, y₁, h₁, he₁⟩ := exists_some_of_ne_zero (zsmul_line_ne_zero hg hk.1)
  obtain ⟨x₂, y₂, h₂, he₂⟩ := exists_some_of_ne_zero (zsmul_line_ne_zero hg hk₀.1)
  have hxx : x₁ = x₂ := by
    have e1 : pointAbscissa ((k : ℤ) • g) = x₁ := by rw [he₁, pointAbscissa_some]
    have e2 : pointAbscissa ((k₀ : ℤ) • g) = x₂ := by rw [he₂, pointAbscissa_some]
    rw [← e1, ← e2, hk.2, hk₀.2]
  rw [Finset.mem_Ico] at hk hk₀
  rcases (TorsionCard.eq_or_add_eq_zero_of_X_eq (E⁄K) h₁ h₂ hxx :
      (Affine.Point.some x₁ y₁ h₁ : (E⁄K).Point) = Affine.Point.some x₂ y₂ h₂ ∨
        (Affine.Point.some x₁ y₁ h₁ : (E⁄K).Point) +
          Affine.Point.some x₂ y₂ h₂ = 0) with hc | hc
  · have hpe : (k : ℤ) • g = (k₀ : ℤ) • g := by rw [he₁, he₂]; exact hc
    have h0 : ((k : ℤ) - (k₀ : ℤ)) • g = 0 := by rw [sub_smul, hpe, sub_self]
    have := eq_of_intCast_sub_dvd (p := p) hk.1.2 hk₀.1.2
      ((zsmul_line_eq_zero_iff hg _).mp h0)
    simp [this]
  · have h0 : ((k : ℤ) + (k₀ : ℤ)) • g = 0 := by rw [add_smul, he₁, he₂]; exact hc
    have hdv := (zsmul_line_eq_zero_iff hg _).mp h0
    have hdn : p ∣ k + k₀ := by
      have : (p : ℤ) ∣ ((k + k₀ : ℕ) : ℤ) := by push_cast; exact hdv
      exact Int.natCast_dvd_natCast.mp this
    have := add_eq_of_dvd_add hk.1.1 hk.1.2 hk₀.1.1 hk₀.1.2 hdn
    have hkk : k = p - k₀ := by omega
    simp [hkk]

omit [E.IsElliptic] in
/-- **The abscissa set of a line of odd order `p` has `(p − 1)/2` elements**,
stated without division. -/
theorem two_mul_card_lineAbscissae (hodd : Odd p) (hg : addOrderOf g = p) :
    2 * (lineAbscissae g p).card = p - 1 := by
  have h1 : 2 * (lineAbscissae g p).card ≤ p - 1 := by
    have h0 := Finset.mul_card_image_le_card (f := fun k : ℕ => pointAbscissa ((k : ℤ) • g))
      (Finset.Ico 1 p) 2 fun a ha => two_le_card_fibre hodd hg ha
    rwa [Nat.card_Ico] at h0
  have h2 : p - 1 ≤ 2 * (lineAbscissae g p).card := by
    have h0 := Finset.card_le_mul_card_image (f := fun k : ℕ => pointAbscissa ((k : ℤ) • g))
      (Finset.Ico 1 p) 2 fun a _ => card_fibre_le_two hg
    rwa [Nat.card_Ico] at h0
  omega

/-- **Every abscissa of a line of order `p` is a root of `preΨ'ₚ`**, since
`ΨSqₚ = preΨ'ₚ²` for odd `p`. -/
theorem eval_preΨ'_eq_zero_of_mem_lineAbscissae (hp : p.Prime) (hodd : Odd p)
    (hg : addOrderOf g = p) {a : K} (ha : a ∈ lineAbscissae g p) :
    ((E⁄K).preΨ' p).eval a = 0 := by
  obtain ⟨k, hk, rfl⟩ := mem_lineAbscissae_iff.mp ha
  obtain ⟨x, y, h, hQ⟩ := exists_some_of_ne_zero (zsmul_line_ne_zero hg hk)
  rw [hQ, pointAbscissa_some]
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have htors : ((p : ℤ)) • (Affine.Point.some x y h : (E⁄K).Point) = 0 := by
    rw [← hQ, smul_smul]
    exact (zsmul_line_eq_zero_iff hg _).mpr ⟨(k : ℤ), rfl⟩
  have hΨ : ((E⁄K).ΨSq (p : ℤ)).eval x = 0 :=
    (TorsionCard.smul_some_eq_zero_iff (E⁄K) hpZ h :
      (((p : ℤ)) • (Affine.Point.some x y h : (E⁄K).Point) = 0) ↔
        (((E⁄K).ΨSq (p : ℤ)).eval x = 0)).mp htors
  have hsq : (E⁄K).ΨSq ((p : ℕ) : ℤ) = ((E⁄K).preΨ' p) ^ 2 := by
    rw [WeierstrassCurve.ΨSq_ofNat, if_neg (Nat.not_even_iff_odd.mpr hodd), mul_one]
  rw [hsq, Polynomial.eval_pow] at hΨ
  exact (pow_eq_zero_iff (n := 2) (by norm_num)).mp hΨ

end Line

section Galois

variable {F : Type u} [Field F] {K : Type v} [Field K] [Algebra F K] [DecidableEq K]
  {E : WeierstrassCurve F} [E.IsElliptic] {p : ℕ} {g : (E⁄K).Point}

omit [E.IsElliptic] in
/-- **The Galois group permutes the abscissa set of a stable line.**  This is the
descent step: `σ` maps `⟨g⟩ ∖ 0` into itself, and the abscissa map intertwines
the two actions. -/
theorem lineAbscissae_image_eq_self (hp : p.Prime) (hg : addOrderOf g = p)
    (hstable : ∀ σ : K ≃ₐ[F] K, ∀ x ∈ AddSubgroup.zmultiples g,
      Affine.Point.map σ.toAlgHom x ∈ AddSubgroup.zmultiples g)
    (σ : K ≃ₐ[F] K) :
    (lineAbscissae g p).image (σ : K → K) = lineAbscissae g p := by
  have hcard : ((lineAbscissae g p).image (σ : K → K)).card = (lineAbscissae g p).card :=
    Finset.card_image_of_injective _ σ.injective
  refine Finset.eq_of_subset_of_card_le ?_ (le_of_eq hcard.symm)
  intro b hb
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨k, hk, rfl⟩ := mem_lineAbscissae_iff.mp ha
  -- the point and its `σ`-image
  obtain ⟨x, y, h, hQ⟩ := exists_some_of_ne_zero (zsmul_line_ne_zero hg hk)
  have hmapmem : Affine.Point.map σ.toAlgHom ((k : ℤ) • g) ∈ AddSubgroup.zmultiples g :=
    hstable σ _ (AddSubgroup.zsmul_mem_zmultiples _ _)
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hmapmem
  -- the image is nonzero, so `p ∤ m`
  have hmapne : Affine.Point.map σ.toAlgHom ((k : ℤ) • g) ≠ 0 := by
    intro hc
    exact zsmul_line_ne_zero hg hk
      (Affine.Point.map_injective _ (hc.trans (Affine.Point.map_zero _).symm))
  have hmne : ¬ ((p : ℤ) ∣ m) := by
    intro hc
    apply hmapne
    rw [← hm]
    exact (zsmul_line_eq_zero_iff hg m).mpr hc
  -- replace `m` by its residue in `[1, p)`
  have hppos : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
  set r : ℤ := m % (p : ℤ) with hrdef
  have hr0 : 0 ≤ r := Int.emod_nonneg m (by omega)
  have hrp : r < (p : ℤ) := Int.emod_lt_of_pos m hppos
  have hrne : r ≠ 0 := by
    intro hc
    apply hmne
    refine Int.dvd_of_emod_eq_zero ?_
    rw [← hrdef]
    exact hc
  have hcong : r • g = m • g := by
    have hdvd : (p : ℤ) ∣ m - r := by
      rw [hrdef]; exact Int.dvd_self_sub_emod
    have h0 : (m - r) • g = 0 := (zsmul_line_eq_zero_iff hg _).mpr hdvd
    rw [sub_smul, sub_eq_zero] at h0
    exact h0.symm
  refine mem_lineAbscissae_iff.mpr ⟨r.toNat, ?_, ?_⟩
  · rw [Finset.mem_Ico]; omega
  · have hrcast : ((r.toNat : ℕ) : ℤ) = r := Int.toNat_of_nonneg hr0
    rw [hrcast, hcong, hm, hQ, Affine.Point.map_some, pointAbscissa_some,
      pointAbscissa_some]
    rfl

omit [E.IsElliptic] in
/-- **Two lines with distinct spans have disjoint abscissa sets.**  A shared
abscissa puts a nonzero point in `⟨g₁⟩ ∩ ⟨g₂⟩`, and a nonzero element of a group
of prime order generates it, forcing `⟨g₁⟩ = ⟨g₂⟩`. -/
theorem disjoint_lineAbscissae (hp : p.Prime) {g₁ g₂ : (E⁄K).Point}
    (hg₁ : addOrderOf g₁ = p) (hg₂ : addOrderOf g₂ = p)
    (hne : AddSubgroup.zmultiples g₁ ≠ AddSubgroup.zmultiples g₂) :
    Disjoint (lineAbscissae g₁ p) (lineAbscissae g₂ p) := by
  -- a nonzero multiple of `g` with index prime to `p` generates `⟨g⟩`
  have hgen : ∀ (g : (E⁄K).Point), addOrderOf g = p → ∀ k : ℕ, k ∈ Finset.Ico 1 p →
      AddSubgroup.zmultiples ((k : ℤ) • g) = AddSubgroup.zmultiples g := by
    intro g hg k hk
    rw [Finset.mem_Ico] at hk
    have hpk : ¬ p ∣ k := fun hc => by
      have := Nat.le_of_dvd (by omega) hc; omega
    obtain ⟨u, v, huv⟩ : IsCoprime ((p : ℤ)) ((k : ℤ)) :=
      Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpk)
    have hmem : g ∈ AddSubgroup.zmultiples ((k : ℤ) • g) := by
      have hpg : ((p : ℤ)) • g = 0 := (zsmul_line_eq_zero_iff hg _).mpr dvd_rfl
      refine AddSubgroup.mem_zmultiples_iff.mpr ⟨v, ?_⟩
      have hone : (u * (p : ℤ) + v * (k : ℤ)) • g = g := by rw [huv, one_zsmul]
      rw [add_zsmul, mul_zsmul, hpg, smul_zero, zero_add, mul_zsmul] at hone
      exact hone
    exact le_antisymm (AddSubgroup.zmultiples_le.mpr
      (AddSubgroup.zsmul_mem_zmultiples _ _)) (AddSubgroup.zmultiples_le.mpr hmem)
  rw [Finset.disjoint_left]
  intro a ha₁ ha₂
  obtain ⟨k, hk, hka⟩ := mem_lineAbscissae_iff.mp ha₁
  obtain ⟨l, hl, hla⟩ := mem_lineAbscissae_iff.mp ha₂
  obtain ⟨x₁, y₁, h₁, he₁⟩ := exists_some_of_ne_zero (zsmul_line_ne_zero hg₁ hk)
  obtain ⟨x₂, y₂, h₂, he₂⟩ := exists_some_of_ne_zero (zsmul_line_ne_zero hg₂ hl)
  have hxx : x₁ = x₂ := by
    have e1 : pointAbscissa ((k : ℤ) • g₁) = x₁ := by rw [he₁, pointAbscissa_some]
    have e2 : pointAbscissa ((l : ℤ) • g₂) = x₂ := by rw [he₂, pointAbscissa_some]
    rw [← e1, ← e2, hka, hla]
  -- the two points agree up to sign
  have hspan : AddSubgroup.zmultiples ((k : ℤ) • g₁) = AddSubgroup.zmultiples ((l : ℤ) • g₂) := by
    rcases (TorsionCard.eq_or_add_eq_zero_of_X_eq (E⁄K) h₁ h₂ hxx :
        (Affine.Point.some x₁ y₁ h₁ : (E⁄K).Point) = Affine.Point.some x₂ y₂ h₂ ∨
          (Affine.Point.some x₁ y₁ h₁ : (E⁄K).Point) +
            Affine.Point.some x₂ y₂ h₂ = 0) with hc | hc
    · have : (k : ℤ) • g₁ = (l : ℤ) • g₂ := by rw [he₁, he₂]; exact hc
      rw [this]
    · have hneg : (k : ℤ) • g₁ = -((l : ℤ) • g₂) := by
        rw [he₁, he₂]; exact (neg_eq_of_add_eq_zero_left hc).symm
      have hnegspan : ∀ Q : (E⁄K).Point,
          AddSubgroup.zmultiples (-Q) = AddSubgroup.zmultiples Q := by
        intro Q
        refine le_antisymm (AddSubgroup.zmultiples_le.mpr
          (neg_mem (AddSubgroup.mem_zmultiples Q))) ?_
        have h2 : -(-Q) ∈ AddSubgroup.zmultiples (-Q) :=
          neg_mem (AddSubgroup.mem_zmultiples (-Q))
        rw [neg_neg] at h2
        exact AddSubgroup.zmultiples_le.mpr h2
      rw [hneg, hnegspan]
  exact hne ((hgen g₁ hg₁ k hk).symm.trans (hspan.trans (hgen g₂ hg₂ l hl)))

end Galois

section Descent

variable {F : Type} [Field F] [CharZero F] [DecidableEq (AlgebraicClosure F)]

/-- **Two independent stable lines multiply into a rational factor of `preΨ'ₚ`
of degree `p − 1`** (PROVEN 2026-07-28).

This is the converse of `exists_point_of_isKernelPolynomial`, taken twice and
multiplied; see the module docstring for the argument.  `hne` is the whole
content: with `⟨g₁⟩ = ⟨g₂⟩` the honest conclusion has degree `(p − 1)/2`. -/
theorem exists_monic_dvd_preΨ'_of_twoStableLines {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (E : WeierstrassCurve F) [E.IsElliptic]
    (g₁ g₂ : (E⁄(AlgebraicClosure F)).Point)
    (hg₁ : addOrderOf g₁ = p) (hg₂ : addOrderOf g₂ = p)
    (hne : AddSubgroup.zmultiples g₁ ≠ AddSubgroup.zmultiples g₂)
    (hs₁ : ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F,
      ∀ x ∈ AddSubgroup.zmultiples g₁,
      Affine.Point.map σ.toAlgHom x ∈ AddSubgroup.zmultiples g₁)
    (hs₂ : ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F,
      ∀ x ∈ AddSubgroup.zmultiples g₂,
      Affine.Point.map σ.toAlgHom x ∈ AddSubgroup.zmultiples g₂) :
    ∃ f : Polynomial F, f.Monic ∧ f.natDegree = p - 1 ∧ f ∣ E.preΨ' p := by
  -- ## the abscissa set of the union of the two lines
  set S : Finset (AlgebraicClosure F) := lineAbscissae g₁ p ∪ lineAbscissae g₂ p with hSdef
  set G : Polynomial (AlgebraicClosure F) :=
    ∏ a ∈ S, (Polynomial.X - Polynomial.C a) with hGdef
  have hdisj : Disjoint (lineAbscissae g₁ p) (lineAbscissae g₂ p) :=
    disjoint_lineAbscissae hp hg₁ hg₂ hne
  -- ## `G` is monic of degree `p − 1`
  have hGmonic : G.Monic := by
    rw [hGdef]
    exact Polynomial.monic_prod_of_monic _ _ fun a _ => Polynomial.monic_X_sub_C a
  have hScard : S.card = p - 1 := by
    have h1 := two_mul_card_lineAbscissae (g := g₁) hodd hg₁
    have h2 := two_mul_card_lineAbscissae (g := g₂) hodd hg₂
    rw [hSdef, Finset.card_union_of_disjoint hdisj]
    omega
  have hGdeg : G.natDegree = p - 1 := by
    rw [hGdef, Polynomial.natDegree_prod_of_monic _ _
      (fun a _ => Polynomial.monic_X_sub_C a)]
    simp [hScard]
  -- ## `G` divides the division polynomial over `K`
  have hroot : ∀ a ∈ S, ((E⁄(AlgebraicClosure F)).preΨ' p).eval a = 0 := by
    intro a ha
    rw [hSdef, Finset.mem_union] at ha
    rcases ha with h | h
    · exact eval_preΨ'_eq_zero_of_mem_lineAbscissae hp hodd hg₁ h
    · exact eval_preΨ'_eq_zero_of_mem_lineAbscissae hp hodd hg₂ h
  have hGdvdK : G ∣ (E⁄(AlgebraicClosure F)).preΨ' p := by
    rw [hGdef]
    refine Finset.prod_dvd_of_coprime (fun a _ b _ hab => ?_) (fun a ha => ?_)
    · exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub
        (isUnit_iff_ne_zero.mpr (sub_ne_zero_of_ne hab))
    · exact Polynomial.dvd_iff_isRoot.mpr (hroot a ha)
  -- ## the coefficients of `G` are `Γ_F`-invariant
  have hSstable : ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, S.image (σ : AlgebraicClosure F → AlgebraicClosure F) = S := by
    intro σ
    rw [hSdef, Finset.image_union, lineAbscissae_image_eq_self hp hg₁ hs₁ σ,
      lineAbscissae_image_eq_self hp hg₂ hs₂ σ]
  have hGmap : ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, G.map (σ : AlgebraicClosure F →+* AlgebraicClosure F) = G := by
    intro σ
    have hinj : Set.InjOn (σ : AlgebraicClosure F → AlgebraicClosure F) (↑S : Set (AlgebraicClosure F)) := fun x _ y _ h => σ.injective h
    have h1 : G.map (σ : AlgebraicClosure F →+* AlgebraicClosure F)
        = ∏ a ∈ S, (Polynomial.X - Polynomial.C ((σ : AlgebraicClosure F → AlgebraicClosure F) a)) := by
      rw [hGdef, Polynomial.map_prod]
      exact Finset.prod_congr rfl fun a _ => by
        rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]; rfl
    have h2 : ∏ b ∈ S.image (σ : AlgebraicClosure F → AlgebraicClosure F),
          (Polynomial.X - Polynomial.C b)
        = ∏ a ∈ S, (Polynomial.X -
          Polynomial.C ((σ : AlgebraicClosure F → AlgebraicClosure F) a)) :=
      Finset.prod_image hinj
    rw [h1, ← h2, hSstable σ, hGdef]
  have hcoeff : ∀ n : ℕ, ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, σ (G.coeff n) = G.coeff n := by
    intro n σ
    have := congrArg (fun q : Polynomial (AlgebraicClosure F) => q.coeff n) (hGmap σ)
    simpa [Polynomial.coeff_map] using this
  -- ## descend `G` to `F[X]`
  have hlifts : G ∈ Polynomial.lifts (algebraMap F (AlgebraicClosure F)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact (InfiniteGalois.mem_range_algebraMap_iff_fixed (G.coeff n)).mpr fun σ => hcoeff n σ
  obtain ⟨f, hfmap, hfdeg, hfmonic⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic hlifts hGmonic
  refine ⟨f, hfmonic, ?_, ?_⟩
  · rw [Polynomial.natDegree_eq_of_degree_eq hfdeg, hGdeg]
  -- ## descend the divisibility
  · have hpre : (E⁄(AlgebraicClosure F)).preΨ' p = (E.preΨ' p).map (algebraMap F (AlgebraicClosure F)) := by
      rw [← WeierstrassCurve.map_preΨ']; rfl
    rw [← Polynomial.map_dvd_map (algebraMap F (AlgebraicClosure F)) (algebraMap F (AlgebraicClosure F)).injective hfmonic, hfmap]
    rw [hpre] at hGdvdK
    exact hGdvdK

end Descent

end WeierstrassCurve
