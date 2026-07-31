/-
ModularCurve/Gamma0Index.lean — own work for the Fermat project.

# The index of `Γ₀(N)` in `SL(2, ℤ)`

This module proves the classical index formula

`[SL(2, ℤ) : Γ₀(N)] = μ(N) = N ∏_{p ∣ N} (1 + 1/p)`

(`Fermat.Gamma0Index.Gamma0_index`), which is what
`Fermat.relIndex_gamma0GL` in `FreyCurve/MazurTorsion.lean` needs — it is the
number of cosets in the norm construction, hence the weight
`2 · [SL(2,ℤ) : Γ₀(M)]` of the level-one norm of a weight-two form on `Γ₀(M)`,
hence the Sturm threshold of the norm/Sturm route to `S₂(Γ₀(M)) = 0`.

Mathlib has none of the three classical ingredients at `a3364fa`: no
surjectivity of `SL(2, ℤ) → SL(2, ℤ/N)`, no `|SL(2, ℤ/N)|`, and no `Γ₀` index
(`grep -rn "Gamma0.*index" .lake/packages/mathlib/Mathlib/NumberTheory/` is
empty).  All three are built here.

## The route

`Γ₀(N)` is the preimage of the Borel `B(ℤ/N) = {g | g₁₀ = 0}` of `SL(2, ℤ/N)`
under reduction (`Gamma0_eq_comap`), and reduction is SURJECTIVE
(`SLMOD_surjective`), so the two indices agree.  The index of the Borel is
computed WITHOUT ever computing `|SL(2, ℤ/N)|` in closed form:

* `card_SL2` — the bottom-row map `SL(2, R) → {unimodular pairs}` is surjective
  with every fibre of size `|R|` (add `t · (c, d)` to the top row), so
  `|SL(2,R)| = U(R) · |R|`;
* `card_borel` — `B(R) ≃ Rˣ × R` by `(u, b) ↦ ![![u, b], ![0, u⁻¹]]`;
* hence `[SL(2,R) : B(R)] · |Rˣ| = U(R)` (`index_borel_mul_card_units`), the
  factor `|R|` cancelling.

So everything reduces to counting unimodular pairs `U(N)` over `ℤ/N`, and that
count is multiplicative by CRT (`unimodCount_mul`: a pair over `R × S` is
unimodular iff both components are) with the prime-power value read off the
LOCAL structure of `ℤ/pᵏ` — there a pair is unimodular iff one entry is a unit
(`isUnimod_iff_isUnit`), so the non-unimodular pairs are exactly the pairs of
non-units and `U(pᵏ) = (pᵏ + pᵏ⁻¹) · φ(pᵏ)` (`unimodCount_prime_pow`).  Since
`gammaZeroIndex` is multiplicative with the same prime-power values,
`Nat.recOnPosPrimePosCoprime` gives `U(N) = μ(N) · φ(N)` for every `N ≠ 0`, and
`φ(N) > 0` cancels.

**Note on `p ^ (k-1)` rather than a division**: the prime-power count is
organised so that `pᵏ⁻¹` never has to be identified with `|{non-units}|` by a
division — `φ(pᵏ) + |{non-units}| = pᵏ` and `U + |{non-units}|² = p²ᵏ` are the
only two facts used, and the closed form enters only when matching
`gammaZeroIndex (pᵏ) = pᵏ + pᵏ⁻¹`.

## The lifting lemma

Surjectivity of `SL(2, ℤ) → SL(2, ℤ/N)` rests on `exists_coprime_lift`: a
unimodular pair `(c, d)` mod `N` lifts to a pair of natural numbers `C, D` with
`gcd(C, D) = 1`.  The witness is
`C = if c.val = 0 then N else c.val` (which makes `C ≠ 0` without changing its
class) and `D = d.val + N · k` with

`k = ∏ {q prime : q ∣ C, q ∤ d.val}`.

For a prime `q ∣ C`: if `q ∣ d.val` then `q ∤ k` (its factors all fail to divide
`d.val`) so `q ∣ D` would force `q ∣ N`, contradicting `gcd(C, d.val, N) = 1`;
and if `q ∤ d.val` then `q ∣ k`, so `q ∣ D` would force `q ∣ d.val`.  Either way
`q ∤ D`.

Given the coprime lift, Bézout completes `(C, D)` to `γ₀ ∈ SL(2, ℤ)` whose
reduction has the same bottom row as the target `g`; then `g · γ̄₀⁻¹` has bottom
row `(0, 1)`, hence is `![![1, b], ![0, 1]]`, which lifts.

## Numerical cross-checks (run 2026-07-31 as `example`s, then removed)

`[SL(2,ℤ) : Γ₀(2)] = 3`, `= 6` at `N = 5`, `= 30` at `N = 25`, each by
`rw [Gamma0_index]; decide`.  The first agrees with the independently proven
`Gamma0_two_index` of `Modularity/Interface.lean` (a `decide` over the six
elements of `SL(2, ℤ/2)`), which is the consistency check
`relIndex_gamma0GL`'s docstring asks for.
-/
module

public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Fermat.FLT.ModularCurve.X0

@[expose] public section

open scoped MatrixGroups
open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup

namespace Fermat.Gamma0Index


section Ring

variable {R : Type*} [CommRing R]

/-- `v` generates the unit ideal of `R`. -/
def IsUnimod (v : R × R) : Prop := ∃ x y : R, x * v.1 + y * v.2 = 1

/-- The bottom row of a matrix of determinant one is unimodular. -/
theorem isUnimod_botRow (g : SL(2, R)) : IsUnimod (g.1 1 0, g.1 1 1) := by
  refine ⟨-(g.1 0 1), g.1 0 0, ?_⟩
  have h : g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0 = 1 := by
    have := g.2
    rwa [Matrix.det_fin_two] at this
  simp only
  linear_combination h

/-- The bottom-row map `SL(2,R) → {unimodular pairs}`. -/
def botRow (g : SL(2, R)) : {v : R × R // IsUnimod v} :=
  ⟨(g.1 1 0, g.1 1 1), isUnimod_botRow g⟩

/-- The elements of `SL(2,R)` with a given unimodular bottom row `(c, d)` are
parametrised by `R`: add `t • (c, d)` to the top row. -/
theorem card_botRow_fiber' [Finite R] (c d x y : R) (hxy : x * c + y * d = 1) :
    Nat.card {g : SL(2, R) // g.1 1 0 = c ∧ g.1 1 1 = d} = Nat.card R := by
  have hdet : ∀ t : R, Matrix.det !![y + t * c, -x + t * d; c, d] = 1 := by
    intro t; rw [Matrix.det_fin_two_of]; linear_combination hxy
  set F : R → {g : SL(2, R) // g.1 1 0 = c ∧ g.1 1 1 = d} := fun t =>
    ⟨⟨!![y + t * c, -x + t * d; c, d], hdet t⟩, by constructor <;> simp⟩ with hF
  have hentry : ∀ t : R, ((F t).1.1 0 0 = y + t * c ∧ (F t).1.1 0 1 = -x + t * d) := by
    intro t; constructor <;> simp [hF]
  have hbij : Function.Bijective F := by
    constructor
    · intro s t hst
      have h1 : y + s * c = y + t * c := by
        rw [← (hentry s).1, ← (hentry t).1, hst]
      have h2 : -x + s * d = -x + t * d := by
        rw [← (hentry s).2, ← (hentry t).2, hst]
      have hc : s * c = t * c := by linear_combination h1
      have hd : s * d = t * d := by linear_combination h2
      linear_combination x * hc + y * hd - (s - t) * hxy
    · rintro ⟨g, hc, hd⟩
      have hdetg : g.1 0 0 * d - g.1 0 1 * c = 1 := by
        have h := g.2
        rw [Matrix.det_fin_two] at h
        rw [← hc, ← hd]; exact h
      set u : R := g.1 0 0 - y with hu
      set w : R := g.1 0 1 + x with hw
      have huw : u * d = w * c := by rw [hu, hw]; linear_combination hdetg - hxy
      refine ⟨u * x + w * y, ?_⟩
      have h1 : (u * x + w * y) * c = u := by linear_combination u * hxy - y * huw
      have h2 : (u * x + w * y) * d = w := by linear_combination x * huw + w * hxy
      apply Subtype.ext
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hF]
      · rw [show y + (u * x + w * y) * c = y + u from by rw [h1], hu]; ring
      · rw [show -x + (u * x + w * y) * d = -x + w from by rw [h2], hw]; ring
      · exact hc.symm
      · exact hd.symm
  exact (Nat.card_eq_of_bijective F hbij).symm

/-- `#SL(2,R) = #{unimodular pairs} · #R`. -/
theorem card_SL2 [Finite R] :
    Nat.card SL(2, R) = Nat.card {v : R × R // IsUnimod v} * Nat.card R := by
  classical
  haveI : Fintype {v : R × R // IsUnimod v} := Fintype.ofFinite _
  have : Nat.card SL(2, R) = Nat.card (Σ v : {v : R × R // IsUnimod v},
      {g : SL(2, R) // botRow g = v}) := (Nat.card_congr (Equiv.sigmaFiberEquiv botRow)).symm
  rw [this, Nat.card_sigma]
  have hfib : ∀ v : {v : R × R // IsUnimod v},
      Nat.card {g : SL(2, R) // botRow g = v} = Nat.card R := by
    rintro ⟨⟨c, d⟩, x, y, hxy⟩
    have hcongr : Nat.card {g : SL(2, R) // botRow g = ⟨(c, d), ⟨x, y, hxy⟩⟩}
        = Nat.card {g : SL(2, R) // g.1 1 0 = c ∧ g.1 1 1 = d} := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
      simp [botRow, Subtype.ext_iff, Prod.ext_iff]
    rw [hcongr]
    exact card_botRow_fiber' c d x y (by simpa using hxy)
  simp only [hfib]
  rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, ← Nat.card_eq_fintype_card]

/-- The Borel subgroup of `SL(2,R)`: the matrices whose lower-left entry vanishes. -/
def borel (R : Type*) [CommRing R] : Subgroup SL(2, R) where
  carrier := {g | g.1 1 0 = 0}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    have h := (Matrix.two_mul_expl a.1 b.1).2.2.1
    simp only [Set.mem_setOf_eq, Matrix.SpecialLinearGroup.coe_mul] at *
    rw [h, ha, hb]; ring
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl a]
    simpa using ha

@[simp] theorem mem_borel {g : SL(2, R)} : g ∈ borel R ↔ g.1 1 0 = 0 := Iff.rfl

/-- `Rˣ × R ≃ B(R)`, by `(u, b) ↦ ![![u, b], ![0, u⁻¹]]`. -/
def borelEquiv : Rˣ × R ≃ borel R where
  toFun p := ⟨⟨!![(p.1 : R), p.2; 0, ((p.1⁻¹ : Rˣ) : R)], by
      rw [Matrix.det_fin_two_of]; simp⟩, by simp [borel]⟩
  invFun g :=
    (⟨g.1.1 0 0, g.1.1 1 1, by
        have h := g.1.2
        rw [Matrix.det_fin_two] at h
        have h0 : g.1.1 1 0 = 0 := g.2
        rw [h0] at h; linear_combination h, by
        have h := g.1.2
        rw [Matrix.det_fin_two] at h
        have h0 : g.1.1 1 0 = 0 := g.2
        rw [h0] at h; linear_combination h⟩, g.1.1 0 1)
  left_inv := by
    rintro ⟨u, b⟩
    ext <;> simp
  right_inv := by
    rintro ⟨g, hg⟩
    have h0 : g.1 1 0 = 0 := hg
    have hdet : g.1 0 0 * g.1 1 1 = 1 := by
      have h := g.2
      rw [Matrix.det_fin_two, h0] at h; linear_combination h
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h0]

theorem card_borel [Finite R] : Nat.card (borel R) = Nat.card Rˣ * Nat.card R := by
  rw [← Nat.card_congr (borelEquiv (R := R)), Nat.card_prod]

/-- The index of the Borel, times the number of units, is the number of
unimodular pairs. -/
theorem index_borel_mul_card_units [Finite R] :
    (borel R).index * Nat.card Rˣ = Nat.card {v : R × R // IsUnimod v} := by
  have h := (borel R).index_mul_card
  rw [card_borel, card_SL2] at h
  have hR : 0 < Nat.card R := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hR ?_
  rw [mul_assoc]; exact h

end Ring

/-- The number of unimodular pairs over `ℤ/n`. -/
noncomputable def unimodCount (n : ℕ) : ℕ := Nat.card {v : ZMod n × ZMod n // IsUnimod v}

section PrimePow

variable {p k : ℕ}

/-- Over `ℤ/pᵏ` (a local ring) a pair is unimodular exactly when one entry is a unit. -/
theorem isUnimod_iff_isUnit (hp : p.Prime) (hk : 0 < k) (a b : ZMod (p ^ k)) :
    IsUnimod (a, b) ↔ IsUnit a ∨ IsUnit b := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  have hunit : ∀ c : ZMod (p ^ k), IsUnit c ↔ ¬ p ∣ c.val := by
    intro c
    have h1 : IsUnit c ↔ Nat.Coprime c.val (p ^ k) := by
      rw [← ZMod.isUnit_iff_coprime c.val (p ^ k)]
      simp [ZMod.natCast_val, ZMod.cast_id]
    rw [h1, Nat.coprime_pow_right_iff hk, Nat.coprime_comm,
      Nat.Prime.coprime_iff_not_dvd hp]
  constructor
  · rintro ⟨x, y, hxy⟩
    by_contra hcon
    obtain ⟨ha, hb⟩ := not_or.mp hcon
    obtain ⟨s, hs⟩ := not_not.mp ((hunit a).not.mp ha)
    obtain ⟨t, ht⟩ := not_not.mp ((hunit b).not.mp hb)
    have hA : a = (p : ZMod (p ^ k)) * (s : ZMod (p ^ k)) := by
      have : ((a.val : ℕ) : ZMod (p ^ k)) = a := by simp [ZMod.natCast_val, ZMod.cast_id]
      rw [← this, hs]; push_cast; ring
    have hB : b = (p : ZMod (p ^ k)) * (t : ZMod (p ^ k)) := by
      have : ((b.val : ℕ) : ZMod (p ^ k)) = b := by simp [ZMod.natCast_val, ZMod.cast_id]
      rw [← this, ht]; push_cast; ring
    have hmul : (p : ZMod (p ^ k)) * (x * s + y * t) = 1 := by
      simp only at hxy
      rw [hA, hB] at hxy
      linear_combination hxy
    have hpunit : IsUnit (p : ZMod (p ^ k)) :=
      ⟨⟨(p : ZMod (p ^ k)), x * s + y * t, hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩
    rw [ZMod.isUnit_iff_coprime p (p ^ k), Nat.coprime_pow_right_iff hk,
      Nat.Coprime, Nat.gcd_self] at hpunit
    exact hp.one_lt.ne' hpunit
  · rintro (⟨u, hu⟩ | ⟨u, hu⟩)
    · exact ⟨(u⁻¹ : (ZMod (p ^ k))ˣ), 0, by simp [← hu]⟩
    · exact ⟨0, (u⁻¹ : (ZMod (p ^ k))ˣ), by simp [← hu]⟩

/-- `Mˣ ≃ {a : M // IsUnit a}`. -/
noncomputable def unitsEquivIsUnit (M : Type*) [Monoid M] : Mˣ ≃ {a : M // IsUnit a} where
  toFun u := ⟨(u : M), u.isUnit⟩
  invFun a := a.2.unit
  left_inv u := Units.ext (IsUnit.unit_spec u.isUnit)
  right_inv a := Subtype.ext a.2.unit_spec

theorem card_isUnit_zmod (n : ℕ) [NeZero n] :
    Nat.card {a : ZMod n // IsUnit a} = Nat.totient n := by
  rw [Nat.card_congr (unitsEquivIsUnit (ZMod n)).symm]
  haveI : Fintype (ZMod n)ˣ := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

/-- The number of unimodular pairs over `ℤ/pᵏ`. -/
theorem unimodCount_prime_pow (hp : p.Prime) (hk : 0 < k) :
    unimodCount (p ^ k) = (p ^ k + p ^ (k - 1)) * Nat.totient (p ^ k) := by
  classical
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  set q : ℕ := p ^ k with hqdef
  set A : ℕ := p ^ (k - 1) with hAdef
  set φ : ℕ := Nat.totient q with hφdef
  set m : ℕ := Nat.card {a : ZMod q // ¬ IsUnit a} with hmdef
  -- `#(ZMod q) = q`
  have hcardq : Nat.card (ZMod q) = q := by simp [Nat.card_eq_fintype_card]
  -- units and non-units partition `ZMod q`
  have hφm : φ + m = q := by
    have h := Nat.card_congr (Equiv.sumCompl (fun a : ZMod q => IsUnit a))
    rw [Nat.card_sum, card_isUnit_zmod q, hcardq] at h
    exact h
  -- unimodular and non-unimodular pairs partition `(ZMod q)²`
  have hU : unimodCount q + Nat.card {v : ZMod q × ZMod q // ¬ IsUnimod v} = q * q := by
    have h := Nat.card_congr (Equiv.sumCompl (fun v : ZMod q × ZMod q => IsUnimod v))
    rw [Nat.card_sum, Nat.card_prod, hcardq] at h
    exact h
  -- the non-unimodular pairs are exactly the pairs of non-units
  have hnon : Nat.card {v : ZMod q × ZMod q // ¬ IsUnimod v} = m * m := by
    have e1 : {v : ZMod q × ZMod q // ¬ IsUnimod v}
        ≃ {v : ZMod q × ZMod q // ¬ IsUnit v.1 ∧ ¬ IsUnit v.2} :=
      Equiv.subtypeEquivRight fun v => by
        rw [show v = (v.1, v.2) from rfl, isUnimod_iff_isUnit hp hk, not_or]
    have e2 : {v : ZMod q × ZMod q // ¬ IsUnit v.1 ∧ ¬ IsUnit v.2}
        ≃ {a : ZMod q // ¬ IsUnit a} × {b : ZMod q // ¬ IsUnit b} :=
      Equiv.subtypeProdEquivProd (p := fun a : ZMod q => ¬ IsUnit a)
        (q := fun b : ZMod q => ¬ IsUnit b)
    rw [Nat.card_congr (e1.trans e2), Nat.card_prod]
  -- the arithmetic
  have hqA : q = A * p := by
    rw [hqdef, hAdef, ← pow_succ]
    congr 1
    omega
  have hφA : φ = A * (p - 1) := by
    rw [hφdef, hqdef, Nat.totient_prime_pow hp hk]
  have hφA' : φ + A = q := by
    rw [hφA, hqA, ← Nat.mul_succ]
    congr 1
    have := hp.two_le
    omega
  have hmA : m = A := by omega
  rw [hnon, hmA] at hU
  have hexp : (φ + A + A) * φ + A * A = (φ + A) * (φ + A) := by ring
  have hgoal : unimodCount q + A * A = (φ + A + A) * φ + A * A := by
    rw [hU, hexp, hφA']
  have hfin : unimodCount q = (φ + A + A) * φ := Nat.add_right_cancel hgoal
  rw [hfin, ← hφA']

end PrimePow

section CRT

/-- A ring isomorphism carries unimodular pairs to unimodular pairs. -/
def unimodCongr {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    {v : R × R // IsUnimod v} ≃ {v : S × S // IsUnimod v} :=
  Equiv.subtypeEquiv (e.toEquiv.prodCongr e.toEquiv) fun v => by
    constructor
    · rintro ⟨x, y, hxy⟩
      exact ⟨e x, e y, by simpa using congrArg e hxy⟩
    · rintro ⟨x, y, hxy⟩
      refine ⟨e.symm x, e.symm y, ?_⟩
      have h := congrArg e.symm hxy
      simpa using h

/-- Unimodularity over a product ring is unimodularity in each factor. -/
theorem isUnimod_prod {R S : Type*} [CommRing R] [CommRing S] (v : (R × S) × (R × S)) :
    IsUnimod v ↔ IsUnimod (v.1.1, v.2.1) ∧ IsUnimod (v.1.2, v.2.2) := by
  constructor
  · rintro ⟨x, y, hxy⟩
    have h1 := congrArg Prod.fst hxy
    have h2 := congrArg Prod.snd hxy
    exact ⟨⟨x.1, y.1, by simpa using h1⟩, ⟨x.2, y.2, by simpa using h2⟩⟩
  · rintro ⟨⟨x1, y1, h1⟩, ⟨x2, y2, h2⟩⟩
    refine ⟨(x1, x2), (y1, y2), ?_⟩
    refine Prod.ext ?_ ?_
    · simpa using h1
    · simpa using h2

/-- Unimodular pairs over `R × S` split. -/
def unimodProdEquiv {R S : Type*} [CommRing R] [CommRing S] :
    {v : (R × S) × (R × S) // IsUnimod v}
      ≃ {v : R × R // IsUnimod v} × {v : S × S // IsUnimod v} :=
  (Equiv.subtypeEquiv (Equiv.prodProdProdComm R S R S)
    (fun v => by rw [isUnimod_prod]; rfl)).trans
      (Equiv.subtypeProdEquivProd (p := fun v : R × R => IsUnimod v)
        (q := fun v : S × S => IsUnimod v))

theorem unimodCount_mul {m n : ℕ} (h : Nat.Coprime m n) :
    unimodCount (m * n) = unimodCount m * unimodCount n := by
  rw [unimodCount, unimodCount, unimodCount, ← Nat.card_prod]
  exact Nat.card_congr ((unimodCongr (ZMod.chineseRemainder h)).trans unimodProdEquiv)

end CRT

section Index

theorem divisors_filter_prime (N : ℕ) :
    N.divisors.filter Nat.Prime = N.primeFactors := by
  ext p
  simp only [Finset.mem_filter, Nat.mem_divisors, Nat.mem_primeFactors]
  tauto

theorem gammaZeroIndex_one : gammaZeroIndex 1 = 1 := by
  rw [gammaZeroIndex, Nat.divisors_one, Finset.filter_singleton, if_neg Nat.not_prime_one]
  simp

theorem gammaZeroIndex_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    gammaZeroIndex (p ^ k) = p ^ k + p ^ (k - 1) := by
  have hpf : (p ^ k).primeFactors = {p} := by
    rw [Nat.primeFactors_pow _ hk.ne', hp.primeFactors]
  rw [gammaZeroIndex, divisors_filter_prime _, hpf]
  simp only [Finset.prod_singleton, id_eq]
  have hdiv : p ^ k / p = p ^ (k - 1) := by
    conv_lhs => rw [show k = (k - 1) + 1 from by omega]
    rw [pow_succ, Nat.mul_div_cancel _ hp.pos]
  rw [hdiv]
  have : p ^ (k - 1) * p = p ^ k := by
    conv_rhs => rw [show k = (k - 1) + 1 from by omega]
    rw [pow_succ]
  rw [Nat.mul_add, mul_one, this]

theorem gammaZeroIndex_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : Nat.Coprime m n) :
    gammaZeroIndex (m * n) = gammaZeroIndex m * gammaZeroIndex n := by
  have hpf : (m * n).primeFactors = m.primeFactors ∪ n.primeFactors :=
    Nat.primeFactors_mul hm hn
  have hdisj : Disjoint m.primeFactors n.primeFactors := Nat.Coprime.disjoint_primeFactors h
  have hradm : (m.primeFactors).prod id ∣ m := by
    simpa using Nat.prod_primeFactors_dvd m
  have hradn : (n.primeFactors).prod id ∣ n := by
    simpa using Nat.prod_primeFactors_dvd n
  rw [gammaZeroIndex, gammaZeroIndex, gammaZeroIndex,
    divisors_filter_prime _, divisors_filter_prime _, divisors_filter_prime _,
    hpf, Finset.prod_union hdisj, Finset.prod_union hdisj,
    ← Nat.div_mul_div_comm hradm hradn]
  ring

theorem unimodCount_one : unimodCount 1 = 1 := by
  have hne : Nonempty {v : ZMod 1 × ZMod 1 // IsUnimod v} :=
    ⟨⟨(0, 0), 0, 0, Subsingleton.elim _ _⟩⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, hne⟩

/-- **The number of unimodular pairs mod `N` is `μ(N) · φ(N)`.** -/
theorem unimodCount_eq_gammaZeroIndex_mul_totient :
    ∀ N : ℕ, N ≠ 0 → unimodCount N = gammaZeroIndex N * Nat.totient N := by
  intro N
  induction N using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
      intro _
      rw [unimodCount_prime_pow hp hk, gammaZeroIndex_prime_pow hp hk]
  | zero => intro h; exact absurd rfl h
  | one => intro _; rw [unimodCount_one, gammaZeroIndex_one, Nat.totient_one]
  | coprime a b ha hb hab iha ihb =>
      intro _
      rw [unimodCount_mul hab, iha (by omega), ihb (by omega),
        gammaZeroIndex_mul (by omega) (by omega) hab, Nat.totient_mul hab]
      ring

/-- **The index of the Borel subgroup of `SL(2, ℤ/N)` is `μ(N)`.** -/
theorem index_borel_zmod (N : ℕ) [NeZero N] :
    (borel (ZMod N)).index = gammaZeroIndex N := by
  have hN : N ≠ 0 := NeZero.ne N
  haveI : Fintype (ZMod N)ˣ := Fintype.ofFinite _
  have hunits : Nat.card (ZMod N)ˣ = Nat.totient N := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have h := index_borel_mul_card_units (R := ZMod N)
  rw [hunits] at h
  have h2 : (borel (ZMod N)).index * Nat.totient N = gammaZeroIndex N * Nat.totient N := by
    rw [h, ← unimodCount, unimodCount_eq_gammaZeroIndex_mul_totient N hN]
  exact Nat.eq_of_mul_eq_mul_right (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hN)) h2

end Index

section Lift

/-- Unimodularity mod `N` says `gcd(c, d, N) = 1`. -/
theorem gcd_val_of_isUnimod {N : ℕ} [NeZero N] {c d : ZMod N} (h : IsUnimod (c, d)) :
    Nat.gcd (Nat.gcd c.val d.val) N = 1 := by
  obtain ⟨x, y, hxy⟩ := h
  simp only at hxy
  set g := Nat.gcd (Nat.gcd c.val d.val) N with hgdef
  have hgN : g ∣ N := Nat.gcd_dvd_right _ _
  have hgne : g ≠ 0 := fun h0 => (NeZero.ne N) (Nat.eq_zero_of_zero_dvd (h0 ▸ hgN))
  haveI : NeZero g := ⟨hgne⟩
  have hc : (ZMod.castHom hgN (ZMod g)) c = 0 := by
    rw [ZMod.castHom_apply, ← ZMod.natCast_val c]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr
      ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _))
  have hd : (ZMod.castHom hgN (ZMod g)) d = 0 := by
    rw [ZMod.castHom_apply, ← ZMod.natCast_val d]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr
      ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _))
  have h10 : ((1 : ℕ) : ZMod g) = 0 := by
    have hmap := congrArg (ZMod.castHom hgN (ZMod g)) hxy
    rw [map_add, map_mul, map_mul, hc, hd, map_one, mul_zero, mul_zero, add_zero] at hmap
    rw [Nat.cast_one, ← hmap]
  exact Nat.dvd_one.mp ((ZMod.natCast_eq_zero_iff 1 g).mp h10)

/-- **The lifting lemma**: a unimodular pair mod `N` lifts to a coprime pair of
natural numbers. -/
theorem exists_coprime_lift {N : ℕ} [NeZero N] {c d : ZMod N} (h : IsUnimod (c, d)) :
    ∃ C D : ℕ, (C : ZMod N) = c ∧ (D : ZMod N) = d ∧ Nat.Coprime C D := by
  classical
  have hgcd := gcd_val_of_isUnimod h
  have hcv : ((c.val : ℕ) : ZMod N) = c := by simp [ZMod.natCast_val, ZMod.cast_id]
  have hdv : ((d.val : ℕ) : ZMod N) = d := by simp [ZMod.natCast_val, ZMod.cast_id]
  set C : ℕ := if c.val = 0 then N else c.val with hCdef
  have hCne : C ≠ 0 := by
    by_cases h0 : c.val = 0
    · rw [hCdef, if_pos h0]; exact NeZero.ne N
    · rw [hCdef, if_neg h0]; exact h0
  have hCc : (C : ZMod N) = c := by
    by_cases h0 : c.val = 0
    · rw [hCdef, if_pos h0, ZMod.natCast_self, ← hcv, h0, Nat.cast_zero]
    · rw [hCdef, if_neg h0]; exact hcv
  have hCdvd : ∀ e : ℕ, e ∣ C → e ∣ c.val := by
    intro e he
    by_cases h0 : c.val = 0
    · rw [h0]; exact dvd_zero e
    · rw [hCdef, if_neg h0] at he; exact he
  have hkey : Nat.gcd (Nat.gcd C d.val) N = 1 := by
    refine Nat.dvd_one.mp ?_
    rw [← hgcd]
    refine Nat.dvd_gcd (Nat.dvd_gcd ?_ ?_) (Nat.gcd_dvd_right _ _)
    · exact hCdvd _ ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _))
    · exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  set k : ℕ := ∏ q ∈ C.primeFactors.filter (fun q => ¬ q ∣ d.val), q with hkdef
  refine ⟨C, d.val + N * k, hCc, ?_, ?_⟩
  · push_cast
    rw [ZMod.natCast_self, zero_mul, add_zero, hdv]
  · rw [Nat.Coprime]
    by_contra hcop
    obtain ⟨p, hp, hpC, hpD⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
    have hpk : ¬ p ∣ d.val → p ∣ k := by
      intro hnd
      refine Finset.dvd_prod_of_mem _ ?_
      simp only [Finset.mem_filter, Nat.mem_primeFactors]
      exact ⟨⟨hp, hpC, hCne⟩, hnd⟩
    by_cases hpd : p ∣ d.val
    · have hNk : p ∣ N * k := by
        have hsub : p ∣ (d.val + N * k) - d.val := Nat.dvd_sub hpD hpd
        simpa using hsub
      have hpN : p ∣ N := by
        rcases (Nat.Prime.dvd_mul hp).mp hNk with hN | hk'
        · exact hN
        · exfalso
          rw [hkdef] at hk'
          obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hk'
          simp only [Finset.mem_filter, Nat.mem_primeFactors] at hq
          exact hq.2 (((Nat.prime_dvd_prime_iff_eq hp hq.1.1).mp hpq) ▸ hpd)
      have : p ∣ 1 := by
        rw [← hkey]
        exact Nat.dvd_gcd (Nat.dvd_gcd hpC hpd) hpN
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    · exact hpd (by
        have h1 : p ∣ N * k := Dvd.dvd.mul_left (hpk hpd) N
        have h2 : p ∣ (d.val + N * k) - N * k := Nat.dvd_sub hpD h1
        simpa using h2)

/-- **Reduction `SL(2,ℤ) → SL(2, ℤ/N)` is surjective.** -/
theorem SLMOD_surjective (N : ℕ) [NeZero N] :
    Function.Surjective
      (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N))) := by
  intro g
  obtain ⟨C, D, hC, hD, hCD⟩ := exists_coprime_lift (isUnimod_botRow g)
  -- Bézout for the coprime lift
  have hbez : (1 : ℤ) = (C : ℤ) * Nat.gcdA C D + (D : ℤ) * Nat.gcdB C D := by
    have h := Nat.gcd_eq_gcd_ab C D
    rw [hCD] at h
    exact_mod_cast h
  set a : ℤ := Nat.gcdA C D with ha
  set b : ℤ := Nat.gcdB C D with hb
  set γ₀ : SL(2, ℤ) := ⟨!![b, -a; (C : ℤ), (D : ℤ)], by
    rw [Matrix.det_fin_two_of]; linear_combination -hbez⟩ with hγ₀
  set M : SL(2, ZMod N) := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ₀ with hM
  have hmapval : ∀ (γ : SL(2, ℤ)) (i j : Fin 2),
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ).1 i j
        = ((γ.1 i j : ℤ) : ZMod N) := by
    intro γ i j; rfl
  have hM10 : M.1 1 0 = g.1 1 0 := by
    rw [hM, hmapval, hγ₀]
    simpa using hC
  have hM11 : M.1 1 1 = g.1 1 1 := by
    rw [hM, hmapval, hγ₀]
    simpa using hD
  have hMdet : M.1 0 0 * M.1 1 1 - M.1 0 1 * M.1 1 0 = 1 := by
    have := M.2; rwa [Matrix.det_fin_two] at this
  set h : SL(2, ZMod N) := g * M⁻¹ with hh
  have hinv : (M⁻¹).1 = !![M.1 1 1, -M.1 0 1; -M.1 1 0, M.1 0 0] := by
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl M]; rfl
  have hi00 : (M⁻¹).1 0 0 = M.1 1 1 := by rw [hinv]; simp
  have hi01 : (M⁻¹).1 0 1 = -M.1 0 1 := by rw [hinv]; simp
  have hi10 : (M⁻¹).1 1 0 = -M.1 1 0 := by rw [hinv]; simp
  have hi11 : (M⁻¹).1 1 1 = M.1 0 0 := by rw [hinv]; simp
  have hentry : ∀ i j : Fin 2,
      h.1 i j = g.1 i 0 * (M⁻¹).1 0 j + g.1 i 1 * (M⁻¹).1 1 j := by
    intro i j
    rw [hh, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have h10 : h.1 1 0 = 0 := by
    rw [hentry, hi00, hi10, ← hM10, ← hM11]; ring
  have h11 : h.1 1 1 = 1 := by
    rw [hentry, hi01, hi11, ← hM10, ← hM11]; linear_combination hMdet
  have h00 : h.1 0 0 = 1 := by
    have hdet := h.2
    rw [Matrix.det_fin_two, h10, h11] at hdet
    linear_combination hdet
  -- `h` is upper unitriangular, hence in the image
  set τ : SL(2, ℤ) := ⟨!![1, ((h.1 0 1).val : ℤ); 0, 1], by
    rw [Matrix.det_fin_two_of]; ring⟩ with hτ
  have hτ00 : τ.1 0 0 = 1 := by rw [hτ]; simp
  have hτ01 : τ.1 0 1 = ((h.1 0 1).val : ℤ) := by rw [hτ]; simp
  have hτ10 : τ.1 1 0 = 0 := by rw [hτ]; simp
  have hτ11 : τ.1 1 1 = 1 := by rw [hτ]; simp
  have hτh : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) τ = h := by
    apply Subtype.ext
    rw [← Matrix.ext_iff]
    simp only [Fin.forall_fin_two]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [hmapval, hτ00, h00]; norm_num
    · rw [hmapval, hτ01]
      push_cast
      simp [ZMod.natCast_val, ZMod.cast_id]
    · rw [hmapval, hτ10, h10]; norm_num
    · rw [hmapval, hτ11, h11]; norm_num
  refine ⟨τ * γ₀, ?_⟩
  rw [map_mul, hτh, ← hM, hh, inv_mul_cancel_right]

end Lift



/-- `Γ₀(N)` is the preimage of the Borel of `SL(2, ℤ/N)`. -/
theorem Gamma0_eq_comap (N : ℕ) :
    CongruenceSubgroup.Gamma0 N
      = (borel (ZMod N)).comap (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N))) := by
  ext g
  simp [mem_borel, CongruenceSubgroup.Gamma0_mem, Subgroup.mem_comap]

/-- **`[SL(2,ℤ) : Γ₀(N)] = μ(N)`.** -/
theorem Gamma0_index (N : ℕ) [NeZero N] :
    (CongruenceSubgroup.Gamma0 N).index = gammaZeroIndex N := by
  rw [Gamma0_eq_comap, Subgroup.index_comap_of_surjective _ (SLMOD_surjective N),
    index_borel_zmod]


end Fermat.Gamma0Index
