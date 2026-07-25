/-
RingTheory/PowerSeries/AdicComplete.lean — own work for the Fermat project.

**`𝔪`-adic precompleteness of a formal power series ring over a local
ring**, and its two consequences used by the Schlessinger cut of
`Modularity/Patching.lean`: `ℤ_p[[x₁, …, x_g]]` is `𝔪`-adically
precomplete, and precompleteness descends along a surjection.

The classical statement "a complete Noetherian local ring stays complete
after adjoining a power-series variable" is not in mathlib: mathlib
knows `IsAdicComplete (span (range X)) (MvPowerSeries σ R)` (completeness
for the ideal of the VARIABLES alone) but nothing about the MAXIMAL
ideal `𝔪_B + (X)` of `B⟦X⟧`, whose adic topology is strictly finer.

The bridge proven here is an exact coefficientwise description of the
powers of that maximal ideal,

  `f ∈ 𝔪_{B⟦X⟧} ^ n  ↔  ∀ j < n, coeff j f ∈ 𝔪_B ^ (n - j)`

(`mem_maximalIdeal_pow_powerSeries`), from which precompleteness is a
coefficientwise limit: each coefficient sequence of a Cauchy sequence of
power series is Cauchy in `B` (with a shift, since the `j`-th
coefficient only becomes controlled at level `> j`), and the series
assembled from the limits is the limit.

Nothing here has arithmetic content; it is the commutative algebra that
puts the de Smit–Lenstra presentation `ℤ_p[[x₁, …, x_g]] ↠ R_univ` of
the universal deformation ring inside Mazur's category.
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Ideal
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Data.Finsupp.Option
public import Mathlib.NumberTheory.Padics.PadicIntegers

@[expose] public section

namespace PowerSeriesAdicComplete

open IsLocalRing

/-! ### Two elementary ideal lemmas -/

/-- Monotonicity of ideal powers (mathlib has this only for the
generic ordered-monoid `pow_le_pow_left'`; spelled out here to keep the
instance search off the ideal lattice). -/
theorem Ideal.pow_le_pow_of_le {R : Type*} [CommRing R] {I J : Ideal R}
    (h : I ≤ J) (n : ℕ) : I ^ n ≤ J ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact Ideal.mul_mono ih h

/-- `x ≡ y [SMOD I • ⊤]` on a ring is plain membership `x - y ∈ I`. -/
theorem smodEq_iff_sub_mem {R : Type*} [CommRing R] (I : Ideal R) (x y : R) :
    x ≡ y [SMOD (I • (⊤ : Submodule R R))] ↔ x - y ∈ I := by
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top]

/-! ### The coefficientwise filtration on `B⟦X⟧` -/

section Filtration

variable {B : Type*} [CommRing B] [IsLocalRing B]

open PowerSeries

/-- A power series lies in the maximal ideal of `B⟦X⟧` exactly when its
constant coefficient lies in `𝔪_B` (a unit of `B⟦X⟧` is exactly a
series with unit constant coefficient). -/
theorem mem_maximalIdeal_powerSeries {f : PowerSeries B} :
    f ∈ maximalIdeal (PowerSeries B) ↔ constantCoeff f ∈ maximalIdeal B := by
  simp [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    PowerSeries.isUnit_iff_constantCoeff]

variable (B) in
/-- **The coefficientwise filtration**: `coeffFilt B n` is the set of
power series whose `j`-th coefficient lies in `𝔪_B ^ (n - j)` for every
`j < n`.  It is an ideal because the Cauchy product only ever pairs the
`j`-th coefficient of the product with coefficients of index `≤ j`.
The point of the section is that it EQUALS `𝔪_{B⟦X⟧} ^ n`. -/
def coeffFilt (n : ℕ) : Ideal (PowerSeries B) where
  carrier := {f | ∀ j < n, coeff j f ∈ maximalIdeal B ^ (n - j)}
  zero_mem' := by intro j _; simp
  add_mem' := by
    intro a b ha hb j hj
    rw [map_add]
    exact Ideal.add_mem _ (ha j hj) (hb j hj)
  smul_mem' := by
    intro c f hf j hj
    rw [smul_eq_mul, PowerSeries.coeff_mul]
    refine Ideal.sum_mem _ ?_
    rintro ⟨a, b⟩ hab
    rw [Finset.mem_antidiagonal] at hab
    exact Ideal.mul_mem_left _ _
      (Ideal.pow_le_pow_right (by omega) (hf b (by omega)))

/-- `X` lies in the maximal ideal of `B⟦X⟧`. -/
theorem X_mem_maximalIdeal : (X : PowerSeries B) ∈ maximalIdeal (PowerSeries B) := by
  rw [mem_maximalIdeal_powerSeries]
  simp

/-- The constants of `𝔪_B` lie in the maximal ideal of `B⟦X⟧`. -/
theorem map_C_maximalIdeal_le :
    (maximalIdeal B).map (C : B →+* PowerSeries B) ≤ maximalIdeal (PowerSeries B) := by
  rw [Ideal.map_le_iff_le_comap]
  intro m hm
  rw [Ideal.mem_comap, mem_maximalIdeal_powerSeries, constantCoeff_C]
  exact hm

/-- **Upper bound**: an element of `𝔪_{B⟦X⟧} ^ n` has its `j`-th
coefficient in `𝔪_B ^ (n - j)` for `j < n`.  Induction on `n`: the
`j`-th coefficient of a product `u · v` with `u ∈ 𝔪^n`, `v ∈ 𝔪` is a
sum over the antidiagonal, and on each summand `coeff a u · coeff b v`
the exponents `(n - a) + (1 - b)` already exceed `n + 1 - j`. -/
theorem maximalIdeal_pow_le_coeffFilt (n : ℕ) :
    maximalIdeal (PowerSeries B) ^ n ≤ coeffFilt B n := by
  induction n with
  | zero =>
    intro f _ j hj
    exact absurd hj (Nat.not_lt_zero j)
  | succ n ih =>
    rw [pow_succ, Ideal.mul_le]
    intro u hu v hv
    have hu2 : ∀ a : ℕ, coeff a u ∈ maximalIdeal B ^ (n - a) := by
      intro a
      by_cases h : a < n
      · exact ih hu a h
      · rw [Nat.sub_eq_zero_of_le (by omega), pow_zero, Ideal.one_eq_top]
        exact Submodule.mem_top
    have hv2 : ∀ b : ℕ, coeff b v ∈ maximalIdeal B ^ (1 - b) := by
      intro b
      match b with
      | 0 =>
        rw [Nat.sub_zero, pow_one, coeff_zero_eq_constantCoeff_apply]
        exact mem_maximalIdeal_powerSeries.mp hv
      | (b + 1) =>
        rw [Nat.sub_eq_zero_of_le (by omega), pow_zero, Ideal.one_eq_top]
        exact Submodule.mem_top
    intro j hj
    rw [PowerSeries.coeff_mul]
    refine Ideal.sum_mem _ ?_
    rintro ⟨a, b⟩ hab
    rw [Finset.mem_antidiagonal] at hab
    refine Ideal.pow_le_pow_right (show n + 1 - j ≤ (n - a) + (1 - b) by omega) ?_
    rw [pow_add]
    exact Ideal.mul_mem_mul (hu2 a) (hv2 b)

/-- **Lower bound**: a power series whose `j`-th coefficient lies in
`𝔪_B ^ (n - j)` for every `j < n` lies in `𝔪_{B⟦X⟧} ^ n`.  Split off the
polynomial part of degree `< n`: each term `C (coeff j f) · X ^ j` lies
in `𝔪^(n-j) · 𝔪^j = 𝔪^n`, and the remainder is divisible by `X ^ n`. -/
theorem coeffFilt_le_maximalIdeal_pow (n : ℕ) :
    coeffFilt B n ≤ maximalIdeal (PowerSeries B) ^ n := by
  intro f hf
  set q : PowerSeries B := ∑ j ∈ Finset.range n, C (coeff j f) * X ^ j with hq
  have hqcoeff : ∀ i < n, coeff i q = coeff i f := by
    intro i hi
    rw [hq, map_sum]
    simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq (Finset.range n) i fun j => coeff j f]
    simp [Finset.mem_range, hi]
  have hqmem : q ∈ maximalIdeal (PowerSeries B) ^ n := by
    refine Ideal.sum_mem _ ?_
    intro j hj
    rw [Finset.mem_range] at hj
    have h1 : (C (coeff j f) : PowerSeries B) ∈ maximalIdeal (PowerSeries B) ^ (n - j) := by
      have hmem : (C (coeff j f) : PowerSeries B) ∈
          ((maximalIdeal B ^ (n - j)).map (C : B →+* PowerSeries B)) :=
        Ideal.mem_map_of_mem _ (hf j hj)
      rw [Ideal.map_pow] at hmem
      exact Ideal.pow_le_pow_of_le map_C_maximalIdeal_le _ hmem
    have h2 : (X : PowerSeries B) ^ j ∈ maximalIdeal (PowerSeries B) ^ j :=
      Ideal.pow_mem_pow X_mem_maximalIdeal j
    have h3 := Ideal.mul_mem_mul h1 h2
    rw [← pow_add, show n - j + j = n by omega] at h3
    exact h3
  have hrest : (X : PowerSeries B) ^ n ∣ (f - q) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro i hi
    rw [map_sub, hqcoeff i hi, sub_self]
  obtain ⟨r, hr⟩ := hrest
  have hfeq : f = q + X ^ n * r := by rw [← hr]; ring
  rw [hfeq]
  exact Ideal.add_mem _ hqmem
    (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow X_mem_maximalIdeal n))

/-- **The coefficientwise description of the powers of `𝔪_{B⟦X⟧}`.** -/
theorem mem_maximalIdeal_pow_powerSeries {n : ℕ} {f : PowerSeries B} :
    f ∈ maximalIdeal (PowerSeries B) ^ n ↔
      ∀ j < n, coeff j f ∈ maximalIdeal B ^ (n - j) :=
  ⟨fun h => maximalIdeal_pow_le_coeffFilt n h, fun h => coeffFilt_le_maximalIdeal_pow n h⟩

end Filtration

/-! ### Precompleteness of `B⟦X⟧` -/

/-- **The one-variable step**: if a local ring `B` is `𝔪_B`-adically
precomplete then `B⟦X⟧` is `𝔪_{B⟦X⟧}`-adically precomplete.

Given a Cauchy sequence `g` of power series, the shifted coefficient
sequence `n ↦ coeff j (g (n + j + 1))` is Cauchy in `B` — the shift is
forced, since `coeff j` of an element of `𝔪_{B⟦X⟧}^m` is only
controlled to depth `m - j`.  The series assembled from the
coefficientwise limits is the limit, by the coefficientwise description
of `𝔪_{B⟦X⟧}^n`. -/
theorem isPrecomplete_powerSeries (B : Type*) [CommRing B] [IsLocalRing B]
    [IsPrecomplete (maximalIdeal B) B] :
    IsPrecomplete (maximalIdeal (PowerSeries B)) (PowerSeries B) := by
  classical
  constructor
  intro g hg
  have hgsub : ∀ {m n : ℕ}, m ≤ n →
      ∀ j < m, PowerSeries.coeff j (g m - g n) ∈ maximalIdeal B ^ (m - j) := by
    intro m n hmn
    exact mem_maximalIdeal_pow_powerSeries.mp
      ((smodEq_iff_sub_mem _ _ _).mp (hg hmn))
  have hcauchy : ∀ j : ℕ, ∀ {m n : ℕ}, m ≤ n →
      (fun i => PowerSeries.coeff j (g (i + j + 1))) m ≡
        (fun i => PowerSeries.coeff j (g (i + j + 1))) n
        [SMOD (maximalIdeal B ^ m • (⊤ : Submodule B B))] := by
    intro j m n hmn
    rw [smodEq_iff_sub_mem]
    have h := hgsub (show m + j + 1 ≤ n + j + 1 by omega) j (by omega)
    rw [map_sub] at h
    exact Ideal.pow_le_pow_right (show m ≤ m + j + 1 - j by omega) h
  choose L hL using fun j : ℕ =>
    IsPrecomplete.prec' (I := maximalIdeal B)
      (fun i => PowerSeries.coeff j (g (i + j + 1))) (hcauchy j)
  refine ⟨PowerSeries.mk L, fun n => ?_⟩
  rw [smodEq_iff_sub_mem, mem_maximalIdeal_pow_powerSeries]
  intro j hj
  have h1 : PowerSeries.coeff j (g n) - PowerSeries.coeff j (g (n + j + 1)) ∈
      maximalIdeal B ^ (n - j) := by
    have h := hgsub (show n ≤ n + j + 1 by omega) j hj
    rwa [map_sub] at h
  have h2 : PowerSeries.coeff j (g (n + j + 1)) - L j ∈ maximalIdeal B ^ (n - j) := by
    refine Ideal.pow_le_pow_right (show n - j ≤ n by omega) ?_
    exact (smodEq_iff_sub_mem _ _ _).mp (hL j n)
  have h3 := Ideal.add_mem _ h1 h2
  rw [map_sub, PowerSeries.coeff_mk]
  simpa using h3

/-! ### Currying `A[[x₀, …, xₙ]]`

The successor step of the induction on the number of variables needs
the currying isomorphism
`MvPowerSeries (Option σ) A ≃+* PowerSeries (MvPowerSeries σ A)`, which
mathlib does not have (only the polynomial analogue
`MvPolynomial.finSuccEquiv`).  It is built from the exponent
equivalence `(Option σ →₀ ℕ) ≃ ℕ × (σ →₀ ℕ)`
(`Finsupp.optionElim`/`Finsupp.some`); multiplicativity is the
antidiagonal-splitting computation. -/

section Curry

variable {σ : Type*} {A : Type*} [CommRing A]

/-- Additivity of the exponent currying `Finsupp.optionElim`. -/
theorem optionElim_add {α M : Type*} [AddZeroClass M] (y₁ y₂ : M) (f₁ f₂ : α →₀ M) :
    Finsupp.optionElim (y₁ + y₂) (f₁ + f₂) =
      Finsupp.optionElim y₁ f₁ + Finsupp.optionElim y₂ f₂ := by
  ext a; cases a <;> simp

/-- **Currying a multivariate power series** in the variable indexed by
`none`. -/
noncomputable def optionCurry (f : MvPowerSeries (Option σ) A) :
    PowerSeries (MvPowerSeries σ A) :=
  PowerSeries.mk fun n =>
    (fun d => MvPowerSeries.coeff (Finsupp.optionElim n d) f : MvPowerSeries σ A)

/-- The inverse of `optionCurry`. -/
noncomputable def optionUncurry (F : PowerSeries (MvPowerSeries σ A)) :
    MvPowerSeries (Option σ) A :=
  fun u => MvPowerSeries.coeff u.some (PowerSeries.coeff (u none) F)

theorem coeff_optionCurry (f : MvPowerSeries (Option σ) A) (n : ℕ) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (PowerSeries.coeff n (optionCurry f)) =
      MvPowerSeries.coeff (Finsupp.optionElim n d) f := by
  simp [optionCurry, MvPowerSeries.coeff_apply]

theorem coeff_optionUncurry (F : PowerSeries (MvPowerSeries σ A)) (u : Option σ →₀ ℕ) :
    MvPowerSeries.coeff u (optionUncurry F) =
      MvPowerSeries.coeff u.some (PowerSeries.coeff (u none) F) := by
  simp [optionUncurry, MvPowerSeries.coeff_apply]

theorem optionUncurry_optionCurry (f : MvPowerSeries (Option σ) A) :
    optionUncurry (optionCurry f) = f := by
  ext u
  rw [coeff_optionUncurry, coeff_optionCurry, Finsupp.optionElim_some]

theorem optionCurry_optionUncurry (F : PowerSeries (MvPowerSeries σ A)) :
    optionCurry (optionUncurry F) = F := by
  ext n d
  rw [coeff_optionCurry, coeff_optionUncurry, Finsupp.optionElim_apply_none,
    Finsupp.some_optionElim]

theorem optionCurry_add (f g : MvPowerSeries (Option σ) A) :
    optionCurry (f + g) = optionCurry f + optionCurry g := by
  ext n d
  simp [coeff_optionCurry]

/-- Multiplicativity of the currying map. -/
theorem optionCurry_mul (f g : MvPowerSeries (Option σ) A) :
    optionCurry (f * g) = optionCurry f * optionCurry g := by
  classical
  ext n d
  rw [coeff_optionCurry, MvPowerSeries.coeff_mul, PowerSeries.coeff_mul, map_sum]
  simp only [MvPowerSeries.coeff_mul, coeff_optionCurry]
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (i := fun u => ((u.1 none, u.2 none), (u.1.some, u.2.some)))
    (j := fun v => (Finsupp.optionElim v.1.1 v.2.1, Finsupp.optionElim v.1.2 v.2.2))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨u, v⟩ hu
    simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hu
    simp only [Finset.mem_product, Finset.HasAntidiagonal.mem_antidiagonal]
    refine ⟨?_, ?_⟩
    · have := congrArg (fun x => (x : Option σ →₀ ℕ) none) hu
      simpa using this
    · have := congrArg Finsupp.some hu
      simpa using this
  · rintro ⟨⟨i, j⟩, ⟨d1, d2⟩⟩ hv
    simp only [Finset.mem_product, Finset.HasAntidiagonal.mem_antidiagonal] at hv
    simp only [Finset.HasAntidiagonal.mem_antidiagonal]
    rw [← optionElim_add, hv.1, hv.2]
  · rintro ⟨u, v⟩ _
    simp [Finsupp.optionElim_some]
  · rintro ⟨⟨i, j⟩, ⟨d1, d2⟩⟩ _
    simp [Finsupp.some_optionElim]
  · rintro ⟨u, v⟩ _
    simp [Finsupp.optionElim_some]

/-- **The currying isomorphism**
`MvPowerSeries (Option σ) A ≃+* PowerSeries (MvPowerSeries σ A)`. -/
noncomputable def optionCurryEquiv (σ : Type*) (A : Type*) [CommRing A] :
    MvPowerSeries (Option σ) A ≃+* PowerSeries (MvPowerSeries σ A) where
  toFun := optionCurry
  invFun := optionUncurry
  left_inv := optionUncurry_optionCurry
  right_inv := optionCurry_optionUncurry
  map_mul' := optionCurry_mul
  map_add' := optionCurry_add

/-- Power series in an empty family of variables are constants. -/
noncomputable def mvPowerSeriesIsEmptyRingEquiv (σ : Type*) (A : Type*) [IsEmpty σ]
    [CommRing A] : A ≃+* MvPowerSeries σ A :=
  RingEquiv.ofBijective MvPowerSeries.C
    ⟨MvPowerSeries.C_injective, MvPowerSeries.C_surjective⟩

end Curry

/-! ### `ℤ_p[[x₁, …, x_g]]` -/

/-- Precompleteness transports along a ring isomorphism of local rings. -/
theorem isPrecomplete_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S)
    (h : IsPrecomplete (maximalIdeal R) R) : IsPrecomplete (maximalIdeal S) S := by
  rw [← IsLocalRing.map_ringEquiv_maximalIdeal e, IsPrecomplete.congr_ringEquiv]
  exact h

/-- **Noetherianity of `A[[x₁, …, x_n]]`** by induction on the number of
variables from mathlib's power-series Hilbert basis theorem. -/
theorem isNoetherianRing_mvPowerSeries.{uA} (n : ℕ) {A : Type uA} [CommRing A]
    [IsNoetherianRing A] : IsNoetherianRing (MvPowerSeries (Fin n) A) := by
  induction n with
  | zero => exact isNoetherianRing_of_ringEquiv A (mvPowerSeriesIsEmptyRingEquiv (Fin 0) A)
  | succ n ih =>
    haveI := ih
    exact isNoetherianRing_of_ringEquiv _
      (((MvPowerSeries.renameEquiv A (finSuccEquiv n)).toRingEquiv.trans
        (optionCurryEquiv (Fin n) A)).symm)

/-- **`𝔪`-adic precompleteness of `A[[x₁, …, x_n]]`** over a local
precomplete base, by induction on the number of variables from the
one-variable step `isPrecomplete_powerSeries`. -/
theorem isPrecomplete_mvPowerSeries.{uA} (n : ℕ) {A : Type uA} [CommRing A]
    [IsLocalRing A] [IsPrecomplete (maximalIdeal A) A] :
    IsPrecomplete (maximalIdeal (MvPowerSeries (Fin n) A)) (MvPowerSeries (Fin n) A) := by
  induction n with
  | zero =>
    exact isPrecomplete_of_ringEquiv (mvPowerSeriesIsEmptyRingEquiv (Fin 0) A)
      inferInstance
  | succ n ih =>
    haveI := ih
    haveI := isPrecomplete_powerSeries (MvPowerSeries (Fin n) A)
    exact isPrecomplete_of_ringEquiv
      (((MvPowerSeries.renameEquiv A (finSuccEquiv n)).toRingEquiv.trans
        (optionCurryEquiv (Fin n) A)).symm) inferInstance

/-- **Precompleteness descends along a surjection**, with the image
ideal: lift a Cauchy sequence of `S` to a Cauchy sequence of `R` by
lifting the successive differences into `I ^ n` (possible because
`I ^ n` maps ONTO `(I.map φ) ^ n`), take the limit upstairs and push it
down. -/
theorem isPrecomplete_of_surjective {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) [IsPrecomplete I R] (φ : R →+* S) (hφ : Function.Surjective φ) :
    IsPrecomplete (I.map φ) S := by
  classical
  constructor
  intro f hf
  have hdiff : ∀ n : ℕ, ∃ x, x ∈ I ^ n ∧ φ x = f (n + 1) - f n := by
    intro n
    have h : f n - f (n + 1) ∈ (I.map φ) ^ n :=
      (smodEq_iff_sub_mem _ _ _).mp (hf (Nat.le_succ n))
    rw [← Ideal.map_pow] at h
    obtain ⟨x, hx, hxeq⟩ := Ideal.mem_map_iff_of_surjective φ hφ |>.mp h
    exact ⟨-x, neg_mem hx, by rw [map_neg, hxeq]; ring⟩
  choose d hdmem hdeq using hdiff
  obtain ⟨r0, hr0⟩ := hφ (f 0)
  set g : ℕ → R := fun n => Nat.rec r0 (fun k gk => gk + d k) n with hgdef
  have hgsucc : ∀ n : ℕ, g (n + 1) = g n + d n := fun n => rfl
  have hgφ : ∀ n : ℕ, φ (g n) = f n := by
    intro n
    induction n with
    | zero => exact hr0
    | succ n ih => rw [hgsucc, map_add, ih, hdeq]; ring
  have hgstep : ∀ m k : ℕ, g (m + k) - g m ∈ I ^ m := by
    intro m k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : g (m + k + 1) - g (m + k) = d (m + k) := by
        rw [hgsucc]; ring
      have h2 : d (m + k) ∈ I ^ m :=
        Ideal.pow_le_pow_right (by omega) (hdmem (m + k))
      have h3 : g (m + (k + 1)) - g m = (g (m + k + 1) - g (m + k)) + (g (m + k) - g m) := by
        rw [show m + (k + 1) = m + k + 1 by omega]; ring
      rw [h3, h1]
      exact Ideal.add_mem _ h2 ih
  have hgcauchy : ∀ {m n : ℕ}, m ≤ n →
      g m ≡ g n [SMOD (I ^ m • (⊤ : Submodule R R))] := by
    intro m n hmn
    rw [smodEq_iff_sub_mem]
    have := hgstep m (n - m)
    rw [show m + (n - m) = n by omega] at this
    simpa using neg_mem this
  obtain ⟨Lr, hLr⟩ := IsPrecomplete.prec' (I := I) g hgcauchy
  refine ⟨φ Lr, fun n => ?_⟩
  rw [smodEq_iff_sub_mem, ← hgφ n, ← map_sub, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ ((smodEq_iff_sub_mem _ _ _).mp (hLr n))

end PowerSeriesAdicComplete
