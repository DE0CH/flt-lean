/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- `IsPGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point`: the fixed-point theorem
-- for a `p`-group acting on a finite set, which is what makes the unipotent (wild) part of
-- the group act with a nonzero fixed vector.
public import Mathlib.GroupTheory.PGroup
-- `sub_pow_char_pow_of_commute`: the Frobenius identity that turns "`f - 1` is nilpotent"
-- into "`f` has `p`-power order".
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Group.Subgroup.Finite
-- `Set.eq_of_subset_of_ncard_le`: the finiteness input to the choice of a MINIMAL nonzero
-- stable subgroup.
public import Mathlib.Data.Set.Card
-- `commutator`, `Subgroup.commutator_mem_commutator`
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Module.End
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# A common eigenvector with scalars in the prime field

Let `G` be a group acting on a finite abelian `p`-torsion group `T`. Suppose

* every element of the COMMUTATOR SUBGROUP of `G` acts UNIPOTENTLY on `T`, and
* every element of `G` satisfies a SPLIT QUADRATIC with integer roots — i.e. for each `g`
  there are `a b : ℕ` with `(g - a)(g - b)` nilpotent on `T`.

Then there is a nonzero `x : T` on which EVERY element of `G` acts by an integer scalar
(`main` result: `CommonEigenvector.exists_common_scalar_eigenvector`).

The proof is four moves, none of them requiring any representation theory over `𝔽̄_p`:

1. a unipotent endomorphism of a `p`-torsion group has `p`-power order, because
   `(f - 1) ^ (p ^ k) = f ^ (p ^ k) - 1` in characteristic `p`;
2. so the image of the commutator subgroup in `Equiv.Perm T` is a `p`-group, and its fixed
   subgroup `Fix` is therefore NONZERO (the fixed-point theorem for `p`-groups) — and it is
   `G`-stable, the commutator subgroup being normal;
3. inside `Fix` all the operators COMMUTE (two elements of `G` differ, after composing, by a
   commutator, which acts as the identity there); pick a MINIMAL nonzero `G`-stable subgroup
   `W ≤ Fix`;
4. for `g : G` the split quadratic has a nonzero kernel vector in `W`, so one of the two
   eigenspaces `ker (g - a) ⊓ W`, `ker (g - b) ⊓ W` is nonzero — and each is `G`-stable
   because everything commutes on `Fix`. Minimality forces it to be all of `W`, so `g` acts
   on `W` by the scalar. Any nonzero vector of `W` is the required `x`.

`exists_scalar_eigenvector_mod` is the RELATIVE form, which is what a triangularisation step
consumes: modulo a proper stable subgroup `N` of a finite `p`-power-torsion module `M`, it
produces `x ∉ N` with `p • x ∈ N` on which every element of `G` acts by an integer scalar
modulo `N`. It is deduced from the absolute form by passing to the `p`-torsion of `M ⧸ N`.

THIS FILE CONTAINS NO ARITHMETIC. It is the algebraic half of
`GaloisRepresentation.IsHardlyRamified.exists_inertiaEigenvector_space_of_charpoly` in
`Fermat/FLT/GaloisRepresentation/HardlyRamified/Family.lean`; the arithmetic half is the
statement that the residual representation's commutators act unipotently on inertia and that
each inertia element satisfies a split quadratic with roots in the prime field, which is
Brauer--Nesbitt plus the Frobenius-conjugation argument.
-/

@[expose] public section

namespace CommonEigenvector


variable {p : ℕ} [hp : Fact p.Prime] {G : Type*} [Group G]
variable {T : Type*} [AddCommGroup T] [Finite T]

section Basic
variable {S : Type*} [AddCommGroup S]

theorem addMonoidEnd_mul_apply (f g : AddMonoid.End S) (x : S) : (f * g) x = f (g x) := rfl

theorem addMonoidEnd_sub_natCast_apply (f : AddMonoid.End S) (c : ℕ) (x : S) :
    (f - (c : AddMonoid.End S)) x = f x - c • x := by
  rw [show ((f - (c : AddMonoid.End S)) x) = f x - (c : AddMonoid.End S) x from rfl]
  simp

theorem addMonoidEnd_one_apply (x : S) : (1 : AddMonoid.End S) x = x := rfl

end Basic

/-- The additive endomorphism ring of a nonzero `p`-torsion abelian group has
characteristic `p`. -/
theorem charP_addMonoidEnd (hptor : ∀ t : T, p • t = 0) {t₀ : T} (ht₀ : t₀ ≠ 0) :
    CharP (AddMonoid.End T) p := by
  constructor
  intro n
  constructor
  · intro h
    have h1 : (n : AddMonoid.End T) t₀ = 0 := by rw [h]; simp
    rw [show ((n : AddMonoid.End T) t₀) = n • t₀ by simp] at h1
    have h2 : addOrderOf t₀ ∣ n := addOrderOf_dvd_of_nsmul_eq_zero h1
    have h3 : addOrderOf t₀ ∣ p := addOrderOf_dvd_of_nsmul_eq_zero (hptor t₀)
    have h4 : addOrderOf t₀ = p := by
      rcases (Nat.Prime.eq_one_or_self_of_dvd (Fact.out : p.Prime) _ h3) with h | h
      · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h) ht₀
      · exact h
    rwa [h4] at h2
  · rintro ⟨k, rfl⟩
    ext t
    show (p * k : ℕ) • t = 0
    rw [mul_comm, mul_nsmul, hptor]

omit [Finite T] in
/-- A nilpotent additive endomorphism has a nonzero kernel vector inside any nonzero
stable subgroup. -/
theorem exists_ne_zero_apply_eq_zero_of_isNilpotent (f : AddMonoid.End T) (W : AddSubgroup T)
    (hW : W ≠ ⊥) (hstab : ∀ x ∈ W, f x ∈ W) (hnil : IsNilpotent f) :
    ∃ w ∈ W, w ≠ 0 ∧ f w = 0 := by
  have hiter : ∀ m : ℕ, ∀ x ∈ W, (f ^ m) x ∈ W := by
    intro m
    induction m with
    | zero => intro x hx; simpa using hx
    | succ m ih =>
      intro x hx
      rw [pow_succ', addMonoidEnd_mul_apply]
      exact hstab _ (ih x hx)
  have key : ∀ n : ℕ, (∀ x ∈ W, (f ^ n) x = 0) → ∃ w ∈ W, w ≠ 0 ∧ f w = 0 := by
    intro n
    induction n with
    | zero =>
      intro h
      exact absurd (by rw [eq_bot_iff]; intro x hx; simpa using h x hx) hW
    | succ n ih =>
      intro h
      by_cases hall : ∀ x ∈ W, (f ^ n) x = 0
      · exact ih hall
      · push_neg at hall
        obtain ⟨x, hxW, hx⟩ := hall
        refine ⟨(f ^ n) x, hiter n x hxW, hx, ?_⟩
        have h1 : (f ^ (n + 1)) x = 0 := h x hxW
        rwa [pow_succ', addMonoidEnd_mul_apply] at h1
  obtain ⟨n, hn⟩ := hnil
  exact key n (fun x _ => by rw [hn]; simp)

/-- **A COMMON EIGENVECTOR, WITH SCALAR IN THE PRIME FIELD, FOR A GROUP ACTING ON A
`p`-TORSION ABELIAN GROUP WHOSE COMMUTATORS ACT UNIPOTENTLY.** -/
theorem exists_common_scalar_eigenvector (φ : G →* AddMonoid.End T)
    {t₀ : T} (ht₀ : t₀ ≠ 0) (hptor : ∀ t : T, p • t = 0)
    (hcomm : ∀ g ∈ commutator G, IsNilpotent (φ g - 1))
    (hquad : ∀ g : G, ∃ a b : ℕ,
      IsNilpotent ((φ g - (a : AddMonoid.End T)) * (φ g - (b : AddMonoid.End T)))) :
    ∃ x : T, x ≠ 0 ∧ ∀ g : G, ∃ c : ℕ, φ g x = c • x := by
  classical
  haveI : CharP (AddMonoid.End T) p := charP_addMonoidEnd hptor ht₀
  have hcomp : ∀ (a b : G) (x : T), φ a (φ b x) = φ (a * b) x := by
    intro a b x; rw [map_mul, addMonoidEnd_mul_apply]
  -- ### step 1: elements of the commutator subgroup act with `p`-power order
  have hporder : ∀ h ∈ commutator G, ∃ k : ℕ, φ (h ^ p ^ k) = 1 := by
    intro h hh
    obtain ⟨n, hn⟩ := hcomm h hh
    refine ⟨n, ?_⟩
    have hle : n ≤ p ^ n := (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
    have h1 : (φ h - 1) ^ p ^ n = 0 := by
      rw [show p ^ n = n + (p ^ n - n) by omega, pow_add, hn, zero_mul]
    rw [sub_pow_char_pow_of_commute p n (Commute.one_right _), one_pow, sub_eq_zero] at h1
    rw [map_pow, h1]
  -- ### step 2: the subgroup fixed by every commutator
  let Fix : AddSubgroup T :=
    { carrier := {x | ∀ h ∈ commutator G, φ h x = x}
      zero_mem' := fun h _ => map_zero _
      add_mem' := fun {a b} ha hb h hh => by
        show φ h (a + b) = a + b
        rw [map_add, ha h hh, hb h hh]
      neg_mem' := fun {a} ha h hh => by
        show φ h (-a) = -a
        rw [map_neg, ha h hh] }
  have hFixmem : ∀ x : T, x ∈ Fix ↔ ∀ h ∈ commutator G, φ h x = x := fun _ => Iff.rfl
  -- ### step 3: `Fix` is nonzero, by the fixed-point theorem for `p`-groups
  have hFixne : Fix ≠ ⊥ := by
    let act : G →* Equiv.Perm T :=
      { toFun := fun g =>
          { toFun := φ g, invFun := φ g⁻¹
            left_inv := fun x => by
              rw [hcomp, inv_mul_cancel, map_one, addMonoidEnd_one_apply]
            right_inv := fun x => by
              rw [hcomp, mul_inv_cancel, map_one, addMonoidEnd_one_apply] }
        map_one' := by
          ext x
          show φ 1 x = x
          rw [map_one, addMonoidEnd_one_apply]
        map_mul' := fun a b => by
          ext x
          show φ (a * b) x = φ a (φ b x)
          rw [hcomp] }
    have hact : ∀ (g : G) (x : T), act g x = φ g x := fun _ _ => rfl
    let Q : Subgroup (Equiv.Perm T) := (commutator G).map act
    have hQ : IsPGroup p Q := by
      intro q
      obtain ⟨h, hh, hqh⟩ := Subgroup.mem_map.mp q.2
      obtain ⟨k, hk⟩ := hporder h hh
      refine ⟨k, ?_⟩
      refine Subtype.ext ?_
      rw [Subgroup.coe_pow, ← hqh, ← map_pow]
      show act (h ^ p ^ k) = ((1 : Q) : Equiv.Perm T)
      ext x
      rw [hact, hk, addMonoidEnd_one_apply]
      simp
    have hpc : p ∣ Nat.card T := by
      have h3 : addOrderOf t₀ ∣ p := addOrderOf_dvd_of_nsmul_eq_zero (hptor t₀)
      have h4 : addOrderOf t₀ = p := by
        rcases (Nat.Prime.eq_one_or_self_of_dvd (Fact.out : p.Prime) _ h3) with h | h
        · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h) ht₀
        · exact h
      exact h4 ▸ addOrderOf_dvd_natCard t₀
    have hzero : (0 : T) ∈ MulAction.fixedPoints Q T := by
      intro q
      obtain ⟨h, _, hqh⟩ := Subgroup.mem_map.mp q.2
      show (q : Equiv.Perm T) 0 = 0
      rw [← hqh, hact, map_zero]
    obtain ⟨b, hb, hb0⟩ := hQ.exists_fixed_point_of_prime_dvd_card_of_fixed_point T hpc hzero
    intro hcon
    apply hb0
    have hbFix : b ∈ Fix := by
      intro h hh
      have h1 := hb ⟨act h, Subgroup.mem_map.mpr ⟨h, hh, rfl⟩⟩
      rw [← hact]
      exact h1
    rw [hcon, AddSubgroup.mem_bot] at hbFix
    exact hbFix.symm
  -- ### step 4: `Fix` is stable under the whole group
  have hFixstab : ∀ g : G, ∀ x ∈ Fix, φ g x ∈ Fix := by
    intro g x hx h hh
    have hconj : g⁻¹ * h * g ∈ commutator G := by
      have h1 := (inferInstance : (commutator G).Normal).conj_mem h hh g⁻¹
      simpa using h1
    show φ h (φ g x) = φ g x
    rw [hcomp, show h * g = g * (g⁻¹ * h * g) by group, ← hcomp, hx _ hconj]
  -- ### step 5: all the operators commute on `Fix`
  have hcommute : ∀ (g₁ g₂ : G), ∀ x ∈ Fix, φ g₁ (φ g₂ x) = φ g₂ (φ g₁ x) := by
    intro g₁ g₂ x hx
    have hc : g₁⁻¹ * g₂⁻¹ * g₁ * g₂ ∈ commutator G := by
      have h1 := Subgroup.commutator_mem_commutator (G := G) (H₁ := ⊤) (H₂ := ⊤)
        (Subgroup.mem_top g₁⁻¹) (Subgroup.mem_top g₂⁻¹)
      rw [commutatorElement_def, inv_inv, inv_inv] at h1
      exact h1
    rw [hcomp, hcomp, show g₁ * g₂ = (g₂ * g₁) * (g₁⁻¹ * g₂⁻¹ * g₁ * g₂) by group,
      ← hcomp, hx _ hc]
  -- ### step 6: a minimal nonzero stable subgroup of `Fix`
  let 𝒮 : Set (AddSubgroup T) := {W | W ≠ ⊥ ∧ W ≤ Fix ∧ ∀ g : G, ∀ x ∈ W, φ g x ∈ W}
  have hFixS : Fix ∈ 𝒮 := ⟨hFixne, le_rfl, hFixstab⟩
  have hex : ∃ n, ∃ W ∈ 𝒮, (W : Set T).ncard = n := ⟨_, Fix, hFixS, rfl⟩
  obtain ⟨W, hWS, hWcard⟩ := Nat.find_spec hex
  have hmin : ∀ W' ∈ 𝒮, W' ≤ W → W' = W := by
    intro W' hW' hle
    have h1 : Nat.find hex ≤ (W' : Set T).ncard := Nat.find_le ⟨W', hW', rfl⟩
    have h2 : (W : Set T).ncard ≤ (W' : Set T).ncard := by rw [hWcard]; exact h1
    exact SetLike.coe_injective (Set.eq_of_subset_of_ncard_le hle h2 (Set.toFinite _))
  obtain ⟨hWne, hWle, hWstab⟩ := hWS
  -- ### step 7: every group element acts on `W` by an integer scalar
  have hscal : ∀ g : G, ∃ c : ℕ, ∀ x ∈ W, φ g x = c • x := by
    intro g
    obtain ⟨a, b, hab⟩ := hquad g
    have hsub : ∀ (c : ℕ), ∀ x ∈ W, (φ g - (c : AddMonoid.End T)) x ∈ W := by
      intro c x hx
      rw [addMonoidEnd_sub_natCast_apply]
      exact W.sub_mem (hWstab g x hx) (W.nsmul_mem hx c)
    obtain ⟨w, hwW, hw0, hwker⟩ :=
      exists_ne_zero_apply_eq_zero_of_isNilpotent
        ((φ g - (a : AddMonoid.End T)) * (φ g - (b : AddMonoid.End T))) W hWne
        (fun x hx => by rw [addMonoidEnd_mul_apply]; exact hsub a _ (hsub b x hx)) hab
    rw [addMonoidEnd_mul_apply] at hwker
    have hkey : ∃ c : ℕ, ∃ w' ∈ W, w' ≠ 0 ∧ φ g w' = c • w' := by
      by_cases hbw : (φ g - (b : AddMonoid.End T)) w = 0
      · rw [addMonoidEnd_sub_natCast_apply, sub_eq_zero] at hbw
        exact ⟨b, w, hwW, hw0, hbw⟩
      · refine ⟨a, (φ g - (b : AddMonoid.End T)) w, hsub b w hwW, hbw, ?_⟩
        rw [addMonoidEnd_sub_natCast_apply, sub_eq_zero] at hwker
        exact hwker
    obtain ⟨c, w', hw'W, hw'0, hw'⟩ := hkey
    refine ⟨c, ?_⟩
    let K : AddSubgroup T :=
      { carrier := {x | x ∈ W ∧ φ g x = c • x}
        zero_mem' := ⟨W.zero_mem, by rw [map_zero, smul_zero]⟩
        add_mem' := fun {u v} hu hv =>
          ⟨W.add_mem hu.1 hv.1, by rw [map_add, hu.2, hv.2, smul_add]⟩
        neg_mem' := fun {u} hu => ⟨W.neg_mem hu.1, by rw [map_neg, hu.2, smul_neg]⟩ }
    have hKS : K ∈ 𝒮 := by
      refine ⟨?_, fun x hx => hWle hx.1, ?_⟩
      · intro hcon
        have h1 : w' ∈ K := ⟨hw'W, hw'⟩
        rw [hcon, AddSubgroup.mem_bot] at h1
        exact hw'0 h1
      · intro g' x hx
        refine ⟨hWstab g' x hx.1, ?_⟩
        show φ g (φ g' x) = c • φ g' x
        rw [hcommute g g' x (hWle hx.1), hx.2, map_nsmul]
    have hKW : K = W := hmin K hKS (fun x hx => hx.1)
    intro x hx
    have h1 : x ∈ K := by rw [hKW]; exact hx
    exact h1.2
  obtain ⟨x, hxW, hx0⟩ : ∃ x ∈ W, x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hWne (by rw [eq_bot_iff]; intro y hy; simpa using hcon y hy)
  refine ⟨x, hx0, fun g => ?_⟩
  obtain ⟨c, hc⟩ := hscal g
  exact ⟨c, hc x hxW⟩

/-! ## transfer of nilpotency along intertwining maps -/

section Transfer

variable {M M' : Type*} [AddCommGroup M] [AddCommGroup M']

/-- `ψ` intertwines `f` and `f'`. -/
def Intertwines (ψ : M →+ M') (f : AddMonoid.End M) (f' : AddMonoid.End M') : Prop :=
  ∀ x, ψ (f x) = f' (ψ x)

theorem Intertwines.mul {ψ : M →+ M'} {f₁ f₂ : AddMonoid.End M} {f₁' f₂' : AddMonoid.End M'}
    (h₁ : Intertwines ψ f₁ f₁') (h₂ : Intertwines ψ f₂ f₂') :
    Intertwines ψ (f₁ * f₂) (f₁' * f₂') := by
  intro x
  rw [addMonoidEnd_mul_apply, addMonoidEnd_mul_apply, h₁, h₂]

theorem Intertwines.sub_natCast {ψ : M →+ M'} {f : AddMonoid.End M} {f' : AddMonoid.End M'}
    (h : Intertwines ψ f f') (c : ℕ) :
    Intertwines ψ (f - (c : AddMonoid.End M)) (f' - (c : AddMonoid.End M')) := by
  intro x
  rw [addMonoidEnd_sub_natCast_apply, addMonoidEnd_sub_natCast_apply, map_sub, h, map_nsmul]

theorem Intertwines.sub_one {ψ : M →+ M'} {f : AddMonoid.End M} {f' : AddMonoid.End M'}
    (h : Intertwines ψ f f') : Intertwines ψ (f - 1) (f' - 1) := by
  have := h.sub_natCast 1
  simpa using this

theorem Intertwines.pow {ψ : M →+ M'} {f : AddMonoid.End M} {f' : AddMonoid.End M'}
    (h : Intertwines ψ f f') (n : ℕ) : Intertwines ψ (f ^ n) (f' ^ n) := by
  induction n with
  | zero => intro x; simp [addMonoidEnd_one_apply]
  | succ n ih => simpa [pow_succ] using ih.mul h

theorem IsNilpotent.of_surjective_intertwines {ψ : M →+ M'} {f : AddMonoid.End M}
    {f' : AddMonoid.End M'} (h : Intertwines ψ f f') (hs : Function.Surjective ψ)
    (hnil : IsNilpotent f) : IsNilpotent f' := by
  obtain ⟨n, hn⟩ := hnil
  refine ⟨n, ?_⟩
  ext y
  obtain ⟨x, rfl⟩ := hs y
  rw [← h.pow n x, hn]
  simp

theorem IsNilpotent.of_injective_intertwines {ψ : M →+ M'} {f : AddMonoid.End M}
    {f' : AddMonoid.End M'} (h : Intertwines ψ f f') (hs : Function.Injective ψ)
    (hnil : IsNilpotent f') : IsNilpotent f := by
  obtain ⟨n, hn⟩ := hnil
  refine ⟨n, ?_⟩
  ext x
  refine hs ?_
  rw [h.pow n x, hn]
  simp

end Transfer

/-! ## restriction to a stable subgroup, and descent to a quotient -/

section Restrict

variable {M : Type*} [AddCommGroup M]

/-- Restriction of an additive endomorphism to a stable subgroup. -/
def restrictEnd (f : AddMonoid.End M) (T : AddSubgroup M) (h : ∀ x ∈ T, f x ∈ T) :
    AddMonoid.End T :=
  AddMonoidHom.codRestrict (f.comp T.subtype) T (fun x => h x.1 x.2)

@[simp] theorem restrictEnd_coe (f : AddMonoid.End M) (T : AddSubgroup M)
    (h : ∀ x ∈ T, f x ∈ T) (x : T) : ((restrictEnd f T h x : T) : M) = f (x : M) := rfl

/-- Restriction of a group action to a stable subgroup. -/
def restrictHom {G : Type*} [Group G] (φ : G →* AddMonoid.End M) (T : AddSubgroup M)
    (h : ∀ g : G, ∀ x ∈ T, φ g x ∈ T) : G →* AddMonoid.End T where
  toFun g := restrictEnd (φ g) T (h g)
  map_one' := by
    ext x
    show (φ 1) (x : M) = (x : M)
    rw [map_one, addMonoidEnd_one_apply]
  map_mul' a b := by
    ext x
    show (φ (a * b)) (x : M) = (φ a) ((φ b) (x : M))
    rw [map_mul, addMonoidEnd_mul_apply]

theorem intertwines_restrictHom {G : Type*} [Group G] (φ : G →* AddMonoid.End M)
    (T : AddSubgroup M) (h : ∀ g : G, ∀ x ∈ T, φ g x ∈ T) (g : G) :
    Intertwines T.subtype (restrictHom φ T h g) (φ g) := fun _ => rfl

/-- Descent of a group action to a quotient by a stable subgroup. -/
def quotientHom {G : Type*} [Group G] (φ : G →* AddMonoid.End M) (N : AddSubgroup M)
    (h : ∀ g : G, ∀ x ∈ N, φ g x ∈ N) : G →* AddMonoid.End (M ⧸ N) where
  toFun g := QuotientAddGroup.map N N (φ g) (fun x hx => h g x hx)
  map_one' := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | _ z =>
      show (QuotientAddGroup.mk ((φ 1) z) : M ⧸ N) = QuotientAddGroup.mk z
      rw [map_one, addMonoidEnd_one_apply]
  map_mul' a b := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | _ z =>
      show (QuotientAddGroup.mk ((φ (a * b)) z) : M ⧸ N) =
        (QuotientAddGroup.map N N (φ a) (fun y hy => h a y hy))
          (QuotientAddGroup.mk ((φ b) z))
      rw [map_mul, addMonoidEnd_mul_apply, QuotientAddGroup.map_mk]
      rfl

theorem intertwines_quotientHom {G : Type*} [Group G] (φ : G →* AddMonoid.End M)
    (N : AddSubgroup M) (h : ∀ g : G, ∀ x ∈ N, φ g x ∈ N) (g : G) :
    Intertwines (QuotientAddGroup.mk' N) (φ g) (quotientHom φ N h g) := fun _ => rfl

end Restrict

/-! ## the relative form: one triangularisation step modulo a proper stable subgroup -/

/-- **ONE TRIANGULARISATION STEP MODULO A PROPER STABLE SUBGROUP.** -/
theorem exists_scalar_eigenvector_mod {M : Type*} [AddCommGroup M] [Finite M]
    (φ : G →* AddMonoid.End M) (N : AddSubgroup M) (hNtop : N ≠ ⊤)
    (hNstab : ∀ g : G, ∀ x ∈ N, φ g x ∈ N)
    (hpgp : ∀ x : M, ∃ k : ℕ, (p ^ k) • x = 0)
    (hcomm : ∀ g ∈ commutator G, IsNilpotent (φ g - 1))
    (hquad : ∀ g : G, ∃ a b : ℕ,
      IsNilpotent ((φ g - (a : AddMonoid.End M)) * (φ g - (b : AddMonoid.End M)))) :
    ∃ x : M, x ∉ N ∧ p • x ∈ N ∧ ∀ g : G, ∃ c : ℕ, φ g x - c • x ∈ N := by
  classical
  set π : M →+ M ⧸ N := QuotientAddGroup.mk' N with hπdef
  have hsurj : Function.Surjective π := fun z =>
    QuotientAddGroup.induction_on z (fun u => ⟨u, rfl⟩)
  have hker : ∀ u : M, π u = 0 ↔ u ∈ N := by
    intro u; rw [hπdef]; exact QuotientAddGroup.eq_zero_iff u
  haveI : Finite (M ⧸ N) := Finite.of_surjective π hsurj
  set φQ : G →* AddMonoid.End (M ⧸ N) := quotientHom φ N hNstab with hφQ
  have hint : ∀ g : G, Intertwines π (φ g) (φQ g) := intertwines_quotientHom φ N hNstab
  -- the quotient is nonzero and `p`-power torsion
  obtain ⟨y, hy⟩ : ∃ y : M, y ∉ N := by
    by_contra hcon
    push_neg at hcon
    exact hNtop (by rw [eq_top_iff]; intro z _; exact hcon z)
  have hy0 : π y ≠ 0 := fun hc => hy ((hker y).mp hc)
  have hQtor : ∃ k : ℕ, (p ^ k) • π y = 0 := by
    obtain ⟨k, hk⟩ := hpgp y
    exact ⟨k, by rw [← map_nsmul, hk, map_zero]⟩
  -- the least `k` killing `π y` is positive, and one step down is `p`-torsion and nonzero
  have hk0 : Nat.find hQtor ≠ 0 := by
    intro hc
    have := Nat.find_spec hQtor
    rw [hc, pow_zero, one_smul] at this
    exact hy0 this
  set k := Nat.find hQtor with hkdef
  set t₀ : M ⧸ N := (p ^ (k - 1)) • π y with ht₀def
  have ht₀ne : t₀ ≠ 0 := Nat.find_min hQtor (m := k - 1) (by omega)
  have ht₀p : p • t₀ = 0 := by
    rw [ht₀def, smul_smul, ← pow_succ']
    rw [show p ^ (k - 1 + 1) = p ^ k by congr 1; omega]
    exact Nat.find_spec hQtor
  -- the `p`-torsion subgroup of the quotient
  let Tsub : AddSubgroup (M ⧸ N) :=
    { carrier := {z | p • z = 0}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        show p • (a + b) = 0
        rw [smul_add, ha, hb, add_zero]
      neg_mem' := fun {a} ha => by
        show p • (-a) = 0
        rw [smul_neg, ha, neg_zero] }
  have hTstab : ∀ g : G, ∀ z ∈ Tsub, φQ g z ∈ Tsub := by
    intro g z hz
    show p • (φQ g z) = 0
    rw [← map_nsmul, show p • z = 0 from hz, map_zero]
  set φT : G →* AddMonoid.End Tsub := restrictHom φQ Tsub hTstab with hφT
  have hintT : ∀ g : G, Intertwines Tsub.subtype (φT g) (φQ g) :=
    intertwines_restrictHom φQ Tsub hTstab
  have hsubinj : Function.Injective (Tsub.subtype) := Subtype.val_injective
  -- transport the two nilpotency hypotheses to the `p`-torsion subgroup
  have hcommT : ∀ g ∈ commutator G, IsNilpotent (φT g - 1) := by
    intro g hg
    refine IsNilpotent.of_injective_intertwines ((hintT g).sub_one) hsubinj ?_
    exact IsNilpotent.of_surjective_intertwines ((hint g).sub_one) hsurj (hcomm g hg)
  have hquadT : ∀ g : G, ∃ a b : ℕ,
      IsNilpotent ((φT g - (a : AddMonoid.End Tsub)) * (φT g - (b : AddMonoid.End Tsub))) := by
    intro g
    obtain ⟨a, b, hab⟩ := hquad g
    refine ⟨a, b, ?_⟩
    refine IsNilpotent.of_injective_intertwines
      (((hintT g).sub_natCast a).mul ((hintT g).sub_natCast b)) hsubinj ?_
    exact IsNilpotent.of_surjective_intertwines
      (((hint g).sub_natCast a).mul ((hint g).sub_natCast b)) hsurj hab
  -- apply the absolute form
  obtain ⟨x, hx0, hxs⟩ :=
    exists_common_scalar_eigenvector (p := p) φT
      (t₀ := ⟨t₀, ht₀p⟩) (by simpa [Subtype.ext_iff] using ht₀ne)
      (fun t => Subtype.ext (by show p • (t : M ⧸ N) = 0; exact t.2)) hcommT hquadT
  -- and read it back on `M`
  obtain ⟨u, hu⟩ := hsurj ((x : M ⧸ N))
  refine ⟨u, ?_, ?_, ?_⟩
  · intro hc
    exact hx0 (Subtype.ext (by rw [← hu, (hker u).mpr hc]; rfl))
  · refine (hker _).mp ?_
    rw [map_nsmul, hu]
    exact x.2
  · intro g
    obtain ⟨c, hc⟩ := hxs g
    refine ⟨c, (hker _).mp ?_⟩
    rw [map_sub, map_nsmul, hint g u, hu]
    have hval : (φQ g) (x : M ⧸ N) = c • (x : M ⧸ N) := by
      have h2 : ((φT g) x : M ⧸ N) = (φQ g) (x : M ⧸ N) := hintT g x
      rw [hc] at h2
      refine h2.symm.trans ?_
      simp
    rw [hval, sub_self]


/-- **THE RELATIVE FORM, WITH `N` A SUBMONOID.** The version consumed by a triangularisation
step: this development's flags are stated with `AddSubmonoid`s (the point group of a Hopf
order reaches its consumers through a bare `Monoid` instance), and in a finite group a
submonoid is automatically a subgroup. -/
theorem exists_scalar_eigenvector_mod_submonoid {M : Type*} [AddCommGroup M] [Finite M]
    (φ : G →* AddMonoid.End M) (N : AddSubmonoid M) (hNtop : N ≠ ⊤)
    (hNstab : ∀ g : G, ∀ x ∈ N, φ g x ∈ N)
    (hpgp : ∀ x : M, ∃ k : ℕ, (p ^ k) • x = 0)
    (hcomm : ∀ g ∈ commutator G, IsNilpotent (φ g - 1))
    (hquad : ∀ g : G, ∃ a b : ℕ,
      IsNilpotent ((φ g - (a : AddMonoid.End M)) * (φ g - (b : AddMonoid.End M)))) :
    ∃ x : M, x ∉ N ∧ p • x ∈ N ∧ ∀ g : G, ∃ c : ℕ, φ g x - c • x ∈ N := by
  -- a submonoid of a finite additive group is closed under negation
  have hneg : ∀ {t : M}, t ∈ N → -t ∈ N := by
    intro t ht
    have hpos : 0 < addOrderOf t := addOrderOf_pos t
    have hkill : addOrderOf t • t = 0 := addOrderOf_nsmul_eq_zero t
    have hmem : (addOrderOf t - 1) • t ∈ N := N.nsmul_mem ht _
    have hsum : (addOrderOf t - 1) • t + t = 0 := by
      rw [← succ_nsmul, Nat.sub_add_cancel hpos]
      exact hkill
    rwa [eq_neg_of_add_eq_zero_left hsum] at hmem
  let N' : AddSubgroup M := { N with neg_mem' := hneg }
  have hN'top : N' ≠ ⊤ := by
    intro hc
    exact hNtop (by
      ext x
      constructor
      · intro _; trivial
      · intro _
        have : x ∈ N' := by rw [hc]; trivial
        exact this)
  obtain ⟨x, h1, h2, h3⟩ :=
    exists_scalar_eigenvector_mod (p := p) φ N' hN'top hNstab hpgp hcomm hquad
  exact ⟨x, h1, h2, h3⟩

end CommonEigenvector
