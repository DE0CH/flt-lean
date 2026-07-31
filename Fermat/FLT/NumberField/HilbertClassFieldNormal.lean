/-
NumberField/HilbertClassFieldNormal.lean — own work for the Fermat project
(not vendored from the FLT project).
-/
module

public import Fermat.FLT.NumberField.CyclotomicModelTransport

/-!
# The Hilbert class field of a Galois number field, inside `ℚ̄`, as a normal extension of `ℚ`

`Fermat/FLT/Modularity/Interface.lean`'s
`exists_unramifiedAbelian_normal_over_rat` asks for the maximal
everywhere-unramified abelian extension `M` of `K := ι(CF)` to exist INSIDE
`ℚ̄`, to have degree `h_K` over `K`, and to be NORMAL OVER `ℚ`. Three of those
four demands are already class field theory as it is stated in
`UnramifiedClassFieldExistence.lean` — only in the wrong model, and phrased
through `Gal(M/ℚ)` rather than through `Gal(M/K)`. This file separates the
two:

* `NumberField.exists_hilbertClassField_intermediateField` — PROVEN. The
  class field exists as an `IntermediateField K ℚ̄`. Pure transport of
  `exists_hilbertClassField` along `IsAlgClosure.equiv`, using
  `exists_unramifiedAbelian_of_algebraicClosureEquiv` of the companion file;
  `ℚ̄` is an algebraic closure of `K` as well, since `K/ℚ` is algebraic.
* `NumberField.eq_one_of_mem_inertia_of_unramifiedAt` — PROVEN, and of
  independent use: unramifiedness at every nonzero prime makes every prime's
  INERTIA GROUP trivial, i.e. an automorphism acting trivially modulo `Q` is
  the identity. `Ideal.card_inertia_eq_ramificationIdxIn` plus
  `Ideal.ramificationIdx_eq_one`.
* `NumberField.exists_hilbertClassField_normal_over_rat` — **PROVEN
  2026-07-30**, closing the last leaf of this file. The residue: the class
  field can be chosen NORMAL OVER `ℚ`. This is the one place where `K/ℚ` being
  Galois is used, and it is the whole mathematical content that the existence
  theorem does not already carry. Proved by the compositum route, over three
  groups of new material in this file — the `_sup` theorems (a compositum of
  everywhere-unramified abelian extensions is one again), the `archimedean`
  theorems (re-exporting the `IsUnramifiedAtInfinitePlaces` instance that
  `exists_hilbertClassField` discards, which the degree bound REQUIRES), and
  `exists_conj_unramifiedAbelian` (the `σ`-conjugate of a class field is a
  class field, moved across a `K`-SEMILINEAR isomorphism).
* `NumberField.corestrictFieldRange` / `NumberField.galFieldRangeEquiv` — the
  bookkeeping that lets `Interface.lean` state its conclusions through
  `{σ : M ≃ₐ[ℚ] M // σ fixes ι(CF) pointwise}` instead of through
  `M ≃ₐ[K] M`. The two really are the same group, and the equivalence is the
  identity on underlying functions.

Nothing here imports `Interface.lean`; `Interface.lean` imports this.
-/

@[expose] public section

open NumberField

namespace NumberField

/-- **UNRAMIFIED AT `Q` ⟹ THE INERTIA GROUP AT `Q` IS TRIVIAL** (PROVEN
2026-07-30).

For `N/K` a finite Galois extension of number fields inside `ℚ̄` and `Q` a
nonzero prime of `𝓞 N`, an automorphism `τ ∈ Gal(N/K)` acting trivially on
`𝓞 N ⧸ Q` is the identity, provided `N/K` is unramified at every nonzero
prime. The hypothesis `hτ` is literally membership in
`Q.inertia Gal(N/K)` (`AddSubgroup.mem_inertia`), and the proof is the chain
`#inertia = e = 1`: `Ideal.card_inertia_eq_ramificationIdxIn`,
`Ideal.ramificationIdxIn_eq_ramificationIdx`, and `Ideal.ramificationIdx_eq_one`
(the easy direction of `ramificationIdx_eq_one_iff`, which needs no
`PerfectField` side condition).

This is the RELATIVE analogue of `MinkowskiUnramified.lean`'s
`isUnramifiedAt_of_inertia_le_fixingSubgroup`, which runs the same chain with
base `ℤ` and in the opposite direction. -/
theorem eq_one_of_mem_inertia_of_unramifiedAt
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    (N : IntermediateField (K : Type _) (AlgebraicClosure ℚ))
    [FiniteDimensional (K : Type _) N] [IsGalois (K : Type _) N]
    (hunr : ∀ (Q : Ideal (𝓞 N)) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 (K : Type _)) Q)
    (Q : Ideal (𝓞 N)) [hQp : Q.IsPrime] (hQ0 : Q ≠ ⊥) (τ : N ≃ₐ[(K : Type _)] N)
    (hτ : ∀ x : 𝓞 N, τ • x - x ∈ Q) : τ = 1 := by
  classical
  haveI : FiniteDimensional ℚ (N : Type _) := FiniteDimensional.trans ℚ (K : Type _) (N : Type _)
  haveI : NumberField (N : Type _) := ⟨⟩
  haveI : IsGaloisGroup (N ≃ₐ[(K : Type _)] N) (𝓞 (K : Type _)) (𝓞 N) :=
    IsGaloisGroup.of_isFractionRing (N ≃ₐ[(K : Type _)] N) (𝓞 (K : Type _)) (𝓞 N)
      (K : Type _) (N : Type _)
  set q : Ideal (𝓞 (K : Type _)) := Q.under (𝓞 (K : Type _)) with hq
  haveI : Q.LiesOver q := ⟨rfl⟩
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn
    (G := (N ≃ₐ[(K : Type _)] N)) q Q
  haveI : Algebra.IsUnramifiedAt (𝓞 (K : Type _)) Q := hunr Q hQp hQ0
  have hram : Q.ramificationIdx (𝓞 (K : Type _)) = 1 :=
    Ideal.ramificationIdx_eq_one Q (𝓞 (K : Type _))
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx q Q (N ≃ₐ[(K : Type _)] N), hram] at hcard
  have hbot : Q.inertia (N ≃ₐ[(K : Type _)] N) = ⊥ := Subgroup.eq_bot_of_card_eq _ hcard
  exact (Subgroup.eq_bot_iff_forall _).mp hbot τ (fun x => hτ x)

/-- **THE CONVERSE: TRIVIAL INERTIA AT EVERY NONZERO PRIME ⟹ UNRAMIFIED**
(PROVEN 2026-07-30).

The mirror image of `eq_one_of_mem_inertia_of_unramifiedAt` above, running the
chain `e = #inertia = 1` in the other direction:
`Ideal.card_inertia_eq_ramificationIdxIn` with the inertia group killed by
`hin`, then `Ideal.ramificationIdxIn_eq_ramificationIdx` and the harder
direction `Ideal.ramificationIdx_eq_one_iff.mp`.

This is what makes unramifiedness of a COMPOSITUM accessible: unramifiedness
is a statement about localisations, which no Galois-theoretic manipulation
touches, whereas triviality of inertia is a statement about automorphisms and
survives every conjugation and restriction argument below. -/
theorem isUnramifiedAt_of_inertia_trivial
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    (N : IntermediateField (K : Type _) (AlgebraicClosure ℚ))
    [FiniteDimensional (K : Type _) N] [IsGalois (K : Type _) N]
    (hin : ∀ (Q : Ideal (𝓞 N)), Q.IsPrime → Q ≠ ⊥ →
      ∀ τ : N ≃ₐ[(K : Type _)] N, (∀ x : 𝓞 N, τ • x - x ∈ Q) → τ = 1)
    (Q : Ideal (𝓞 N)) (hQp : Q.IsPrime) (hQ0 : Q ≠ ⊥) :
    Algebra.IsUnramifiedAt (𝓞 (K : Type _)) Q := by
  classical
  haveI := hQp
  haveI : FiniteDimensional ℚ (N : Type _) := FiniteDimensional.trans ℚ (K : Type _) (N : Type _)
  haveI : NumberField (N : Type _) := ⟨⟩
  haveI : IsGaloisGroup (N ≃ₐ[(K : Type _)] N) (𝓞 (K : Type _)) (𝓞 N) :=
    IsGaloisGroup.of_isFractionRing (N ≃ₐ[(K : Type _)] N) (𝓞 (K : Type _)) (𝓞 N)
      (K : Type _) (N : Type _)
  set q : Ideal (𝓞 (K : Type _)) := Q.under (𝓞 (K : Type _)) with hq
  haveI : Q.LiesOver q := ⟨rfl⟩
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn
    (G := (N ≃ₐ[(K : Type _)] N)) q Q
  have hbot : Q.inertia (N ≃ₐ[(K : Type _)] N) = ⊥ :=
    (Subgroup.eq_bot_iff_forall _).mpr fun τ hτ => hin Q hQp hQ0 τ (fun x => hτ x)
  rw [hbot] at hcard
  have h1 : Ideal.ramificationIdxIn q (𝓞 N) = 1 := by
    rw [← hcard]; simp
  have h2 : Q.ramificationIdx (𝓞 (K : Type _)) = 1 := by
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx q Q (N ≃ₐ[(K : Type _)] N)]
    exact h1
  exact Ideal.ramificationIdx_eq_one_iff.mp h2

/-- **THE HILBERT CLASS FIELD OF `K ⊆ ℚ̄` LIVES INSIDE `ℚ̄`** (PROVEN
2026-07-30 over `exists_hilbertClassField` and nothing else).

`exists_hilbertClassField` delivers its field inside `AlgebraicClosure K`;
the consumers in `Interface.lean` need one inside `AlgebraicClosure ℚ`. Since
`K/ℚ` is algebraic, `ℚ̄` IS an algebraic closure of `K`, so `IsAlgClosure.equiv`
gives an isomorphism of the two ambient closures and
`exists_unramifiedAbelian_of_algebraicClosureEquiv` carries the whole package
(finite, Galois, abelian Galois group, unramified at every finite prime, of
degree `h_K`) along it. NO normality over `ℚ` is claimed — that is the leaf
below. -/
theorem exists_hilbertClassField_intermediateField
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K] :
    ∃ (N : IntermediateField (K : Type _) (AlgebraicClosure ℚ))
      (_ : FiniteDimensional (K : Type _) N) (_ : IsGalois (K : Type _) N),
      (∀ a b : N ≃ₐ[(K : Type _)] N, a * b = b * a) ∧
      (∀ (Q : Ideal (𝓞 N)) (_ : Q.IsPrime), Q ≠ ⊥ →
        Algebra.IsUnramifiedAt (𝓞 (K : Type _)) Q) ∧
      Module.finrank (K : Type _) N = Nat.card (ClassGroup (𝓞 (K : Type _))) := by
  obtain ⟨H, hfd, hgal, hab, hunrH, hrank⟩ :=
    NumberField.exists_hilbertClassField (K : Type _)
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : Algebra.IsAlgebraic (K : Type _) (AlgebraicClosure ℚ) :=
    Algebra.IsAlgebraic.tower_top (K := ℚ) (K : Type _)
  haveI : IsAlgClosure (K : Type _) (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  obtain ⟨H'', hfd'', hgal'', hab'', hunr'', hrank''⟩ :=
    NumberField.exists_unramifiedAbelian_of_algebraicClosureEquiv
      (IsAlgClosure.equiv (K : Type _) (AlgebraicClosure (K : Type _)) (AlgebraicClosure ℚ))
      H hab hunrH
  exact ⟨H'', hfd'', hgal'', hab'', hunr'', hrank''.trans hrank⟩

section Compositum

/-! ### A compositum of everywhere-unramified abelian extensions is one again

The three `_sup` theorems below are what the route recorded in the leaf's
docstring needs, and they are all proved the same way: lift an automorphism of
the compositum to `Gal(ℚ̄/K)` with `AlgEquiv.liftNormal`, show the lift fixes
each factor pointwise, and conclude with `IntermediateField.fixingSubgroup_sup`.
Nothing here is specific to the class field. -/

/-- The lift to `Gal(ℚ̄/K)` of an INERTIA element of a bigger field `M` fixes
any everywhere-unramified subfield `L ≤ M` pointwise: the restriction of the
lift to `L` lies in the inertia group of `L` at the prime below, which is
trivial by `eq_one_of_mem_inertia_of_unramifiedAt`. -/
theorem mem_fixingSubgroup_of_unramifiedAt
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    (M : IntermediateField (K : Type _) (AlgebraicClosure ℚ))
    [FiniteDimensional (K : Type _) M] [IsGalois (K : Type _) M]
    (L : IntermediateField (K : Type _) (AlgebraicClosure ℚ))
    [FiniteDimensional (K : Type _) L] [IsGalois (K : Type _) L] (hLM : L ≤ M)
    (hu : ∀ (Q₁ : Ideal (𝓞 L)) (_ : Q₁.IsPrime), Q₁ ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 (K : Type _)) Q₁)
    (Q : Ideal (𝓞 M)) (hQp : Q.IsPrime) (hQ0 : Q ≠ ⊥)
    (τ : M ≃ₐ[(K : Type _)] M) (hτ : ∀ x : 𝓞 M, τ • x - x ∈ Q)
    (ρ : AlgebraicClosure ℚ ≃ₐ[(K : Type _)] AlgebraicClosure ℚ)
    (hρM : ∀ x : (M : Type _), ρ (algebraMap (M : Type _) (AlgebraicClosure ℚ) x)
      = algebraMap (M : Type _) (AlgebraicClosure ℚ) (τ x)) :
    ρ ∈ L.fixingSubgroup := by
  classical
  haveI := hQp
  haveI : FiniteDimensional ℚ (M : Type _) := FiniteDimensional.trans ℚ (K : Type _) (M : Type _)
  haveI : NumberField (M : Type _) := ⟨⟩
  haveI : FiniteDimensional ℚ (L : Type _) := FiniteDimensional.trans ℚ (K : Type _) (L : Type _)
  haveI : NumberField (L : Type _) := ⟨⟩
  -- the tower `K ⊆ L ⊆ M`
  letI : Algebra (L : Type _) (M : Type _) := (IntermediateField.inclusion hLM).toRingHom.toAlgebra
  haveI : IsScalarTower (K : Type _) (L : Type _) (M : Type _) :=
    IsScalarTower.of_algebraMap_eq' (IntermediateField.inclusion hLM).comp_algebraMap.symm
  have hLMcoe : ∀ x : (L : Type _),
      algebraMap (M : Type _) (AlgebraicClosure ℚ) (algebraMap (L : Type _) (M : Type _) x)
        = algebraMap (L : Type _) (AlgebraicClosure ℚ) x := fun x => rfl
  -- `g`, the restriction of `ρ` to `L`
  set g : (L : Type _) ≃ₐ[(K : Type _)] (L : Type _) := ρ.restrictNormal (L : Type _) with hgdef
  have hgc : ∀ x : (L : Type _),
      algebraMap (L : Type _) (AlgebraicClosure ℚ) (g x)
        = ρ (algebraMap (L : Type _) (AlgebraicClosure ℚ) x) :=
    fun x => AlgEquiv.restrictNormal_commutes ρ (L : Type _) x
  -- `g` lies in the inertia group at the prime below `Q`
  haveI : Algebra.IsIntegral (𝓞 (L : Type _)) (𝓞 (M : Type _)) := by
    infer_instance
  set Q₁ : Ideal (𝓞 (L : Type _)) := Q.under (𝓞 (L : Type _)) with hQ₁def
  haveI hQ₁p : Q₁.IsPrime := Ideal.comap_isPrime _ _
  have hQ₁0 : Q₁ ≠ ⊥ := Ideal.under_ne_bot (𝓞 (L : Type _)) hQ0
  have hg1 : g = 1 := by
    refine eq_one_of_mem_inertia_of_unramifiedAt K L hu Q₁ hQ₁0 g ?_
    intro y
    have hkey : algebraMap (𝓞 (L : Type _)) (𝓞 (M : Type _)) (g • y)
        = τ • algebraMap (𝓞 (L : Type _)) (𝓞 (M : Type _)) y := by
      apply NumberField.RingOfIntegers.ext
      apply (algebraMap (M : Type _) (AlgebraicClosure ℚ)).injective
      show algebraMap (M : Type _) (AlgebraicClosure ℚ)
            (algebraMap (L : Type _) (M : Type _) (g ((y : (L : Type _)))))
          = algebraMap (M : Type _) (AlgebraicClosure ℚ)
            (τ (algebraMap (L : Type _) (M : Type _) ((y : (L : Type _)))))
      rw [hLMcoe, hgc, ← hρM, hLMcoe]
    show algebraMap (𝓞 (L : Type _)) (𝓞 (M : Type _)) (g • y - y) ∈ Q
    rw [map_sub, hkey]
    exact hτ _
  simp only [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have h := hgc ⟨x, hx⟩
  rw [hg1] at h
  simpa using h.symm

/-- **A COMPOSITUM OF EVERYWHERE-UNRAMIFIED EXTENSIONS IS EVERYWHERE
UNRAMIFIED** (PROVEN 2026-07-30).

By `isUnramifiedAt_of_inertia_trivial` it suffices to kill the inertia group of
`L₁ ⊔ L₂` at each nonzero prime. An inertia element `τ` lifts to
`ρ ∈ Gal(ℚ̄/K)`, which fixes `L₁` and `L₂` pointwise by
`mem_fixingSubgroup_of_unramifiedAt`, hence fixes `L₁ ⊔ L₂` pointwise
(`IntermediateField.fixingSubgroup_sup`), hence `τ = 1`. -/
theorem isUnramifiedAt_sup
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    (L₁ L₂ : IntermediateField (K : Type _) (AlgebraicClosure ℚ))
    [FiniteDimensional (K : Type _) L₁] [IsGalois (K : Type _) L₁]
    [FiniteDimensional (K : Type _) L₂] [IsGalois (K : Type _) L₂]
    (hu₁ : ∀ (Q : Ideal (𝓞 L₁)) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 (K : Type _)) Q)
    (hu₂ : ∀ (Q : Ideal (𝓞 L₂)) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 (K : Type _)) Q) :
    ∀ (Q : Ideal (𝓞 (L₁ ⊔ L₂ : IntermediateField (K : Type _) (AlgebraicClosure ℚ))))
      (_ : Q.IsPrime), Q ≠ ⊥ → Algebra.IsUnramifiedAt (𝓞 (K : Type _)) Q := by
  classical
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  haveI : Normal ℚ (AlgebraicClosure ℚ) := inferInstance
  haveI : Normal (K : Type _) (AlgebraicClosure ℚ) := inferInstance
  haveI : IsGalois (K : Type _)
      (L₁ ⊔ L₂ : IntermediateField (K : Type _) (AlgebraicClosure ℚ)) := ⟨⟩
  refine isUnramifiedAt_of_inertia_trivial K (L₁ ⊔ L₂) ?_
  intro Q hQp hQ0 τ hτ
  set ρ : AlgebraicClosure ℚ ≃ₐ[(K : Type _)] AlgebraicClosure ℚ :=
    τ.liftNormal (AlgebraicClosure ℚ) with hρdef
  have hρM : ∀ x : ((L₁ ⊔ L₂ : IntermediateField (K : Type _) (AlgebraicClosure ℚ)) : Type _),
      ρ (algebraMap _ (AlgebraicClosure ℚ) x) = algebraMap _ (AlgebraicClosure ℚ) (τ x) :=
    fun x => AlgEquiv.liftNormal_commutes τ (AlgebraicClosure ℚ) x
  have h1 := mem_fixingSubgroup_of_unramifiedAt K (L₁ ⊔ L₂) L₁ le_sup_left hu₁ Q hQp hQ0 τ hτ ρ hρM
  have h2 := mem_fixingSubgroup_of_unramifiedAt K (L₁ ⊔ L₂) L₂ le_sup_right hu₂ Q hQp hQ0 τ hτ ρ hρM
  have h3 : ρ ∈ (L₁ ⊔ L₂).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup]
    exact ⟨h1, h2⟩
  simp only [IntermediateField.mem_fixingSubgroup_iff] at h3
  refine AlgEquiv.ext fun x => ?_
  have h5 : ρ (algebraMap _ (AlgebraicClosure ℚ) x)
      = algebraMap _ (AlgebraicClosure ℚ) x := h3 _ x.2
  have h6 : algebraMap _ (AlgebraicClosure ℚ) (τ x)
      = algebraMap _ (AlgebraicClosure ℚ) x := by rw [← hρM x, h5]
  simpa using (algebraMap _ (AlgebraicClosure ℚ)).injective h6

/-- `ρ` fixes `L` pointwise iff its restriction to `L` is the identity. -/
theorem mem_fixingSubgroup_iff_restrictNormalHom_eq_one
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (L : IntermediateField (K : Type _) (AlgebraicClosure ℚ)) [Normal (K : Type _) L]
    (ρ : AlgebraicClosure ℚ ≃ₐ[(K : Type _)] AlgebraicClosure ℚ) :
    ρ ∈ L.fixingSubgroup ↔ AlgEquiv.restrictNormalHom (L : Type _) ρ = 1 := by
  constructor
  · intro hρ
    simp only [IntermediateField.mem_fixingSubgroup_iff] at hρ
    refine AlgEquiv.ext fun x => ?_
    have h := AlgEquiv.restrictNormalHom_apply L ρ x
    have h2 : ρ (algebraMap (L : Type _) (AlgebraicClosure ℚ) x)
        = algebraMap (L : Type _) (AlgebraicClosure ℚ) x := hρ _ x.2
    show (AlgEquiv.restrictNormalHom (L : Type _) ρ) x = x
    exact (algebraMap (L : Type _) (AlgebraicClosure ℚ)).injective (h.trans h2)
  · intro hρ
    simp only [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have h := AlgEquiv.restrictNormalHom_apply L ρ ⟨x, hx⟩
    rw [hρ] at h
    simpa using h.symm

/-- **A COMPOSITUM OF ABELIAN EXTENSIONS IS ABELIAN** (PROVEN 2026-07-30).
Lift `a` and `b` to `Gal(ℚ̄/K)`; the commutator restricts to `1` on each
factor, hence lies in the fixing subgroup of the compositum. -/
theorem mul_comm_aut_sup
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    (L₁ L₂ : IntermediateField (K : Type _) (AlgebraicClosure ℚ))
    [FiniteDimensional (K : Type _) L₁] [IsGalois (K : Type _) L₁]
    [FiniteDimensional (K : Type _) L₂] [IsGalois (K : Type _) L₂]
    (h₁ : ∀ a b : L₁ ≃ₐ[(K : Type _)] L₁, a * b = b * a)
    (h₂ : ∀ a b : L₂ ≃ₐ[(K : Type _)] L₂, a * b = b * a) :
    ∀ a b : (L₁ ⊔ L₂ : IntermediateField (K : Type _) (AlgebraicClosure ℚ))
        ≃ₐ[(K : Type _)] (L₁ ⊔ L₂ : IntermediateField (K : Type _) (AlgebraicClosure ℚ)),
      a * b = b * a := by
  classical
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  haveI : Normal ℚ (AlgebraicClosure ℚ) := inferInstance
  haveI : Normal (K : Type _) (AlgebraicClosure ℚ) := inferInstance
  haveI : IsGalois (K : Type _)
      (L₁ ⊔ L₂ : IntermediateField (K : Type _) (AlgebraicClosure ℚ)) := ⟨⟩
  intro a b
  obtain ⟨α, hα⟩ := AlgEquiv.restrictNormalHom_surjective
    (F := (K : Type _)) (E := AlgebraicClosure ℚ)
    (K₁ := ((L₁ ⊔ L₂ : IntermediateField (K : Type _) (AlgebraicClosure ℚ)) : Type _)) a
  obtain ⟨β, hβ⟩ := AlgEquiv.restrictNormalHom_surjective
    (F := (K : Type _)) (E := AlgebraicClosure ℚ)
    (K₁ := ((L₁ ⊔ L₂ : IntermediateField (K : Type _) (AlgebraicClosure ℚ)) : Type _)) b
  set γ : AlgebraicClosure ℚ ≃ₐ[(K : Type _)] AlgebraicClosure ℚ := α * β * (β * α)⁻¹ with hγ
  have e₁ : γ ∈ L₁.fixingSubgroup := by
    rw [mem_fixingSubgroup_iff_restrictNormalHom_eq_one]
    have hc := h₁ (AlgEquiv.restrictNormalHom (L₁ : Type _) α)
      (AlgEquiv.restrictNormalHom (L₁ : Type _) β)
    rw [hγ, map_mul, map_mul, map_inv, map_mul, hc, mul_inv_cancel]
  have e₂ : γ ∈ L₂.fixingSubgroup := by
    rw [mem_fixingSubgroup_iff_restrictNormalHom_eq_one]
    have hc := h₂ (AlgEquiv.restrictNormalHom (L₂ : Type _) α)
      (AlgEquiv.restrictNormalHom (L₂ : Type _) β)
    rw [hγ, map_mul, map_mul, map_inv, map_mul, hc, mul_inv_cancel]
  have e₃ : γ ∈ (L₁ ⊔ L₂).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup]; exact ⟨e₁, e₂⟩
  rw [mem_fixingSubgroup_iff_restrictNormalHom_eq_one] at e₃
  rw [hγ, map_mul, map_mul, map_inv, map_mul, hα, hβ] at e₃
  exact mul_inv_eq_one.mp e₃

/-- Archimedean analogue of `mem_fixingSubgroup_of_unramifiedAt`: the lift of a
DECOMPOSITION element at an infinite place fixes pointwise any subfield that is
unramified at the infinite places, because `Stab w = ⊥` there
(`InfinitePlace.isUnramified_iff_stabilizer_eq_bot`). -/
theorem mem_fixingSubgroup_of_isUnramifiedAtInfinitePlaces
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    (M : IntermediateField (K : Type _) (AlgebraicClosure ℚ))
    [FiniteDimensional (K : Type _) M] [IsGalois (K : Type _) M]
    (L : IntermediateField (K : Type _) (AlgebraicClosure ℚ))
    [FiniteDimensional (K : Type _) L] [IsGalois (K : Type _) L]
    [IsUnramifiedAtInfinitePlaces (K : Type _) L] (hLM : L ≤ M)
    (w : NumberField.InfinitePlace (M : Type _)) (τ : M ≃ₐ[(K : Type _)] M) (hτ : τ • w = w)
    (ρ : AlgebraicClosure ℚ ≃ₐ[(K : Type _)] AlgebraicClosure ℚ)
    (hρM : ∀ x : (M : Type _), ρ (algebraMap (M : Type _) (AlgebraicClosure ℚ) x)
      = algebraMap (M : Type _) (AlgebraicClosure ℚ) (τ x)) :
    ρ ∈ L.fixingSubgroup := by
  classical
  haveI : FiniteDimensional ℚ (M : Type _) := FiniteDimensional.trans ℚ (K : Type _) (M : Type _)
  haveI : NumberField (M : Type _) := ⟨⟩
  haveI : FiniteDimensional ℚ (L : Type _) := FiniteDimensional.trans ℚ (K : Type _) (L : Type _)
  haveI : NumberField (L : Type _) := ⟨⟩
  set f : (L : Type _) →+* (M : Type _) := (IntermediateField.inclusion hLM).toRingHom with hfdef
  have hfcoe : ∀ y : (L : Type _),
      algebraMap (M : Type _) (AlgebraicClosure ℚ) (f y)
        = algebraMap (L : Type _) (AlgebraicClosure ℚ) y := fun y => rfl
  rw [mem_fixingSubgroup_iff_restrictNormalHom_eq_one]
  set g : (L : Type _) ≃ₐ[(K : Type _)] (L : Type _) :=
    AlgEquiv.restrictNormalHom (L : Type _) ρ with hgdef
  have hg : ∀ y : (L : Type _), f (g y) = τ (f y) := by
    intro y
    apply (algebraMap (M : Type _) (AlgebraicClosure ℚ)).injective
    rw [hfcoe, ← hρM, ← hfcoe]
    exact AlgEquiv.restrictNormalHom_apply L ρ y
  have hcomp : f.comp (g.symm : (L : Type _) →+* (L : Type _))
      = (τ.symm : (M : Type _) →+* (M : Type _)).comp f := by
    refine RingHom.ext fun y => ?_
    have h := hg (g.symm y)
    simp only [AlgEquiv.apply_symm_apply] at h
    show f (g.symm y) = τ.symm (f y)
    rw [h, AlgEquiv.symm_apply_apply]
  have hstab : g ∈ MulAction.stabilizer ((L : Type _) ≃ₐ[(K : Type _)] (L : Type _))
      (w.comap f) := by
    rw [MulAction.mem_stabilizer_iff, NumberField.InfinitePlace.smul_eq_comap,
      ← NumberField.InfinitePlace.comap_comp, hcomp, NumberField.InfinitePlace.comap_comp,
      ← NumberField.InfinitePlace.smul_eq_comap, hτ]
  have hu : NumberField.InfinitePlace.IsUnramified (K : Type _) (w.comap f) :=
    IsUnramifiedAtInfinitePlaces.isUnramified _
  rw [NumberField.InfinitePlace.isUnramified_iff_stabilizer_eq_bot] at hu
  exact (Subgroup.eq_bot_iff_forall _).mp hu g hstab

end Compositum
section Archimedean
/-- **A COMPOSITUM OF EXTENSIONS UNRAMIFIED AT THE INFINITE PLACES IS
**RENAMED 2026-07-31 (release 29).**  `UnramifiedClassFieldExistence.lean`
declares a theorem of the same name about `IntermediateField K
(AlgebraicClosure K)`; this one is about `IntermediateField K
(AlgebraicClosure ℚ)`, which is what this file works in.  The qualified
names collided, so this one carries a suffix.

UNRAMIFIED AT THE INFINITE PLACES** (PROVEN 2026-07-30).

This one is NOT decoration: `finrank_le_card_classGroup_of_unramified_abelian_of_isUnramifiedAtInfinitePlaces`
— the only degree bound this development has — REQUIRES it, and the leaf's
docstring records a PARI/GP counterexample (`ℚ(√3)`, `h = 1`, narrow `h⁺ = 2`)
showing the bound is FALSE with unramifiedness only at the finite places. So
the compositum argument below cannot be run at finite places alone. -/
theorem isUnramifiedAtInfinitePlaces_sup_algClosRat
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    (L₁ L₂ : IntermediateField (K : Type _) (AlgebraicClosure ℚ))
    [FiniteDimensional (K : Type _) L₁] [IsGalois (K : Type _) L₁]
    [FiniteDimensional (K : Type _) L₂] [IsGalois (K : Type _) L₂]
    [IsUnramifiedAtInfinitePlaces (K : Type _) L₁]
    [IsUnramifiedAtInfinitePlaces (K : Type _) L₂] :
    IsUnramifiedAtInfinitePlaces (K : Type _)
      (L₁ ⊔ L₂ : IntermediateField (K : Type _) (AlgebraicClosure ℚ)) := by
  classical
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  haveI : Normal ℚ (AlgebraicClosure ℚ) := inferInstance
  haveI : Normal (K : Type _) (AlgebraicClosure ℚ) := inferInstance
  haveI : IsGalois (K : Type _)
      (L₁ ⊔ L₂ : IntermediateField (K : Type _) (AlgebraicClosure ℚ)) := ⟨⟩
  haveI : FiniteDimensional ℚ
      ((L₁ ⊔ L₂ : IntermediateField (K : Type _) (AlgebraicClosure ℚ)) : Type _) :=
    FiniteDimensional.trans ℚ (K : Type _) _
  haveI : NumberField ((L₁ ⊔ L₂ : IntermediateField (K : Type _) (AlgebraicClosure ℚ)) : Type _) :=
    ⟨⟩
  refine ⟨fun w => ?_⟩
  rw [NumberField.InfinitePlace.isUnramified_iff_stabilizer_eq_bot, Subgroup.eq_bot_iff_forall]
  intro τ hτ
  have hτw : τ • w = w := hτ
  set ρ : AlgebraicClosure ℚ ≃ₐ[(K : Type _)] AlgebraicClosure ℚ :=
    τ.liftNormal (AlgebraicClosure ℚ) with hρdef
  have hρM : ∀ x : ((L₁ ⊔ L₂ : IntermediateField (K : Type _) (AlgebraicClosure ℚ)) : Type _),
      ρ (algebraMap _ (AlgebraicClosure ℚ) x) = algebraMap _ (AlgebraicClosure ℚ) (τ x) :=
    fun x => AlgEquiv.liftNormal_commutes τ (AlgebraicClosure ℚ) x
  have e₁ := mem_fixingSubgroup_of_isUnramifiedAtInfinitePlaces K (L₁ ⊔ L₂) L₁ le_sup_left w τ
    hτw ρ hρM
  have e₂ := mem_fixingSubgroup_of_isUnramifiedAtInfinitePlaces K (L₁ ⊔ L₂) L₂ le_sup_right w τ
    hτw ρ hρM
  have e₃ : ρ ∈ (L₁ ⊔ L₂).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup]; exact ⟨e₁, e₂⟩
  simp only [IntermediateField.mem_fixingSubgroup_iff] at e₃
  refine AlgEquiv.ext fun x => ?_
  have h5 : ρ (algebraMap _ (AlgebraicClosure ℚ) x)
      = algebraMap _ (AlgebraicClosure ℚ) x := e₃ _ x.2
  have h6 : algebraMap _ (AlgebraicClosure ℚ) (τ x)
      = algebraMap _ (AlgebraicClosure ℚ) x := by rw [← hρM x, h5]
  simpa using (algebraMap _ (AlgebraicClosure ℚ)).injective h6

end Compositum

section Archimedean

/-! ### Keeping the archimedean unramifiedness that `exists_hilbertClassField` discards

`exists_classField_of_subgroup` PRODUCES `IsUnramifiedAtInfinitePlaces K H`;
`exists_classField_finrank_eq_index` consumes it and deliberately does not
re-export it, and `exists_hilbertClassField` inherits that. The compositum
argument needs it, so the three theorems below re-derive the Hilbert class
field keeping it, and carry it into `ℚ̄`. -/


/-- `mult` is invariant under pulling an infinite place back along a ring ISO:
`InfinitePlace.mult_comap_le` in both directions. -/
theorem mult_comap_ringEquiv {k K : Type*} [Field k] [Field K] (f : k ≃+* K)
    (w : NumberField.InfinitePlace K) :
    (w.comap (f : k →+* K)).mult = w.mult := by
  refine le_antisymm (NumberField.InfinitePlace.mult_comap_le _ _) ?_
  have h := NumberField.InfinitePlace.mult_comap_le (f.symm : K →+* k) (w.comap (f : k →+* K))
  rwa [← NumberField.InfinitePlace.comap_comp, show
    ((f : k →+* K).comp (f.symm : K →+* k)) = RingHom.id K from by ext x; simp,
    NumberField.InfinitePlace.comap_id] at h

/-- `IsUnramifiedAtInfinitePlaces` is carried by an isomorphism over the base —
the archimedean companion of `isUnramifiedAt_of_algEquiv`. -/
theorem isUnramifiedAtInfinitePlaces_of_algEquiv {E H H' : Type*} [Field E] [Field H] [Field H']
    [Algebra E H] [Algebra E H'] (eH : H ≃ₐ[E] H') [IsUnramifiedAtInfinitePlaces E H] :
    IsUnramifiedAtInfinitePlaces E H' := by
  refine ⟨fun w => ?_⟩
  have h1 : (w.comap (eH : H →+* H')).mult = w.mult :=
    mult_comap_ringEquiv eH.toRingEquiv w
  have h2 : NumberField.InfinitePlace.IsUnramified E (w.comap (eH : H →+* H')) :=
    IsUnramifiedAtInfinitePlaces.isUnramified _
  have h3 : w.comap (algebraMap E H') = (w.comap (eH : H →+* H')).comap (algebraMap E H) := by
    rw [← NumberField.InfinitePlace.comap_comp]
    congr 1
    ext x
    exact (eH.commutes x).symm
  show (w.comap (algebraMap E H')).mult = w.mult
  rw [h3, h2, h1]

/-- `exists_unramifiedAbelian_of_algebraicClosureEquiv` of
`CyclotomicModelTransport.lean` with the archimedean clause added; the extra
clause is `isUnramifiedAtInfinitePlaces_of_algEquiv` and everything else is
that theorem's proof verbatim. It is restated rather than reused because that
theorem returns its field EXISTENTIALLY, so the archimedean property cannot be
transported afterwards. -/
theorem exists_unramifiedAbelian_archimedean_of_algEquiv {E : Type*} [Field E] [NumberField E]
    {H H' : Type*} [Field H] [Field H'] [Algebra E H] [Algebra E H']
    [NumberField H] [NumberField H']
    [FiniteDimensional E H] [IsGalois E H] [IsUnramifiedAtInfinitePlaces E H]
    (eH : H ≃ₐ[E] H')
    (hab : ∀ a b : H ≃ₐ[E] H, a * b = b * a)
    (hunr : ∀ (Q : Ideal (𝓞 H)) (_ : Q.IsPrime), Q ≠ ⊥ → Algebra.IsUnramifiedAt (𝓞 E) Q) :
    ∃ (_ : FiniteDimensional E H') (_ : IsGalois E H') (_ : IsUnramifiedAtInfinitePlaces E H'),
      (∀ a b : H' ≃ₐ[E] H', a * b = b * a) ∧
      (∀ (Q : Ideal (𝓞 H')) (_ : Q.IsPrime), Q ≠ ⊥ → Algebra.IsUnramifiedAt (𝓞 E) Q) ∧
      Module.finrank E H' = Module.finrank E H := by
  haveI : FiniteDimensional E H' := Module.Finite.equiv eH.toLinearEquiv
  refine ⟨inferInstance, IsGalois.of_algEquiv eH, isUnramifiedAtInfinitePlaces_of_algEquiv eH,
    ?_, ?_, eH.toLinearEquiv.finrank_eq.symm⟩
  · intro a b
    have h1 := hab ((AlgEquiv.autCongr eH).symm a) ((AlgEquiv.autCongr eH).symm b)
    have h2 := congrArg (AlgEquiv.autCongr eH) h1
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h2
  · intro Q hQp hQ0
    haveI := hQp
    let f : (𝓞 H) ≃ₐ[𝓞 E] (𝓞 H') := NumberField.RingOfIntegers.mapAlgEquiv eH
    haveI hprime : (Ideal.comap (f : 𝓞 H →+* 𝓞 H') Q).IsPrime := Ideal.comap_isPrime _ _
    have hne : Ideal.comap (f : 𝓞 H →+* 𝓞 H') Q ≠ ⊥ := by
      intro hbot
      refine hQ0 (le_bot_iff.mp fun y hy => ?_)
      rw [Ideal.mem_bot]
      have h1 : f.symm y ∈ Ideal.comap (f : 𝓞 H →+* 𝓞 H') Q := by
        rw [Ideal.mem_comap]
        show f (f.symm y) ∈ Q
        rwa [AlgEquiv.apply_symm_apply]
      rw [hbot, Ideal.mem_bot] at h1
      have h2 : y = f (f.symm y) := (AlgEquiv.apply_symm_apply f y).symm
      rw [h2, h1, map_zero]
    exact NumberField.isUnramifiedAt_of_algEquiv f _ Q rfl (hunr _ hprime hne)

/-- **THE HILBERT CLASS FIELD, KEEPING ITS ARCHIMEDEAN UNRAMIFIEDNESS**
(PROVEN 2026-07-30). This is `exists_hilbertClassField` with the
`IsUnramifiedAtInfinitePlaces` instance that `exists_classField_of_subgroup`
already produces, re-exported instead of dropped; the degree is pinned by the
same `le_antisymm` that `exists_classField_finrank_eq_index` performs. -/
theorem exists_hilbertClassField_isUnramifiedAtInfinitePlaces (E : Type*) [Field E]
    [NumberField E] :
    ∃ (H : IntermediateField E (AlgebraicClosure E))
      (_ : FiniteDimensional E H) (_ : NumberField H) (_ : IsGalois E H)
      (_ : IsUnramifiedAtInfinitePlaces E H),
      (∀ a b : H ≃ₐ[E] H, a * b = b * a) ∧
      (∀ (Q : Ideal (𝓞 H)) (_ : Q.IsPrime), Q ≠ ⊥ →
        Algebra.IsUnramifiedAt (𝓞 E) Q) ∧
      Module.finrank E H = Nat.card (ClassGroup (𝓞 E)) := by
  obtain ⟨H, hfd, hnf, hgal, hinf, hab, hunr, hnorm⟩ :=
    NumberField.exists_classField_of_subgroup E ⊥
  haveI := hfd; haveI := hnf; haveI := hgal; haveI := hinf
  refine ⟨H, hfd, hnf, hgal, hinf, hab, hunr, ?_⟩
  rw [← Subgroup.index_bot (G := ClassGroup (𝓞 E))]
  refine le_antisymm ?_ ?_
  · have h := NumberField.finrank_le_index_relNormClassSubgroup E H hab hunr
    rwa [hnorm] at h
  · have h := NumberField.index_relNormClassSubgroup_le_finrank E H hab hunr
    rwa [hnorm] at h

/-- **THE HILBERT CLASS FIELD OF `K ⊆ ℚ̄` LIVES INSIDE `ℚ̄`, ARCHIMEDEAN CLAUSE
INCLUDED** (PROVEN 2026-07-30). `exists_hilbertClassField_intermediateField`
with `IsUnramifiedAtInfinitePlaces` carried along `IsAlgClosure.equiv`. -/
theorem exists_hilbertClassField_intermediateField_archimedean
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K] :
    ∃ (N : IntermediateField (K : Type _) (AlgebraicClosure ℚ))
      (_ : FiniteDimensional (K : Type _) N) (_ : IsGalois (K : Type _) N)
      (_ : IsUnramifiedAtInfinitePlaces (K : Type _) N),
      (∀ a b : N ≃ₐ[(K : Type _)] N, a * b = b * a) ∧
      (∀ (Q : Ideal (𝓞 N)) (_ : Q.IsPrime), Q ≠ ⊥ →
        Algebra.IsUnramifiedAt (𝓞 (K : Type _)) Q) ∧
      Module.finrank (K : Type _) N = Nat.card (ClassGroup (𝓞 (K : Type _))) := by
  obtain ⟨H, hfd, hnf, hgal, hinf, hab, hunrH, hrank⟩ :=
    exists_hilbertClassField_isUnramifiedAtInfinitePlaces (K : Type _)
  haveI := hfd; haveI := hnf; haveI := hgal; haveI := hinf
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : Algebra.IsAlgebraic (K : Type _) (AlgebraicClosure ℚ) :=
    Algebra.IsAlgebraic.tower_top (K := ℚ) (K : Type _)
  haveI : IsAlgClosure (K : Type _) (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  set ee : AlgebraicClosure (K : Type _) ≃ₐ[(K : Type _)] AlgebraicClosure ℚ :=
    IsAlgClosure.equiv (K : Type _) (AlgebraicClosure (K : Type _)) (AlgebraicClosure ℚ) with hee
  set H'' : IntermediateField (K : Type _) (AlgebraicClosure ℚ) := H.map ee.toAlgHom with hH''
  have eH : (H : Type _) ≃ₐ[(K : Type _)] (H'' : Type _) :=
    IntermediateField.intermediateFieldMap ee H
  haveI : FiniteDimensional (K : Type _) (H'' : Type _) := Module.Finite.equiv eH.toLinearEquiv
  haveI : FiniteDimensional ℚ (H'' : Type _) :=
    FiniteDimensional.trans ℚ (K : Type _) (H'' : Type _)
  haveI : NumberField (H'' : Type _) := ⟨⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := exists_unramifiedAbelian_archimedean_of_algEquiv eH hab hunrH
  exact ⟨H'', h1, h2, h3, h4, h5, h6.trans hrank⟩

end Archimedean

section Conjugation

/-! ### The `σ`-conjugate of a class field is a class field

`σ ∈ Gal(ℚ̄/ℚ)` maps `K` to `K` but does NOT fix it pointwise, so `σ : N → σN`
is only `K`-SEMILINEAR, over the base automorphism `σ|_K`. That is why nothing
here can go through `isUnramifiedAt_of_algEquiv` (which needs an isomorphism
over a FIXED base) and why unramifiedness is instead moved across as TRIVIALITY
OF INERTIA, which is a statement about automorphisms and conjugates cleanly. -/

/-- An element of `Gal(M/K)` does not move an element of `M` that already lies
in `K`. -/
theorem coe_aut_eq_of_mem_base
    {K : IntermediateField ℚ (AlgebraicClosure ℚ)}
    {M : IntermediateField (K : Type _) (AlgebraicClosure ℚ)}
    (t : M ≃ₐ[(K : Type _)] M) (z : (M : Type _))
    (hz : ((z : AlgebraicClosure ℚ) ∈ K)) :
    ((t z : (M : Type _)) : AlgebraicClosure ℚ) = (z : AlgebraicClosure ℚ) := by
  have hz' : z = algebraMap (K : Type _) (M : Type _) ⟨(z : AlgebraicClosure ℚ), hz⟩ := by
    apply Subtype.ext; rfl
  rw [hz', AlgEquiv.commutes]

/-- **THE CONJUGATE OF AN EVERYWHERE-UNRAMIFIED ABELIAN EXTENSION IS ONE
AGAIN** (PROVEN 2026-07-30).

For `σ ∈ Gal(ℚ̄/ℚ)` and `K/ℚ` Galois, `σ` maps `K` onto `K`, so `σ` restricts
to a field isomorphism `φ : N ≃ σN` that is `K`-semilinear over
`σ|_K ∈ Gal(K/ℚ)`. Conjugation by `φ` is then a group isomorphism
`Gal(σN/K) ≃ Gal(N/K)` — `φ⁻¹τφ` IS `K`-linear, because for `k ∈ K` one has
`σk ∈ K`, which `τ` fixes — and every clause is moved across it:

* NORMAL: for `ρ ∈ Gal(ℚ̄/K)`, `σ⁻¹ρσ ∈ Gal(ℚ̄/K)` preserves `N`, so `ρ`
  preserves `σN` (`IntermediateField.normal_iff_forall_map_le'`);
* ABELIAN: `Gal(σN/K)` embeds in the abelian `Gal(N/K)`;
* FINITE PRIMES: via `isUnramifiedAt_of_inertia_trivial` and
  `eq_one_of_mem_inertia_of_unramifiedAt` — `φ` carries `𝓞 N` onto `𝓞 σN` and
  matches the two inertia groups;
* INFINITE PLACES: `mult` is invariant under pulling back along a ring iso
  (`mult_comap_ringEquiv`), applied to `φ` upstairs and to `σ|_K` downstairs.

**⚠ `IsGalois ℚ K` IS LOAD-BEARING HERE**, and this is the only place the whole
file uses it: without `σK = K` the field `σN` is an extension of `σK ≠ K` and
is not even an object of the right type. -/
theorem exists_conj_unramifiedAbelian
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K] [IsGalois ℚ K]
    (N N₂ : IntermediateField (K : Type _) (AlgebraicClosure ℚ))
    [FiniteDimensional (K : Type _) N] [IsGalois (K : Type _) N]
    [IsUnramifiedAtInfinitePlaces (K : Type _) N]
    (hab : ∀ a b : N ≃ₐ[(K : Type _)] N, a * b = b * a)
    (hunr : ∀ (Q : Ideal (𝓞 N)) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 (K : Type _)) Q)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hN₂ : (N₂ : Set (AlgebraicClosure ℚ)) = σ '' (N : Set (AlgebraicClosure ℚ))) :
    ∃ (_ : FiniteDimensional (K : Type _) N₂) (_ : IsGalois (K : Type _) N₂)
      (_ : IsUnramifiedAtInfinitePlaces (K : Type _) N₂),
      (∀ a b : N₂ ≃ₐ[(K : Type _)] N₂, a * b = b * a) ∧
      (∀ (Q : Ideal (𝓞 N₂)) (_ : Q.IsPrime), Q ≠ ⊥ →
        Algebra.IsUnramifiedAt (𝓞 (K : Type _)) Q) := by
  classical
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  haveI : Normal ℚ (AlgebraicClosure ℚ) := inferInstance
  haveI : Normal (K : Type _) (AlgebraicClosure ℚ) := inferInstance
  haveI hnK : Normal ℚ (K : Type _) := IsGalois.to_normal
  -- `K` is stable under `σ`, in both directions.
  have hKσ : K.map (σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ) = K :=
    (IntermediateField.normal_iff_forall_map_eq' (L := AlgebraicClosure ℚ)).mp hnK σ
  have hKfwd : ∀ x : AlgebraicClosure ℚ, x ∈ K → σ x ∈ K := by
    intro x hx; rw [← hKσ]; exact ⟨x, hx, rfl⟩
  have hKbwd : ∀ x : AlgebraicClosure ℚ, x ∈ K → σ.symm x ∈ K := by
    intro x hx
    have : x ∈ K.map (σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ) := by rw [hKσ]; exact hx
    obtain ⟨z, hz, rfl⟩ := this
    simpa using hz
  -- `σ` restricted to `N`, as a `ℚ`-algebra isomorphism onto `N₂`.
  have hmem : ∀ x : AlgebraicClosure ℚ, x ∈ N → σ x ∈ N₂ := by
    intro x hx
    have : σ x ∈ (N₂ : Set (AlgebraicClosure ℚ)) := by rw [hN₂]; exact ⟨x, hx, rfl⟩
    exact this
  have hmem' : ∀ y : AlgebraicClosure ℚ, y ∈ N₂ → σ.symm y ∈ N := by
    intro y hy
    have hy' : y ∈ (N₂ : Set (AlgebraicClosure ℚ)) := hy
    rw [hN₂] at hy'
    obtain ⟨x, hx, rfl⟩ := hy'
    simpa using hx
  set φ : (N : Type _) ≃ₐ[ℚ] (N₂ : Type _) :=
    { toFun := fun x => ⟨σ (x : AlgebraicClosure ℚ), hmem _ x.2⟩
      invFun := fun y => ⟨σ.symm (y : AlgebraicClosure ℚ), hmem' _ y.2⟩
      left_inv := fun x => by apply Subtype.ext; simp
      right_inv := fun y => by apply Subtype.ext; simp
      map_mul' := fun x y => by apply Subtype.ext; simp
      map_add' := fun x y => by apply Subtype.ext; simp
      commutes' := fun r => by apply Subtype.ext; simp } with hφdef
  have hφ : ∀ x : (N : Type _), ((φ x : (N₂ : Type _)) : AlgebraicClosure ℚ)
      = σ ((x : (N : Type _)) : AlgebraicClosure ℚ) := fun _ => rfl
  have hφs : ∀ y : (N₂ : Type _), ((φ.symm y : (N : Type _)) : AlgebraicClosure ℚ)
      = σ.symm ((y : (N₂ : Type _)) : AlgebraicClosure ℚ) := fun _ => rfl
  -- basic finiteness
  haveI : FiniteDimensional ℚ (N : Type _) := FiniteDimensional.trans ℚ (K : Type _) (N : Type _)
  haveI : NumberField (N : Type _) := ⟨⟩
  haveI : FiniteDimensional ℚ (N₂ : Type _) := Module.Finite.equiv φ.toLinearEquiv
  haveI : NumberField (N₂ : Type _) := ⟨⟩
  haveI hfd₂ : FiniteDimensional (K : Type _) (N₂ : Type _) :=
    Module.Finite.of_restrictScalars_finite ℚ (K : Type _) (N₂ : Type _)
  -- `N₂` is normal over `K`: conjugate the `K`-automorphisms of `ℚ̄` by `σ`.
  haveI hnor₂ : Normal (K : Type _) (N₂ : Type _) := by
    refine (IntermediateField.normal_iff_forall_map_le' (L := AlgebraicClosure ℚ)).mpr ?_
    intro ρ
    have hρK : ∀ x : AlgebraicClosure ℚ, x ∈ K → ρ x = x := by
      intro x hx
      exact ρ.commutes (⟨x, hx⟩ : (K : Type _))
    set ρ' : AlgebraicClosure ℚ ≃ₐ[(K : Type _)] AlgebraicClosure ℚ :=
      { σ.trans ((ρ.restrictScalars ℚ).trans σ.symm) with
        commutes' := fun k => by
          show σ.symm (ρ (σ ((k : AlgebraicClosure ℚ)))) = ((k : AlgebraicClosure ℚ))
          rw [hρK _ (hKfwd _ k.2)]
          simp } with hρ'def
    have hρ'app : ∀ x, ρ' x = σ.symm (ρ (σ x)) := fun _ => rfl
    have hNρ' : (N : IntermediateField (K : Type _) (AlgebraicClosure ℚ)).map
        (ρ' : AlgebraicClosure ℚ →ₐ[(K : Type _)] AlgebraicClosure ℚ) ≤ N :=
      (IntermediateField.normal_iff_forall_map_le' (L := AlgebraicClosure ℚ)).mp
        (IsGalois.to_normal) ρ'
    rintro y ⟨x, hx, rfl⟩
    have hx' : x ∈ (N₂ : Set (AlgebraicClosure ℚ)) := hx
    rw [hN₂] at hx'
    obtain ⟨n, hn, rfl⟩ := hx'
    have h1 : ρ' n ∈ N := hNρ' ⟨n, hn, rfl⟩
    have h2 : ρ (σ n) = σ (ρ' n) := by rw [hρ'app]; simp
    show ρ (σ n) ∈ N₂
    rw [h2]
    exact hmem _ h1
  haveI hgal₂ : IsGalois (K : Type _) (N₂ : Type _) := ⟨⟩
  -- conjugation of automorphism groups
  have hcomm : ∀ (t : N₂ ≃ₐ[(K : Type _)] N₂) (k : (K : Type _)),
      (φ.trans ((t.restrictScalars ℚ).trans φ.symm))
          (algebraMap (K : Type _) (N : Type _) k)
        = algebraMap (K : Type _) (N : Type _) k := by
    intro t k
    apply Subtype.ext
    show ((φ.symm (t (φ (algebraMap (K : Type _) (N : Type _) k))) : (N : Type _))
        : AlgebraicClosure ℚ) = _
    rw [hφs]
    have hin : ((φ (algebraMap (K : Type _) (N : Type _) k) : (N₂ : Type _))
        : AlgebraicClosure ℚ) ∈ K := by
      rw [hφ]
      exact hKfwd _ k.2
    rw [coe_aut_eq_of_mem_base t _ hin, hφ]
    show σ.symm (σ ((k : AlgebraicClosure ℚ))) = _
    simp
  set Ψ : (N₂ ≃ₐ[(K : Type _)] N₂) → (N ≃ₐ[(K : Type _)] N) := fun t =>
    { φ.trans ((t.restrictScalars ℚ).trans φ.symm) with commutes' := hcomm t } with hΨdef
  have hΨ : ∀ (t : N₂ ≃ₐ[(K : Type _)] N₂) (y : (N : Type _)), φ (Ψ t y) = t (φ y) := by
    intro t y
    show φ (φ.symm (t (φ y))) = t (φ y)
    simp
  refine ⟨hfd₂, hgal₂, ?_, ?_, ?_⟩
  · -- unramified at the infinite places
    refine ⟨fun w => ?_⟩
    set w' : NumberField.InfinitePlace (N : Type _) :=
      w.comap (φ : (N : Type _) →+* (N₂ : Type _)) with hw'
    have h1 : w'.mult = w.mult := mult_comap_ringEquiv φ.toRingEquiv w
    have h2 : NumberField.InfinitePlace.IsUnramified (K : Type _) w' :=
      IsUnramifiedAtInfinitePlaces.isUnramified _
    set τK : (K : Type _) ≃ₐ[ℚ] (K : Type _) := σ.restrictNormal (K : Type _) with hτK
    have hτKc : ∀ k : (K : Type _), ((τK k : (K : Type _)) : AlgebraicClosure ℚ)
        = σ ((k : (K : Type _)) : AlgebraicClosure ℚ) :=
      fun k => AlgEquiv.restrictNormal_commutes σ (K : Type _) k
    have hcompeq : (φ : (N : Type _) →+* (N₂ : Type _)).comp
          (algebraMap (K : Type _) (N : Type _))
        = (algebraMap (K : Type _) (N₂ : Type _)).comp
          ((τK.toRingEquiv : (K : Type _) ≃+* (K : Type _)) : (K : Type _) →+* (K : Type _)) := by
      ext k
      show σ ((k : AlgebraicClosure ℚ)) = ((τK k : (K : Type _)) : AlgebraicClosure ℚ)
      rw [hτKc]
    have h3 : w'.comap (algebraMap (K : Type _) (N : Type _))
        = (w.comap (algebraMap (K : Type _) (N₂ : Type _))).comap
          ((τK.toRingEquiv : (K : Type _) ≃+* (K : Type _)) : (K : Type _) →+* (K : Type _)) := by
      rw [hw', ← NumberField.InfinitePlace.comap_comp, ← NumberField.InfinitePlace.comap_comp,
        hcompeq]
    have h5 : ((w.comap (algebraMap (K : Type _) (N₂ : Type _))).comap
          ((τK.toRingEquiv : (K : Type _) ≃+* (K : Type _)) : (K : Type _) →+* (K : Type _))).mult
        = (w.comap (algebraMap (K : Type _) (N₂ : Type _))).mult :=
      mult_comap_ringEquiv τK.toRingEquiv _
    have h6 : (w'.comap (algebraMap (K : Type _) (N : Type _))).mult = w'.mult := h2
    rw [h3] at h6
    show (w.comap (algebraMap (K : Type _) (N₂ : Type _))).mult = w.mult
    rw [← h5, h6]
    exact h1
  · -- abelian
    intro a b
    refine AlgEquiv.ext fun z => ?_
    obtain ⟨y, rfl⟩ := φ.surjective z
    have hcomm' := hab (Ψ a) (Ψ b)
    have e1 : (a * b) (φ y) = φ (Ψ a (Ψ b y)) := by
      rw [AlgEquiv.mul_apply, ← hΨ, ← hΨ]
    have e2 : (b * a) (φ y) = φ (Ψ b (Ψ a y)) := by
      rw [AlgEquiv.mul_apply, ← hΨ, ← hΨ]
    rw [e1, e2]
    congr 1
    have := congrArg (fun (f : N ≃ₐ[(K : Type _)] N) => f y) hcomm'
    simpa [AlgEquiv.mul_apply] using this
  · -- unramified at the finite primes
    refine isUnramifiedAt_of_inertia_trivial K N₂ ?_
    intro Q hQp hQ0 t ht
    haveI := hQp
    set f : (𝓞 (N : Type _)) ≃+* (𝓞 (N₂ : Type _)) :=
      NumberField.RingOfIntegers.mapRingEquiv φ.toRingEquiv with hf
    set Q₀ : Ideal (𝓞 (N : Type _)) := Ideal.comap (f : 𝓞 (N : Type _) →+* 𝓞 (N₂ : Type _)) Q
      with hQ₀
    haveI hQ₀p : Q₀.IsPrime := Ideal.comap_isPrime _ _
    have hQ₀0 : Q₀ ≠ ⊥ := by
      intro hbot
      refine hQ0 (le_bot_iff.mp fun y hy => ?_)
      rw [Ideal.mem_bot]
      have h1 : f.symm y ∈ Q₀ := by
        rw [hQ₀, Ideal.mem_comap]
        show f (f.symm y) ∈ Q
        rwa [RingEquiv.apply_symm_apply]
      rw [hbot, Ideal.mem_bot] at h1
      have h2 : y = f (f.symm y) := (RingEquiv.apply_symm_apply f y).symm
      rw [h2, h1, map_zero]
    have hg1 : Ψ t = 1 := by
      refine eq_one_of_mem_inertia_of_unramifiedAt K N hunr Q₀ hQ₀0 (Ψ t) ?_
      intro y
      rw [hQ₀, Ideal.mem_comap, map_sub]
      have hkey : f (Ψ t • y) = t • f y := by
        apply NumberField.RingOfIntegers.ext
        show ((φ (((Ψ t • y : 𝓞 (N : Type _))) : (N : Type _)) : (N₂ : Type _)))
          = ((t • f y : 𝓞 (N₂ : Type _)) : (N₂ : Type _))
        show φ (Ψ t ((y : 𝓞 (N : Type _)) : (N : Type _)))
          = t (φ ((y : 𝓞 (N : Type _)) : (N : Type _)))
        exact hΨ t _
      show f (Ψ t • y) - f y ∈ Q
      rw [hkey]
      exact ht (f y)
    refine AlgEquiv.ext fun z => ?_
    obtain ⟨y, rfl⟩ := φ.surjective z
    have := hΨ t y
    rw [hg1] at this
    simpa using this.symm

end Conjugation

set_option maxHeartbeats 1000000 in
/-- **THE HILBERT CLASS FIELD OF A GALOIS `K` CAN BE CHOSEN NORMAL OVER `ℚ`**
(PROVEN 2026-07-30 along the formal route this docstring already prescribed;
cut out of
`Fermat/FLT/Modularity/Interface.lean`'s `exists_unramifiedAbelian_normal_over_rat`,
which is now PROVEN over this together with
`exists_hilbertClassField_intermediateField` above. This is the ENTIRE residue
of that node: everything else it asked for is class field theory as already
stated in `UnramifiedClassFieldExistence.lean`, plus bookkeeping.)

**Content.** `N` is a finite abelian everywhere-unramified extension of `K`
of degree exactly `h_K` — a Hilbert class field of `K`. The claim is that
some such field is stable under every `ℚ`-automorphism of `ℚ̄`, equivalently
normal over `ℚ`. Classically this is CANONICITY: `H` is *the* maximal
everywhere-unramified abelian extension of `K`, and for `σ ∈ Gal(ℚ̄/ℚ)` the
field `σH` is the maximal everywhere-unramified abelian extension of
`σK = K` (using `K/ℚ` Galois), hence `σH = H`. In the class-group language
`H` corresponds to the subgroup `⊥ ≤ Cl(𝓞 K)`, which is stable under the
`Gal(K/ℚ)`-action for trivial reasons.

**⚠ THE *CONCLUSION'S* RANK CLAUSE IS LOAD-BEARING — the same statement for an
arbitrary degree is FALSE, and this is exactly the trap that a
"generalisation" would fall into.** Drop it (and the `hrank` hypothesis) and the
statement asks, for every `d ∣ h_K`, for an everywhere-unramified abelian
extension of degree `d` that is normal over `ℚ`. Under the class field
correspondence such a field is a subgroup of `Cl(𝓞 K)` of index `d` that is
STABLE under `Gal(K/ℚ)`, and stable subgroups of a prescribed index need not
exist: if `Cl(𝓞 K) ⊗ 𝔽_ℓ` is an IRREDUCIBLE `𝔽_ℓ[Gal(K/ℚ)]`-module of
dimension `2` then there are `ℓ + 1` subgroups of index `ℓ` and not one of
them is stable, so no everywhere-unramified abelian extension of degree `ℓ`
is normal over `ℚ`. `Gal(K/ℚ)` cyclic of order `8` acting on `𝔽_3²` through
a generator of `𝔽_9ˣ ⊆ GL₂(𝔽_3)` is such an action. With `hrank` the
subgroup is `⊥`, which is stable under everything — and that is precisely
why the Hilbert class field, and only it, is canonical.

**⚠ `IsGalois ℚ K` IS ALSO LOAD-BEARING.** For a number field `K` with `K/ℚ`
not Galois the Hilbert class field of `K` is in general NOT normal over `ℚ`
(`σK ≠ K`, so `σH` is a class field of a different field), and no `N'` as
demanded exists.

**Not vacuous.** `h(ℚ(μ_23)) = 3`, so at `K = ℚ(μ_23)` the conclusion demands
a genuine cubic everywhere-unramified abelian extension normal over `ℚ`, and
`N' = K` does not discharge it. The leaf is trivial exactly when `h_K = 1`.

**The check that would refute it**: a Galois number field `K ⊆ ℚ̄` for which
every everywhere-unramified abelian extension of degree `h_K` fails to be
normal over `ℚ` — which would contradict canonicity of the Hilbert class
field.

**Route taken** — the uniqueness-free one this docstring already prescribed,
and no analysis at all. For each `σ ∈ Gal(ℚ̄/ℚ)`, `σN₀` is again abelian and
everywhere-unramified over `K` (`exists_conj_unramifiedAbelian`); the
compositum `N₀ ⊔ σN₀` inherits all three properties (`isUnramifiedAt_sup`,
`mul_comm_aut_sup`, `isUnramifiedAtInfinitePlaces_sup`); the degree bound
forces `[N₀ ⊔ σN₀ : K] ≤ h_K = [N₀ : K]`, so
`IntermediateField.eq_of_le_of_finrank_eq` gives `N₀ ⊔ σN₀ = N₀`, i.e.
`σN₀ ≤ N₀`; and `IntermediateField.normal_iff_forall_map_le'` turns that into
normality over `ℚ`. Literature for the uniqueness route instead: Neukirch VI
(6.9); Childress ch. 4–5; Lang *ANT* ch. X.

**⚠ THE ARCHIMEDEAN CONDITION IS WHAT MAKES THE ROUTE RUN, and it is why the
given `N` cannot be used.** The only degree bound in this development,
`finrank_le_card_classGroup_of_unramified_abelian_of_isUnramifiedAtInfinitePlaces`,
REQUIRES unramifiedness at the infinite places as well, and its leaf's
docstring records a PARI/GP counterexample (`ℚ(√3)`: `h = 1` but narrow
`h⁺ = 2`) showing the bound is FALSE without it. The hypothesis `N` here
carries no archimedean clause, so `N` may be a narrow class field and the
compositum argument cannot start from it. The proof therefore DISCARDS `N` and
builds its own `N₀` with `exists_hilbertClassField_intermediateField_archimedean`.

**Consequence, and it is a real finding: `N`, `hab`, `hunr` and `hrank` are
not needed.** The conclusion is a pure existence statement, so the input field
is inert; the hypotheses are kept only because the sole consumer
(`Interface.lean`'s `exists_unramifiedAbelian_normal_over_rat`) passes them
positionally and the statement is not worth an interface split. The binders are
underscore-prefixed to say so. Anyone tightening this signature must fix that
call site in the SAME commit. -/
theorem exists_hilbertClassField_normal_over_rat
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K] [IsGalois ℚ K]
    (N : IntermediateField (K : Type _) (AlgebraicClosure ℚ))
    [FiniteDimensional (K : Type _) N] [IsGalois (K : Type _) N]
    (_hab : ∀ a b : N ≃ₐ[(K : Type _)] N, a * b = b * a)
    (_hunr : ∀ (Q : Ideal (𝓞 N)) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 (K : Type _)) Q)
    (_hrank : Module.finrank (K : Type _) N = Nat.card (ClassGroup (𝓞 (K : Type _)))) :
    ∃ (N' : IntermediateField (K : Type _) (AlgebraicClosure ℚ))
      (_ : FiniteDimensional (K : Type _) N') (_ : IsGalois (K : Type _) N')
      (_ : Normal ℚ (N'.restrictScalars ℚ)),
      (∀ a b : N' ≃ₐ[(K : Type _)] N', a * b = b * a) ∧
      (∀ (Q : Ideal (𝓞 N')) (_ : Q.IsPrime), Q ≠ ⊥ →
        Algebra.IsUnramifiedAt (𝓞 (K : Type _)) Q) ∧
      Module.finrank (K : Type _) N' = Nat.card (ClassGroup (𝓞 (K : Type _))) := by
  classical
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  haveI : Normal ℚ (AlgebraicClosure ℚ) := inferInstance
  obtain ⟨N₀, hfd₀, hgal₀, harch₀, hab₀, hunr₀, hrank₀⟩ :=
    exists_hilbertClassField_intermediateField_archimedean K
  refine ⟨N₀, hfd₀, hgal₀, ?_, hab₀, hunr₀, hrank₀⟩
  have key : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      (N₀.restrictScalars ℚ).map (σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ)
        ≤ N₀.restrictScalars ℚ := ?_
  · exact (IntermediateField.normal_iff_forall_map_le' (L := AlgebraicClosure ℚ)).mpr key
  intro σ
  -- `K` is stable under `σ`, so `σ N₀` is again an intermediate field of `ℚ̄/K`.
  haveI hnK : Normal ℚ (K : Type _) := IsGalois.to_normal
  have hKσ : K.map (σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ) = K :=
    (IntermediateField.normal_iff_forall_map_eq' (L := AlgebraicClosure ℚ)).mp hnK σ
  have hKleN : K ≤ (N₀.restrictScalars ℚ) := fun x hx => N₀.algebraMap_mem ⟨x, hx⟩
  have hle : K ≤ (N₀.restrictScalars ℚ).map (σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ) := by
    intro x hx
    have hx' : x ∈ K.map (σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ) := by
      rw [hKσ]; exact hx
    obtain ⟨z, hz, rfl⟩ := hx'
    exact ⟨z, hKleN hz, rfl⟩
  obtain ⟨N₂, hcar⟩ : ∃ N₂ : IntermediateField (K : Type _) (AlgebraicClosure ℚ),
      (N₂ : Set (AlgebraicClosure ℚ)) = σ '' (N₀ : Set (AlgebraicClosure ℚ)) :=
    ⟨IntermediateField.extendScalars hle, by ext y; simp⟩
  obtain ⟨hfd₂, hgal₂, harch₂, hab₂, hunr₂⟩ :=
    exists_conj_unramifiedAbelian K N₀ N₂ hab₀ hunr₀ σ hcar
  haveI := hfd₂
  haveI := hgal₂
  haveI := harch₂
  haveI := harch₀
  haveI : IsGalois (K : Type _) (N₀ ⊔ N₂ : IntermediateField (K : Type _) (AlgebraicClosure ℚ)) :=
    ⟨⟩
  haveI : IsUnramifiedAtInfinitePlaces (K : Type _)
      (N₀ ⊔ N₂ : IntermediateField (K : Type _) (AlgebraicClosure ℚ)) :=
    isUnramifiedAtInfinitePlaces_sup_algClosRat K N₀ N₂
  haveI : FiniteDimensional ℚ
      ((N₀ ⊔ N₂ : IntermediateField (K : Type _) (AlgebraicClosure ℚ)) : Type _) :=
    FiniteDimensional.trans ℚ (K : Type _)
      ((N₀ ⊔ N₂ : IntermediateField (K : Type _) (AlgebraicClosure ℚ)) : Type _)
  haveI : NumberField ((N₀ ⊔ N₂ : IntermediateField (K : Type _) (AlgebraicClosure ℚ)) : Type _) :=
    ⟨⟩
  -- the compositum is still abelian and everywhere unramified, so `h_K` bounds its degree
  have hbound :=
    NumberField.finrank_le_card_classGroup_of_unramified_abelian_of_isUnramifiedAtInfinitePlaces
      (K : Type _) ((N₀ ⊔ N₂ : IntermediateField (K : Type _) (AlgebraicClosure ℚ)) : Type _)
      (mul_comm_aut_sup K N₀ N₂ hab₀ hab₂) (isUnramifiedAt_sup K N₀ N₂ hunr₀ hunr₂)
  have hmono : Module.finrank (K : Type _) N₀
      ≤ Module.finrank (K : Type _)
        (N₀ ⊔ N₂ : IntermediateField (K : Type _) (AlgebraicClosure ℚ)) :=
    IntermediateField.finrank_le_of_le_right le_sup_left
  have heq : (N₀ : IntermediateField (K : Type _) (AlgebraicClosure ℚ)) = N₀ ⊔ N₂ :=
    IntermediateField.eq_of_le_of_finrank_eq le_sup_left
      (le_antisymm hmono (by rw [hrank₀]; exact hbound))
  have h2le : N₂ ≤ N₀ := le_sup_right.trans heq.ge
  intro y hy
  obtain ⟨z, hz, rfl⟩ := hy
  exact h2le (hcar.ge ⟨z, hz, rfl⟩)

section Corestriction

variable {CF : Type} [Field CF] [NumberField CF] (ι : CF →ₐ[ℚ] AlgebraicClosure ℚ)

/-- `ι` corestricted to an intermediate field containing its range. -/
noncomputable def corestrictFieldRange (M : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hle : ι.fieldRange ≤ M) : CF →ₐ[ℚ] M :=
  ι.codRestrict M.toSubalgebra (fun z => hle ⟨z, rfl⟩)

/-- **THE ELEMENTS OF `Gal(M/ℚ)` FIXING `ι(CF)` POINTWISE *ARE* `Gal(M/ι(CF))`**
(PROVEN 2026-07-30). Both directions are the identity on underlying
functions: a `ℚ`-automorphism fixing every `ι z` is `ι(CF)`-linear because
every element of `ι.fieldRange` is some `ι z`, and conversely
`AlgEquiv.restrictScalars` forgets the larger base. This is what lets
`Interface.lean` phrase its conclusions through the subtype — which keeps
`Algebra CF ↥M` and `Algebra (𝓞 CF) (𝓞 M)` out of the statement entirely —
while the proof works with the honest relative Galois group. -/
noncomputable def galFieldRangeEquiv (M : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hle : ι.fieldRange ≤ M) :
    {σ : M ≃ₐ[ℚ] M // ∀ z : CF,
        σ (corestrictFieldRange ι M hle z) = corestrictFieldRange ι M hle z} ≃
      ((IntermediateField.extendScalars hle) ≃ₐ[ι.fieldRange]
        (IntermediateField.extendScalars hle)) where
  toFun σ := { σ.1 with
    commutes' := by
      rintro ⟨r, hr⟩
      obtain ⟨z, rfl⟩ := hr
      exact σ.2 z }
  invFun τ := ⟨τ.restrictScalars ℚ, fun z => τ.commutes ⟨ι z, ⟨z, rfl⟩⟩⟩
  left_inv σ := by ext x; rfl
  right_inv τ := by ext x; rfl

end Corestriction

end NumberField
