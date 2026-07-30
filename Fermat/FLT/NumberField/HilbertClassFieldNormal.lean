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
* `NumberField.exists_hilbertClassField_normal_over_rat` — **SORRY LEAF.**
  The residue: the class field can be chosen NORMAL OVER `ℚ`. This is the one
  place where `K/ℚ` being Galois is used, and it is the whole mathematical
  content that the existence theorem does not already carry.
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

/-- **THE HILBERT CLASS FIELD OF A GALOIS `K` CAN BE CHOSEN NORMAL OVER `ℚ`**
(SORRY LEAF, cut 2026-07-30 out of
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

**⚠ `hrank` IS LOAD-BEARING — the same statement for an arbitrary degree is
FALSE, and this is exactly the trap that a "generalisation" would fall
into.** Drop `hrank` (and the matching clause in the conclusion) and the
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

**Route.** Neukirch VI (6.9) and the uniqueness half of the class field
correspondence at modulus `1`; Childress ch. 4–5; Lang *ANT* ch. X. The
formal route that avoids uniqueness altogether: take `N'` to be the
compositum of the conjugates `σ N` (normal by construction), note each `σ N`
is again abelian and everywhere-unramified over `K`, and use
`finrank_le_card_classGroup_of_unramified_abelian` of
`UnramifiedClassFieldBound.lean` to force `[N' : K] ≤ h_K = [N : K]`, hence
`N' = N`. That route needs one lemma this project does not yet have — a
compositum of abelian everywhere-unramified extensions is abelian and
everywhere-unramified — and no analysis at all. -/
theorem exists_hilbertClassField_normal_over_rat
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K] [IsGalois ℚ K]
    (N : IntermediateField (K : Type _) (AlgebraicClosure ℚ))
    [FiniteDimensional (K : Type _) N] [IsGalois (K : Type _) N]
    (hab : ∀ a b : N ≃ₐ[(K : Type _)] N, a * b = b * a)
    (hunr : ∀ (Q : Ideal (𝓞 N)) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 (K : Type _)) Q)
    (hrank : Module.finrank (K : Type _) N = Nat.card (ClassGroup (𝓞 (K : Type _)))) :
    ∃ (N' : IntermediateField (K : Type _) (AlgebraicClosure ℚ))
      (_ : FiniteDimensional (K : Type _) N') (_ : IsGalois (K : Type _) N')
      (_ : Normal ℚ (N'.restrictScalars ℚ)),
      (∀ a b : N' ≃ₐ[(K : Type _)] N', a * b = b * a) ∧
      (∀ (Q : Ideal (𝓞 N')) (_ : Q.IsPrime), Q ≠ ⊥ →
        Algebra.IsUnramifiedAt (𝓞 (K : Type _)) Q) ∧
      Module.finrank (K : Type _) N' = Nat.card (ClassGroup (𝓞 (K : Type _))) :=
  sorry

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
