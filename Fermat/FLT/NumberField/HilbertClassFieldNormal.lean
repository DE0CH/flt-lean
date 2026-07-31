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
  2026-07-31**, over the three leaves below. The residue: the class field can be
  chosen NORMAL OVER `ℚ`. This is the one place where `K/ℚ` being Galois is
  used, and it is the whole mathematical content that the existence theorem does
  not already carry.
* `NumberField.isUnramifiedAtInfinitePlaces_of_algEquiv`,
  `NumberField.exists_unramifiedAbelianInf_of_algebraicClosureEquiv`,
  `NumberField.exists_hilbertClassField_intermediateField_isUnramifiedAtInfinitePlaces`
  — PROVEN 2026-07-31. The class field inside `ℚ̄` carrying the INFINITE-PLACE
  clause as well, which `exists_unramifiedAbelian_of_algebraicClosureEquiv`
  drops and which the upper bound of `UnramifiedClassFieldBound.lean` cannot do
  without.
* `NumberField.restrictNormal_sup_eq_one`, `NumberField.sup_commutes`,
  `NumberField.restrictNormalHom_eq_one_of_stabilizer`,
  `NumberField.sup_isUnramifiedAtInfinitePlaces` — PROVEN 2026-07-31. Two of the
  three clauses of `NumberField.sup_unramifiedAbelian`, the "next piece of
  plumbing" named in `exists_hilbertClassField_artinIso`'s docstring: the
  compositum of two everywhere-unramified abelian extensions of `K` is one
  again. All three clauses run off ONE lemma, `restrictNormal_sup_eq_one`.
* `NumberField.sup_isUnramifiedAt`, `NumberField.conj_unramifiedAbelian` —
  **SORRY LEAVES**, what is left of that node (2026-07-31). The first is the
  third clause of the compositum lemma, at the FINITE primes — the same
  argument as the archimedean one with the inertia group in place of the
  decomposition group; its docstring lists the plumbing. The second says a
  `ℚ`-conjugate of an everywhere-unramified abelian extension of `K` is one
  again. Neither needs class field theory or analysis.
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

/-- **UNRAMIFIEDNESS AT THE INFINITE PLACES CROSSES A `K`-ALGEBRA
ISOMORPHISM** (PROVEN 2026-07-31).

The archimedean companion of `isUnramifiedAt_of_algEquiv` in
`CyclotomicModelTransport.lean`, and the one clause that
`exists_unramifiedAbelian_of_algebraicClosureEquiv` does not carry. All three of
`InfinitePlace.comap_id`, `comap_comp` and the definition of `IsUnramified` are
`rfl`, so the whole content is `IsUnramified.comap_algHom` applied to `e.symm`:
the place `w` of `H'` restricts along `e` to a place of `H`, which is unramified
by hypothesis, and restricting THAT along `e.symm` returns `w` itself. -/
theorem isUnramifiedAtInfinitePlaces_of_algEquiv {E H H' : Type*} [Field E] [Field H] [Field H']
    [Algebra E H] [Algebra E H'] (e : H ≃ₐ[E] H')
    [IsUnramifiedAtInfinitePlaces E H] : IsUnramifiedAtInfinitePlaces E H' := by
  refine ⟨fun w => ?_⟩
  have h : NumberField.InfinitePlace.IsUnramified E (w.comap (e : H →+* H')) :=
    IsUnramifiedAtInfinitePlaces.isUnramified _
  have h2 := h.comap_algHom (e.symm : H' →ₐ[E] H)
  have hcomp : (e : H →+* H').comp ((e.symm : H' →ₐ[E] H) : H' →+* H) = RingHom.id H' := by
    ext x; simp
  rwa [← NumberField.InfinitePlace.comap_comp, hcomp,
    NumberField.InfinitePlace.comap_id] at h2

/-- **THE PACKAGE, WITH THE ARCHIMEDEAN CLAUSE, MOVES ALONG AN ISOMORPHISM OF
AMBIENT ALGEBRAIC CLOSURES** (PROVEN 2026-07-31).

`exists_unramifiedAbelian_of_algebraicClosureEquiv` of
`CyclotomicModelTransport.lean` with `IsUnramifiedAtInfinitePlaces` added, over
`isUnramifiedAtInfinitePlaces_of_algEquiv` above. The other five clauses are
proven exactly as there and the proof is repeated rather than invoked, because
that theorem returns an EXISTENTIALLY quantified `H''` and the sixth clause has
to be established for the SAME field.

**⚠ KEEP `ee` A HYPOTHESIS.** Building it from `IsAlgClosure.equiv` at the point
of use — inside a `set` or a `let` — makes every subsequent `isDefEq` try to
unfold `IsAlgClosed.lift`, and the declaration times out at 200000 heartbeats.
That was observed here on 2026-07-31 and is the same trap the companion file's
docstring records. -/
theorem exists_unramifiedAbelianInf_of_algebraicClosureEquiv {E : Type*} [Field E] [NumberField E]
    {Ω : Type*} [Field Ω] [Algebra E Ω]
    (ee : AlgebraicClosure E ≃ₐ[E] Ω)
    (H : IntermediateField E (AlgebraicClosure E)) [FiniteDimensional E H] [IsGalois E H]
    [IsUnramifiedAtInfinitePlaces E H]
    (hab : ∀ a b : H ≃ₐ[E] H, a * b = b * a)
    (hunrH : ∀ (Q : Ideal (𝓞 H)) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 E) Q) :
    ∃ (H'' : IntermediateField E Ω) (_ : FiniteDimensional E H'') (_ : IsGalois E H'')
      (_ : IsUnramifiedAtInfinitePlaces E H''),
      (∀ a b : H'' ≃ₐ[E] H'', a * b = b * a) ∧
      (∀ (Q : Ideal (𝓞 H'')) (_ : Q.IsPrime), Q ≠ ⊥ →
        Algebra.IsUnramifiedAt (𝓞 E) Q) ∧
      Module.finrank E H'' = Module.finrank E H := by
  obtain ⟨H'', ⟨eH⟩⟩ : ∃ H'' : IntermediateField E Ω, Nonempty (H ≃ₐ[E] H'') :=
    ⟨H.map ee.toAlgHom, ⟨IntermediateField.intermediateFieldMap ee H⟩⟩
  haveI : FiniteDimensional E H'' := Module.Finite.equiv eH.toLinearEquiv
  refine ⟨H'', inferInstance, IsGalois.of_algEquiv eH,
    isUnramifiedAtInfinitePlaces_of_algEquiv eH, ?_, ?_, eH.toLinearEquiv.finrank_eq.symm⟩
  · intro a b
    have h1 := hab ((AlgEquiv.autCongr eH).symm a) ((AlgEquiv.autCongr eH).symm b)
    have h2 := congrArg (AlgEquiv.autCongr eH) h1
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h2
  · intro Q hQp hQ0
    haveI := hQp
    let f : (𝓞 H) ≃ₐ[𝓞 E] (𝓞 H'') := NumberField.RingOfIntegers.mapAlgEquiv eH
    haveI hprime : (Ideal.comap (f : 𝓞 H →+* 𝓞 H'') Q).IsPrime := Ideal.comap_isPrime _ _
    have hne : Ideal.comap (f : 𝓞 H →+* 𝓞 H'') Q ≠ ⊥ := by
      intro hbot
      refine hQ0 (le_bot_iff.mp fun y hy => ?_)
      rw [Ideal.mem_bot]
      have h1 : f.symm y ∈ Ideal.comap (f : 𝓞 H →+* 𝓞 H'') Q := by
        rw [Ideal.mem_comap]
        show f (f.symm y) ∈ Q
        rwa [AlgEquiv.apply_symm_apply]
      rw [hbot, Ideal.mem_bot] at h1
      have h2 : y = f (f.symm y) := (AlgEquiv.apply_symm_apply f y).symm
      rw [h2, h1, map_zero]
    exact NumberField.isUnramifiedAt_of_algEquiv f _ Q rfl (hunrH _ hprime hne)

/-- **THE HILBERT CLASS FIELD OF `K ⊆ ℚ̄` LIVES INSIDE `ℚ̄`, AND IS UNRAMIFIED
AT THE INFINITE PLACES TOO** (PROVEN 2026-07-31; cut the same day out of
`exists_hilbertClassField_normal_over_rat` below).

`exists_hilbertClassField_intermediateField` above is this statement WITHOUT the
`IsUnramifiedAtInfinitePlaces` clause, and that clause is the only thing missing:
`exists_classField_of_subgroup K ⊥` already produces it on the
`AlgebraicClosure K` side (it is what makes the companion file's upper bound
applicable, see `exists_classField_finrank_eq_index`'s docstring), and
`exists_unramifiedAbelian_of_algebraicClosureEquiv` simply DROPS it while
carrying the other four properties across `IsAlgClosure.equiv`.

**⚠ WHY THE CLAUSE CANNOT BE DROPPED HERE, even though the consumer does not ask
for it.** The proof of `exists_hilbertClassField_normal_over_rat` needs
`finrank_le_card_classGroup_of_unramified_abelian_of_isUnramifiedAtInfinitePlaces`
— maximality of the class field — and that bound is FALSE without unramifiedness
at the infinite places (`ℚ(√3)`: `h = 1` but the narrow class number is `2`, so
there is a quadratic extension unramified at every FINITE prime). A field of
degree `h_K` unramified only at the finite primes need not be the Hilbert class
field, hence need not be canonical, hence need not be normal over `ℚ`. That is
also why the hypotheses on `N` in the theorem below are not used: the witness
must be a genuine Hilbert class field, and `N` is not known to be one.

**Route.** Redo `exists_hilbertClassField_intermediateField`'s two steps with the
extra clause: take `exists_classField_of_subgroup K ⊥`, whose output carries
`IsUnramifiedAtInfinitePlaces K H` and `relNormClassSubgroup K H = ⊥`, pin the
degree with the two inequalities exactly as `exists_classField_finrank_eq_index`
does, and then transport along `IsAlgClosure.equiv` — which needs one new lemma,
`IsUnramifiedAtInfinitePlaces` transported along a `K`-algebra isomorphism
`H ≃ₐ[K] H''`. That last is `NumberField.InfinitePlace.comap` bookkeeping:
`InfinitePlace H'' → InfinitePlace H` along the equivalence commutes with
`comap` to `InfinitePlace K` and preserves `mult`, so `IsUnramified` (defined as
`mult (w.comap (algebraMap K H)) = mult w`) crosses verbatim. -/
theorem exists_hilbertClassField_intermediateField_isUnramifiedAtInfinitePlaces
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K] :
    ∃ (N : IntermediateField (K : Type _) (AlgebraicClosure ℚ))
      (_ : FiniteDimensional (K : Type _) N) (_ : IsGalois (K : Type _) N)
      (_ : IsUnramifiedAtInfinitePlaces (K : Type _) N),
      (∀ a b : N ≃ₐ[(K : Type _)] N, a * b = b * a) ∧
      (∀ (Q : Ideal (𝓞 N)) (_ : Q.IsPrime), Q ≠ ⊥ →
        Algebra.IsUnramifiedAt (𝓞 (K : Type _)) Q) ∧
      Module.finrank (K : Type _) N = Nat.card (ClassGroup (𝓞 (K : Type _))) := by
  classical
  obtain ⟨H, hfd, hnf, hgal, hinf, hab, hunrH, hnorm⟩ :=
    NumberField.exists_classField_of_subgroup (K : Type _) ⊥
  haveI := hfd; haveI := hnf; haveI := hgal; haveI := hinf
  have hrank : Module.finrank (K : Type _) H = Nat.card (ClassGroup (𝓞 (K : Type _))) := by
    refine le_antisymm ?_ ?_
    · have h := NumberField.finrank_le_index_relNormClassSubgroup (K : Type _) H hab hunrH
      rwa [hnorm, Subgroup.index_bot] at h
    · have h := NumberField.index_relNormClassSubgroup_le_finrank (K : Type _) H hab hunrH
      rwa [hnorm, Subgroup.index_bot] at h
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : Algebra.IsAlgebraic (K : Type _) (AlgebraicClosure ℚ) :=
    Algebra.IsAlgebraic.tower_top (K := ℚ) (K : Type _)
  haveI : IsAlgClosure (K : Type _) (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  obtain ⟨H'', hfd'', hgal'', hinf'', hab'', hunr'', hrank''⟩ :=
    exists_unramifiedAbelianInf_of_algebraicClosureEquiv
      (IsAlgClosure.equiv (K : Type _) (AlgebraicClosure (K : Type _)) (AlgebraicClosure ℚ))
      H hab hunrH
  exact ⟨H'', hfd'', hgal'', hinf'', hab'', hunr'', hrank''.trans hrank⟩

/-- **A `ℚ`-CONJUGATE OF AN EVERYWHERE-UNRAMIFIED ABELIAN EXTENSION OF `K` IS
ONE AGAIN** (SORRY LEAF, cut 2026-07-31 out of
`exists_hilbertClassField_normal_over_rat` below).

`σ : ℚ̄ ≃ₐ[ℚ] ℚ̄` maps `K` onto `K` because `K/ℚ` is Galois, so it carries an
intermediate field `N` of `ℚ̄/K` to another one, `N'`. All five properties cross.

**⚠ THE ISOMORPHISM `N ≃ N'` IS ONLY `ℚ`-LINEAR, NOT `K`-LINEAR** — it is
`τ`-semilinear for `τ := σ|_K ∈ Gal(K/ℚ)` — so this is NOT an instance of
`exists_unramifiedAbelian_of_algebraicClosureEquiv`, which needs a `K`-algebra
equivalence. That is the entire difficulty of this leaf and the reason it is
stated separately.

**Route.** `e : N ≃ₐ[ℚ] N'` is `IntermediateField.intermediateFieldMap σ`
restricted; it satisfies `e (k • x) = τ k • e x`. Then:

* *degree*: `[N' : K] = [N : K]` because `[N' : ℚ] = [N : ℚ]` (a `ℚ`-linear
  equivalence) and `[K : ℚ]` is the same on both sides — `Module.finrank_mul_finrank`.
* *Galois, abelian*: `AlgEquiv.autCongr e` is a group isomorphism
  `(N ≃ₐ[ℚ] N) ≃* (N' ≃ₐ[ℚ] N')` carrying the subgroup fixing `K` pointwise
  onto the subgroup fixing `K` pointwise (because `e` maps `K` ONTO `K`), and
  `galFieldRangeEquiv` below is the dictionary between that subgroup and
  `≃ₐ[K]`.
* *unramified at the finite primes*: `𝓞 N ≃+* 𝓞 N'` induced by `e`, which is
  `𝓞 K`-semilinear along `τ`. Since `τ` restricts to a ring automorphism of
  `𝓞 K`, `Algebra.FormallyUnramified (𝓞 K) (Localization.AtPrime q)` transports:
  the Kähler differentials are literally the same module, only the `𝓞 K`-action
  is precomposed with an automorphism. `isUnramifiedAt_of_algEquiv` of
  `CyclotomicModelTransport.lean` is the `K`-linear special case and wants
  generalising to this semilinear one.
* *unramified at the infinite places*: `InfinitePlace.comap` along `e` is a
  bijection `InfinitePlace N' ≃ InfinitePlace N` commuting with restriction to
  `K` up to the bijection `InfinitePlace K ≃ InfinitePlace K` induced by `τ`,
  and `mult` is preserved. -/
theorem conj_unramifiedAbelian
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K] [IsGalois ℚ K]
    (N : IntermediateField (K : Type _) (AlgebraicClosure ℚ))
    [FiniteDimensional (K : Type _) N] [IsGalois (K : Type _) N]
    [IsUnramifiedAtInfinitePlaces (K : Type _) N]
    (hab : ∀ a b : N ≃ₐ[(K : Type _)] N, a * b = b * a)
    (hunr : ∀ (Q : Ideal (𝓞 N)) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 (K : Type _)) Q)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (N' : IntermediateField (K : Type _) (AlgebraicClosure ℚ))
    (hN' : N'.restrictScalars ℚ =
      (N.restrictScalars ℚ).map (σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ)) :
    ∃ (_ : FiniteDimensional (K : Type _) N') (_ : IsGalois (K : Type _) N')
      (_ : IsUnramifiedAtInfinitePlaces (K : Type _) N'),
      (∀ a b : N' ≃ₐ[(K : Type _)] N', a * b = b * a) ∧
      (∀ (Q : Ideal (𝓞 N')) (_ : Q.IsPrime), Q ≠ ⊥ →
        Algebra.IsUnramifiedAt (𝓞 (K : Type _)) Q) ∧
      Module.finrank (K : Type _) N' = Module.finrank (K : Type _) N :=
  sorry

/-- **AN AUTOMORPHISM FIXING `N₁` AND `N₂` POINTWISE FIXES `N₁ ⊔ N₂`
POINTWISE** (PROVEN 2026-07-31).

Equivalently, the restriction homomorphism
`Gal(E/F) → Gal(N₁/F) × Gal(N₂/F)` has the same kernel as
`Gal(E/F) → Gal(N₁ ⊔ N₂/F)`; since restriction to the compositum is surjective
onto `Gal(N₁N₂/F)` when `E/F` is normal, that is exactly the injection
`Gal(N₁N₂/F) ↪ Gal(N₁/F) × Gal(N₂/F)`.

**THIS ONE LEMMA CARRIES ALL THREE CLAUSES of `sup_unramifiedAbelian` below** —
commutativity, unramifiedness at the finite primes, unramifiedness at the
infinite places — because each is the statement that some subgroup of
`Gal(N₁N₂/K)` is trivial, and in each case the subgroup's image in the two
factors is trivial by hypothesis.

The proof is the Galois connection and nothing else: `σ` fixing `N₁` pointwise
says `σ ∈ N₁.fixingSubgroup`, so `N₁ ≤ fixedField (closure {σ})`, and likewise
for `N₂`; `sup_le` then puts `N₁ ⊔ N₂` inside that fixed field. -/
theorem restrictNormal_sup_eq_one {F E : Type*} [Field F] [Field E] [Algebra F E]
    (N₁ N₂ : IntermediateField F E) [Normal F N₁] [Normal F N₂]
    (σ : E ≃ₐ[F] E) (h₁ : σ.restrictNormal N₁ = 1) (h₂ : σ.restrictNormal N₂ = 1) :
    σ.restrictNormal ↥(N₁ ⊔ N₂) = 1 := by
  rw [AlgEquiv.restrictNormal_eq_one_iff] at h₁ h₂ ⊢
  intro x hx
  have hsub : (N₁ ⊔ N₂ : IntermediateField F E) ≤
      IntermediateField.fixedField (Subgroup.closure {σ}) := by
    refine sup_le ?_ ?_ <;> rw [IntermediateField.le_iff_le] <;>
      refine (Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr ?_)
    · exact (IntermediateField.mem_fixingSubgroup_iff _ _).mpr h₁
    · exact (IntermediateField.mem_fixingSubgroup_iff _ _).mpr h₂
  exact (IntermediateField.mem_fixedField_iff _ _).mp (hsub hx) σ
    (Subgroup.subset_closure (Set.mem_singleton σ))

/-- `ℚ̄` is normal over every intermediate field of `ℚ̄/ℚ` — it is an algebraic
closure of it. Packaged as a theorem rather than left to instance search, which
does not chain `IsAlgClosure → IsGalois → Normal` on its own. -/
theorem normal_algebraicClosure_rat (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    [NumberField K] : Normal (K : Type _) (AlgebraicClosure ℚ) := by
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : Algebra.IsAlgebraic (K : Type _) (AlgebraicClosure ℚ) :=
    Algebra.IsAlgebraic.tower_top (K := ℚ) (K : Type _)
  haveI : IsAlgClosure (K : Type _) (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  exact (IsAlgClosure.isGalois (K : Type _) (AlgebraicClosure ℚ)).to_normal

/-- **THE COMPOSITUM IS ABELIAN** (PROVEN 2026-07-31), the first clause of
`sup_unramifiedAbelian` below.

Every automorphism of `N₁ ⊔ N₂` over `K` lifts to `ℚ̄`
(`AlgEquiv.restrictNormalHom_surjective`), the commutator of two lifts restricts
to a commutator in each of `Gal(N₁/K)` and `Gal(N₂/K)` — trivial by hypothesis —
and `restrictNormal_sup_eq_one` above turns that into triviality on the
compositum. -/
theorem sup_commutes
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    (N₁ N₂ : IntermediateField (K : Type _) (AlgebraicClosure ℚ))
    [IsGalois (K : Type _) N₁] [IsGalois (K : Type _) N₂]
    (hab₁ : ∀ a b : N₁ ≃ₐ[(K : Type _)] N₁, a * b = b * a)
    (hab₂ : ∀ a b : N₂ ≃ₐ[(K : Type _)] N₂, a * b = b * a) :
    ∀ a b : (↥(N₁ ⊔ N₂) ≃ₐ[(K : Type _)] ↥(N₁ ⊔ N₂)), a * b = b * a := by
  haveI := normal_algebraicClosure_rat K
  intro a b
  obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective
    (F := (K : Type _)) (K₁ := ↥(N₁ ⊔ N₂)) (E := AlgebraicClosure ℚ) a
  obtain ⟨ρ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective
    (F := (K : Type _)) (K₁ := ↥(N₁ ⊔ N₂)) (E := AlgebraicClosure ℚ) b
  have hc : AlgEquiv.restrictNormalHom (↥(N₁ ⊔ N₂)) (σ * ρ * σ⁻¹ * ρ⁻¹) = 1 := by
    refine restrictNormal_sup_eq_one N₁ N₂ _ ?_ ?_
    · have h := hab₁ (AlgEquiv.restrictNormalHom (↥N₁) σ) (AlgEquiv.restrictNormalHom (↥N₁) ρ)
      show AlgEquiv.restrictNormalHom (↥N₁) (σ * ρ * σ⁻¹ * ρ⁻¹) = 1
      simp only [map_mul, map_inv, h]
      group
    · have h := hab₂ (AlgEquiv.restrictNormalHom (↥N₂) σ) (AlgEquiv.restrictNormalHom (↥N₂) ρ)
      show AlgEquiv.restrictNormalHom (↥N₂) (σ * ρ * σ⁻¹ * ρ⁻¹) = 1
      simp only [map_mul, map_inv, h]
      group
  simp only [map_mul, map_inv] at hc
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hc
  exact hc

/-- **AN AUTOMORPHISM OF `ℚ̄` STABILISING AN INFINITE PLACE OF `M` IS TRIVIAL ON
EVERY UNRAMIFIED-AT-INFINITY SUBEXTENSION `N ≤ M`** (PROVEN 2026-07-31).

The archimedean half of the "one injection" argument. The place `w` of `M`
restricts along the inclusion `N ↪ M` to a place `w₁` of `N`, the restriction of
`σ` to `N` stabilises `w₁` because `σ|_M` stabilises `w` and restriction commutes
with the inclusion (`AlgEquiv.restrictNormal_commutes`), and
`IsUnramified.stabilizer_eq_bot` then kills it. -/
theorem restrictNormalHom_eq_one_of_stabilizer
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    (M N : IntermediateField (K : Type _) (AlgebraicClosure ℚ))
    [IsGalois (K : Type _) M] [IsGalois (K : Type _) N]
    [IsUnramifiedAtInfinitePlaces (K : Type _) N]
    (hle : N ≤ M) (w : NumberField.InfinitePlace ↥M)
    (σ : AlgebraicClosure ℚ ≃ₐ[(K : Type _)] AlgebraicClosure ℚ)
    (hσ : (AlgEquiv.restrictNormalHom (↥M) σ) • w = w) :
    AlgEquiv.restrictNormalHom (↥N) σ = 1 := by
  haveI := normal_algebraicClosure_rat K
  set ι : (↥N) →ₐ[(K : Type _)] (↥M) := IntermediateField.inclusion hle with hι
  have hcomm : ∀ x : ↥N,
      (AlgEquiv.restrictNormalHom (↥M) σ) (ι x) = ι (AlgEquiv.restrictNormalHom (↥N) σ x) := by
    intro x
    have h1 : algebraMap (↥M) (AlgebraicClosure ℚ)
        ((AlgEquiv.restrictNormalHom (↥M) σ) (ι x)) =
        σ (algebraMap (↥M) (AlgebraicClosure ℚ) (ι x)) :=
      AlgEquiv.restrictNormal_commutes σ (↥M) (ι x)
    have h2 : algebraMap (↥N) (AlgebraicClosure ℚ)
        ((AlgEquiv.restrictNormalHom (↥N) σ) x) =
        σ (algebraMap (↥N) (AlgebraicClosure ℚ) x) :=
      AlgEquiv.restrictNormal_commutes σ (↥N) x
    have hι2 : ∀ y : ↥N, algebraMap (↥M) (AlgebraicClosure ℚ) (ι y)
        = algebraMap (↥N) (AlgebraicClosure ℚ) y := fun _ => rfl
    apply (algebraMap (↥M) (AlgebraicClosure ℚ)).injective
    rw [h1, hι2, hι2]
    exact h2.symm
  have hfun : ((AlgEquiv.restrictNormalHom (↥M) σ).symm : ↥M →+* ↥M).comp (ι : ↥N →+* ↥M)
      = (ι : ↥N →+* ↥M).comp ((AlgEquiv.restrictNormalHom (↥N) σ).symm : ↥N →+* ↥N) := by
    refine RingHom.ext fun y => ?_
    have hy := hcomm ((AlgEquiv.restrictNormalHom (↥N) σ).symm y)
    rw [AlgEquiv.apply_symm_apply] at hy
    show (AlgEquiv.restrictNormalHom (↥M) σ).symm (ι y)
      = ι ((AlgEquiv.restrictNormalHom (↥N) σ).symm y)
    rw [← hy, AlgEquiv.symm_apply_apply]
  have hstab : (AlgEquiv.restrictNormalHom (↥N) σ) •
      (w.comap (ι : ↥N →+* ↥M)) = w.comap (ι : ↥N →+* ↥M) := by
    show (w.comap (ι : ↥N →+* ↥M)).comap
      ((AlgEquiv.restrictNormalHom (↥N) σ).symm : ↥N →+* ↥N) = _
    rw [← NumberField.InfinitePlace.comap_comp, ← hfun,
      NumberField.InfinitePlace.comap_comp]
    exact congrArg (fun v => NumberField.InfinitePlace.comap v (ι : ↥N →+* ↥M)) hσ
  have hunr : NumberField.InfinitePlace.IsUnramified (K : Type _) (w.comap (ι : ↥N →+* ↥M)) :=
    IsUnramifiedAtInfinitePlaces.isUnramified _
  have hbot := hunr.stabilizer_eq_bot
  have : AlgEquiv.restrictNormalHom (↥N) σ ∈
      MulAction.stabilizer (↥N ≃ₐ[(K : Type _)] ↥N) (w.comap (ι : ↥N →+* ↥M)) := hstab
  rw [hbot] at this
  exact this

/-- **THE COMPOSITUM IS UNRAMIFIED AT THE INFINITE PLACES** (PROVEN 2026-07-31),
the third clause of `sup_unramifiedAbelian` below. -/
theorem sup_isUnramifiedAtInfinitePlaces
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    (N₁ N₂ : IntermediateField (K : Type _) (AlgebraicClosure ℚ))
    [FiniteDimensional (K : Type _) N₁] [IsGalois (K : Type _) N₁]
    [IsUnramifiedAtInfinitePlaces (K : Type _) N₁]
    [FiniteDimensional (K : Type _) N₂] [IsGalois (K : Type _) N₂]
    [IsUnramifiedAtInfinitePlaces (K : Type _) N₂] :
    IsUnramifiedAtInfinitePlaces (K : Type _) ↥(N₁ ⊔ N₂) := by
  haveI := normal_algebraicClosure_rat K
  haveI : FiniteDimensional (K : Type _) ↥(N₁ ⊔ N₂) :=
    IntermediateField.finiteDimensional_sup N₁ N₂
  haveI : IsGalois (K : Type _) ↥(N₁ ⊔ N₂) := ⟨⟩
  refine ⟨fun w => ?_⟩
  rw [NumberField.InfinitePlace.isUnramified_iff_stabilizer_eq_bot, Subgroup.eq_bot_iff_forall]
  intro τ hτ
  obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective
    (F := (K : Type _)) (K₁ := ↥(N₁ ⊔ N₂)) (E := AlgebraicClosure ℚ) τ
  exact restrictNormal_sup_eq_one N₁ N₂ σ
    (restrictNormalHom_eq_one_of_stabilizer K _ N₁ le_sup_left w σ hτ)
    (restrictNormalHom_eq_one_of_stabilizer K _ N₂ le_sup_right w σ hτ)

/-- **THE COMPOSITUM IS UNRAMIFIED AT THE FINITE PRIMES** (SORRY LEAF, the one
clause of `sup_unramifiedAbelian` below still open as of 2026-07-31; the other
two — `sup_commutes` and `sup_isUnramifiedAtInfinitePlaces` — are proven above).

**This is the exact analogue of `sup_isUnramifiedAtInfinitePlaces`, with the
INERTIA group in place of the decomposition group at an archimedean place**, and
the shared engine `restrictNormal_sup_eq_one` is already here. What is missing is
only the finite-prime counterpart of
`restrictNormalHom_eq_one_of_stabilizer`, i.e.

    (K) (M N) [FiniteDimensional K M] [IsGalois K M] [FiniteDimensional K N]
      [IsGalois K N] (hunr : N is unramified at every nonzero prime)
      (hle : N ≤ M) (Q : Ideal (𝓞 M)) [Q.IsPrime] (hQ0 : Q ≠ ⊥)
      (σ : ℚ̄ ≃ₐ[K] ℚ̄) (hQ : ∀ x : 𝓞 M, (restrictNormalHom M σ) • x - x ∈ Q) :
      restrictNormalHom N σ = 1

whose proof is `eq_one_of_mem_inertia_of_unramifiedAt` (top of this file) applied
to `Q.under (𝓞 N)`, plus `restrictNormal_commutes` to see that the restriction of
`σ` to `N` moves `y` by the same amount that `σ` moves it inside `M`.

**The plumbing this needs, and where each piece lives.**

* `Algebra ↥N ↥M` is NOT an instance — `N ≤ M` gives only
  `IntermediateField.inclusion hle : ↥N →ₐ[K] ↥M`. Install it with
  `letI : Algebra ↥N ↥M := (IntermediateField.inclusion hle).toRingHom.toAlgebra`
  and `IsScalarTower.of_algebraMap_eq'`, exactly as
  `exists_classField_of_subgroup` does in
  `UnramifiedClassFieldExistence.lean`. `Algebra (𝓞 N) (𝓞 M)` then follows from
  mathlib's `RingOfIntegers` instance.
* `Q.under (𝓞 N) ≠ ⊥` is `Ideal.IsIntegral.comap_ne_bot` in
  `Mathlib/RingTheory/Ideal/GoingUp.lean`, which wants
  `Algebra.IsIntegral (𝓞 N) (𝓞 M)`.
* Then the closing chain, which is `eq_one_of_mem_inertia_of_unramifiedAt` run
  BACKWARDS on `M`: inertia trivial gives
  `Nat.card (Q.inertia Gal(M/K)) = 1`, so
  `Ideal.card_inertia_eq_ramificationIdxIn` and
  `Ideal.ramificationIdxIn_eq_ramificationIdx` give
  `Q.ramificationIdx (𝓞 K) = 1`, and `Ideal.ramificationIdx_eq_one_iff` converts
  that to `Algebra.IsUnramifiedAt`. That last one carries a
  `PerfectField (Q.under (𝓞 K)).ResidueField` side condition, which is free
  because residue fields of `𝓞 K` are finite.

No class field theory is used here, and no analysis. -/
theorem sup_isUnramifiedAt
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    (N₁ N₂ : IntermediateField (K : Type _) (AlgebraicClosure ℚ))
    [FiniteDimensional (K : Type _) N₁] [IsGalois (K : Type _) N₁]
    [FiniteDimensional (K : Type _) N₂] [IsGalois (K : Type _) N₂]
    (hunr₁ : ∀ (Q : Ideal (𝓞 N₁)) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 (K : Type _)) Q)
    (hunr₂ : ∀ (Q : Ideal (𝓞 N₂)) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 (K : Type _)) Q) :
    ∀ (Q : Ideal (𝓞 ↥(N₁ ⊔ N₂))) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 (K : Type _)) Q :=
  sorry

/-- **THE COMPOSITUM OF TWO EVERYWHERE-UNRAMIFIED ABELIAN EXTENSIONS OF `K` IS
EVERYWHERE-UNRAMIFIED AND ABELIAN** (cut 2026-07-31 out of
`exists_hilbertClassField_normal_over_rat` below; two of its three clauses are
PROVEN the same day, the third is `sup_isUnramifiedAt` just above).

This is the "next piece of plumbing" that
`exists_hilbertClassField_artinIso`'s docstring names — the MAXIMALITY of the
Hilbert class field, in the only form that does not presuppose it. With it, the
upper bound `[N₁N₂ : K] ≤ h_K` follows from the companion file, and a class
field of degree exactly `h_K` absorbs every conjugate of itself.

**One injection proves all three clauses**, which is why they are collected
here. `N₁, N₂` are Galois over `K` inside `ℚ̄`, so an automorphism of `ℚ̄/K`
restricting trivially to both restricts trivially to `N₁ ⊔ N₂`
(`restrictNormal_sup_eq_one` above — the Galois connection and nothing else);
combined with the surjectivity of restriction that is the injection
`Gal(N₁N₂/K) ↪ Gal(N₁/K) × Gal(N₂/K)`. Each clause is then the triviality of
some subgroup of `Gal(N₁N₂/K)`: the commutator subgroup, the inertia group at a
finite prime, the decomposition group at an archimedean place.

No class field theory is used, and no analysis. -/
theorem sup_unramifiedAbelian
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    (N₁ N₂ : IntermediateField (K : Type _) (AlgebraicClosure ℚ))
    [FiniteDimensional (K : Type _) N₁] [IsGalois (K : Type _) N₁]
    [IsUnramifiedAtInfinitePlaces (K : Type _) N₁]
    [FiniteDimensional (K : Type _) N₂] [IsGalois (K : Type _) N₂]
    [IsUnramifiedAtInfinitePlaces (K : Type _) N₂]
    (hab₁ : ∀ a b : N₁ ≃ₐ[(K : Type _)] N₁, a * b = b * a)
    (hab₂ : ∀ a b : N₂ ≃ₐ[(K : Type _)] N₂, a * b = b * a)
    (hunr₁ : ∀ (Q : Ideal (𝓞 N₁)) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 (K : Type _)) Q)
    (hunr₂ : ∀ (Q : Ideal (𝓞 N₂)) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 (K : Type _)) Q) :
    (∀ a b : (↥(N₁ ⊔ N₂) ≃ₐ[(K : Type _)] ↥(N₁ ⊔ N₂)), a * b = b * a) ∧
      (∀ (Q : Ideal (𝓞 ↥(N₁ ⊔ N₂))) (_ : Q.IsPrime), Q ≠ ⊥ →
        Algebra.IsUnramifiedAt (𝓞 (K : Type _)) Q) ∧
      IsUnramifiedAtInfinitePlaces (K : Type _) ↥(N₁ ⊔ N₂) :=
  ⟨sup_commutes K N₁ N₂ hab₁ hab₂, sup_isUnramifiedAt K N₁ N₂ hunr₁ hunr₂,
    sup_isUnramifiedAtInfinitePlaces K N₁ N₂⟩

-- `hab`, `hunr` and `hrank` are deliberately unused; see the docstring.
set_option linter.unusedVariables false in
/-- **THE HILBERT CLASS FIELD OF A GALOIS `K` CAN BE CHOSEN NORMAL OVER `ℚ`**
(PROVEN 2026-07-31 over the three leaves above; cut 2026-07-30 out of
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

**PROVEN 2026-07-31** over the three leaves above and
`finrank_le_card_classGroup_of_unramified_abelian_of_isUnramifiedAtInfinitePlaces`
of `UnramifiedClassFieldBound.lean`. The route is the one this docstring used to
propose, corrected on one point (see the warning below): pick a Hilbert class
field `N₀` inside `ℚ̄` — unramified at the infinite places TOO — and show
`σ N₀ ≤ N₀` for every `σ ∈ Gal(ℚ̄/ℚ)` by applying the upper bound to the
compositum `N₀ ⊔ σN₀`, which is abelian and everywhere-unramified and therefore
of degree at most `h_K = [N₀ : K]`. `IntermediateField.normal_iff_forall_map_le'`
turns "stable under every `σ`" into `Normal ℚ`.

**⚠ THE GIVEN `N` IS NOT USED, AND CANNOT BE — the witness must be built.**
`hab`, `hunr` and `hrank` are inert: the conclusion is an EXISTENCE statement,
and the field it asks for is a genuine Hilbert class field, which `N` is not
known to be. The reason is the correction just mentioned. The upper bound
`[L : K] ≤ h_K` needs `L/K` unramified at the INFINITE places as well
(`UnramifiedClassFieldBound.lean` records the counterexample without it:
`ℚ(√3)` has `h = 1` and narrow class number `2`), and `N`'s hypotheses say
nothing about infinity. A degree-`h_K` extension unramified only at the finite
primes can be a subfield of the NARROW class field instead — a different field,
not canonical, and with no reason to be normal over `ℚ`. So the old route's
"note each `σN` is again abelian and everywhere-unramified over `K`, and force
`[N' : K] ≤ h_K = [N : K]`, hence `N' = N`" is a genuine gap **for the given
`N`**, and it closes only by discarding `N` and constructing the class field
afresh. Keeping the hypotheses costs nothing and keeps the consumer in
`Interface.lean` unchanged. -/
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
      Module.finrank (K : Type _) N' = Nat.card (ClassGroup (𝓞 (K : Type _))) := by
  classical
  clear! N
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  haveI : Normal ℚ (AlgebraicClosure ℚ) :=
    (IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)).to_normal
  obtain ⟨N₀, hfd0, hgal0, hinf0, hab0, hunr0, hrank0⟩ :=
    exists_hilbertClassField_intermediateField_isUnramifiedAtInfinitePlaces K
  haveI := hfd0; haveI := hgal0; haveI := hinf0
  have hKN : K ≤ N₀.restrictScalars ℚ := by
    intro x hx
    simpa using N₀.algebraMap_mem ⟨x, hx⟩
  have key : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      (N₀.restrictScalars ℚ).map (σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ) ≤
        N₀.restrictScalars ℚ := by
    intro σ
    have hKnormal : Normal ℚ (K : Type _) := IsGalois.to_normal
    have hKmap : K.map (σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ) = K :=
      IntermediateField.normal_iff_forall_map_eq'.mp hKnormal σ
    have hKE :
        K ≤ (N₀.restrictScalars ℚ).map (σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ) := by
      have hmono := IntermediateField.map_mono
        (σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ) hKN
      rwa [hKmap] at hmono
    set N₁ : IntermediateField (K : Type _) (AlgebraicClosure ℚ) :=
      IntermediateField.extendScalars hKE with hN₁def
    have hN₁ : N₁.restrictScalars ℚ =
        (N₀.restrictScalars ℚ).map (σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ) :=
      IntermediateField.extendScalars_restrictScalars hKE
    obtain ⟨hfd1, hgal1, hinf1, hab1, hunr1, hrank1⟩ :=
      conj_unramifiedAbelian K N₀ hab0 hunr0 σ N₁ hN₁
    haveI := hfd1; haveI := hgal1; haveI := hinf1
    obtain ⟨habM, hunrM, hinfM⟩ := sup_unramifiedAbelian K N₀ N₁ hab0 hab1 hunr0 hunr1
    haveI := hinfM
    haveI : FiniteDimensional ℚ ↥(N₀ ⊔ N₁ : IntermediateField (K : Type _) (AlgebraicClosure ℚ)) :=
      FiniteDimensional.trans ℚ (K : Type _) _
    haveI : NumberField ↥(N₀ ⊔ N₁ : IntermediateField (K : Type _) (AlgebraicClosure ℚ)) := ⟨⟩
    have hbound :
        Module.finrank (K : Type _)
          ↥(N₀ ⊔ N₁ : IntermediateField (K : Type _) (AlgebraicClosure ℚ)) ≤
          Nat.card (ClassGroup (𝓞 (K : Type _))) :=
      NumberField.finrank_le_card_classGroup_of_unramified_abelian_of_isUnramifiedAtInfinitePlaces
        (K : Type _) _ habM hunrM
    have heq : N₀ = N₀ ⊔ N₁ :=
      IntermediateField.eq_of_le_of_finrank_le le_sup_left (by rw [hrank0]; exact hbound)
    have hle : N₁ ≤ N₀ := by rw [heq]; exact le_sup_right
    intro x hx
    rw [← hN₁] at hx
    exact hle hx
  exact ⟨N₀, hfd0, hgal0, IntermediateField.normal_iff_forall_map_le'.mpr key,
    hab0, hunr0, hrank0⟩

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
