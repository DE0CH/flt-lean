/-
NumberField/CyclotomicModelTransport.lean — own work for the Fermat
project (not vendored from the FLT project).
-/
module

public import Fermat.FLT.NumberField.UnramifiedClassFieldExistence
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Moving an everywhere-unramified abelian extension between models of `ℚ(μ_p)`

`Fermat/FLT/Modularity/Interface.lean` runs its Galois dictionary inside the
CONCRETE model `muSubfield p ⊆ AlgebraicClosure ℚ` — that is where `Γℚ`,
`ker χ` and `localInertiaGroup` live — while its class-field-theoretic inputs
are stated for an ABSTRACT `CF` with `IsCyclotomicExtension {p} ℚ CF` and its
own algebraic closure. Two of that file's leaves ask for a finite abelian
everywhere-finite-unramified extension to be carried across, in each
direction, WITH ITS DEGREE.

**THE ROUTE TAKEN HERE IS NOT THE ONE THOSE TWO LEAVES' DOCSTRINGS
ANTICIPATED, and it is much cheaper.** They budgeted a literal transport:
build `e : CF ≃ₐ[ℚ] muSubfield p`, lift it to an isomorphism of algebraic
closures, carry the intermediate field along it, and then re-prove
`Module.finrank`, `IsGalois`, commutativity and `Algebra.IsUnramifiedAt` on
the other side — the last of which means carrying rings of integers,
localisations at primes and ramification indices through the lift. That is a
correct route and a long one.

The observation that avoids it: **the extension itself does not have to
travel — only a NUMBER does.** By the class field correspondence at modulus
`1` (`UnramifiedClassFieldExistence.lean`), over any model `K` the degrees
available to a finite abelian everywhere-unramified extension are exactly the
indices of subgroups of `Cl(𝓞 K)`, and `Cl(𝓞 K)` is transported by a bare ring
isomorphism `𝓞 K ≃+* 𝓞 K'` (`ClassGroup.mulEquiv`). So one reads off the
degree on the source side as the index of the kernel of the Artin surjection,
carries that SUBGROUP across the class-group isomorphism, and asks the
existence theorem on the target side for a class field of that index. No
algebraic closure is lifted and no ring of integers is compared.

The price is that the two leaves now rest on class field theory
(`NumberField.exists_classField_of_subgroup` and the three Chebotarev/
reciprocity leaves under `exists_surjective_classGroupHom_aut_of_unramified_abelian`)
rather than on nothing. That adds no NEW open leaf: every one of them is
already in the import cone of the same cluster of `Interface.lean`, which
proves `exists_unramifiedAbelian_primePow_dvd_finrank_of_dvd` over
`exists_hilbertClassField` and `finrank_le_card_classGroup_of_unramified_abelian`
over the companion bound. There is no cycle: this file is imported BY
`Interface.lean` and imports nothing from it.

## Main results

* `NumberField.exists_unramifiedAbelian_transport` — PROVEN. The core: an
  everywhere-finite-unramified abelian `M/K'` has a counterpart of the SAME
  degree over any other model `K` of `ℚ(μ_p)`, inside `AlgebraicClosure K`.
  The `p = 2` and `p` odd cases are genuinely disjoint and are discharged
  separately; see the proof.
* `NumberField.isUnramifiedAt_of_algEquiv` — PROVEN, and of independent use:
  `Algebra.IsUnramifiedAt` is carried by an isomorphism of `A`-algebras.
* `NumberField.exists_unramifiedAbelian_of_algebraicClosureEquiv` — PROVEN.
  The package (finite, Galois, abelian, everywhere-unramified, of a given
  degree) moves along an isomorphism of AMBIENT algebraic closures. This is
  the one place a literal transport is unavoidable, because the second leaf
  demands its output inside `AlgebraicClosure ℚ` while the existence theorem
  produces it inside `AlgebraicClosure (muSubfield p)`.
-/

@[expose] public section

open NumberField

namespace NumberField

/-- **`Algebra.IsUnramifiedAt` IS CARRIED BY AN ISOMORPHISM OVER THE BASE**
(PROVEN 2026-07-30).

If `h : R ≃ₐ[A] P` and the prime `Q` of `P` pulls back to the prime `q` of
`R`, then `A`-unramifiedness at `q` gives `A`-unramifiedness at `Q`. The proof
is the only thing it can be: `h` carries `q.primeCompl` onto `Q.primeCompl`,
so `IsLocalization.algEquivOfAlgEquiv` gives an `A`-algebra isomorphism of the
two localisations, and `Algebra.FormallyUnramified.of_equiv` transports the
definition (`IsUnramifiedAt A q` is by definition
`FormallyUnramified A (Localization.AtPrime q)`). -/
theorem isUnramifiedAt_of_algEquiv {A R P : Type*} [CommRing A] [CommRing R] [CommRing P]
    [Algebra A R] [Algebra A P] (h : R ≃ₐ[A] P) (q : Ideal R) [q.IsPrime]
    (Q : Ideal P) [Q.IsPrime] (hQ : Ideal.comap (h : R →+* P) Q = q)
    (hu : Algebra.IsUnramifiedAt A q) : Algebra.IsUnramifiedAt A Q := by
  have hiff : ∀ x : R, x ∈ q ↔ h x ∈ Q := by
    intro x; rw [← hQ]; rfl
  have hmap : Submonoid.map (h : R →* P) q.primeCompl = Q.primeCompl := by
    ext y
    simp only [Submonoid.mem_map, Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk,
      Set.mem_compl_iff, SetLike.mem_coe]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact fun hmem => hx ((hiff x).mpr hmem)
    · intro hy
      exact ⟨h.symm y, fun hmem => hy (by simpa using (hiff _).mp hmem), by simp⟩
  exact Algebra.FormallyUnramified.of_equiv
    (IsLocalization.algEquivOfAlgEquiv (Localization.AtPrime q) (Localization.AtPrime Q) h hmap)

variable (p : ℕ) [hp : Fact p.Prime]

/-- **THE MODEL-TRANSPORT CORE: an everywhere-finite-unramified abelian
extension of one model of `ℚ(μ_p)` has a counterpart of the SAME degree over
any other model** (PROVEN 2026-07-30 over unramified class field theory at
modulus `1`, and over nothing else).

Note the source `M` is an arbitrary `K'`-algebra that is a number field —
NOT an intermediate field of any particular algebraic closure. That is
deliberate and is what lets the single statement serve both directions of the
transport in `Interface.lean`: the ambient closure of the source plays no
role, since only `Module.finrank K' M` crosses.

**The two cases are disjoint and neither implies the other.**

* `p = 2`. Then `Module.finrank ℚ K' = Nat.totient 2 = 1`, so `K'` is a model
  of `ℚ` and MINKOWSKI (`finrank_eq_one_of_unramified_of_finrank_rat_eq_one`)
  forces `Module.finrank K' M = 1`. The target is then the class field of the
  subgroup `⊤`, of index `1`. Class field theory is used on the target side
  only, and only in its trivial case; the archimedean hypothesis that the
  reciprocity leaf needs is NOT available here and is not needed — see that
  theorem's docstring for why supplying it over `ℚ` would already require
  knowing the answer.
* `p` odd. Then `2 < p`, so `K'` is totally complex
  (`IsCyclotomicExtension.Rat.isTotallyComplex`) and every infinite place of
  `M` is unramified over `K'` for free. That discharges the archimedean
  hypothesis of `exists_surjective_classGroupHom_aut_of_unramified_abelian`,
  whose kernel then has index `#Gal(M/K') = [M : K']`. `ClassGroup.mulEquiv`
  applied to `RingOfIntegers.mapRingEquiv` of the cyclotomic uniqueness
  isomorphism `K ≃ₐ[ℚ] K'` carries that subgroup to `Cl(𝓞 K)` with its index
  intact, and `exists_classField_finrank_eq_index` returns a field of exactly
  that degree.

**Not vacuous.** `h(ℚ(μ_23)) = 3`, so at `p = 23` the conclusion can be a
genuine cubic extension and is not satisfiable by `K` itself. -/
theorem exists_unramifiedAbelian_transport
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (K' : Type*) [Field K'] [NumberField K'] [IsCyclotomicExtension {p} ℚ K']
    (M : Type*) [Field M] [Algebra K' M] [NumberField M] [IsGalois K' M]
    (habel : ∀ a b : M ≃ₐ[K'] M, a * b = b * a)
    (hunr : ∀ (Q : Ideal (𝓞 M)) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 K') Q) :
    ∃ (H : IntermediateField K (AlgebraicClosure K))
      (_ : FiniteDimensional K H) (_ : IsGalois K H),
      (∀ a b : H ≃ₐ[K] H, a * b = b * a) ∧
      (∀ (Q : Ideal (𝓞 H)) (_ : Q.IsPrime), Q ≠ ⊥ →
        Algebra.IsUnramifiedAt (𝓞 K) Q) ∧
      Module.finrank K H = Module.finrank K' M := by
  rcases eq_or_ne p 2 with rfl | hp2
  · -- `p = 2`: `ℚ(μ₂) = ℚ`, and Minkowski forces `M = K'`.
    have hE : Module.finrank ℚ K' = 1 := by
      rw [IsCyclotomicExtension.finrank (n := 2) K'
        (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
      decide
    have h1 : Module.finrank K' M = 1 :=
      NumberField.finrank_eq_one_of_unramified_of_finrank_rat_eq_one K' M hE hunr
    obtain ⟨H, hfd, hgal, hab, hunrH, hrank⟩ :=
      NumberField.exists_classField_finrank_eq_index K (⊤ : Subgroup (ClassGroup (𝓞 K)))
    exact ⟨H, hfd, hgal, hab, hunrH, by rw [hrank, Subgroup.index_top, h1]⟩
  · -- odd `p`: `ℚ(μ_p)` is totally complex, so nothing ramifies at infinity.
    haveI : NeZero p := ⟨hp.out.ne_zero⟩
    have h2p : 2 < p := lt_of_le_of_ne hp.out.two_le (Ne.symm hp2)
    haveI : NumberField.IsTotallyComplex K' :=
      IsCyclotomicExtension.Rat.isTotallyComplex K' h2p
    haveI : IsUnramifiedAtInfinitePlaces K' M :=
      ⟨fun w => NumberField.InfinitePlace.isUnramified_iff.mpr
        (Or.inr (NumberField.IsTotallyComplex.isComplex _))⟩
    obtain ⟨φ, hsurj, -⟩ :=
      NumberField.exists_surjective_classGroupHom_aut_of_unramified_abelian K' M habel hunr
    have hidx : φ.ker.index = Module.finrank K' M := by
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top]
      exact IsGalois.card_aut_eq_finrank _ _
    let g : K ≃ₐ[ℚ] K' := IsCyclotomicExtension.algEquiv {p} ℚ K K'
    let ge : ClassGroup (𝓞 K) ≃* ClassGroup (𝓞 K') :=
      ClassGroup.mulEquiv (NumberField.RingOfIntegers.mapRingEquiv g.toRingEquiv)
    obtain ⟨H, hfd, hgal, hab, hunrH, hrank⟩ :=
      NumberField.exists_classField_finrank_eq_index K (φ.ker.comap ge.toMonoidHom)
    refine ⟨H, hfd, hgal, hab, hunrH, ?_⟩
    rw [hrank, Subgroup.index_comap_of_surjective _ ge.surjective, hidx]

/-- **THE PACKAGE MOVES ALONG AN ISOMORPHISM OF AMBIENT ALGEBRAIC CLOSURES**
(PROVEN 2026-07-30).

Given `ee : AlgebraicClosure E ≃ₐ[E] Ω`, an intermediate field of
`AlgebraicClosure E/E` that is finite, Galois, with abelian Galois group and
unramified at every nonzero prime has an image in `Ω` with the same four
properties and the same degree. Everything is transport along the induced
`H ≃ₐ[E] H''`: `Module.Finite.equiv` and `LinearEquiv.finrank_eq` for
finiteness and degree, `IsGalois.of_algEquiv` for Galoisness,
`AlgEquiv.autCongr` for commutativity, and `RingOfIntegers.mapAlgEquiv`
followed by `isUnramifiedAt_of_algEquiv` above for unramifiedness.

`ee` is taken as a HYPOTHESIS rather than built inside from `IsAlgClosure.equiv`
on purpose: with it opaque, no defeq check can try to unfold `IsAlgClosed.lift`,
which is what made an earlier in-line version of this argument time out. -/
theorem exists_unramifiedAbelian_of_algebraicClosureEquiv {E : Type*} [Field E] [NumberField E]
    {Ω : Type*} [Field Ω] [Algebra E Ω]
    (ee : AlgebraicClosure E ≃ₐ[E] Ω)
    (H : IntermediateField E (AlgebraicClosure E)) [FiniteDimensional E H] [IsGalois E H]
    (hab : ∀ a b : H ≃ₐ[E] H, a * b = b * a)
    (hunrH : ∀ (Q : Ideal (𝓞 H)) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 E) Q) :
    ∃ (H'' : IntermediateField E Ω) (_ : FiniteDimensional E H'') (_ : IsGalois E H''),
      (∀ a b : H'' ≃ₐ[E] H'', a * b = b * a) ∧
      (∀ (Q : Ideal (𝓞 H'')) (_ : Q.IsPrime), Q ≠ ⊥ →
        Algebra.IsUnramifiedAt (𝓞 E) Q) ∧
      Module.finrank E H'' = Module.finrank E H := by
  obtain ⟨H'', ⟨eH⟩⟩ : ∃ H'' : IntermediateField E Ω, Nonempty (H ≃ₐ[E] H'') :=
    ⟨H.map ee.toAlgHom, ⟨IntermediateField.intermediateFieldMap ee H⟩⟩
  haveI : FiniteDimensional E H'' := Module.Finite.equiv eH.toLinearEquiv
  refine ⟨H'', inferInstance, IsGalois.of_algEquiv eH, ?_, ?_,
    eH.toLinearEquiv.finrank_eq.symm⟩
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
    exact isUnramifiedAt_of_algEquiv f _ Q rfl (hunrH _ hprime hne)

end NumberField
