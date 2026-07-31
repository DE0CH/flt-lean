/-
CyclotomicIdealSymbol.lean — own work for the Fermat project.

Support for `Fermat/FLT/Modularity/Interface.lean`'s
`exists_zmodIdealSymbol_of_frobIdeal`, which builds the `ZMod nn`-valued
ideal symbol of `ℚ(μ_p)` attached to a character of `Γℚ` with open kernel.

That leaf was DECOMPOSED on 2026-07-30.  Its CONSTRUCTION — the transport
`Γ CF → ker χ` along the mod-`p` cyclotomic character, the multiplicative
extension of `w ↦ χ'(Frob_w)` from the height-one primes to the whole ideal
monoid, the openness of `ker χ'`, and the reduction of the `frobIdeal`
compatibility clause to a statement about ONE prime — is now PROVEN in
`Interface.lean` over the two leaves stated here, which carry the genuine
mathematical content:

* `exists_conj_localInertia_rat_of_localInertia` — the INERTIA TRANSPORT
  `Γ CF_w → Γ CF → Γℚ` versus `Γ CF_w → Γ ℚ_ℓ → Γℚ`;
* `globalFrob_map_mul_inv_mem_of_isArithFrobAt` — the FROBENIUS COMPARISON,
  "two Frobenius elements at the same prime agree modulo `N`".

Both are stated with no `ψ`, no `ZMod`, no ideal symbol and no `nn`: they are
about `Γ`'s and `N` alone.  See their own docstrings for their routes.

**The first of those was itself CLOSED the same day**, over the strictly
smaller `exists_residueChar_adicCompletionHom`.  The step that made it possible
is `exists_conj_of_two_embeddings`: `Field.absoluteGaloisGroup.map` has no
functoriality equation, because it is built from an arbitrarily chosen
embedding of algebraic closures — but any two `k`-embeddings of
`AlgebraicClosure k` into a field differ by an element of `Γ k`, so the two
routes are CONJUGATE, and that is all the consumer ever needed.  What is left
of that leaf is local-field bookkeeping: exhibit the residue characteristic `ℓ`
and the local ring hom `ℚ_ℓ → CF_w`, for which `CompletionTransport.lean`
already supplies `adicCompletionMap`, `adicCompletionMap_coe` and
`adicCompletionMap_mem_integers`.

`exists_residueChar_adicCompletionHom` was CLOSED on 2026-07-31, so
`exists_conj_localInertia_rat_of_localInertia` is now unconditionally proven and
the module's live frontier is the single leaf
`globalFrob_map_mul_inv_mem_of_isArithFrobAt` (the Frobenius comparison).

**THAT REMAINING LEAF IS FALSE AS STATED** — see the FALSITY AUDIT at the end of
its docstring, with a `p = 23` counterexample.  It mixes the free embedding
parameter `ι` with the fixed embedding buried in `Field.absoluteGaloisGroup.map`,
and asks for `[w] = [γ w]` in `Cl(ℚ(μ_p))`.  **Do not dispatch a proof effort at
it**; the repair is a statement change that also touches `Interface.lean`, and
the audit sets out the two candidate routes.  Its last step is already proven
here, as `mul_inv_mem_of_conj_localInertia_mul_commutator`, and is unaffected by
whichever repair is chosen.

`exists_idealSymbolMonoidHom` is proven here and is pure Dedekind-domain
theory.

The module is separate from `Interface.lean` for the reason recorded there
about `UnramifiedClassFieldBound.lean`: `Interface.lean` elaborates for the
better part of an hour on one core and none of this material needs any of it.
-/

module

-- `localInertiaGroup`, `Field.absoluteGaloisGroup.map`.
public import Fermat.FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
-- `Nat.Prime.toHeightOneSpectrumRingOfIntegersRat`.
public import Fermat.FLT.Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
-- `GaloisRepresentation.globalFrob`.
public import Fermat.FLT.GaloisRepresentation.Chebotarev
-- `adicCompletionMap`, `Field.absoluteGaloisGroup.map_mem_localInertiaGroup`.
public import Fermat.FLT.Deformations.RepresentationTheory.CompletionTransport
-- `IsArithFrobAt`.
public import Mathlib.RingTheory.Frobenius
-- `Ring.HasFiniteQuotients.finiteQuotient`, for finiteness of the residue field
-- of `w` (which is what makes its characteristic a prime).
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
-- `cyclotomicCharacter`.
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
-- `IsCyclotomicExtension`.
public import Mathlib.NumberTheory.Cyclotomic.Basic

@[expose] public section

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace NumberField

universe u

/-- **EVERY FUNCTION ON THE HEIGHT-ONE PRIMES OF A DEDEKIND DOMAIN EXTENDS
TO A MONOID HOM ON THE NONZERO IDEALS** (PROVEN 2026-07-30).

The extension is by unique factorisation: send `I` to the product of `u`
over the normalised factors of `I`.  Multiplicativity is
`UniqueFactorizationMonoid.normalizedFactors_mul`, and the value at a prime
`w` is `u w` because `normalizedFactors` of an irreducible is the singleton
`{normalize w} = {w}` (ideals of a Dedekind domain are already normalised).

This is what makes the ideal symbol of `Interface.lean`'s
`exists_zmodIdealSymbol_of_frobIdeal` a MONOID HOM on all of
`(Ideal (𝓞 CF))⁰` while being PINNED at every height-one prime — the trap
recorded on that leaf, where a symbol defined only on the image of
`frobIdeal` would be junk at the higher-degree primes a principal ideal can
involve. -/
theorem exists_idealSymbolMonoidHom {R : Type*} [CommRing R] [IsDedekindDomain R]
    {A : Type*} [CommMonoid A] (u : IsDedekindDomain.HeightOneSpectrum R → A) :
    ∃ c : (Ideal R)⁰ →* A,
      ∀ (w : IsDedekindDomain.HeightOneSpectrum R) (hw : w.asIdeal ∈ (Ideal R)⁰),
        c ⟨w.asIdeal, hw⟩ = u w := by
  classical
  set g : Ideal R → A := fun J =>
    if h : J.IsPrime ∧ J ≠ ⊥ then u ⟨J, h.1, h.2⟩ else 1 with hgdef
  have hne : ∀ I : (Ideal R)⁰, (I : Ideal R) ≠ 0 := by
    intro I
    exact mem_nonZeroDivisors_iff_ne_zero.mp I.2
  refine ⟨⟨⟨fun I => ((UniqueFactorizationMonoid.normalizedFactors (I : Ideal R)).map g).prod,
    ?_⟩, ?_⟩, ?_⟩
  · show ((UniqueFactorizationMonoid.normalizedFactors ((1 : (Ideal R)⁰) : Ideal R)).map g).prod = 1
    rw [Submonoid.coe_one, UniqueFactorizationMonoid.normalizedFactors_one]
    simp
  · intro I J
    show ((UniqueFactorizationMonoid.normalizedFactors ((I * J : (Ideal R)⁰) : Ideal R)).map g).prod
      = _
    rw [Submonoid.coe_mul,
      UniqueFactorizationMonoid.normalizedFactors_mul (hne I) (hne J),
      Multiset.map_add, Multiset.prod_add]
  · intro w hw
    have hv : w.asIdeal ≠ ⊥ := w.ne_bot
    have hirr : Irreducible w.asIdeal :=
      (Ideal.prime_of_isPrime hv w.isPrime).irreducible
    show ((UniqueFactorizationMonoid.normalizedFactors w.asIdeal).map g).prod = u w
    rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hirr, normalize_eq,
      Multiset.map_singleton, Multiset.prod_singleton, hgdef]
    exact dif_pos ⟨w.isPrime, hv⟩

/-- **ANY TWO `k`-EMBEDDINGS OF `AlgebraicClosure k` INTO A FIELD DIFFER BY AN
ELEMENT OF `Γ k`** (PROVEN 2026-07-30).

This is the tool that stands in for the missing functoriality of
`Field.absoluteGaloisGroup.map`.  `map` is built from `IsAlgClosed.lift`, an
ARBITRARILY CHOSEN embedding of algebraic closures, so there is no equation
`map f ∘ map g = map (g ∘ f)` and none exists in this project (the point is
recorded at `KhareWintenberger.lean:3402`, where the workaround was to descend
one step at a time).  What IS true is that the two composites agree up to
conjugacy, and this lemma is why: the two embeddings have the same image — both
ranges are the algebraic closure of `k` inside `Ω`, an algebraically closed
subfield, so every `k`-conjugate of an element of one range already lies in it —
so `F₂⁻¹ ∘ F₁` is a `k`-automorphism of `AlgebraicClosure k`.

In Lean that is exactly `AlgHom.restrictNormal'`, the same construction
`Field.absoluteGaloisGroup.mapAux` itself uses, applied with the target made an
`AlgebraicClosure k`-algebra along `F₂`. -/
theorem exists_conj_of_two_embeddings
    {k : Type*} [Field k] {Ω : Type*} [Field Ω]
    (F₁ F₂ : AlgebraicClosure k →+* Ω)
    (h : ∀ x : k, F₁ (algebraMap k (AlgebraicClosure k) x)
      = F₂ (algebraMap k (AlgebraicClosure k) x)) :
    ∃ τ : Field.absoluteGaloisGroup k, ∀ x, F₁ x = F₂ (τ x) := by
  letI : Algebra (AlgebraicClosure k) Ω := F₂.toAlgebra
  letI : Algebra k Ω := (F₂.comp (algebraMap k (AlgebraicClosure k))).toAlgebra
  haveI : IsScalarTower k (AlgebraicClosure k) Ω := .of_algebraMap_eq (fun _ => rfl)
  let F₁' : AlgebraicClosure k →ₐ[k] Ω := { F₁ with commutes' := h }
  refine ⟨F₁'.restrictNormal' (AlgebraicClosure k), fun x => ?_⟩
  exact (AlgHom.restrictNormal_commutes F₁' (AlgebraicClosure k) x).symm

/-- **THE INERTIA TRANSPORT, WITH THE LOCAL EMBEDDING OF COMPLETIONS GIVEN**
(PROVEN 2026-07-30).  This is the whole mathematical content of
`exists_conj_localInertia_rat_of_localInertia` below; what that leaf adds on
top is only the EXISTENCE of `ℓ` and `φ`, which is
`exists_residueChar_adicCompletionHom`.

Two ingredients, both already in the tree:

* `Field.absoluteGaloisGroup.map_mem_localInertiaGroup` (`CompletionTransport.lean`)
  — inertia goes down along a LOCAL `φ`, which is what `hφloc` supplies;
* `exists_conj_of_two_embeddings` above — the two routes
  `Γ CF_w → Γ CF → Γℚ` and `Γ CF_w → Γ ℚ_v → Γℚ` are conjugate.

The computation is then forced.  Writing `F₁` and `F₂` for the two composed
embeddings `ℚᵃˡᵍ → (CF_w)ᵃˡᵍ` and `τ` for the element with `F₁ = F₂ ∘ τ`,
applying `Field.absoluteGaloisGroup.lift_map` twice on each side gives
`Fᵢ (Lᵢ n y) = n (Fᵢ y)`, whence `τ ∘ L₁ n = L₂ n ∘ τ` by injectivity of `F₂`,
i.e. `L₁ n = τ⁻¹ · L₂ n · τ`.  Conjugating by `map (algebraMap ℚ CF) σ` turns
that into the statement, with conjugator `map (algebraMap ℚ CF) σ · τ⁻¹`. -/
theorem exists_conj_localInertia_of_adicCompletionHom
    (CF : Type) [Field CF] [NumberField CF]
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 CF))
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    (φ : v.adicCompletion ℚ →+* w.adicCompletion CF)
    (hφcomm : ∀ x : ℚ, φ (algebraMap ℚ (v.adicCompletion ℚ) x)
      = algebraMap CF (w.adicCompletion CF) (algebraMap ℚ CF x))
    (hφloc : ∀ y ∈ v.adicCompletionIntegers ℚ, φ y ∈ w.adicCompletionIntegers CF)
    (σ : Field.absoluteGaloisGroup CF)
    (n : Field.absoluteGaloisGroup (w.adicCompletion CF))
    (hn : n ∈ localInertiaGroup w) :
    ∃ (τ : Field.absoluteGaloisGroup ℚ)
      (m : Field.absoluteGaloisGroup (v.adicCompletion ℚ)),
      m ∈ localInertiaGroup v ∧
      Field.absoluteGaloisGroup.map (algebraMap ℚ CF)
          (σ * Field.absoluteGaloisGroup.map
            (algebraMap CF (w.adicCompletion CF)) n * σ⁻¹)
        = τ * Field.absoluteGaloisGroup.map
            (algebraMap ℚ (v.adicCompletion ℚ)) m * τ⁻¹ := by
  classical
  -- NOTE: `Algebra ℚ (AlgebraicClosure ℚ)` elaborates to `DivisionRing.toRatAlgebra`,
  -- not to `AlgebraicClosure.instAlgebra`; the two are defeq but not syntactically
  -- equal, so `rw [AlgebraicClosure.map_algebraMap]` MISSES.  Stating each instance
  -- as an explicitly-typed `have` elaborates it against the goal's instance.
  have hcomm : ∀ x : ℚ,
      ((AlgebraicClosure.map (algebraMap CF (w.adicCompletion CF))).comp
        (AlgebraicClosure.map (algebraMap ℚ CF))) (algebraMap ℚ (AlgebraicClosure ℚ) x)
      = ((AlgebraicClosure.map φ).comp
        (AlgebraicClosure.map (algebraMap ℚ (v.adicCompletion ℚ))))
          (algebraMap ℚ (AlgebraicClosure ℚ) x) := by
    intro x
    have e1 : (AlgebraicClosure.map (algebraMap ℚ CF)) (algebraMap ℚ (AlgebraicClosure ℚ) x)
        = algebraMap CF (AlgebraicClosure CF) (algebraMap ℚ CF x) :=
      AlgebraicClosure.map_algebraMap _ _
    have e2 : (AlgebraicClosure.map (algebraMap ℚ (v.adicCompletion ℚ)))
          (algebraMap ℚ (AlgebraicClosure ℚ) x)
        = algebraMap (v.adicCompletion ℚ) (AlgebraicClosure (v.adicCompletion ℚ))
            (algebraMap ℚ (v.adicCompletion ℚ) x) :=
      AlgebraicClosure.map_algebraMap _ _
    have e3 : (AlgebraicClosure.map (algebraMap CF (w.adicCompletion CF)))
          (algebraMap CF (AlgebraicClosure CF) (algebraMap ℚ CF x))
        = algebraMap (w.adicCompletion CF) (AlgebraicClosure (w.adicCompletion CF))
            (algebraMap CF (w.adicCompletion CF) (algebraMap ℚ CF x)) :=
      AlgebraicClosure.map_algebraMap _ _
    have e4 : (AlgebraicClosure.map φ)
          (algebraMap (v.adicCompletion ℚ) (AlgebraicClosure (v.adicCompletion ℚ))
            (algebraMap ℚ (v.adicCompletion ℚ) x))
        = algebraMap (w.adicCompletion CF) (AlgebraicClosure (w.adicCompletion CF))
            (φ (algebraMap ℚ (v.adicCompletion ℚ) x)) :=
      AlgebraicClosure.map_algebraMap _ _
    rw [RingHom.comp_apply, RingHom.comp_apply, e1, e2, e3, e4, hφcomm x]
  obtain ⟨τ, hτ⟩ := exists_conj_of_two_embeddings _ _ hcomm
  refine ⟨Field.absoluteGaloisGroup.map (algebraMap ℚ CF) σ * τ⁻¹,
    Field.absoluteGaloisGroup.map φ n,
    Field.absoluteGaloisGroup.map_mem_localInertiaGroup v w φ hφloc n hn, ?_⟩
  have hkey : ∀ y, τ (Field.absoluteGaloisGroup.map (algebraMap ℚ CF)
        (Field.absoluteGaloisGroup.map (algebraMap CF (w.adicCompletion CF)) n) y)
      = Field.absoluteGaloisGroup.map (algebraMap ℚ (v.adicCompletion ℚ))
          (Field.absoluteGaloisGroup.map φ n) (τ y) := by
    intro y
    refine ((AlgebraicClosure.map φ).comp
      (AlgebraicClosure.map (algebraMap ℚ (v.adicCompletion ℚ)))).injective ?_
    have hL : ((AlgebraicClosure.map φ).comp
          (AlgebraicClosure.map (algebraMap ℚ (v.adicCompletion ℚ))))
            (τ (Field.absoluteGaloisGroup.map (algebraMap ℚ CF)
              (Field.absoluteGaloisGroup.map (algebraMap CF (w.adicCompletion CF)) n) y))
        = n (((AlgebraicClosure.map (algebraMap CF (w.adicCompletion CF))).comp
              (AlgebraicClosure.map (algebraMap ℚ CF))) y) := by
      rw [← hτ, RingHom.comp_apply, RingHom.comp_apply,
        Field.absoluteGaloisGroup.lift_map (algebraMap ℚ CF),
        Field.absoluteGaloisGroup.lift_map (algebraMap CF (w.adicCompletion CF))]
    have hR : ((AlgebraicClosure.map φ).comp
          (AlgebraicClosure.map (algebraMap ℚ (v.adicCompletion ℚ))))
            (Field.absoluteGaloisGroup.map (algebraMap ℚ (v.adicCompletion ℚ))
              (Field.absoluteGaloisGroup.map φ n) (τ y))
        = n (((AlgebraicClosure.map φ).comp
              (AlgebraicClosure.map (algebraMap ℚ (v.adicCompletion ℚ)))) (τ y)) := by
      rw [RingHom.comp_apply, RingHom.comp_apply,
        Field.absoluteGaloisGroup.lift_map (algebraMap ℚ (v.adicCompletion ℚ)),
        Field.absoluteGaloisGroup.lift_map φ]
    rw [hL, hR, hτ y]
  have hconj : Field.absoluteGaloisGroup.map (algebraMap ℚ CF)
        (Field.absoluteGaloisGroup.map (algebraMap CF (w.adicCompletion CF)) n)
      = τ⁻¹ * Field.absoluteGaloisGroup.map (algebraMap ℚ (v.adicCompletion ℚ))
          (Field.absoluteGaloisGroup.map φ n) * τ := by
    have h1 : τ * Field.absoluteGaloisGroup.map (algebraMap ℚ CF)
          (Field.absoluteGaloisGroup.map (algebraMap CF (w.adicCompletion CF)) n)
        = Field.absoluteGaloisGroup.map (algebraMap ℚ (v.adicCompletion ℚ))
            (Field.absoluteGaloisGroup.map φ n) * τ := by
      ext y
      exact hkey y
    calc Field.absoluteGaloisGroup.map (algebraMap ℚ CF)
          (Field.absoluteGaloisGroup.map (algebraMap CF (w.adicCompletion CF)) n)
        = τ⁻¹ * (τ * Field.absoluteGaloisGroup.map (algebraMap ℚ CF)
          (Field.absoluteGaloisGroup.map (algebraMap CF (w.adicCompletion CF)) n)) := by group
      _ = τ⁻¹ * (Field.absoluteGaloisGroup.map (algebraMap ℚ (v.adicCompletion ℚ))
            (Field.absoluteGaloisGroup.map φ n) * τ) := by rw [h1]
      _ = _ := by group
  rw [map_mul, map_mul, map_inv, hconj]
  group

/-- **PLUMBING LEAF: THE COMPLETION OF `ℚ` AT THE PRIME BELOW `w` EMBEDS
LOCALLY IN THE COMPLETION OF `CF` AT `w`** (PROVEN 2026-07-31; cut 2026-07-30
out of `exists_conj_localInertia_rat_of_localInertia` below, whose mathematical
content is proven above).

Standard local-field bookkeeping, with every ingredient already in
`CompletionTransport.lean`:

* `ℓ` is the residue characteristic of `w`, and
  `hℓ.toHeightOneSpectrumRingOfIntegersRat` must be identified with the prime of
  `𝓞 ℚ` under `w`.  **The `𝓞 ℚ ≅ ℤ` bookkeeping the leaf was cut for turns out
  to be avoidable, and that is the one thing worth remembering here**: rather
  than classify the nonzero primes of `𝓞 ℚ` (which does need the equivalence
  with `ℤ`, a generator, and `Int.prime_iff_natAbs_prime`), take `ℓ` to be
  `ringChar` of the RESIDUE FIELD `𝓞 CF ⧸ w` — finite by
  `Ring.HasFiniteQuotients.finiteQuotient`, a domain because `w` is prime,
  hence of prime characteristic — and observe that `(ℓ) ≤ w.under (𝓞 ℚ)` with
  `(ℓ)` already MAXIMAL, so the inclusion is an equality for free.  Going down
  from the residue field replaces the classification with one `Ideal.IsMaximal.eq_of_le`;
* `φ` is `IsDedekindDomain.HeightOneSpectrum.adicCompletionMap v w (algebraMap ℚ CF) _`,
  whose uniform-continuity side condition is
  `WithVal.uniformContinuous_map_of_le` fed by `valuation_map_le_of_le_one`
  (both in `CompletionTransport.lean`), applied to the fact that `w` lies over
  `v`;
* the commuting square is `adicCompletionMap_coe`;
* locality is `adicCompletionMap_mem_integers`.

**The check that would refute it**: a prime `w` of a number field lying over no
rational prime, or a `ℚ → CF` that fails to be `v`-to-`w` norm-decreasing —
neither of which can happen, `𝓞 CF` being integral over `ℤ`. -/
theorem exists_residueChar_adicCompletionHom
    (CF : Type) [Field CF] [NumberField CF]
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 CF)) :
    ∃ (ℓ : ℕ) (hℓ : ℓ.Prime)
      (φ : (hℓ.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ) →+*
           (w.adicCompletion CF)),
      (∀ x : ℚ, φ (algebraMap ℚ
          (hℓ.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ) x)
        = algebraMap CF (w.adicCompletion CF) (algebraMap ℚ CF x)) ∧
      (∀ y ∈ hℓ.toHeightOneSpectrumRingOfIntegersRat.adicCompletionIntegers ℚ,
        φ y ∈ w.adicCompletionIntegers CF) := by
  classical
  haveI hwp : w.asIdeal.IsPrime := w.isPrime
  -- (1) `ℓ` is the residue characteristic of `w`: the residue field is a FINITE
  -- domain, so its characteristic is a prime, and that prime lies in `w`.
  obtain ⟨ℓ, hℓ, hℓw⟩ : ∃ (ℓ : ℕ) (_ : ℓ.Prime), ((ℓ : ℕ) : 𝓞 CF) ∈ w.asIdeal := by
    haveI hfin : Finite (𝓞 CF ⧸ w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
    haveI hdom : IsDomain (𝓞 CF ⧸ w.asIdeal) := Ideal.Quotient.isDomain w.asIdeal
    refine ⟨ringChar (𝓞 CF ⧸ w.asIdeal), CharP.prime_ringChar _, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact (ringChar.spec (𝓞 CF ⧸ w.asIdeal) _).mpr dvd_rfl
  -- (2) the prime of `𝓞 ℚ` under `w` IS the place attached to `ℓ`.  One inclusion
  -- is `ℓ ∈ w`, and it is an equality because `(ℓ)` is already maximal.
  have hvcomap : hℓ.toHeightOneSpectrumRingOfIntegersRat.asIdeal
      = Ideal.comap (algebraMap (𝓞 ℚ) (𝓞 CF)) w.asIdeal := by
    haveI hcp : (Ideal.comap (algebraMap (𝓞 ℚ) (𝓞 CF)) w.asIdeal).IsPrime :=
      Ideal.IsPrime.comap _
    have hle : hℓ.toHeightOneSpectrumRingOfIntegersRat.asIdeal
        ≤ Ideal.comap (algebraMap (𝓞 ℚ) (𝓞 CF)) w.asIdeal := by
      rw [asIdeal_toHeightOneSpectrumRingOfIntegersRat hℓ, Ideal.span_singleton_le_iff_mem,
        Ideal.mem_comap, map_natCast]
      exact hℓw
    have hmax : hℓ.toHeightOneSpectrumRingOfIntegersRat.asIdeal.IsMaximal :=
      hℓ.toHeightOneSpectrumRingOfIntegersRat.isPrime.isMaximal_of_ne_bot
        hℓ.toHeightOneSpectrumRingOfIntegersRat.ne_bot
    exact hmax.eq_of_le hcp.ne_top hle
  -- (3) the commuting square `𝓞 ℚ → ℚ → CF` versus `𝓞 ℚ → 𝓞 CF → CF`
  have hcomm : ∀ a : 𝓞 ℚ, algebraMap ℚ CF (algebraMap (𝓞 ℚ) ℚ a)
      = algebraMap (𝓞 CF) CF (algebraMap (𝓞 ℚ) (𝓞 CF) a) := by
    intro a
    rw [← IsScalarTower.algebraMap_apply (𝓞 ℚ) ℚ CF,
      ← IsScalarTower.algebraMap_apply (𝓞 ℚ) (𝓞 CF) CF]
  have hmem : hℓ.toHeightOneSpectrumRingOfIntegersRat.asIdeal
      ≤ Ideal.comap (algebraMap (𝓞 ℚ) (𝓞 CF)) w.asIdeal := le_of_eq hvcomap
  have hcompl : ∀ s : 𝓞 ℚ, s ∉ hℓ.toHeightOneSpectrumRingOfIntegersRat.asIdeal →
      algebraMap (𝓞 ℚ) (𝓞 CF) s ∉ w.asIdeal := by
    intro s hs hcon
    exact hs (hvcomap ▸ Ideal.mem_comap.mpr hcon)
  -- (4) hence `ℚ → CF` is valuation-decreasing, so uniformly continuous, so it
  -- completes to `ℚ_ℓ → CF_w`
  have hle : ∀ x : ℚ, hℓ.toHeightOneSpectrumRingOfIntegersRat.valuation ℚ x ≤ 1 →
      w.valuation CF (algebraMap ℚ CF x)
        ≤ hℓ.toHeightOneSpectrumRingOfIntegersRat.valuation ℚ x :=
    fun x hx => IsDedekindDomain.HeightOneSpectrum.valuation_map_le_of_le_one
      hℓ.toHeightOneSpectrumRingOfIntegersRat w (algebraMap (𝓞 ℚ) (𝓞 CF))
      (algebraMap ℚ CF) hcomm hmem hcompl x hx
  have huc : UniformContinuous (WithVal.map
      (hℓ.toHeightOneSpectrumRingOfIntegersRat.valuation ℚ) (w.valuation CF)
      (algebraMap ℚ CF)) :=
    WithVal.uniformContinuous_map_of_le _ _
      (hℓ.toHeightOneSpectrumRingOfIntegersRat.valuation_surjective ℚ) _ hle
  refine ⟨ℓ, hℓ, IsDedekindDomain.HeightOneSpectrum.adicCompletionMap
    hℓ.toHeightOneSpectrumRingOfIntegersRat w (algebraMap ℚ CF) huc, fun x => ?_, fun y hy => ?_⟩
  -- NOTE the same instance trap as in `exists_conj_localInertia_of_adicCompletionHom`
  -- below, in mirror image: the STATEMENT's `algebraMap ℚ (ℚ_ℓ)` elaborates to
  -- `DivisionRing.toRatAlgebra`, while `adicCompletionMap_coe` produces
  -- `instAlgebraAdicCompletion`.  They are equal, but only up to
  -- `Algebra.algebra_rat_subsingleton` — `RingHom.ext_rat` is the usable form.
  · refine Eq.trans ?_ (IsDedekindDomain.HeightOneSpectrum.adicCompletionMap_coe
      hℓ.toHeightOneSpectrumRingOfIntegersRat w (algebraMap ℚ CF) huc x)
    congr 1
    exact RingHom.congr_fun (RingHom.ext_rat _ _) x
  · exact IsDedekindDomain.HeightOneSpectrum.adicCompletionMap_mem_integers _ _ _ huc
      (algebraMap (𝓞 ℚ) (𝓞 CF)) hcomm hy

/-- **INERTIA TRANSPORT: A LOCAL INERTIA ELEMENT OF A NUMBER FIELD, PUSHED
DOWN TO `Γℚ`, IS A CONJUGATE OF A LOCAL INERTIA ELEMENT OF `ℚ`** (PROVEN
2026-07-30 over `exists_residueChar_adicCompletionHom` above and nothing else;
it was cut 2026-07-30 out of `Interface.lean`'s
`exists_zmodIdealSymbol_of_frobIdeal` as item 3 of that leaf's own "what must be
built" list, "`hunr` from `hNinert`", and DECOMPOSED the same day).

`Interface.lean` measures unramifiedness of the constructed character `χ'` by
inertia subgroups inside `Γ CF`, while the hypothesis it is given (`hNinert`)
measures it by inertia subgroups inside `Γℚ`.  This is the conversion, and it
mentions no character at all.

The conclusion is stated UP TO CONJUGACY, and must be — see
`exists_conj_of_two_embeddings` above for why.  It costs the consumer nothing:
`hNinert` already quantifies over an arbitrary conjugating `σ ∈ Γℚ`, which is
precisely why it was stated that way. -/
theorem exists_conj_localInertia_rat_of_localInertia
    (CF : Type) [Field CF] [NumberField CF]
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 CF))
    (σ : Field.absoluteGaloisGroup CF)
    (n : Field.absoluteGaloisGroup
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion CF w))
    (hn : n ∈ localInertiaGroup w) :
    ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (τ : Field.absoluteGaloisGroup ℚ)
      (m : Field.absoluteGaloisGroup
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hℓ.toHeightOneSpectrumRingOfIntegersRat)),
      m ∈ localInertiaGroup hℓ.toHeightOneSpectrumRingOfIntegersRat ∧
      Field.absoluteGaloisGroup.map (algebraMap ℚ CF)
          (σ * Field.absoluteGaloisGroup.map
            (algebraMap CF (IsDedekindDomain.HeightOneSpectrum.adicCompletion CF w)) n * σ⁻¹)
        = τ * Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hℓ.toHeightOneSpectrumRingOfIntegersRat)) m * τ⁻¹ := by
  obtain ⟨ℓ, hℓ, φ, hφcomm, hφloc⟩ := exists_residueChar_adicCompletionHom CF w
  obtain ⟨τ, m, hm, heq⟩ := exists_conj_localInertia_of_adicCompletionHom CF w
    hℓ.toHeightOneSpectrumRingOfIntegersRat φ hφcomm hφloc σ n hn
  exact ⟨ℓ, hℓ, τ, m, hm, heq⟩

/-- **THE ABSORPTION STEP OF THE FROBENIUS COMPARISON** (PROVEN 2026-07-31).

This is everything in `globalFrob_map_mul_inv_mem_of_isArithFrobAt` below that
happens AFTER the geometry: once the discrepancy has been written in the shape

  `map ι₀ F · x⁻¹  =  (τ · map(n) · τ⁻¹) · (g · x · g⁻¹ · x⁻¹)`

with `n` a LOCAL INERTIA element at some rational prime `ℓ` and `g` in the image
of `Γ CF`, the two hypotheses `hNinert` and `hNab` put both factors into `N` and
`N` is a subgroup.  Isolated as its own lemma because it is independent of how
the decomposition is obtained, hence survives the repair of the falsity recorded
on that leaf — whatever the repair turns out to be, this is the last step.

**The `χ` bookkeeping is the only content.**  `hNinert` needs `χ` of the inertia
factor to be `1`, and that is not free: it is READ OFF the identity, from
`χ (map ι₀ F) = 1` (which is `hχCF`, i.e. "`Γ CF` maps into `ker χ`", the
consumer's `chi_map_eq_one_of_isCyclotomicExtension`) and `χ x = 1`, together
with the fact that a commutator of `ker χ` is killed by `χ` because `kk'` is
commutative.  `hχCF` is passed in rather than derived here: its proof needs
`[IsCyclotomicExtension {p} ℚ CF]` and the roots-of-unity computation, both of
which live in `Interface.lean` DOWNSTREAM of this module, and duplicating them
here would collide at merge with that file's own copy. -/
theorem mul_inv_mem_of_conj_localInertia_mul_commutator {p : ℕ} [Fact p.Prime]
    {kk' : Type u} [Field kk'] [Finite kk'] [Algebra ℤ_[p] kk'] [CharP kk' p]
    (χ : Field.absoluteGaloisGroup ℚ →* kk')
    (CF : Type) [Field CF] [NumberField CF]
    (hχCF : ∀ h : Field.absoluteGaloisGroup CF,
      χ (Field.absoluteGaloisGroup.map (algebraMap ℚ CF) h) = 1)
    (N : Subgroup (Field.absoluteGaloisGroup ℚ))
    (hNinert : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime)
        (n : Field.absoluteGaloisGroup
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hℓ.toHeightOneSpectrumRingOfIntegersRat))
        (σ : Field.absoluteGaloisGroup ℚ),
      n ∈ localInertiaGroup hℓ.toHeightOneSpectrumRingOfIntegersRat →
      χ (σ * Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hℓ.toHeightOneSpectrumRingOfIntegersRat)) n * σ⁻¹) = 1 →
      σ * Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hℓ.toHeightOneSpectrumRingOfIntegersRat)) n * σ⁻¹ ∈ N)
    (hNab : ∀ a b : Field.absoluteGaloisGroup ℚ, χ a = 1 → χ b = 1 →
      a * b * a⁻¹ * b⁻¹ ∈ N)
    (F : Field.absoluteGaloisGroup CF) (x : Field.absoluteGaloisGroup ℚ) (hx : χ x = 1)
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (n : Field.absoluteGaloisGroup
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hℓ.toHeightOneSpectrumRingOfIntegersRat))
    (hn : n ∈ localInertiaGroup hℓ.toHeightOneSpectrumRingOfIntegersRat)
    (τ : Field.absoluteGaloisGroup ℚ) (h : Field.absoluteGaloisGroup CF)
    (hdecomp : Field.absoluteGaloisGroup.map (algebraMap ℚ CF) F * x⁻¹
      = (τ * Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hℓ.toHeightOneSpectrumRingOfIntegersRat)) n * τ⁻¹)
        * (Field.absoluteGaloisGroup.map (algebraMap ℚ CF) h * x
            * (Field.absoluteGaloisGroup.map (algebraMap ℚ CF) h)⁻¹ * x⁻¹)) :
    Field.absoluteGaloisGroup.map (algebraMap ℚ CF) F * x⁻¹ ∈ N := by
  -- `χ` kills inverses of elements it kills: its values are units of `kk'`.
  have hinv : ∀ a : Field.absoluteGaloisGroup ℚ, χ a = 1 → χ a⁻¹ = 1 := by
    intro a ha
    have hmul : χ a * χ a⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rwa [ha, one_mul] at hmul
  set g : Field.absoluteGaloisGroup ℚ := Field.absoluteGaloisGroup.map (algebraMap ℚ CF) h with hg
  have hgχ : χ g = 1 := hχCF h
  -- the commutator factor is killed by `χ` because `kk'` is commutative
  have hcomm : χ (g * x * g⁻¹ * x⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, hgχ, hx, hinv g hgχ, hinv x hx]
    simp
  -- hence so is the inertia factor, being the quotient of two things `χ` kills
  have hinert : χ (τ * Field.absoluteGaloisGroup.map (algebraMap ℚ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hℓ.toHeightOneSpectrumRingOfIntegersRat)) n * τ⁻¹) = 1 := by
    have hlhs : χ (Field.absoluteGaloisGroup.map (algebraMap ℚ CF) F * x⁻¹) = 1 := by
      rw [map_mul, hχCF F, hinv x hx, one_mul]
    rw [hdecomp, map_mul, hcomm, mul_one] at hlhs
    exact hlhs
  rw [hdecomp]
  exact N.mul_mem (hNinert ℓ hℓ n τ hn hinert) (hNab g x hgχ hx)

/-- **TWO FROBENIUS ELEMENTS AT THE SAME PRIME OF `ℚ(μ_p)` AGREE MODULO `N`**
(SORRY LEAF, cut 2026-07-30 out of `Interface.lean`'s
`exists_zmodIdealSymbol_of_frobIdeal` — it is the "why the compatibility
clause is TRUE" paragraph of that leaf's docstring, and the only
non-plumbing content there).

`x` is assumed to be a Frobenius element at `w` in the strong,
finite-level sense the consumer can supply: for EVERY finite normal
`M/ℚ` inside `ℚ̄` carrying an `ι`-compatible copy `jj` of `CF`, the
restriction of `x` to `M` is an arithmetic Frobenius at some prime `Q` of
`𝓞 M` contracting along `jj` to `w`.  The conclusion says it then agrees
with the completion-theoretic `globalFrob w`, pushed down to `Γℚ`, modulo
`N`.

**ROUTE**, following the consumer's own docstring.  `globalFrob w` pushed
down to `Γℚ` is also a Frobenius element at `w`, by construction.  Two
Frobenius elements at the same prime `w` of a number field differ by an
element of the INERTIA subgroup at `w` composed with a conjugation by the
DECOMPOSITION group.  `hNinert` kills the inertia discrepancy — after the
transport of `exists_conj_localInertia_rat_of_localInertia` above, which is
why the two leaves are stated together — and `hNab` makes `Γℚ/N` receive
every commutator of `ker χ`, so `N` absorbs the conjugation as well: both
elements lie in `ker χ` (the image of `Γ CF` does, by `hχcyc`; and `x` by
`hx`), and conjugation is trivial on an abelian quotient.

**WHY `hχcyc` IS LOAD-BEARING AND NOT DECORATION.** `hNab` only supplies
commutators of elements of `ker χ`.  The conjugating element produced by
the decomposition-group step is a priori an arbitrary element of `Γℚ`, and
for it to be absorbed it must be recognised as lying in `ker χ` — which is
`Γ_{ℚ(μ_p)}` precisely because `χ` is the mod-`p` cyclotomic character.
This is the same identification (item 1 of the consumer's list) that makes
`Γ CF → ker χ` well defined.

**Why `hNker` is NOT among the hypotheses.** The argument needs `N ⊆ ker χ`
nowhere; it only ever needs to put elements INTO `N`.  The consumer holds
`hNker` and discards it here deliberately.

**The check that would refute it**: a prime `w` and two Frobenius elements
at `w` whose ratio is outside `N` — which, `N` containing every conjugate
of every inertia subgroup meeting `ker χ` and every commutator of `ker χ`,
would contradict the standard description of the Frobenius conjugacy class
at an unramified prime.

---

**FALSITY AUDIT, 2026-07-31: THIS LEAF IS FALSE AS STATED, AND THE DEFECT IS
`ι`.  DO NOT ATTEMPT TO PROVE IT — the repair is a STATEMENT change and it
belongs to whoever owns `Interface.lean`'s side of the interface.**

The statement mixes TWO DIFFERENT embeddings of `CF` into `ℚ̄`, and is only true
when they agree.

* `hxfrob` pins `x` through the PARAMETER `ι`: the prime `Q` at which `x|_M` is
  an arithmetic Frobenius contracts along `jj` — and `jj` is `ι` corestricted —
  to `w`.  So `x` is a Frobenius above `ι(w)`.
* `GaloisRepresentation.globalFrob w` pins the other side through the embedding
  `IsAlgClosed.lift : ℚ̄ →ₐ[ℚ] CFᵃˡᵍ` buried in
  `Field.absoluteGaloisGroup.mapAux` (`AbsoluteGaloisGroup.lean:50`), which is
  arbitrary but FIXED and has nothing to do with `ι`.  Write `ι₀` for the copy of
  `CF` in `ℚ̄` that it determines.  So `map ι₀ (globalFrob w)` is a Frobenius
  above `ι₀(w)`.

`CF` is cyclotomic, hence Galois over `ℚ`, so `ι` and `ι₀` have the SAME image
`F ⊆ ℚ̄` and differ by `γ := ι₀⁻¹ ∘ ι ∈ Gal(CF/ℚ)`.  The two sides are therefore
Frobenius elements above `ι₀(γ w)` and `ι₀(w)` — DIFFERENT primes of `F` unless
`γ` fixes `w`.  In `ker χ / N` the Artin symbol sees exactly that difference, so
the conclusion asks for `[w] = [γ w]` in a class group, which is false as soon as
`Gal(CF/ℚ)` moves the class of `w`.

**EXPLICIT COUNTEREXAMPLE** (PARI/GP, verified 2026-07-31 — witnesses only, the
arithmetic below is standard).  Take `p = 23`, `CF = ℚ(μ₂₃)`:

* `bnfinit(polcyclo(23)).cyc = [3]`, so `Cl(CF) ≅ ℤ/3`; and
  `bnfinit(polsubcyclo(23,11)).no = 1`, so `h⁺ = 1` and `Cl = Cl⁻`, i.e. complex
  conjugation `c : ζ ↦ ζ⁻¹` acts on `Cl(CF)` by `−1`.
* `ℓ = 47 ≡ 1 (mod 23)` splits completely: `idealprimedec` gives 22 primes of
  residue degree 1, with classes
  `[1,1,1,1,1,2,2,1,1,2,1,2,1,1,2,2,2,2,2,2,1,2]` — and for `P₁` in particular
  `bnfisprincipal` returns class `1` while `nfgaloisapply` by `x ↦ x²²`
  (= complex conjugation) sends it to a prime of class `2`.

So put `w := P₁`, `γ := c`, `ι := ι₀ ∘ c`.  Take `N := Γ_H` for `H` the Hilbert
class field of `CF`; `N` satisfies both hypotheses — `hNinert` because `H/CF` is
unramified at every finite place, so any inertia element lying in `ker χ = Γ_F`
restricts trivially to `H`, and `hNab` because `Gal(H/CF) = Cl(CF)` is abelian.
Let `x` be a Frobenius at a prime of `ℚ̄` above `ι(w) = ι₀(c w)`; `ℓ` splits
completely in `F`, so `x ∈ Γ_F = ker χ` and `hx` holds, and `hxfrob` holds by
construction.  Then `map ι₀ (globalFrob w) · x⁻¹` maps to `[w] · [c w]⁻¹ =
[w] · [w] = [w]² ≠ 1` in `Gal(H/CF) = Cl(CF) ≅ ℤ/3`, i.e. it is NOT in `N`.

**WHY NO EARLIER CHECK CAUGHT IT.**  The leaf is `ι`-covariant on one side and
`ι`-blind on the other, and neither side is wrong by itself; the docstring's own
route is correct once the two primes coincide.  In particular the "`hχcyc` is
load-bearing" paragraph above is RIGHT about the absorption step and says nothing
about which prime each side sits over — the conjugator `g` does lie in `ker χ`,
but only because transitivity on the primes above a FIXED prime of `F` is by
`Γ_F`, which presupposes the two primes lie over the same one.

**THE TWO CANDIDATE REPAIRS**, neither of which can be made from inside this
module, since both change what the consumer must supply:

1. *Pin `ι`.*  Add
   `hι : ∀ z : CF, AlgebraicClosure.map (algebraMap ℚ CF) (ι z) =
     algebraMap CF (AlgebraicClosure CF) z`
   (i.e. `ι = ι₀`) here, and thread it up through
   `Interface.lean`'s `exists_zmodIdealSymbol_of_frobIdeal` and
   `prod_frobConj_mem_of_mk0_prod_frobIdeal_eq_one_of_primePowChar`, which both
   carry `ι` as a free parameter.  Cheapest at this end, a cascade at the other.
2. *Twist the symbol instead.*  `exists_zmodIdealSymbol_of_frobIdeal` produces
   its `c` EXISTENTIALLY, so its proof may instead define the symbol by
   `c(w) := χ'(globalFrob (γ⁻¹ w))`.  Nothing above it changes, but `hcfrob`
   (`c` pinned at every height-one prime by `χ' ∘ globalFrob`) must be restated
   with the same twist, and `γ` must be produced from `ι` — which needs
   `IsAlgClosed.lift` to be compared with `ι`, i.e. `exists_conj_of_two_embeddings`
   above.

Route 2 is the one that keeps the interface, and `exists_conj_of_two_embeddings`
— already proven in this file, for exactly this class of problem — is most of
what it needs.  **Recorded here rather than acted on because changing either
statement breaks `Interface.lean`, which is not this module's to break.**

What SURVIVES the repair unchanged is the last step,
`mul_inv_mem_of_conj_localInertia_mul_commutator` immediately above: it is
proven, and it consumes only the shape of the discrepancy, not the geometry that
produces it. -/
theorem globalFrob_map_mul_inv_mem_of_isArithFrobAt {p : ℕ} [hp : Fact p.Prime]
    {kk' : Type u} [Field kk'] [Finite kk'] [Algebra ℤ_[p] kk'] [CharP kk' p]
    (χ : Field.absoluteGaloisGroup ℚ →* kk')
    (hχcyc : ∀ g : Field.absoluteGaloisGroup ℚ, χ g =
      algebraMap ℤ_[p] kk'
        (cyclotomicCharacter (AlgebraicClosure ℚ) p g.toRingEquiv))
    (CF : Type) [Field CF] [NumberField CF] [IsCyclotomicExtension {p} ℚ CF]
    (ι : CF →ₐ[ℚ] AlgebraicClosure ℚ)
    (N : Subgroup (Field.absoluteGaloisGroup ℚ))
    (hNinert : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime)
        (n : Field.absoluteGaloisGroup
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hℓ.toHeightOneSpectrumRingOfIntegersRat))
        (σ : Field.absoluteGaloisGroup ℚ),
      n ∈ localInertiaGroup hℓ.toHeightOneSpectrumRingOfIntegersRat →
      χ (σ * Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hℓ.toHeightOneSpectrumRingOfIntegersRat)) n * σ⁻¹) = 1 →
      σ * Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hℓ.toHeightOneSpectrumRingOfIntegersRat)) n * σ⁻¹ ∈ N)
    (hNab : ∀ a b : Field.absoluteGaloisGroup ℚ, χ a = 1 → χ b = 1 →
      a * b * a⁻¹ * b⁻¹ ∈ N)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 CF))
    (x : Field.absoluteGaloisGroup ℚ) (hx : χ x = 1)
    (hxfrob : ∀ (M : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ M]
        [Normal ℚ M] (jj : CF →ₐ[ℚ] M),
        (∀ z : CF, algebraMap M (AlgebraicClosure ℚ) (jj z) = ι z) →
        ∃ Q : Ideal (𝓞 M), Q.IsPrime ∧
          IsArithFrobAt (𝓞 ℚ) (AlgEquiv.restrictNormalHom M x) Q ∧
          Ideal.comap (NumberField.RingOfIntegers.mapRingHom (jj : CF →+* M)) Q =
            w.asIdeal) :
    Field.absoluteGaloisGroup.map (algebraMap ℚ CF)
        (GaloisRepresentation.globalFrob w) * x⁻¹ ∈ N :=
  sorry

end NumberField
