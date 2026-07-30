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
-- `IsArithFrobAt`.
public import Mathlib.RingTheory.Frobenius
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

/-- **INERTIA TRANSPORT: A LOCAL INERTIA ELEMENT OF A NUMBER FIELD, PUSHED
DOWN TO `Γℚ`, IS A CONJUGATE OF A LOCAL INERTIA ELEMENT OF `ℚ`** (SORRY
LEAF, cut 2026-07-30 out of `Interface.lean`'s
`exists_zmodIdealSymbol_of_frobIdeal` — it is item 3 of that leaf's own
"what must be built" list, "`hunr` from `hNinert`").

`Interface.lean` measures unramifiedness of the constructed character `χ'`
by inertia subgroups inside `Γ CF`, while the hypothesis it is given
(`hNinert`) measures it by inertia subgroups inside `Γℚ`.  This leaf is
exactly the conversion, and it mentions no character at all.

**ROUTE.** Let `ℓ` be the residue characteristic of `w`, i.e. the rational
prime under `w`.  Then `CF_w / ℚ_ℓ` is a finite extension of local fields,
so there is an embedding `ℚ_ℓ → CF_w`, and the induced
`Γ CF_w → Γ ℚ_ℓ` carries `localInertiaGroup w` into
`localInertiaGroup ℓ`: inertia is defined by acting trivially on the
residue field of the integral closure of the valuation ring in the
algebraic closure, and that integral closure is the SAME ring for `CF_w`
and for `ℚ_ℓ` once the algebraic closures are identified — `CF_w^alg` is an
algebraic closure of `ℚ_ℓ` as well.

**WHY THE CONCLUSION IS STATED UP TO CONJUGACY, AND WHY IT MUST BE.**
`Field.absoluteGaloisGroup.map` is built from `IsAlgClosed.lift`, an
ARBITRARILY CHOSEN embedding of algebraic closures, so there is no
functoriality equation `map f ∘ map g = map (g ∘ f)` — and none exists in
the pin or in this project (the point is recorded explicitly at
`KhareWintenberger.lean:3402`).  The two routes `Γ CF_w → Γ CF → Γℚ` and
`Γ CF_w → Γ ℚ_ℓ → Γℚ` therefore agree only after conjugation by some
`τ ∈ Γℚ`, because any two `ℚ`-embeddings `ℚ̄ → CF_w^alg` have the same image
(the algebraic closure of `ℚ` inside `CF_w^alg`) and hence differ by an
element of `Γℚ`.  Supplying that `τ` is the substance of the proof.

This costs the consumer nothing: `hNinert` already quantifies over an
arbitrary conjugating `σ ∈ Γℚ`, which is precisely why it was stated that
way.

**The check that would refute it**: a number field `CF`, a prime `w`, and
an element of `localInertiaGroup w` whose image in `Γℚ` acts nontrivially
on the maximal unramified extension of `ℚ_ℓ` — which would contradict
`e(w/ℓ) · f(w/ℓ) ≤ [CF : ℚ] < ∞` and the fact that inertia upstairs maps
into inertia downstairs in any tower. -/
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
              hℓ.toHeightOneSpectrumRingOfIntegersRat)) m * τ⁻¹ :=
  sorry

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
at an unramified prime. -/
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
