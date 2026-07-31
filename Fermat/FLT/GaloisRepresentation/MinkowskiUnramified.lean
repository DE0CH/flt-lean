/-
MinkowskiUnramified.lean — own work for the Fermat project (not vendored
from the FLT project).

**Everywhere-unramified characters of `ℚ` are trivial**, and the
inertia-to-ideal-inertia bridge they rest on.

HOISTED 2026-07-27, VERBATIM, out of
`Fermat/FLT/FreyCurve/MazurTorsion.lean`, where this block sat ~27000
lines BELOW its first would-be consumer (the isogeny-character section
of Mazur's isogeny theorem).  Lean has no forward references, so that
part of the file could not use its own file's Minkowski node; leaf `C`,
`WeierstrassCurve.isogenyCharacter_pow_twelve_eq_of_localInertia`, stayed
sorried for that reason alone.  The block was checked to depend only on
the imports below and on nothing else declared in `MazurTorsion`, so it
lives here and `MazurTorsion` `public import`s it.

Every NAME and STATEMENT is unchanged, so all downstream use sites —
`InertiaCardTransport.lean`, `HardlyRamified/{Family,ModThree,
HermiteMinkowski,HilbertModularity}.lean`, `Modularity/Interface.lean` —
keep resolving without edits.

SECOND HOIST, 2026-07-31: the inertia dictionary proper — the four
theorems `exists_prime_over_inertia_eq_bot_of_le_fixingSubgroup`,
`inertia_eq_bot_of_exists_prime_over`,
`inertia_eq_bot_of_le_fixingSubgroup` and
`isUnramifiedAt_of_inertia_le_fixingSubgroup` — moved on to
`Fermat/FLT/GaloisRepresentation/InertiaUnramified.lean`, which this file
now `public import`s, so every name below and downstream still resolves.
The reason is the same shape as the first hoist: `ModularCurve/X0.lean`
needs the dictionary, and this file is downstream of it, but only because
of the `Chebotarev` import that `isOpen_setOf_galoisRep_eq_one` (the LAST
declaration here) needs.  The dictionary needs none of that.

Contents, in dependency order:

* `open_normal_subgroup_eq_top_of_inertia_le` — Minkowski's discriminant
  theorem in subgroup form: an open subgroup of `Γ ℚ` containing every
  local inertia image is everything.
* `minkowski_character_trivial` — its character form.
* `isOpen_setOf_galoisRep_eq_one` — openness of the triviality locus of a
  Galois representation over a discrete field; hoisted with the block
  because deriving the open-kernel hypothesis of
  `minkowski_character_trivial` for a character coming from torsion
  points needs it, and it was equally stranded below.
-/

module

-- `localInertiaGroup`, `Field.absoluteGaloisGroup.map` and `lift_map`.
public import Fermat.FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
-- The inertia-to-discriminant dictionary, hoisted 2026-07-31 so that
-- `ModularCurve/X0.lean` can reach it without Chebotarev.
public import Fermat.FLT.GaloisRepresentation.InertiaUnramified
-- The local inertia-fixed-field node
-- (`maximalIdeal_map_eq_of_le_fixedField_localInertiaGroup`): `e(M/ℚ_q) = 1`
-- for finite subextensions of `ℚ_qᵃˡᵍ` fixed by the local inertia.
public import Fermat.FLT.Deformations.RepresentationTheory.LocalInertiaFixedField
-- `Nat.Prime.toHeightOneSpectrumRingOfIntegersRat` and
-- `maximalIdeal_adicCompletionIntegers_eq_span`.
public import Fermat.FLT.Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
-- `GaloisRep` and its continuity field.
public import Fermat.FLT.Deformations.RepresentationTheory.GaloisRep
-- `GaloisRepresentation.discreteTopology_moduleTopology`.
public import Fermat.FLT.GaloisRepresentation.Chebotarev
-- Minkowski's discriminant theorem
-- (`exists_not_isUnramifiedAt_int_of_isGalois`) and the going-up prime
-- lifting, used in the Minkowski assembly proof.
public import Mathlib.NumberTheory.NumberField.ExistsRamified
public import Mathlib.RingTheory.Ideal.GoingUp
-- `Ideal.inertia` and `Ideal.card_inertia_eq_ramificationIdxIn`.
public import Mathlib.NumberTheory.RamificationInertia.Galois

-- The block lived inside `MazurTorsion.lean`'s `@[expose] public section`
-- (its line 203); replicating that here is what keeps the hoist a no-op for
-- consumers — without it the declarations would not be exported at all.
@[expose] public section


set_option backward.isDefEq.respectTransparency false in
/-- **Minkowski, subgroup form** (DERIVED 2026-07-16 from the inertia
dictionary and mathlib's discriminant theory): an open normal subgroup
of `G_ℚ` containing the image of the local inertia group at every prime
is everything. Assembly: the fixed field `L` of `H` recovers `H` by the
infinite Galois correspondence (`H` is closed since open); `L` is a
finite Galois number field (`isOpen_iff_finite`, `normal_iff_isGalois`);
if `H ≠ ⊤` then `L ≠ ⊥` so `1 < finrank ℚ L`, and
`exists_not_isUnramifiedAt_int_of_isGalois` produces a prime `p` all of
whose primes in `𝓞 L` are ramified; but the inertia hypothesis plus the
dictionary make the lifted prime above `p` unramified — contradiction. -/
theorem open_normal_subgroup_eq_top_of_inertia_le
    (H : Subgroup (Field.absoluteGaloisGroup ℚ)) [hnorm : H.Normal]
    (hopen : IsOpen (H : Set (Field.absoluteGaloisGroup ℚ)))
    (hinertia : ∀ (q : ℕ) (hq : q.Prime),
      Subgroup.map (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom
        (localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat) ≤ H) :
    H = ⊤ := by
  haveI hgal : IsGalois ℚ (AlgebraicClosure ℚ) := inferInstance
  by_contra hne
  have hclosed : IsClosed (H : Set (Field.absoluteGaloisGroup ℚ)) :=
    Subgroup.isClosed_of_isOpen H hopen
  set L : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.fixedField (E := AlgebraicClosure ℚ) H
  have hfix : L.fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨H, hclosed⟩
  haveI hfd : FiniteDimensional ℚ L :=
    (InfiniteGalois.isOpen_iff_finite L).mp (by rw [hfix]; exact hopen)
  haveI hgalL : IsGalois ℚ L := (InfiniteGalois.normal_iff_isGalois L).mp
    (by rw [hfix]; exact hnorm)
  haveI : NumberField L := ⟨⟩
  have hrank : 1 < Module.finrank ℚ L := by
    rcases Nat.lt_or_ge 1 (Module.finrank ℚ L) with h | h
    · exact h
    · exfalso
      have h0 : 0 < Module.finrank ℚ L := Module.finrank_pos
      have h1 : Module.finrank ℚ L = 1 := by omega
      apply hne
      rw [← hfix, IntermediateField.finrank_eq_one_iff.mp h1,
        IntermediateField.fixingSubgroup_bot]
  obtain ⟨p, hp, hram⟩ := NumberField.exists_not_isUnramifiedAt_int_of_isGalois
    (K := L) (𝒪 := NumberField.RingOfIntegers L) hrank
  -- lift `p` to a prime of `𝓞 L`
  haveI := IsIntegralClosure.isIntegral_algebra ℤ (A := NumberField.RingOfIntegers L) L
  have hpZ : Prime ((p : ℤ)) := Nat.prime_iff_prime_int.mp hp
  haveI hPspan : (Ideal.span {((p : ℤ))} : Ideal ℤ).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr hpZ
  have hker : RingHom.ker (algebraMap ℤ (NumberField.RingOfIntegers L)) ≤
      Ideal.span {((p : ℤ))} := by
    intro x hx
    have hx0 : algebraMap ℤ (NumberField.RingOfIntegers L) x = 0 := hx
    have hxL : algebraMap ℤ L x = 0 := by
      rw [IsScalarTower.algebraMap_eq ℤ (NumberField.RingOfIntegers L) L, RingHom.comp_apply,
        hx0, map_zero]
    have : (x : ℤ) = 0 := by
      have := congrArg (fun y => y) hxL
      exact_mod_cast (by simpa using hxL : ((x : ℤ) : L) = 0)
    rw [this]
    exact Ideal.zero_mem _
  obtain ⟨Q, hQprime, hQcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
      (S := NumberField.RingOfIntegers L) (Ideal.span {((p : ℤ))}) hker
  haveI := hQprime
  have hpQ : ((p : ℕ) : NumberField.RingOfIntegers L) ∈ Q := by
    have hmem : ((p : ℤ)) ∈ Ideal.span {((p : ℤ))} :=
      Ideal.subset_span rfl
    rw [← hQcomap] at hmem
    have := Ideal.mem_comap.mp hmem
    simpa using this
  exact hram Q hQprime hpQ
    (isUnramifiedAt_of_inertia_le_fixingSubgroup L hp
      (le_trans (hinertia p hp) (le_of_eq hfix.symm)) Q hpQ)

/-- **Minkowski for mod-`p` characters** (DERIVED 2026-07-16 from the
subgroup form): a character `χ : G_ℚ → (ℤ/p)ˣ` with open kernel that is
unramified at every finite place (the local inertia group at every
prime `q` is killed by the restriction of `χ` to `G_{ℚ_q}`) is trivial.
The kernel is an open normal subgroup containing every inertia image,
hence everything. -/
theorem minkowski_character_trivial {T : Type*} [Group T]
    (χ : Field.absoluteGaloisGroup ℚ →* T)
    (hker : IsOpen (χ.ker : Set (Field.absoluteGaloisGroup ℚ)))
    (hunram : ∀ (q : ℕ) (hq : q.Prime),
      localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat ≤
        (χ.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker) :
    χ = 1 := by
  have hker_top : χ.ker = ⊤ := by
    refine open_normal_subgroup_eq_top_of_inertia_le χ.ker hker ?_
    intro q hq
    rw [Subgroup.map_le_iff_le_comap]
    intro σ hσ
    have h := hunram q hq hσ
    rw [MonoidHom.mem_ker] at h
    rw [Subgroup.mem_comap, MonoidHom.mem_ker]
    exact h
  ext g
  have hg : g ∈ χ.ker := hker_top ▸ Subgroup.mem_top g
  simpa [MonoidHom.mem_ker] using hg

set_option backward.isDefEq.respectTransparency false in
/-- **Openness of the kernel-level set of a mod-`ℓ`-style representation over a discrete field**
(PROVEN): the set where the representation is trivial is open — the
endomorphism space is discrete (finite module over the discrete
`F`), so the representation is locally constant. Stated with the
finiteness input as a plain hypothesis so that callers can supply it
for any definitionally-equal spelling of `V`. -/
lemma isOpen_setOf_galoisRep_eq_one {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [DiscreteTopology F]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρbar : GaloisRep ℚ F V) (hfinV : Finite V) :
    IsOpen {g : Field.absoluteGaloisGroup ℚ | ρbar g = 1} := by
  haveI := hfinV
  letI := moduleTopology F (Module.End F V)
  haveI : Finite (Module.End F V) :=
    Finite.of_injective (fun f => (f : V → V)) DFunLike.coe_injective
  haveI : Module.Finite F (Module.End F V) :=
    Module.Finite.of_finite
  haveI : DiscreteTopology (Module.End F V) :=
    GaloisRepresentation.discreteTopology_moduleTopology F
      (Module.End F V)
  have hcont : Continuous fun g : Field.absoluteGaloisGroup ℚ => ρbar g :=
    ρbar.continuous_toFun
  exact (isOpen_discrete ({1} : Set (Module.End F V))).preimage hcont
