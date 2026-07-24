/-
Modularity/Patching.lean — own work for the Fermat project (not
vendored from the FLT project).

# The deformation-theoretic cut behind `R = 𝕋` (pillar 3b of the
Taylor–Wiles section of `Modularity/Interface.lean`)

This module opens the deformation-theoretic subtree behind the
patching pillar `exists_ringHom_charFrob_eq_of_heckeDeformation`
(`Modularity/Interface.lean`, pillar 3b): a hardly ramified `p`-adic
representation `ρ` over `R` whose residual representation is
irreducible and underlies a Hecke-side hardly ramified deformation
`(T, ρT, π)` factors through that deformation on Frobenius traces via
a ring homomorphism `Φ : T →+* R`.  Following the actual architecture
of the Wiles/Taylor–Wiles proof, the pillar is cut into the three
classical deformation-theoretic statements, each stated against the
vocabulary of `Fermat/FLT/Deformations/RepresentationTheory/`
(`GaloisRep`, `charFrob`, `IsUnramifiedAt`/`IsFlatAt` through
`IsHardlyRamified`) and sorried with its literature route recorded:

* **Mazur representability**
  (`exists_weaklyUniversal_hardlyRamifiedDeformation`): the hardly
  ramified deformation problem of an irreducible residual `ρbar` has
  a weakly universal object `(Runiv, ρuniv, πuniv)` in Mazur's
  category — a complete Noetherian local topological `ℤ_p`-algebra —
  through which every hardly ramified deformation over a
  module-finite local `ℤ_p`-algebra factors on Frobenius traces.
  PROVEN 2026-07-24 over two sorried leaves, mirroring `Lift.lean`'s
  accepted decomposition of its parallel (downstream) stratum: the
  strict representability leaf
  `exists_weaklyUniversalOnIdentified_hardlyRamifiedDeformation`
  (Mazur/Ramakrishna/CDT proper, factoring residually identified
  deformations) and the Chebotarev–Brauer–Nesbitt conjugacy leaf
  `exists_conj_of_charFrob_eq_away`; the upgrade glue — automatic
  continuity and `ℤ_p`-rigidity of the reduction maps, determinant
  pinning of the constant `charFrob` coefficient, monic-quadratic
  reconstruction from the trace datum — is proven in this module.
* **Carayol trace generation — the surjection `R_univ ↠ 𝕋`**
  (`surjective_ringHom_of_charFrob_eq`): every trace-compatible ring
  homomorphism from the universal object to the Hecke-side
  deformation is surjective.
* **Taylor–Wiles patching — `R = 𝕋`**
  (`injective_ringHom_of_isWeaklyUniversal`): every trace-compatible
  ring homomorphism from a weakly universal object to the Hecke-side
  deformation is injective.

The assembly (pillar 3b's proof, in `Modularity/Interface.lean`)
classifies both the Hecke package `(T, ρT, π)` and `ρ` itself by maps
out of `Runiv` (two instances of the weak-universality clause),
upgrades the `T`-side classifying map to a ring isomorphism
`Runiv ≃+* T` by the two pillars above, and takes `Φ` to be the
composite `T ≃+* Runiv →+* R`.

## Vocabulary, and its relation to `HardlyRamified/Lift.lean`

`Lift.lean` already develops a hardly ramified deformation vocabulary
(`HardlyRamifiedDeformation`, `IsUniversal`/`IsWeaklyUniversal`,
`IsTraceGenerated`, Mazur representability at `ℓ ≥ 5`) — but for the
residual coefficient field `ZMod ℓ` only and, decisively, DOWNSTREAM
of this module's consumer: `Lift.lean` imports `Family.lean`, which
imports `Modularity/Interface.lean`.  The circularity guard on pillar
3b ("never through `Family.lean`") is therefore structural — reusing
that vocabulary would be an import cycle — and this module states the
parallel vocabulary UPSTREAM (importing only `HardlyRamified/Defs`),
generalized from `ZMod ℓ` to the abstract finite residue fields the
interface's Taylor–Wiles section quantifies over.  The statement
shapes (the compatibility triple `ℤ_p`-structure/reduction/`charFrob`,
the weak-universality clause) are aligned with `Lift.lean`'s so that
a future de-duplication can identify the two developments.

## Design notes (SOUNDNESS AUDIT, 2026-07-24)

* **Trace-only compatibility.**  All reduction and factorization
  clauses carry only the LINEAR `charFrob` coefficient (the trace up
  to sign), matching the Taylor–Wiles section's convention, and each
  clause holds away from an existentially quantified finite
  exceptional set of places.  Against the full-charpoly convention of
  `Lift.lean` no information is lost: the representations are rank 2,
  `charFrob` is monic of degree 2, and the hardly ramified
  determinant condition pins the constant coefficient to the fixed
  cyclotomic value, so at every good prime the trace determines the
  whole `charFrob`.
* **Module-finite test category.**  Weak universality is tested
  against deformations over module-finite local `ℤ_p`-algebras
  carrying the `ℤ_p`-module topology
  (`HardlyRamifiedFiniteDeformation`) — the exact shape of the
  interface's `R` and `T`.  Classically these are complete Noetherian
  local rings with the `𝔪`-adic topology (mod `p` the ring is
  Artinian local, so `𝔪` is nilpotent mod `p` and the `p`-adic and
  `𝔪`-adic topologies agree; completeness is inherited from `ℤ_p` by
  module-finiteness), hence legitimate test objects of Mazur's
  category — the clause is the restriction of the genuine universal
  property to that subcategory, which is exactly what the assembly
  consumes.
* **Trace-level reduction data.**  A test deformation reduces to
  `ρbar` only trace-by-trace off a finite set (`charFrob_compat`),
  not by an isomorphism of its residual representation with `ρbar`.
  Classically the two are equivalent under the standing residual
  irreducibility: traces off a finite set determine the residual
  semisimplification everywhere (continuity plus Chebotarev density
  plus Brauer–Nesbitt), and a deformation whose residual
  semisimplification is the irreducible `ρbar` can be conjugated into
  an honest lift of `ρbar` (Carayol, *Formes modulaires et
  représentations galoisiennes à valeurs dans un anneau local
  complet*, Contemp. Math. 165 (1994), Théorème 1).
* **Abstract quantification.**  As everywhere in the Taylor–Wiles
  section (see the section docstring in `Interface.lean`), the
  Hecke-side package `(T, ρT, π)` and the universal-side package
  range over ALL data of the stated shape, not only the genuine
  `𝕋_𝔪` and `R_univ` for which the literature proves the pillars.
  Every pillar's hypothesis set includes an IRREDUCIBLE hardly
  ramified residual representation, which the classical chain of the
  section audit (residual modularity → level optimization →
  `S₂(Γ₀(2)) = 0`) shows to be unsatisfiable — so each pillar is
  classically true outright, while its intended discharge
  instantiates the genuine objects, for which it is verbatim the
  cited literature statement.  This both-ways audit is repeated in
  each declaration's docstring.
-/
module

public import Fermat.FLT.GaloisRepresentation.HardlyRamified.Defs
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Algebra.CharP.Basic
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

namespace GaloisRepresentation.Modularity

open IsDedekindDomain
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
/-- **`charFrob` commutes with base change** (PROVEN): the Frobenius
characteristic polynomial of `ρ.baseChange B` at a finite place is the
image under `algebraMap A B` of that of `ρ`.  Unfolds `charFrob` to
the charpoly of the localized representation at the arithmetic
Frobenius, identifies the base-changed endomorphism with
`LinearMap.baseChange` (definitional through the exposed module
exports), and finishes by mathlib's `LinearMap.charpoly_baseChange`.
This is the bridge that lets the pillar-3b assembly present the
`p`-adic representation `ρ` itself as a deformation of its own
residual representation `ρ.baseChange kk`: the reduction datum
`algebraMap R kk ∘ (coeff 1 of charFrob ρ) = coeff 1 of charFrob
(ρ.baseChange kk)` holds at EVERY place, with empty exceptional set.
(`Family.lean` proves the conjugated variant `charFrob_baseChange_conj`
by the same route; it lives downstream of this module's consumer and
cannot be imported here.) -/
lemma charFrob_baseChange {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] {B : Type*} [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [Algebra A B] [ContinuousSMul A B]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Free A M]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (ρ : GaloisRep ℚ A M) :
    (ρ.baseChange B).charFrob v = (ρ.charFrob v).map (algebraMap A B) := by
  show ((ρ.baseChange B).toLocal v
      (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly =
    ((ρ.toLocal v (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly).map
      (algebraMap A B)
  rw [show (ρ.baseChange B).toLocal v
        (Field.AbsoluteGaloisGroup.adicArithFrob v) =
      LinearMap.baseChange B (ρ.toLocal v
        (Field.AbsoluteGaloisGroup.adicArithFrob v)) from rfl,
    LinearMap.charpoly_baseChange]

/-!
## `p`-adic coefficient glue (PROVEN)

The residual coefficient field `k` of the Taylor–Wiles section is an
abstract finite field carrying a `ℤ_p`-algebra structure.  Three
elementary facts about such fields drive the assembly of Mazur
representability below: any ring homomorphism `ℤ_p →+* k` forces
`k` to have characteristic `p` (the kernel is a nonzero prime of the
DVR `ℤ_p`, necessarily `(p)`); any two ring homomorphisms
`ℤ_p →+* k` coincide (both kill `p` and agree on the dense first
digit `x.appr 1`); and any ring homomorphism `ℤ_p →+* k` into the
discrete `k` is continuous (it is constant on cosets of the open
ideal `(p) = ball 0 1`).  These are what make the reduction maps of
`HardlyRamifiedFiniteDeformation`s automatically continuous and
`ℤ_p`-compatible.
-/

/-- **A finite field receiving `ℤ_p` has characteristic `p`** (PROVEN):
the kernel of a ring homomorphism `f : ℤ_p →+* k`, `k` a finite field,
is a nonzero ideal (else the infinite `ℤ_p` embeds in the finite `k`)
that is prime (the target is a domain), hence — by the DVR ideal
classification of `ℤ_p` — contains `p`; so `(p : k) = 0` and the
characteristic, a prime dividing `p`, is `p` itself. -/
lemma charP_of_ringHom_padicInt {p : ℕ} [Fact p.Prime] {k : Type*}
    [Field k] [Finite k] (f : ℤ_[p] →+* k) : CharP k p := by
  have hker : RingHom.ker f ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective f := by
      rw [RingHom.injective_iff_ker_eq_bot]
      exact hbot
    haveI := Finite.of_injective f hinj
    exact not_finite ℤ_[p]
  obtain ⟨n, hn⟩ := PadicInt.ideal_eq_span_pow_p hker
  have hpmem : (p : ℤ_[p]) ∈ RingHom.ker f := by
    have hpow : (p : ℤ_[p]) ^ n ∈ RingHom.ker f := by
      rw [hn]
      exact Ideal.mem_span_singleton_self _
    exact (RingHom.ker_isPrime f).mem_of_pow_mem n hpow
  have hpk : (p : k) = 0 := by
    rw [RingHom.mem_ker, map_natCast] at hpmem
    exact hpmem
  have hdvd : ringChar k ∣ p := (CharP.cast_eq_zero_iff k (ringChar k) p).mp hpk
  rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd _ hdvd with h1 | hp
  · exact absurd
      (show (1 : k) = 0 by
        rw [← Nat.cast_one, ← h1]
        exact CharP.cast_eq_zero k (ringChar k))
      one_ne_zero
  · exact ringChar.of_eq hp

/-- **Rigidity of `ℤ_p`-points of a finite field** (PROVEN): any two
ring homomorphisms `ℤ_p →+* k` into a finite field agree.  Both kill
`p` (`k` has characteristic `p` by `charP_of_ringHom_padicInt`), and
every `x : ℤ_p` is `x.appr 1 + p·z` with `x.appr 1 : ℕ`, on which any
ring homomorphism is the natural-number cast.  This is what turns the
`ℤ_p`-structure compatibility `π ∘ algebraMap = algebraMap` of the
deformation vocabulary into a theorem rather than a datum. -/
lemma ringHom_padicInt_eq {p : ℕ} [Fact p.Prime] {k : Type*}
    [Field k] [Finite k] (f g : ℤ_[p] →+* k) : f = g := by
  haveI := charP_of_ringHom_padicInt f
  ext x
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp
    (by simpa using PadicInt.appr_spec 1 x)
  have hx : x = (x.appr 1 : ℤ_[p]) + (p : ℤ_[p]) * c := by
    rw [← hc]
    ring
  rw [hx]
  simp

/-- **Automatic continuity into a discrete finite field** (PROVEN): a
ring homomorphism `ℤ_p →+* k`, `k` a finite discrete field, is
continuous — it kills the ideal `(p)`, which is the open unit ball of
`ℤ_p`, so it is locally constant. -/
lemma continuous_ringHom_padicInt {p : ℕ} [Fact p.Prime] {k : Type*}
    [Field k] [Finite k] [TopologicalSpace k] [DiscreteTopology k]
    (f : ℤ_[p] →+* k) : Continuous f := by
  haveI := charP_of_ringHom_padicInt f
  have hopen : IsOpen ((Ideal.span {(p : ℤ_[p])} : Ideal ℤ_[p]) : Set ℤ_[p]) := by
    have hball : ((Ideal.span {(p : ℤ_[p])} : Ideal ℤ_[p]) : Set ℤ_[p]) =
        Metric.ball (0 : ℤ_[p]) 1 := by
      ext x
      simp only [SetLike.mem_coe, Ideal.mem_span_singleton, Metric.mem_ball,
        dist_zero_right]
      exact (PadicInt.norm_lt_one_iff_dvd x).symm
    rw [hball]
    exact Metric.isOpen_ball
  apply continuous_of_continuousAt_zero f
  unfold ContinuousAt
  rw [map_zero, nhds_discrete k, Filter.tendsto_pure]
  filter_upwards [hopen.mem_nhds (Submodule.zero_mem _)] with x hx
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hx
  rw [hc, map_mul, map_natCast, CharP.cast_eq_zero k p, zero_mul]

/-!
## Frobenius characteristic-polynomial glue (PROVEN)

`charFrob` at a rank-2 representation is monic of degree 2, and for a
hardly ramified representation its constant coefficient is pinned to
the fixed cyclotomic value by the determinant condition — so at every
finite place the LINEAR coefficient (the trace datum carried by the
deformation vocabulary of this module) determines the whole
polynomial.  This is the audit note of the module docstring made into
lemmas: it upgrades the trace-level reduction data of a test
deformation to full `charFrob` matching, the input the
Chebotarev–Brauer–Nesbitt conjugacy leaf consumes.
-/

/-- **Two monic quadratics with equal lower coefficients are equal**
(PROVEN, elementary): coefficientwise, degrees `0` and `1` are the
hypotheses, degree `2` is monicity, and everything above is zero. -/
lemma monic_natDegree_two_ext {R : Type*} [Semiring R] {P Q : Polynomial R}
    (hP : P.Monic) (hQ : Q.Monic) (hPd : P.natDegree = 2)
    (hQd : Q.natDegree = 2) (h0 : P.coeff 0 = Q.coeff 0)
    (h1 : P.coeff 1 = Q.coeff 1) : P = Q := by
  ext n
  match n with
  | 0 => exact h0
  | 1 => exact h1
  | 2 =>
    have hP2 : P.coeff 2 = 1 := by
      have h := hP.coeff_natDegree
      rwa [hPd] at h
    have hQ2 : Q.coeff 2 = 1 := by
      have h := hQ.coeff_natDegree
      rwa [hQd] at h
    rw [hP2, hQ2]
  | (m + 3) =>
    rw [P.coeff_eq_zero_of_natDegree_lt (by rw [hPd]; omega),
      Q.coeff_eq_zero_of_natDegree_lt (by rw [hQd]; omega)]

set_option backward.isDefEq.respectTransparency false in
/-- **`charFrob` is monic** (PROVEN): it is a characteristic
polynomial. -/
lemma charFrob_monic {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] {M : Type*} [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Module.Free A M]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (ρ : GaloisRep ℚ A M) : (ρ.charFrob v).Monic := by
  show ((ρ.toLocal v (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly).Monic
  exact LinearMap.charpoly_monic _

set_option backward.isDefEq.respectTransparency false in
/-- **`charFrob` of a rank-2 representation has degree 2** (PROVEN):
the characteristic polynomial of an endomorphism of a finite free
rank-2 module has degree the rank. -/
lemma charFrob_natDegree {A : Type*} [CommRing A] [Nontrivial A]
    [TopologicalSpace A] [IsTopologicalRing A] {M : Type*} [AddCommGroup M]
    [Module A M] [Module.Finite A M] [Module.Free A M]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (ρ : GaloisRep ℚ A M) (hdim : Module.rank A M = 2) :
    (ρ.charFrob v).natDegree = 2 := by
  show ((ρ.toLocal v
    (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly).natDegree = 2
  rw [LinearMap.charpoly_natDegree]
  exact Module.finrank_eq_of_rank_eq (by exact_mod_cast hdim)

set_option backward.isDefEq.respectTransparency false in
/-- **The determinant pins the constant `charFrob` coefficient of a
hardly ramified representation** (PROVEN): at every finite place `v`,
the constant coefficient of `charFrob` — which is `(-1)² · det = det`
of the Frobenius endomorphism on the rank-2 module — is the image
under `algebraMap ℤ_p` of the cyclotomic-character value at the
(fixed, coefficient-ring-independent) global Galois element underlying
the arithmetic Frobenius at `v`.  Hence two hardly ramified
representations linked by a ring homomorphism compatible with the
`ℤ_p`-structures match constant `charFrob` coefficients EVERYWHERE —
the trace-determines-`charFrob` audit point of the module docstring,
stated directly in the transported two-representation form the
assembly consumes. -/
lemma coeff_zero_charFrob_eq_of_isHardlyRamified {p : ℕ} {hpodd : Odd p}
    [Fact p.Prime] {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLocalRing R] [Algebra ℤ_[p] R]
    {V : Type*} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Free R V] {hdim : Module.rank R V = 2} {ρ : GaloisRep ℚ R V}
    (hρ : IsHardlyRamified hpodd hdim ρ)
    {k : Type*} [CommRing k] [TopologicalSpace k] [IsTopologicalRing k]
    [IsLocalRing k] [Algebra ℤ_[p] k]
    {W : Type*} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W] {hW : Module.rank k W = 2} {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hpodd hW ρbar)
    (f : R →+* k) (hf : f.comp (algebraMap ℤ_[p] R) = algebraMap ℤ_[p] k)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    f ((ρ.charFrob v).coeff 0) = (ρbar.charFrob v).coeff 0 := by
  have hfinR : Module.finrank R V = 2 :=
    Module.finrank_eq_of_rank_eq (by exact_mod_cast hdim)
  have hfink : Module.finrank k W = 2 :=
    Module.finrank_eq_of_rank_eq (by exact_mod_cast hW)
  have hdetR := LinearMap.det_eq_sign_charpoly_coeff
    (ρ.toLocal v (Field.AbsoluteGaloisGroup.adicArithFrob v))
  have hdetk := LinearMap.det_eq_sign_charpoly_coeff
    (ρbar.toLocal v (Field.AbsoluteGaloisGroup.adicArithFrob v))
  rw [hfinR] at hdetR
  rw [hfink] at hdetk
  show f (((ρ.toLocal v
      (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly).coeff 0) =
    ((ρbar.toLocal v
      (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly).coeff 0
  have hcR : ((ρ.toLocal v
      (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly).coeff 0 =
      LinearMap.det (ρ.toLocal v
        (Field.AbsoluteGaloisGroup.adicArithFrob v)) := by
    rw [hdetR]
    ring
  have hck : ((ρbar.toLocal v
      (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly).coeff 0 =
      LinearMap.det (ρbar.toLocal v
        (Field.AbsoluteGaloisGroup.adicArithFrob v)) := by
    rw [hdetk]
    ring
  rw [hcR, hck, GaloisRep.toLocal_apply, GaloisRep.toLocal_apply,
    ← GaloisRep.det_apply, ← GaloisRep.det_apply, hρ.det, hρbar.det,
    ← RingHom.comp_apply, hf]

set_option linter.checkUnivs false in
/-- **A hardly ramified deformation of `ρbar` over a module-finite
local `ℤ_p`-algebra** — the test objects of the weak-universality
clause of Mazur representability, and simultaneously the common shape
of the two deformations the pillar-3b assembly classifies (the
interface's `p`-adic representation `ρ` over `R` and its Hecke-side
package `ρT` over `T`).  The data: a coefficient ring `A` that is a
local topological `ℤ_p`-algebra, module-finite over `ℤ_p` and carrying
the `ℤ_p`-module topology (classically: a complete Noetherian local
ring with finite residue field, with its `𝔪`-adic topology — see the
module docstring's audit); a free rank-2 module `Vd` over it; a hardly
ramified representation on `Vd`; and a surjective reduction map
`π : A →+* k` to the residual coefficient field carrying the linear
`charFrob` coefficients of `ρ` to those of `ρbar` away from a finite
exceptional set (`π` is automatically local: its kernel is a maximal
ideal of the local ring `A`, hence THE maximal ideal, so `A/𝔪 ≅ k`).
This is the interface-side counterpart of `Lift.lean`'s
`HardlyRamifiedDeformation` (which lives in Mazur's full category,
over `ZMod ℓ`, downstream of this module's consumer — see the module
docstring).

(The `checkUnivs` linter is disabled: the coefficient-ring universe
`s` and the module universe `t` are deliberately independent — the
pillar-3b assembly instantiates the structure at `(u, u)` for the
standard-framed Hecke side and at `(u, v)` for the interface's
abstract rank-2 module `V : Type v` — and a structure bundling a
`Type s` and a `Type t` field intrinsically lives in a `max`-only
sort.) -/
structure HardlyRamifiedFiniteDeformation.{s, t, uK, uW}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [CommRing k] [TopologicalSpace k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (ρbar : GaloisRep ℚ k W) where
  /-- The coefficient ring of the deformation. -/
  A : Type s
  [commRing : CommRing A]
  [topologicalSpace : TopologicalSpace A]
  [isTopologicalRing : IsTopologicalRing A]
  [isLocalRing : IsLocalRing A]
  [algebra : Algebra ℤ_[p] A]
  [moduleFinite : Module.Finite ℤ_[p] A]
  [isModuleTopology : IsModuleTopology ℤ_[p] A]
  /-- The underlying module of the deformation. -/
  Vd : Type t
  [addCommGroup : AddCommGroup Vd]
  [module : Module A Vd]
  [moduleFiniteVd : Module.Finite A Vd]
  [moduleFreeVd : Module.Free A Vd]
  /-- The module has rank 2. -/
  rank_eq : Module.rank A Vd = 2
  /-- The deformed representation. -/
  ρ : GaloisRep ℚ A Vd
  /-- The deformation is hardly ramified. -/
  isHardlyRamified : IsHardlyRamified hpodd rank_eq ρ
  /-- The reduction map to the residual coefficient ring. -/
  π : A →+* k
  /-- The reduction map is surjective (so `A` has residue field `k`). -/
  π_surjective : Function.Surjective π
  /-- The finite exceptional set of the reduction datum. -/
  S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
  /-- The deformation reduces to `ρbar`: the linear `charFrob`
  coefficients (the Frobenius traces up to sign) match through `π`
  away from the exceptional set. -/
  charFrob_compat : ∀ (q : ℕ) (hq : q.Prime),
    hq.toHeightOneSpectrumRingOfIntegersRat ∉ S →
    π ((ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
      (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1

/-- **Continuity of the reduction map** (PROVEN): the reduction map
`π : A →+* k` of a hardly ramified finite deformation is continuous
when the residual field is finite and discrete.  The coefficient ring
carries the `ℤ_p`-module topology, so any ring homomorphism out of it
whose restriction to `ℤ_p` is continuous is continuous
(`IsModuleTopology.continuous_of_ringHom`), and `π ∘ algebraMap` is a
ring homomorphism `ℤ_p →+* k`, continuous by
`continuous_ringHom_padicInt`.  (Ingredient of the
residual-identification vocabulary below: it makes `k` a topological
`A`-algebra, so the reduction of `D.ρ` can be formed by `baseChange` —
the same role `continuous_pi` plays in `Lift.lean`'s parallel,
downstream vocabulary.) -/
lemma HardlyRamifiedFiniteDeformation.continuous_pi.{s, t, uK, uW}
    {p : ℕ} {hpodd : Odd p} [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [TopologicalSpace k]
    [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W] {ρbar : GaloisRep ℚ k W}
    (D : HardlyRamifiedFiniteDeformation.{s, t, uK, uW} hpodd ρbar) :
    letI := D.commRing
    letI := D.topologicalSpace
    Continuous D.π := by
  letI := D.commRing
  letI := D.topologicalSpace
  letI := D.algebra
  letI := D.isModuleTopology
  exact IsModuleTopology.continuous_of_ringHom (R := ℤ_[p]) D.π
    (continuous_ringHom_padicInt (D.π.comp (algebraMap ℤ_[p] D.A)))

open scoped TensorProduct in
/-- **Residual identification**: the reduction of `D.ρ` along the
reduction map `D.π` — the base change of `D.ρ` to `k`, a continuous
`D.A`-algebra via `continuous_pi` — is conjugate to `ρbar` itself.
This is the datum with which Mazur-style strict-deformation
universality can be applied to `D`: the
`HardlyRamifiedFiniteDeformation` vocabulary matches `D` with `ρbar`
only through linear `charFrob` coefficients off a finite set
(`charFrob_compat`), and the Chebotarev–Brauer–Nesbitt leaf
`exists_conj_of_charFrob_eq_away` upgrades that matching to an actual
conjugation whenever `ρbar` is irreducible.  Interface-side
counterpart of `Lift.lean`'s `IsResidualIdentified` (which lives over
`ZMod ℓ`, downstream of this module's consumer). -/
def HardlyRamifiedFiniteDeformation.IsResidualIdentified.{s, t, uK, uW}
    {p : ℕ} {hpodd : Odd p} [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [TopologicalSpace k]
    [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W] {ρbar : GaloisRep ℚ k W}
    (D : HardlyRamifiedFiniteDeformation.{s, t, uK, uW} hpodd ρbar) : Prop :=
  letI := D.commRing
  letI := D.topologicalSpace
  letI := D.isTopologicalRing
  letI := D.addCommGroup
  letI := D.module
  letI := D.moduleFiniteVd
  letI := D.moduleFreeVd
  letI : Algebra D.A k := D.π.toAlgebra
  letI : ContinuousSMul D.A k := continuousSMul_of_algebraMap D.A k
    (by rw [RingHom.algebraMap_toAlgebra]; exact D.continuous_pi)
  ∃ e : (k ⊗[D.A] D.Vd) ≃ₗ[k] W, (D.ρ.baseChange k).conj e = ρbar

/-- **The weak-universality clause** (the existence half of Mazur
universality, at trace level): every hardly ramified deformation of
`ρbar` over a module-finite local `ℤ_p`-algebra (with rank-2 module in
`Type t`) receives a ring homomorphism `ψ` from `Runiv` that is
compatible with the `ℤ_p`-algebra structures, intertwines the two
reduction maps, and carries the linear `charFrob` coefficients of the
universal representation `ρuniv` to those of the deformation away from
a finite exceptional set.  This is `Lift.lean`'s `IsWeaklyUniversal`
transported to the interface's vocabulary (abstract finite residual
field, trace-level compatibility, module-finite test category — see
the module docstring for the audit of each change).  Classically, for
the genuine universal deformation ring of an irreducible `ρbar` the
clause holds with `ψ` the classifying map of the test deformation
(Mazur; the trace compatibility is the definitional compatibility of
the classifying map with the universal representation, read off on
traces, which are conjugation-invariant — this is where residual
irreducibility kills the framing).  Uniqueness of `ψ` (Carayol trace
generation of `Runiv`) is deliberately NOT part of the clause: the
pillar-3b assembly never needs it, and keeping the clause existential
keeps pillar 1 exactly the representability statement. -/
def IsWeaklyUniversalDeformation.{s, t, uK, uW, uR}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [CommRing k] [TopologicalSpace k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (ρbar : GaloisRep ℚ k W)
    {Runiv : Type uR} [CommRing Runiv] [TopologicalSpace Runiv]
    [IsTopologicalRing Runiv] [IsLocalRing Runiv] [Algebra ℤ_[p] Runiv]
    (ρuniv : GaloisRep ℚ Runiv (Fin 2 → Runiv)) (πuniv : Runiv →+* k) :
    Prop :=
  ∀ D : HardlyRamifiedFiniteDeformation.{s, t, uK, uW} hpodd ρbar,
    letI := D.commRing
    letI := D.topologicalSpace
    letI := D.isTopologicalRing
    letI := D.isLocalRing
    letI := D.algebra
    letI := D.addCommGroup
    letI := D.module
    letI := D.moduleFiniteVd
    letI := D.moduleFreeVd
    ∃ ψ : Runiv →+* D.A,
      ψ.comp (algebraMap ℤ_[p] Runiv) = algebraMap ℤ_[p] D.A ∧
      D.π.comp ψ = πuniv ∧
      ∃ Sψ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)),
        ∀ (q : ℕ) (hq : q.Prime),
          hq.toHeightOneSpectrumRingOfIntegersRat ∉ Sψ →
          ψ ((ρuniv.charFrob
              hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
            (D.ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1

/-- **Weak universality on residually identified deformations**: the
package `(Runiv, ρuniv, πuniv)` factors every test deformation `D`
that comes EQUIPPED with a residual identification — a conjugation of
its reduction onto `ρbar`.  This is what Mazur-style strict-deformation
representability produces directly (the classifying map exists for
deformations whose reduction is identified with `ρbar`), without the
Chebotarev–Brauer–Nesbitt input, which is exactly what upgrades this
clause to full `IsWeaklyUniversalDeformation` in the proven assembly
`isWeaklyUniversal_of_isWeaklyUniversalOnIdentified` below.
Interface-side counterpart of `Lift.lean`'s
`IsWeaklyUniversalOnIdentified`. -/
def IsWeaklyUniversalOnIdentifiedDeformation.{s, t, uK, uW, uR}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [TopologicalSpace k]
    [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (ρbar : GaloisRep ℚ k W)
    {Runiv : Type uR} [CommRing Runiv] [TopologicalSpace Runiv]
    [IsTopologicalRing Runiv] [IsLocalRing Runiv] [Algebra ℤ_[p] Runiv]
    (ρuniv : GaloisRep ℚ Runiv (Fin 2 → Runiv)) (πuniv : Runiv →+* k) :
    Prop :=
  ∀ D : HardlyRamifiedFiniteDeformation.{s, t, uK, uW} hpodd ρbar,
    D.IsResidualIdentified →
    letI := D.commRing
    letI := D.topologicalSpace
    letI := D.isTopologicalRing
    letI := D.isLocalRing
    letI := D.algebra
    letI := D.addCommGroup
    letI := D.module
    letI := D.moduleFiniteVd
    letI := D.moduleFreeVd
    ∃ ψ : Runiv →+* D.A,
      ψ.comp (algebraMap ℤ_[p] Runiv) = algebraMap ℤ_[p] D.A ∧
      D.π.comp ψ = πuniv ∧
      ∃ Sψ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)),
        ∀ (q : ℕ) (hq : q.Prime),
          hq.toHeightOneSpectrumRingOfIntegersRat ∉ Sψ →
          ψ ((ρuniv.charFrob
              hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
            (D.ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1

/-- **Chebotarev–Brauer–Nesbitt conjugacy leaf** (sorry node — the
identification half of the Mazur representability pillar): a
continuous representation `τ` of `Gal(ℚ̄/ℚ)` on a 2-dimensional space
over a finite discrete field `k` whose Frobenius characteristic
polynomials agree with those of an *irreducible* 2-dimensional `ρbar`
at all primes outside a finite exceptional set `S` is conjugate to
`ρbar`.

Mathematical content: by Chebotarev density the Frobenius conjugacy
classes at the places outside ANY finite set are dense in the Galois
group (`Chebotarev.lean`'s density node; removing the finitely many
classes of `S` does not affect density, since the argument produces
infinitely many places in each open conjugacy-stable set); `τ` and
`ρbar` are continuous into the discrete finite endomorphism spaces, so
the agreement set of the two characteristic polynomials is closed and
conjugation-stable, hence everything.  By Brauer–Nesbitt (valid over
any field when full characteristic polynomials — not just traces —
agree) the semisimplifications are then isomorphic; `ρbar` is
irreducible of full dimension 2, so the semisimplification of `τ` is
irreducible, hence `τ` itself is irreducible and isomorphic to `ρbar`,
and an intertwining isomorphism is the required conjugation (Carayol,
Contemp. Math. 165 (1994), Théorème 1, in the trivial
residual-coefficient case; Diamond–Darmon–Taylor, *Fermat's Last
Theorem* (1995), Lemma 3.27 for the standard argument).  This is
`Lift.lean`'s `exists_conj_of_charFrob_eq` generalized from `ZMod ℓ`
to an abstract finite coefficient field and from the fixed exceptional
set `{2, ℓ}` to an arbitrary finite one — `Lift.lean` is downstream of
this module's consumer, so the statement is restated here upstream
(dedupe deferred until the import cycle is broken).

Both-ways audit: the statement quantifies over abstract `τ`, `ρbar`
with no hardly-ramified hypothesis, and is the plain classical
Chebotarev–Brauer–Nesbitt statement — true outright, no vacuity
needed. -/
theorem exists_conj_of_charFrob_eq_away.{uK, uW, uW'}
    {k : Type uK} [Field k] [Finite k] [TopologicalSpace k]
    [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2)
    {ρbar : GaloisRep ℚ k W} (hirr : ρbar.IsIrreducible)
    {W' : Type uW'} [AddCommGroup W'] [Module k W'] [Module.Finite k W']
    [Module.Free k W']
    (hW' : Module.rank k W' = 2)
    (τ : GaloisRep ℚ k W')
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
    (hcf : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S →
      τ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat) :
    ∃ e : W' ≃ₗ[k] W, τ.conj e = ρbar :=
  sorry

/-- **Strict Mazur representability leaf** (sorry node — the
representability half of the Mazur pillar): the hardly ramified
deformation problem of an irreducible hardly ramified `ρbar` over a
finite coefficient field admits a Mazur-category package
`(Runiv, ρuniv, πuniv)` — complete Noetherian local topological
`ℤ_p`-algebra with the `𝔪`-adic topology, hardly ramified universal
representation, surjective reduction matching linear `charFrob`
coefficients off a finite set — that factors every *residually
identified* test deformation, at both module universes the pillar-3b
assembly instantiates.  The Chebotarev–Brauer–Nesbitt matching is NOT
part of this leaf (it is supplied by `exists_conj_of_charFrob_eq_away`
through the proven assemblies below); this leaf is Mazur/Ramakrishna/CDT
representability proper.

Classical construction (as in the parent pillar's docstring, which this
leaf now carries alone): `ρbar` is odd (cyclotomic determinant, odd
`p`), and an odd irreducible 2-dimensional representation over a
finite field of odd characteristic is absolutely irreducible, so
`End_{k[Γ]}(ρbar) = k` (Schur) and the framing is a torsor: by
Schlessinger's criterion the unframed deformation functor of `ρbar` on
complete Noetherian local `ℤ_p`-algebras with residue field `k` is
pro-representable (Mazur, *Deforming Galois representations*, MSRI
Publ. 16 (1989), §1.2; Schlessinger H1–H4 hold with finite tangent
space `H¹(G_{ℚ,{2,p}}, ad ρbar)`, finite by global Euler
characteristic/class-field finiteness).  The hardly ramified
conditions cut out a relatively representable closed subfunctor:
cyclotomic determinant and unramifiedness outside `2p` are
limit-stable; flatness at `p` in the `IsFlatAt` sense is Ramakrishna's
flat condition (Compositio 87 (1994)); the tame quadratic quotient at
`2` is an ordinary-type condition (Conrad–Diamond–Taylor, JAMS 12
(1999), §2; FLT blueprint's `S`-good theory with `S = {2}`).  `Runiv`
is the universal ring — a quotient of `ℤ_p[[x₁,…,x_g]]` (de
Smit–Lenstra presentation), hence Noetherian, `𝔪`-adically complete,
with the `𝔪`-adic topology; `ρuniv` the universal representation
framed by any basis; `πuniv` the residue map.  Given a test
deformation `D` WITH a residual identification, conjugating the
framing carries `D.ρ` to an honest deformation of `ρbar` over the
module-finite local `ℤ_p`-algebra `D.A` — a legitimate Mazur test
object (complete Noetherian local with the `𝔪`-adic topology, per the
module docstring's audit) — and its classifying map is the required
`ψ`: `ℤ_p`-compatibility and reduction compatibility are strictness,
and the trace clause is conjugation-invariance of characteristic
polynomials (residual irreducibility kills the framing ambiguity on
traces).

Both-ways audit: for the genuine hardly ramified problem this is the
cited Mazur/Ramakrishna/CDT representability; abstractly the
hypothesis set contains an irreducible hardly ramified `ρbar`, which
the section audit of `Interface.lean` shows to be classically
unsatisfiable, so the statement is also classically true outright.
CIRCULARITY GUARD (inherited): must not be proven through
`Family.lean` or anything downstream of it (`Lift.lean` included). -/
theorem exists_weaklyUniversalOnIdentified_hardlyRamifiedDeformation.{s, t, uK, uW}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hpodd hW ρbar)
    (hirr : ρbar.IsIrreducible) :
    ∃ (Runiv : Type s) (_ : CommRing Runiv) (_ : TopologicalSpace Runiv)
      (_ : IsTopologicalRing Runiv) (_ : IsLocalRing Runiv)
      (_ : Algebra ℤ_[p] Runiv) (_ : IsNoetherianRing Runiv)
      (_ : IsAdic (IsLocalRing.maximalIdeal Runiv))
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal Runiv) Runiv)
      (ρuniv : GaloisRep ℚ Runiv (Fin 2 → Runiv))
      (hranku : Module.rank Runiv (Fin 2 → Runiv) = 2)
      (_ : IsHardlyRamified hpodd hranku ρuniv)
      (πuniv : Runiv →+* k) (_ : Function.Surjective πuniv)
      (Suniv : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      (∀ (q : ℕ) (hq : q.Prime),
        hq.toHeightOneSpectrumRingOfIntegersRat ∉ Suniv →
        πuniv ((ρuniv.charFrob
            hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
          (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) ∧
      IsWeaklyUniversalOnIdentifiedDeformation.{s, s, uK, uW, s} hpodd ρbar
        ρuniv πuniv ∧
      IsWeaklyUniversalOnIdentifiedDeformation.{s, t, uK, uW, s} hpodd ρbar
        ρuniv πuniv :=
  sorry

open scoped TensorProduct in
/-- **Upgrade from identified to unconditional weak universality**
(PROVEN — the glue of the Mazur pillar's 2026-07-24 decomposition):
a package that factors residually identified deformations factors ALL
deformations, when `ρbar` is irreducible and hardly ramified.  Given a
test deformation `D`, its reduction `D.ρ.baseChange k` along the
(automatically continuous, `continuous_pi`) reduction map is a
2-dimensional representation over `k` whose `charFrob` at each prime
off `D.S` MATCHES that of `ρbar` in full: the linear coefficients
match by `charFrob_compat` and `charFrob_baseChange`, the constant
coefficients match at EVERY place because both determinants are pinned
to the same cyclotomic value
(`coeff_zero_charFrob_eq_of_isHardlyRamified`, which also consumes the
rigidity `ringHom_padicInt_eq` of `ℤ_p →+* k`), and both polynomials are
monic quadratics (`charFrob_monic`, `charFrob_natDegree`,
`monic_natDegree_two_ext`).  The Chebotarev–Brauer–Nesbitt leaf
`exists_conj_of_charFrob_eq_away` turns the matching into a residual
identification, and the identified factorization applies. -/
theorem isWeaklyUniversal_of_isWeaklyUniversalOnIdentified.{s, t, uK, uW, uR}
    {p : ℕ} {hpodd : Odd p} [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    {hW : Module.rank k W = 2} {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hpodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    {Runiv : Type uR} [CommRing Runiv] [TopologicalSpace Runiv]
    [IsTopologicalRing Runiv] [IsLocalRing Runiv] [Algebra ℤ_[p] Runiv]
    {ρuniv : GaloisRep ℚ Runiv (Fin 2 → Runiv)} {πuniv : Runiv →+* k}
    (h : IsWeaklyUniversalOnIdentifiedDeformation.{s, t, uK, uW, uR} hpodd
      ρbar ρuniv πuniv) :
    IsWeaklyUniversalDeformation.{s, t, uK, uW, uR} hpodd ρbar ρuniv
      πuniv := by
  intro D
  letI := D.commRing
  letI := D.topologicalSpace
  letI := D.isTopologicalRing
  letI := D.isLocalRing
  letI := D.algebra
  letI := D.addCommGroup
  letI := D.module
  letI := D.moduleFiniteVd
  letI := D.moduleFreeVd
  letI : Algebra D.A k := D.π.toAlgebra
  letI : ContinuousSMul D.A k := continuousSMul_of_algebraMap D.A k
    (by rw [RingHom.algebraMap_toAlgebra]; exact D.continuous_pi)
  refine h D ?_
  -- the reduction is 2-dimensional …
  have hrankW' : Module.rank k (k ⊗[D.A] D.Vd) = 2 := by
    rw [Module.rank_baseChange, D.rank_eq]
    simp
  -- … and its Frobenius characteristic polynomials are those of `ρbar`
  have hcf : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ D.S →
      (D.ρ.baseChange k).charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat := by
    intro q hq hqS
    have hmap := charFrob_baseChange (B := k)
      hq.toHeightOneSpectrumRingOfIntegersRat D.ρ
    rw [RingHom.algebraMap_toAlgebra] at hmap
    refine monic_natDegree_two_ext ?_
      (charFrob_monic hq.toHeightOneSpectrumRingOfIntegersRat ρbar) ?_
      (charFrob_natDegree hq.toHeightOneSpectrumRingOfIntegersRat ρbar hW)
      ?_ ?_
    · rw [hmap]
      exact (charFrob_monic hq.toHeightOneSpectrumRingOfIntegersRat D.ρ).map
        D.π
    · rw [hmap, (charFrob_monic hq.toHeightOneSpectrumRingOfIntegersRat
        D.ρ).natDegree_map D.π]
      exact charFrob_natDegree hq.toHeightOneSpectrumRingOfIntegersRat D.ρ
        D.rank_eq
    · rw [hmap, Polynomial.coeff_map]
      exact coeff_zero_charFrob_eq_of_isHardlyRamified D.isHardlyRamified
        hρbar D.π
        (ringHom_padicInt_eq (D.π.comp (algebraMap ℤ_[p] D.A))
          (algebraMap ℤ_[p] k))
        hq.toHeightOneSpectrumRingOfIntegersRat
    · rw [hmap, Polynomial.coeff_map]
      exact D.charFrob_compat q hq hqS
  obtain ⟨e, he⟩ := exists_conj_of_charFrob_eq_away hW hirr hrankW'
    (D.ρ.baseChange k) D.S hcf
  exact ⟨e, he⟩

/-- **Mazur representability of the hardly ramified deformation
problem** (pillar 3b-i; DECOMPOSED 2026-07-24 into the strict Mazur
representability leaf
`exists_weaklyUniversalOnIdentified_hardlyRamifiedDeformation` — the
classifying maps for residually identified deformations — and the
Chebotarev–Brauer–Nesbitt conjugacy leaf
`exists_conj_of_charFrob_eq_away` — which produces the residual
identification from the trace-level `charFrob_compat` matching via the
determinant pinning of `coeff_zero_charFrob_eq_of_isHardlyRamified`; the
assembly below and its glue
`isWeaklyUniversal_of_isWeaklyUniversalOnIdentified` are PROVEN):
an irreducible hardly ramified
mod-`p` representation `ρbar` over a finite coefficient field admits a
weakly universal hardly ramified deformation: a coefficient ring
`Runiv` in Mazur's category — a Noetherian local topological
`ℤ_p`-algebra whose topology is the `𝔪`-adic one and which is
`𝔪`-adically complete and separated — carrying a hardly ramified
representation `ρuniv` on `Fin 2 → Runiv` that reduces trace-by-trace
to `ρbar` through a surjection `πuniv`, such that every hardly
ramified deformation of `ρbar` over a module-finite local
`ℤ_p`-algebra factors through `(Runiv, ρuniv, πuniv)` on Frobenius
traces.  The two clauses are the same factorization property at the
two module universes the pillar-3b assembly instantiates (`Type s`
for the standard-framed Hecke side, `Type t` for the interface's
abstract rank-2 module `V`).

Classical construction: the framed deformation functor of `ρbar` on
complete Noetherian local `ℤ_p`-algebras with residue field `k` is
representable (Schlessinger's criterion; Mazur, *Deforming Galois
representations*, in Galois Groups over ℚ, MSRI Publ. 16 (1989),
§1.2); residual irreducibility gives `End_{k[Γ]}(ρbar) = k` (Schur —
hardly ramified representations are odd, having cyclotomic
determinant, and an odd irreducible 2-dimensional representation over
a finite field of odd characteristic is absolutely irreducible), so
the framing is a torsor and the unframed functor is representable as
well (Mazur §1.2 Prop. 1).  The hardly ramified conditions cut out a
closed subfunctor that is again representable: cyclotomic determinant
and unramifiedness outside `2p` are manifestly limit-stable
conditions; flatness at `p` in the `IsFlatAt` sense (every open-ideal
quotient has a flat prolongation) is Ramakrishna's flat deformation
condition, relatively representable by (Ramakrishna, *On a variation
of Mazur's deformation functor*, Compositio Math. 87 (1994)); the tame
condition at `2` (rank-1 unramified square-trivial quotient) is an
ordinary-type condition, relatively representable per
Conrad–Diamond–Taylor (*Modularity of certain potentially
Barsotti–Tate Galois representations*, JAMS 12 (1999), §2) — the FLT
blueprint packages the same problem as the "`S`-good" deformation
theory with `S = {2}` (ch. 4).  `Runiv` is the resulting universal
ring, `ρuniv` the universal representation (framed by any basis:
trace data is frame-invariant), `πuniv` the residue map; the
universal representation itself satisfies the hardly ramified
conditions because each condition holds on all Artinian quotients and
is, in the `IsFlatAt`/inertia-kernel/quotient-character spelling of
`Deformations/RepresentationTheory/`, precisely a limit of those
quotient conditions.  The factorization clause holds because a test
deformation reduces to `ρbar` honestly, not just trace-wise, by
Chebotarev + Brauer–Nesbitt + Carayol's conjugation theorem (see the
module docstring), and its classifying map carries `ρuniv` to it up to
conjugation, hence equates traces.

Both-ways audit: for the genuine hardly ramified problem this is the
cited Mazur/Ramakrishna/CDT representability; abstractly, the
hypothesis set contains an irreducible hardly ramified `ρbar`, which
the section audit of `Interface.lean` shows to be classically
unsatisfiable, so the statement is also classically true outright.
CIRCULARITY GUARD (inherited from pillar 3b): must not be proven
through `Family.lean` or anything downstream of it (`Lift.lean`
included — its parallel representability infrastructure is
import-unreachable from here by design; see the module docstring). -/
theorem exists_weaklyUniversal_hardlyRamifiedDeformation.{s, t, uK, uW}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hpodd hW ρbar)
    (hirr : ρbar.IsIrreducible) :
    ∃ (Runiv : Type s) (_ : CommRing Runiv) (_ : TopologicalSpace Runiv)
      (_ : IsTopologicalRing Runiv) (_ : IsLocalRing Runiv)
      (_ : Algebra ℤ_[p] Runiv) (_ : IsNoetherianRing Runiv)
      (_ : IsAdic (IsLocalRing.maximalIdeal Runiv))
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal Runiv) Runiv)
      (ρuniv : GaloisRep ℚ Runiv (Fin 2 → Runiv))
      (hranku : Module.rank Runiv (Fin 2 → Runiv) = 2)
      (_ : IsHardlyRamified hpodd hranku ρuniv)
      (πuniv : Runiv →+* k) (_ : Function.Surjective πuniv)
      (Suniv : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      (∀ (q : ℕ) (hq : q.Prime),
        hq.toHeightOneSpectrumRingOfIntegersRat ∉ Suniv →
        πuniv ((ρuniv.charFrob
            hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
          (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) ∧
      IsWeaklyUniversalDeformation.{s, s, uK, uW, s} hpodd ρbar ρuniv
        πuniv ∧
      IsWeaklyUniversalDeformation.{s, t, uK, uW, s} hpodd ρbar ρuniv
        πuniv := by
  obtain ⟨Runiv, iCR, iTS, iTR, iLR, iAlg, iNoeth, hadic, hcomplete, ρuniv,
    hranku, hHR, πuniv, hπsurj, Suniv, hred, hws, hwt⟩ :=
    exists_weaklyUniversalOnIdentified_hardlyRamifiedDeformation.{s, t, uK, uW}
      hpodd hW hρbar hirr
  letI := iCR
  letI := iTS
  letI := iTR
  letI := iLR
  letI := iAlg
  exact ⟨Runiv, iCR, iTS, iTR, iLR, iAlg, iNoeth, hadic, hcomplete, ρuniv,
    hranku, hHR, πuniv, hπsurj, Suniv, hred,
    isWeaklyUniversal_of_isWeaklyUniversalOnIdentified hρbar hirr hws,
    isWeaklyUniversal_of_isWeaklyUniversalOnIdentified hρbar hirr hwt⟩

/-- **Carayol trace generation: the surjection `R_univ ↠ 𝕋`** (pillar
3b-ii; sorry node): a ring homomorphism `ψ` from a Mazur-category
deformation `(Runiv, ρuniv, πuniv)` of the irreducible residual
`ρbar` to a Hecke-side hardly ramified deformation `(T, ρT, π)` that
is compatible with the `ℤ_p`-structures, the reduction maps, and the
Frobenius traces away from a finite set, is SURJECTIVE.

Classical route, at the intended instantiation `T = 𝕋_𝔪` (the
weight-2 Hecke algebra at the Serre-optimal level localized at the
non-Eisenstein maximal ideal of `ρbar`, the packet produced by pillar
3a of `Interface.lean`): `𝕋_𝔪` is generated as a `ℤ_p`-algebra by the
Hecke operators `T_q` with `q` outside ANY given finite set of primes
— by Chebotarev density and the Carayol/Serre linearization argument
(Carayol, Contemp. Math. 165 (1994), the "critère de surjectivité";
Diamond–Darmon–Taylor, *Fermat's Last Theorem*, Current Developments
in Math. (1995), Lemma 4.6? — the standard duality/Chebotarev
argument; Wiles, Ann. of Math. 141 (1995), ch. 2), and `T_q` is
`−(coeff 1)` of `charFrob ρT` at `q`, which lies in the image of `ψ`
by the trace-compatibility hypothesis.  The image of `ψ` is a closed
`ℤ_p`-subalgebra (compatibility with the reduction maps makes `ψ`
local — both kernels of the reduction maps are the maximal ideals —
hence continuous from the `𝔪`-adic source, and `Runiv` is compact:
`𝔪`-adically complete Noetherian local with finite residue field, so
its image is compact, hence closed in the Hausdorff `T`), and a
closed subalgebra containing all the `T_q` off a finite set is
everything.

Both-ways audit: at the intended packet this is verbatim the cited
generation lemma; abstractly the packet `(T, ρT, π)` is NOT assumed
trace-generated, and the statement is covered by the section audit of
`Interface.lean` (the hypothesis set contains the classically
unsatisfiable irreducible hardly ramified `ρbar`).  CIRCULARITY
GUARD: must not be proven through `Family.lean` or anything
downstream of it. -/
theorem surjective_ringHom_of_charFrob_eq.{s, uK, uW, uR}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hpodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    {Runiv : Type uR} [CommRing Runiv] [TopologicalSpace Runiv]
    [IsTopologicalRing Runiv] [IsLocalRing Runiv] [Algebra ℤ_[p] Runiv]
    [IsNoetherianRing Runiv]
    (hadic : IsAdic (IsLocalRing.maximalIdeal Runiv))
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal Runiv) Runiv)
    {ρuniv : GaloisRep ℚ Runiv (Fin 2 → Runiv)}
    (hranku : Module.rank Runiv (Fin 2 → Runiv) = 2)
    (hρuniv : IsHardlyRamified hpodd hranku ρuniv)
    {πuniv : Runiv →+* k} (hπuniv : Function.Surjective πuniv)
    {Suniv : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hunivred : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ Suniv →
      πuniv ((ρuniv.charFrob
          hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)
    {T : Type s} [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [Algebra ℤ_[p] T] [IsLocalRing T] [Module.Finite ℤ_[p] T]
    [Module.Free ℤ_[p] T] [IsModuleTopology ℤ_[p] T]
    {ρT : GaloisRep ℚ T (Fin 2 → T)}
    (hrankT : Module.rank T (Fin 2 → T) = 2)
    (hρT : IsHardlyRamified hpodd hrankT ρT)
    {π : T →+* k} (hπ : Function.Surjective π)
    {S_T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hred : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S_T →
      π ((ρT.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)
    (ψ : Runiv →+* T)
    (hψalg : ψ.comp (algebraMap ℤ_[p] Runiv) = algebraMap ℤ_[p] T)
    (hψπ : π.comp ψ = πuniv)
    {Sψ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hψ : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ Sψ →
      ψ ((ρuniv.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρT.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) :
    Function.Surjective ψ :=
  sorry

/-- **Taylor–Wiles patching: `R = 𝕋`, the injectivity half** (pillar
3b-iii; sorry node — the mathematical heart of the modularity-lifting
theorem): a ring homomorphism `ψ` from a WEAKLY UNIVERSAL
Mazur-category deformation `(Runiv, ρuniv, πuniv)` of the irreducible
residual `ρbar` to a Hecke-side hardly ramified deformation
`(T, ρT, π)`, compatible with the `ℤ_p`-structures, the reduction
maps, and the Frobenius traces away from a finite set, is INJECTIVE.

Classical route, at the intended instantiation (`Runiv` the genuine
universal ring of the hardly ramified problem, `T = 𝕋_𝔪`): the hardly
ramified conditions are the deformation conditions of the
Taylor–Wiles setting with the flat condition at `p` and the tame
condition at `2` ("`S`-good" with `S = {2}` in the FLT blueprint,
ch. 4), and the classifying map `R_univ → 𝕋_𝔪` — which is what `ψ`
is: trace compatibility pins `ψ` on the closed subalgebra
topologically generated by the traces, which is all of `R_univ` by
Carayol's theorem, so any compatible `ψ` IS the classifying map — is
an isomorphism by the Taylor–Wiles patching argument: auxiliary sets
`Q_n` of Taylor–Wiles primes (`q ≡ 1 mod p^n`, Frobenius with
distinct eigenvalues, produced by Chebotarev from the residual
irreducibility, using `p > 2`), the associated augmented deformation
rings and Hecke modules patched to a power-series situation where a
commutative-algebra dimension count forces `R_∞ = 𝕋_∞`, which
descends to `R_univ = 𝕋_𝔪`.  Literature: Wiles, *Modular elliptic
curves and Fermat's Last Theorem*, Ann. of Math. 141 (1995), ch. 3
(the numerical criterion) and ch. 2 §3; Taylor–Wiles,
*Ring-theoretic properties of certain Hecke algebras*, ibid. (the
patching input); Diamond, *The Taylor–Wiles construction and
multiplicity one*, Invent. Math. 128 (1997) (removing multiplicity
one); Conrad–Diamond–Taylor, JAMS 12 (1999), and Kisin, *Moduli of
finite flat group schemes, and modularity*, Ann. of Math. 170 (2009)
(the flat-at-`p` refinements matching the `IsFlatAt` condition);
Diamond–Darmon–Taylor (1995) §5 for the assembled exposition.

The weak-universality hypothesis `hfact` is the universality
certificate that identifies `ψ` with the classifying map — it is what
distinguishes the genuine `R_univ` from an arbitrary deformation ring
(for a non-universal `Runiv` the injectivity claim would have no
classical content).  Both-ways audit: at the intended packet the
statement is verbatim `R = 𝕋`; abstractly (a weakly universal package
that is not the genuine universal ring, a Hecke packet smaller than
`𝕋_𝔪`) it is covered by the section audit of `Interface.lean` (the
hypothesis set contains the classically unsatisfiable irreducible
hardly ramified `ρbar`).  CIRCULARITY GUARD: must not be proven
through `Family.lean` or anything downstream of it. -/
theorem injective_ringHom_of_isWeaklyUniversal.{s, t, uK, uW, uR}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hpodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    {Runiv : Type uR} [CommRing Runiv] [TopologicalSpace Runiv]
    [IsTopologicalRing Runiv] [IsLocalRing Runiv] [Algebra ℤ_[p] Runiv]
    [IsNoetherianRing Runiv]
    (hadic : IsAdic (IsLocalRing.maximalIdeal Runiv))
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal Runiv) Runiv)
    {ρuniv : GaloisRep ℚ Runiv (Fin 2 → Runiv)}
    (hranku : Module.rank Runiv (Fin 2 → Runiv) = 2)
    (hρuniv : IsHardlyRamified hpodd hranku ρuniv)
    {πuniv : Runiv →+* k} (hπuniv : Function.Surjective πuniv)
    {Suniv : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hunivred : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ Suniv →
      πuniv ((ρuniv.charFrob
          hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)
    (hfact : IsWeaklyUniversalDeformation.{s, t, uK, uW, uR} hpodd ρbar
      ρuniv πuniv)
    {T : Type s} [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [Algebra ℤ_[p] T] [IsLocalRing T] [Module.Finite ℤ_[p] T]
    [Module.Free ℤ_[p] T] [IsModuleTopology ℤ_[p] T]
    {ρT : GaloisRep ℚ T (Fin 2 → T)}
    (hrankT : Module.rank T (Fin 2 → T) = 2)
    (hρT : IsHardlyRamified hpodd hrankT ρT)
    {π : T →+* k} (hπ : Function.Surjective π)
    {S_T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hred : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S_T →
      π ((ρT.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)
    (ψ : Runiv →+* T)
    (hψalg : ψ.comp (algebraMap ℤ_[p] Runiv) = algebraMap ℤ_[p] T)
    (hψπ : π.comp ψ = πuniv)
    {Sψ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hψ : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ Sψ →
      ψ ((ρuniv.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρT.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) :
    Function.Injective ψ :=
  sorry

end GaloisRepresentation.Modularity
