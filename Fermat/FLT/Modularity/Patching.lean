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
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Data.Nat.ModEq
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Basis.Basic

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

/-- **Mazur representability of the hardly ramified deformation
problem** (pillar 3b-i; sorry node): an irreducible hardly ramified
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
        πuniv :=
  sorry

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

/-! ### The Taylor–Wiles patching architecture behind pillar 3b-iii

The injectivity pillar `injective_ringHom_of_isWeaklyUniversal` is
ASSEMBLED below (proof written, 2026-07-24) from three sorried leaves
that are exactly the classically-cited components of the Taylor–Wiles
patching argument, plus one PROVEN commutative-algebra assembly:

1. `exists_taylorWilesPrimeSet` (leaf) — Taylor–Wiles prime sets at
   every level `p^n` and of every size: Chebotarev density against the
   residual representation.
2. `exists_patchedModule` (leaf) — the pigeonhole patching
   construction (Taylor–Wiles 1995, as reorganized by Diamond 1997 and
   Fujiwara): from the tower of auxiliary levels `Q_n` it produces a
   `PatchedModule`, the limit object of the patching process.
3. `free_of_isRegular_mvPowerSeries` (leaf) — the commutative-algebra
   endgame: over the regular local ring `ℤ_p[[x₁, …, x_q]]` a finite
   module carrying a regular sequence of length `q + 1` (depth ≥ dim)
   is FREE (Auslander–Buchsbaum; Diamond 1997, Thm. 2.4).
4. `PatchedModule.injective` (PROVEN) — the faithfulness argument
   assembling 3 into the conclusion: the patched module is free over
   `R_∞ = ℤ_p[[x₁, …, x_q]]`, its bottom quotient `M₀` therefore has
   free coordinates over `Runiv = R_∞/𝔞`, and since the `R_∞`-action
   on `M₀` factors as the `T`-action through `ψ ∘ (R_∞ ↠ Runiv)`, any
   element of `ker ψ` annihilates a coordinate of a free module and
   vanishes.

The shapes are aligned with the abstract patching formalization of the
FLT project (`FLT/Patching/{Algebra,Module,System,REqualsT}.lean`,
Andrew Yang) so that its sorry-free material can be vendored to
discharge leaf 2; note that that development ends at
`ker_RtoT_le_nilradical` (`R_red = 𝕋_red`), while the freeness route
through Diamond 1997 taken here yields full injectivity — the
difference is exactly leaf 3's Auslander–Buchsbaum input, for which
mathlib currently has no depth/Cohen–Macaulay theory (audited
2026-07-24: no `Module.depth`, no Auslander–Buchsbaum under
`Mathlib/RingTheory/`; the FLT project's `FLT/Patching/Utils/Depth.lean`
is a vendorable model). -/

/-- **Taylor–Wiles prime sets.**  A finite set `Q` of rational primes
is a Taylor–Wiles set of level `n` for the residual representation
`ρbar` if every `q ∈ Q` is a prime that is `≡ 1 (mod p^n)` and whose
Frobenius characteristic polynomial under `ρbar` splits over the
residual coefficient ring with two DISTINCT roots (the classical
"`ρbar(Frob_q)` has distinct rational eigenvalues" condition; the two
roots are the eigenvalues `α_q ≠ β_q`).  For `n ≥ 1` the congruence
forces `q ∉ {2, p}` (as `q ≥ p^n + 1 ≥ 4`), so such `q` are unramified
for any hardly ramified `ρbar` and `charFrob` at `q` genuinely reads
off the Frobenius conjugacy class.  This is the local condition that
makes the auxiliary deformation theory at `q` a torus: the deformation
of a `q`-unramified representation with distinct Frobenius eigenvalues
along `q ≡ 1 (mod p^n)` splits into two characters, giving the
`ℤ_p[Δ_Q]`-structure (`Δ_Q = ∏_{q ∈ Q} (ℤ/q)^×(p)`) on the auxiliary
Hecke modules that patching feeds on (Taylor–Wiles, Ann. of Math. 141
(1995), §2; Diamond–Darmon–Taylor (1995), §5.3; the eigenvalue
rationality over the FIXED `k` follows classically after the harmless
scalar enlargement built into the choice of `k`, and abstractly is
part of the audited hypothesis set). -/
def IsTaylorWilesPrimeSet.{uK, uW}
    {k : Type uK} [CommRing k] [TopologicalSpace k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (ρbar : GaloisRep ℚ k W) (p n : ℕ) (Q : Finset ℕ) : Prop :=
  ∀ q ∈ Q, ∃ hq : q.Prime,
    q ≡ 1 [MOD p ^ n] ∧
    ∃ α β : k, α ≠ β ∧
      ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
        (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C β)

/-- **Existence of Taylor–Wiles primes** (patching leaf 1; sorry
node): for the irreducible hardly ramified residual `ρbar` there are
Taylor–Wiles prime sets of every level `n` and every size `r`.

Classical route: apply Chebotarev density to the compositum of the
splitting field of `ρbar` and `ℚ(ζ_{p^n})`.  One needs an element
`σ ∈ Gal(F(ζ_{p^n})/ℚ)` that fixes `ζ_{p^n}` and has `ρbar(σ)` with
distinct eigenvalues; this is the classical group-theoretic lemma of
Wiles/Taylor–Wiles (Wiles, Ann. of Math. 141 (1995), ch. 3, Lemma
"1.10–1.12" circle; Diamond–Darmon–Taylor (1995), Lemma 5.31; de
Shalit in Cornell–Silverman–Stevens, §"Taylor–Wiles primes"), and its
proof uses exactly this pillar's standing hypotheses: `p` odd and
`ρbar` irreducible (whence `ρbar` restricted to `Gal(ℚ(ζ_p))` is
absolutely irreducible for hardly ramified — odd, cyclotomic
determinant — `ρbar`, so the image cannot centralize `ζ_{p^n}`-fixing
subgroups into scalars).  Primes `q` whose Frobenius lies in the
conjugacy class of `σ` then satisfy both conditions, and Chebotarev
supplies infinitely many, hence sets of any size.  In this project the
Frobenius-density input is CONSUMABLE: the Chebotarev development of
`Fermat/FLT/GaloisRepresentation/Chebotarev.lean` provides
`dense_conjClasses_globalFrob` (density of the global Frobenius
conjugacy classes avoiding any finite set of places in `Γ ℚ`) together
with `charFrob_eq_charpoly_globalFrob`, which translate "Frobenius in
the open conjugation-stable set determined by `σ`" into exactly the
`charFrob` splitting recorded by `IsTaylorWilesPrimeSet` (the
eigenvalue condition is open: it is detected by the discriminant and
the finitely many coefficient values over the finite `k`).

Both-ways audit: at the intended instantiation this is the cited
Taylor–Wiles prime existence; abstractly the hypothesis set contains
the classically unsatisfiable irreducible hardly ramified `ρbar`
(section audit of `Interface.lean`), so the statement is also
classically true outright.  CIRCULARITY GUARD (inherited from pillar
3b): must not be proven through `Family.lean` or anything downstream
of it. -/
theorem exists_taylorWilesPrimeSet.{uK, uW}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hpodd hW ρbar)
    (hirr : ρbar.IsIrreducible) (n r : ℕ) :
    ∃ Q : Finset ℕ, r ≤ Q.card ∧ IsTaylorWilesPrimeSet ρbar p n Q :=
  sorry

set_option linter.checkUnivs false in
/-- **The patched module** — the limit object of the Taylor–Wiles
patching process, recorded with exactly the properties the injectivity
assembly consumes.  Classically (Taylor–Wiles, Ann. of Math. 141
(1995); Diamond, Invent. Math. 128 (1997); Diamond–Darmon–Taylor
(1995), §5.5; Kisin, Ann. of Math. 170 (2009) for the flat-condition
refinement matching `IsFlatAt`), the data is produced by running the
pigeonhole/inverse-limit argument over a tower of Taylor–Wiles levels
`Q_n`:

* `q` is the common size `#Q_n = dim_k H¹_{Q_n}(ℚ, ad⁰ρbar)` given by
  Wiles's product formula (the numerical coincidence that drives the
  whole method).
* The coefficient ring of the limit is `R_∞ = ℤ_p[[x₁, …, x_q]]`: the
  auxiliary deformation rings `R_{Q_n}` are quotients of a power
  series ring in `q` variables (tangent-space bound from the
  `Q_n`-cohomology count), and in the FLT setting the local conditions
  are SMOOTH — flatness at `p` is Ramakrishna's condition
  (Compositio 87 (1994)), the tame condition at `2` is of CDT ordinary
  type (JAMS 12 (1999), §2) — so the patched deformation ring is the
  full power series ring; this concrete choice is the statement-level
  form of "`R_∞` is regular of dimension `1 + q`".
* `Minf` is the patched Hecke module `M_∞ = lim H_{Q_{n(m)}}/(fixed
  open levels)` with its `R_∞`-action.
* `exists_isRegular` is the Taylor–Wiles freeness input: each `H_Q` is
  finite FREE over the auxiliary group ring `ℤ_p[Δ_Q]` (Taylor–Wiles,
  the key Lemma; Diamond 1997, Thm. 2.1 removes multiplicity one), so
  `M_∞` is finite free over `Λ_∞ = ℤ_p[[S₁, …, S_q]]` and the images
  of the maximal `Λ_∞`-regular sequence `(p, S₁, …, S_q)` form an
  `M_∞`-regular sequence of length `q + 1` inside the maximal ideal of
  `R_∞` — the statement "depth_{R_∞} M_∞ ≥ q + 1 = dim R_∞" in
  regular-sequence vocabulary (mathlib has no depth theory; see the
  section comment).
* `toRuniv` is the patching surjection `R_∞ ↠ R_univ` (classically
  `R_univ = R_∞/(S₁, …, S_q)R_∞`; its existence for the abstract
  `Runiv` of the pillar is Cohen-structure-theoretic: a complete
  Noetherian local `ℤ_p`-algebra with finite residue field is a
  power-series quotient).
* `M0` is the bottom Hecke module (classically `H¹(X₀(N), ℤ_p)_𝔪`, a
  module over the Hecke side `T` of the pillar), `proj` the patching
  identification `M_∞/𝔞M_∞ ≅ M₀` (`𝔞 = ker toRuniv`), stated as: a
  surjective additive map whose kernel is exactly `𝔞·M_∞`
  (`mem_smul_top_of_proj_eq_zero` gives the nontrivial inclusion; the
  reverse is forced by `proj_smul`), and `proj_smul` the ACTION
  COMPATIBILITY: the `R_∞`-action descends through `toRuniv` and `ψ`
  to the `T`-action on `M₀`.  This last field is where the pillar's
  map `ψ` (identified with the classifying map by weak universality
  and trace compatibility) enters the patched situation.

Both-ways audit: at the intended instantiation every field is the
cited patching output; abstractly, inhabitation is asserted only by
`exists_patchedModule` below, whose hypothesis set contains the
classically unsatisfiable irreducible hardly ramified `ρbar`.  (The
`checkUnivs` linter is disabled as for
`HardlyRamifiedFiniteDeformation`: the two module universes are
deliberately independent.) -/
structure PatchedModule.{v, w, s, uR} (p : ℕ) [Fact p.Prime]
    {Runiv : Type uR} [CommRing Runiv]
    {T : Type s} [CommRing T] (ψ : Runiv →+* T) where
  /-- The number of Taylor–Wiles primes at each level (equivalently,
  power-series variables of `R_∞`). -/
  q : ℕ
  /-- The patched module `M_∞`. -/
  Minf : Type v
  [addCommGroupMinf : AddCommGroup Minf]
  [moduleMinf : Module (MvPowerSeries (Fin q) ℤ_[p]) Minf]
  /-- `M_∞` is finite over `R_∞` (patched from module-finiteness at
  every level). -/
  finiteMinf : Module.Finite (MvPowerSeries (Fin q) ℤ_[p]) Minf
  /-- The Taylor–Wiles depth input: an `M_∞`-regular sequence of
  length `q + 1` inside the maximal ideal of `R_∞` (the image of the
  maximal regular sequence of `Λ_∞ = ℤ_p[[S₁, …, S_q]]`, over which
  `M_∞` is finite free by the Taylor–Wiles freeness lemma). -/
  exists_isRegular : ∃ rs : List (MvPowerSeries (Fin q) ℤ_[p]),
    rs.length = q + 1 ∧
    (∀ x ∈ rs, x ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin q) ℤ_[p])) ∧
    RingTheory.Sequence.IsRegular Minf rs
  /-- The patching surjection `R_∞ ↠ R_univ`. -/
  toRuniv : MvPowerSeries (Fin q) ℤ_[p] →+* Runiv
  toRuniv_surjective : Function.Surjective toRuniv
  /-- The bottom Hecke module (classically `H¹(X₀(N), ℤ_p)_𝔪`). -/
  M0 : Type w
  [addCommGroupM0 : AddCommGroup M0]
  [moduleM0 : Module T M0]
  nontrivialM0 : Nontrivial M0
  /-- The bottom identification `M_∞ ↠ M_∞/𝔞M_∞ ≅ M₀`. -/
  proj : Minf →+ M0
  proj_surjective : Function.Surjective proj
  /-- Action compatibility: the `R_∞`-action on `M_∞` descends through
  `toRuniv` and `ψ` to the `T`-action on `M₀`. -/
  proj_smul : ∀ (x : MvPowerSeries (Fin q) ℤ_[p]) (m : Minf),
    proj (x • m) = ψ (toRuniv x) • proj m
  /-- The kernel of the bottom identification is exactly the
  augmentation submodule `𝔞·M_∞`, `𝔞 = ker(R_∞ ↠ R_univ)` (this
  inclusion; the reverse follows from `proj_smul`). -/
  mem_smul_top_of_proj_eq_zero : ∀ m : Minf, proj m = 0 →
    m ∈ RingHom.ker toRuniv •
      (⊤ : Submodule (MvPowerSeries (Fin q) ℤ_[p]) Minf)

/-- **The commutative-algebra endgame** (patching leaf 3; sorry node):
a finite module over the regular local ring
`R_∞ = ℤ_p[[x₁, …, x_q]]` carrying a regular sequence of length
`q + 1 = dim R_∞` inside the maximal ideal — i.e. of depth at least
`dim R_∞` — is FREE.  This is the Auslander–Buchsbaum step of the
patching argument (Diamond, *The Taylor–Wiles construction and
multiplicity one*, Invent. Math. 128 (1997), Thm. 2.4: over a regular
local ring, `depth M ≥ dim R` forces `pd M = 0`; see also
Diamond–Darmon–Taylor (1995), Thm. 5.28 and Bruns–Herzog,
*Cohen–Macaulay rings*, Thm. 1.3.3 + 2.2.7).  Unconditionally true —
no arithmetic content.  Mathlib audit (2026-07-24): mathlib has
regular sequences (`RingTheory.Sequence.IsRegular`,
`Mathlib/RingTheory/Regular/RegularSequence.lean`) but no
depth/Cohen–Macaulay/Auslander–Buchsbaum theory yet; the FLT project's
`FLT/Patching/Utils/Depth.lean` (same-shaped development, different
mathlib pin) is a vendorable model for the missing layer, and
`ℤ_p[[x₁, …, x_q]]` is regular local of dimension `q + 1` by the
standard power-series induction. -/
theorem free_of_isRegular_mvPowerSeries.{v} {p : ℕ} [Fact p.Prime] {q : ℕ}
    {M : Type v} [AddCommGroup M]
    [Module (MvPowerSeries (Fin q) ℤ_[p]) M]
    (hfin : Module.Finite (MvPowerSeries (Fin q) ℤ_[p]) M)
    {rs : List (MvPowerSeries (Fin q) ℤ_[p])} (hlen : rs.length = q + 1)
    (hmem : ∀ x ∈ rs, x ∈ IsLocalRing.maximalIdeal
      (MvPowerSeries (Fin q) ℤ_[p]))
    (hreg : RingTheory.Sequence.IsRegular M rs) :
    Module.Free (MvPowerSeries (Fin q) ℤ_[p]) M :=
  sorry

/-- **The patched faithfulness assembly** (PROVEN): a `PatchedModule`
for `ψ` forces `ψ` to be injective.  This is the classical endgame of
Taylor–Wiles patching, written out: by the Auslander–Buchsbaum leaf
(`free_of_isRegular_mvPowerSeries`) the patched module `M_∞` is free
over `R_∞`; picking a basis vector `e` and an element
`x ∈ R_∞` lifting a given `r ∈ ker ψ` (via the patching surjection
`toRuniv`), the action compatibility `proj_smul` shows
`proj (x • e) = ψ(r) • proj e = 0`, so `x • e` lies in the
augmentation submodule `𝔞·M_∞` (`mem_smul_top_of_proj_eq_zero`);
reading off the `e`-coordinate — a basis coordinate functional maps
`𝔞·M_∞` into `𝔞` — gives `x ∈ 𝔞 = ker toRuniv`, i.e. `r = 0`.
(Nontriviality of `M₀` guarantees the basis is nonempty.)  This is
exactly "a nonzero free module is faithful, and the `R_univ`-action on
`M₀` factors through `ψ`". -/
theorem PatchedModule.injective.{v, w, s, uR} {p : ℕ} [Fact p.Prime]
    {Runiv : Type uR} [CommRing Runiv] {T : Type s} [CommRing T]
    {ψ : Runiv →+* T} (P : PatchedModule.{v, w, s, uR} p ψ) :
    Function.Injective ψ := by
  letI := P.addCommGroupMinf
  letI := P.moduleMinf
  letI := P.addCommGroupM0
  letI := P.moduleM0
  haveI : Nontrivial P.M0 := P.nontrivialM0
  haveI : Nontrivial P.Minf := P.proj_surjective.nontrivial
  obtain ⟨rs, hlen, hmem, hreg⟩ := P.exists_isRegular
  haveI : Module.Free (MvPowerSeries (Fin P.q) ℤ_[p]) P.Minf :=
    free_of_isRegular_mvPowerSeries P.finiteMinf hlen hmem hreg
  rw [injective_iff_map_eq_zero]
  intro r hr
  obtain ⟨x, rfl⟩ := P.toRuniv_surjective r
  let b := Module.Free.chooseBasis (MvPowerSeries (Fin P.q) ℤ_[p]) P.Minf
  obtain ⟨i⟩ := b.index_nonempty
  have hproj0 : P.proj (x • b i) = 0 := by
    rw [P.proj_smul, hr, zero_smul]
  have hmem2 := P.mem_smul_top_of_proj_eq_zero _ hproj0
  have hle : Submodule.map (b.coord i)
      (RingHom.ker P.toRuniv •
        (⊤ : Submodule (MvPowerSeries (Fin P.q) ℤ_[p]) P.Minf)) ≤
      RingHom.ker P.toRuniv := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_le.mpr fun a ha y _ => by
      rw [smul_eq_mul]; exact Ideal.mul_mem_right _ _ ha
  have hcoord : b.coord i (x • b i) = x := by
    simp [Module.Basis.coord]
  have hx : x ∈ RingHom.ker P.toRuniv := by
    rw [← hcoord]
    exact hle (Submodule.mem_map_of_mem hmem2)
  exact RingHom.mem_ker.mp hx

/-- **The Taylor–Wiles patching construction** (patching leaf 2; sorry
node — the pigeonhole heart): under the full hypothesis set of pillar
3b-iii, together with the Taylor–Wiles prime supply `hTW`, the patched
situation exists.

Classical route (Taylor–Wiles, Ann. of Math. 141 (1995), as
reorganized by Diamond, Invent. Math. 128 (1997), Fujiwara, and
Diamond–Darmon–Taylor (1995) §5.5; Kisin, Ann. of Math. 170 (2009) for
the flat refinement): for each level `n` pick a Taylor–Wiles set `Q_n`
of the common size `q = dim_k H¹_{Q_n}(ad⁰ρbar)` (from `hTW` refined
by the dual-Selmer annihilation argument — the cohomological
sharpening of the prime supply is internal to this leaf, `hTW`
records its Chebotarev skeleton); form the auxiliary deformation rings
`R_{Q_n}` (quotients of `R_∞ = ℤ_p[[x₁, …, x_q]]` by the tangent-space
bound and smoothness of the local conditions — Ramakrishna flatness at
`p`, CDT tameness at `2`) and the auxiliary Hecke modules `H_{Q_n}`,
finite free over `ℤ_p[Δ_{Q_n}]` by the Taylor–Wiles freeness lemma
(Diamond 1997, Thm. 2.1, without multiplicity one); the weak
universality certificate `hfact` classifies the Hecke-side
deformations by maps out of `Runiv`, identifying `ψ` with the
classifying map on Frobenius traces (Carayol's argument pins any
trace-compatible map, which is how `hψ`, `hψalg`, `hψπ` enter); a
pigeonhole over the finitely many isomorphism types of each finite
level (or an ultrafilter, as in `FLT/Patching/Ultraproduct.lean`)
extracts a compatible subtower whose inverse limit is the
`PatchedModule`: `M_∞` finite over `R_∞` with the `(p, S₁, …, S_q)`
regular sequence, `R_∞ ↠ R_univ` the patching surjection, and the
bottom identification `M_∞/𝔞M_∞ ≅ M₀` intertwining the actions
through `ψ`.  The sorry-free abstract patching system of the FLT
project (`FLT/Patching/System.lean`, `Module.lean`, `Algebra.lean`,
`Ultraproduct.lean` — Andrew Yang; different mathlib pin, audit before
vendoring) implements exactly this extraction step.

Both-ways audit: at the intended instantiation (`Runiv` the genuine
universal ring, `T = 𝕋_𝔪`, `M₀ = H¹(X₀(N), ℤ_p)_𝔪`) this is the cited
construction; abstractly the hypothesis set contains the classically
unsatisfiable irreducible hardly ramified `ρbar` (section audit of
`Interface.lean`), so the statement is also classically true outright.
CIRCULARITY GUARD (inherited from pillar 3b): must not be proven
through `Family.lean` or anything downstream of it. -/
theorem exists_patchedModule.{v, w, s, t, uK, uW, uR}
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
        (ρT.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)
    (hTW : ∀ n r : ℕ, ∃ Q : Finset ℕ,
      r ≤ Q.card ∧ IsTaylorWilesPrimeSet ρbar p n Q) :
    Nonempty (PatchedModule.{v, w, s, uR} p ψ) :=
  sorry

/-- **Taylor–Wiles patching: `R = 𝕋`, the injectivity half** (pillar
3b-iii; ASSEMBLED 2026-07-24 from the three patching leaves above —
the mathematical heart of the modularity-lifting
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
    Function.Injective ψ := by
  obtain ⟨P⟩ :=
    exists_patchedModule.{uR, s, s, t, uK, uW, uR} hpodd hW hρbar hirr hadic
      hcomplete hranku hρuniv hπuniv hunivred hfact hrankT hρT hπ hred ψ hψalg
      hψπ hψ (exists_taylorWilesPrimeSet hpodd hW hρbar hirr)
  exact P.injective

end GaloisRepresentation.Modularity
