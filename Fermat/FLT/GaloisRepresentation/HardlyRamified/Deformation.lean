/-
GaloisRepresentation/HardlyRamified/Deformation.lean — own work for the
Fermat project (not vendored from the FLT project).

# The Khare–Wintenberger lifting development, Family-free, over a general
finite coefficient field

This module is the proof-sharing refactor (2026-07-24) anticipated by
pillar α of `Modularity/KhareWintenberger.lean` and by `Lift.lean`'s
B6a: the deformation-theoretic lifting development formerly inlined in
`Lift.lean` — Mazur's category (`HardlyRamifiedDeformation`), the
universality strata, the finiteness and presentation strata with their
commutative-algebra leaves, the topology glue, the base-change /
conjugation transfer lemmas and the specialization-to-a-domain endgame
— extracted with exactly two deliberate changes:

1. **Family-freedom.** `Lift.lean` `public import`s `Family.lean`, which
   imports `Modularity/Interface.lean`, which imports
   `Modularity/KhareWintenberger.lean`; so nothing living in `Lift.lean`
   can be consumed by the Khare–Wintenberger cut without closing the
   interface's forbidden dependency cycle. The import audit (2026-07-24)
   showed the deformation development consumes NOTHING from
   `Family.lean` — only the B6bc compatibility chain, which stays in
   `Lift.lean`, does. This module imports only `Defs.lean`,
   `Chebotarev.lean` (proof-only, for `globalFrob`) and mathlib, so both
   `Lift.lean` (at `k = ZMod ℓ`) and `KhareWintenberger.lean` (pillar α)
   consume it. CIRCULARITY GUARD: no import from `Family.lean`,
   `Lift.lean` or `Modularity/*` may ever be added here.

2. **Coefficient generalization `ZMod ℓ` → `k`.** The residue
   coefficient field is an arbitrary finite field `k` carrying
   `Algebra ℤ_[ℓ] k` — which forces `char k = ℓ`
   (`natCast_self_eq_zero`) — as pillar α requires. Two statements
   changed shape relative to the historical `ZMod ℓ` development:
   * a reduction map `π : R →+* k` is no longer automatically surjective
     (over `ZMod ℓ` its image is a subring of the prime field), so
     surjectivity became a structure field of `HardlyRamifiedDeformation`
     (`π_surjective`) — matching Mazur's deformation category, where the
     residue identification is part of the data;
   * the presentation strata present the universal ring over a
     coefficient ring `Λ` — classically the Witt vectors `W(k)`, and
     just `ℤ_ℓ` at `k = ZMod ℓ` — pinned up to isomorphism by:
     complete Noetherian local domain, module-finite over `ℤ_ℓ`, maximal
     ideal `(ℓ)` (unramifiedness), residue field `k` (forced by the
     surjection onto the deformation ring). The pure
     commutative-algebra leaves (`isNoetherianRing_mvPowerSeries`, the
     prime-chain and height lemmas, the Krull glue) are correspondingly
     stated over an arbitrary Noetherian local domain base.

The sorried leaves (all SHARED by the two consumers; the names are those
of their historical `Lift.lean` twins — `exists_conj_of_charFrob_eq` was
PROVEN 2026-07-24 via the shared Chebotarev–Brauer–Nesbitt node of
`BrauerNesbittConjugacy.lean`).

ONE LEAF PER LINE, and please keep it that way: this list conflicted on
five consecutive integrations in a single day because concurrent owners
each re-flowed the same prose paragraph. One name per line means two
owners adding different leaves touch different lines, and git merges
them without a human. Do not re-wrap it.

- `finite_setOf_isHardlyRamified_frames`
- `exists_isStrictlyUniversalOnFrames_of_finite_lifts`
- `isWeaklyUniversalOnIdentifiedFrames_of_finite`
- `exists_isLocalRing_traceSubring`
- `exists_framedGaloisRep_traceSubring`
- `subring_closure_charFrob_coeff_eq_top`
- `eq_maximalIdeal_of_isPrime_of_isWeaklyUniversal_isTraceGenerated`
- `exists_coefficientRing_ringHom`
- `surjective_of_mvPowerSeries_ringHom`
- `ker_le_of_minimal_mvPowerSeries_ringHom`
- `exists_relations_lt_le_smul_of_minimal_mvPowerSeries_presentation`

Both former strata above them were narrowed on 2026-07-25 into those
ten, and every statement they replace is now PROVEN here.

* The three UNIVERSALITY leaves were narrowed so that the universality
  leaf carries the representation-level classifying datum rather than
  its `charFrob` shadow, the Carayol leaf receives the Chebotarev
  density step as a hypothesis, and the finiteness leaf is stated as
  `𝔪`-primarity of `(ℓ)`; the trace-shadow glue, the density step and
  the Artinian-to-finite dévissage are PROVEN, in
  `exists_isWeaklyUniversalOnIdentified`,
  `exists_isTraceGenerated_ringHom` and
  `finite_quotient_span_of_isWeaklyUniversal_isTraceGenerated`
  respectively (the last over the general lemma
  `finite_quotient_of_maximalIdeal_pow_le`).
* Mazur representability was then CUT AGAIN, along Schlessinger's
  architecture, into `exists_isStrictlyUniversalOnFiniteFrames` (all of
  the arithmetic, tested only against finite/Artinian raw framed test
  objects) and `isWeaklyUniversalOnIdentifiedFrames_of_finite` (the pure
  commutative-algebra/topology pro-finite limit);
  `exists_isWeaklyUniversalOnIdentifiedFrames` is PROVEN over them, the
  glue showing that a finite object of the bundled deformation category
  IS a raw Schlessinger test object — which is why the leaves carry no
  `IsModuleTopology`, Noetherian, adic or completeness burden.
  `exists_isStrictlyUniversalOnFiniteFrames` was then CUT once more
  (2026-07-26) into H3 (`finite_setOf_isHardlyRamified_frames`), H4
  (`exists_smul_eq_of_commute_of_isIrreducible`) and the
  deformation-theoretic core
  `exists_isStrictlyUniversalOnFrames_of_finite_lifts`, over which it is
  now PROVEN (the bundling glue, `charFrob_compat` from the residual
  identification). **H4 was then PROVEN outright (2026-07-26)** over the
  new complex-conjugation vocabulary
  `GaloisRepresentation/ComplexConjugation.lean` — `complexConj : Γ ℚ`,
  its involutivity, and `cyclotomicCharacter_complexConj` (the character
  sends it to `−1`) — so only H3 and the core remain as leaves of that
  cut.
* The two PRESENTATION leaves became proven assemblies over the four
  commutative-algebra strata of the minimal presentation and the
  arithmetic relation count: `exists_minimal_mvPowerSeries_presentation`
  is PROVEN over `exists_coefficientRing_ringHom`, the convergent
  substitution `exists_mvPowerSeries_ringHom_of_mem_maximalIdeal`
  (itself PROVEN, through mathlib's `MvPowerSeries.eval₂Hom`),
  `surjective_of_mvPowerSeries_ringHom` and
  `ker_le_of_minimal_mvPowerSeries_ringHom`, over the PROVEN choice of a
  minimal generating family `exists_minimal_span_sup_of_isNoetherianRing`;
  and `exists_relations_lt_of_minimal_mvPowerSeries_presentation` is
  PROVEN by Nakayama over
  `exists_relations_lt_le_smul_of_minimal_mvPowerSeries_presentation`.
  That arithmetic leaf was RESTATED on 2026-07-25: its conclusion
  `r < g` is FALSE (it fails whenever the deformation problem is rigid,
  `g = r = 0`, and for a characteristic-`0` coefficient ring it
  contradicts the finiteness stratum of this very module, since
  `r < g` would force `dim D.R ≥ 2`). Poitou–Tate gives `r ≤ g`; the
  unit of Krull dimension that the endgame needs is `dim Λ = 1`, now
  carried explicitly as `ℓ ≠ 0` in `Λ` and consumed by the
  strengthened `succ_le_height_maximalIdeal_mvPowerSeries`. See that
  leaf's docstring for the Euler-characteristic computation.

* The FINITENESS leaf was then narrowed once more: its `𝔪`-primarity
  form `exists_maximalIdeal_pow_le_span_of_isWeaklyUniversal_isTraceGenerated`
  is now PROVEN over the pure commutative algebra
  `exists_maximalIdeal_pow_le_span_of_forall_isPrime` (Noetherian local,
  `𝔪` the only prime containing `x` ⟹ `∃ n, 𝔪^n ≤ (x)`), leaving the
  strictly geometric `eq_maximalIdeal_of_isPrime_of_isWeaklyUniversal_isTraceGenerated`
  — the mod-`ℓ` fibre of `Spec D.R` is one point. That pointwise form is
  what this module's own specialization machinery consumes
  (`isFlatAt_baseChange_quotient`, `isTameAtTwo_baseChange`,
  `isHardlyRamified_baseChange_quotient` are all stated for PRIME
  quotients), and it is the exact `dim ≤ 1` counterpart of the already
  proven `exists_isPrime_lt_maximalIdeal_of_isWeaklyUniversal_isTraceGenerated`.

* The CARAYOL leaf was then decomposed once more, into
  `exists_isLocalRing_traceSubring` (the ring-theoretic half of
  Théorème 1: `R'` local, Noetherian — the real content, false for a
  general closed subring of a complete Noetherian local ring — with
  subspace topology `𝔪'`-adic and adically complete),
  `exists_framedGaloisRep_traceSubring` (Théorème 1 proper: conjugation
  of `D.ρ` into `GL₂(R')` by the Rouquier–Nyssen pseudo-character route,
  plus descent of the hardly ramified conditions) and
  `subring_closure_charFrob_coeff_eq_top` (`k` IS the trace field of
  `ρbar`). The descent assembly and `traceSubring_eq_top_of_charFrob_map`
  — that `R'` is topologically generated by the traces of the DESCENDED
  representation, the half Théorème 1 does not give you — are PROVEN.

  **Statement-level caveat, isolated deliberately rather than buried:**
  this node is false as written unless the Frobenius-trace field of
  `ρbar` is all of `k`, because `π_surjective` demands the descended
  ring's residue field be `k` on the nose while `R'`'s residue field is
  the trace field. That is not an artifact of the split — the node's own
  conclusion implies it — and it is exactly what
  `subring_closure_charFrob_coeff_eq_top` states. It is trivially true at
  `k = 𝔽_ℓ` (the Frey-curve consumer in `Lift.lean`); for pillar α's
  general `k` it is the usual "take `k` to be the trace field"
  normalization, the alternative being to narrow `k` at the pillar-α
  interface.

Everything else is proven glue, culminating in
`exists_hardlyRamified_lift_of_five_le` — verbatim the statement of
Khare–Wintenberger pillar α
(`exists_hardlyRamified_lift_residual_of_five_le`).
-/
module

public import Fermat.FLT.GaloisRepresentation.HardlyRamified.Defs
-- `IsAdic` / `IsAdicComplete`: they appear in the exposed field types of
-- the deformation-category structure `HardlyRamifiedDeformation`.
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.RingTheory.AdicCompletion.Basic
-- `MvPowerSeries` with its local-ring structure, and `Ideal.height`:
-- the vocabulary of the Böckle presentation stratum (exposed in the
-- presentation-leaf signatures).
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.Ideal.Height
-- single-variable power series: the variable-splitting leaf
-- `nonempty_ringEquiv_mvPowerSeries_powerSeries` is stated on them.
public import Mathlib.RingTheory.PowerSeries.Basic
-- proof-only: `globalFrob` (the Frobenius transport of
-- `charpoly_baseChange_conj`'s consumers) — Family-free, see the module
-- docstring.
import Fermat.FLT.GaloisRepresentation.Chebotarev
-- proof-only: the shared Chebotarev–Brauer–Nesbitt conjugacy node
-- (`exists_conj_of_charFrob_eq_away`), from which the `{2, ℓ}` leaf
-- below is derived.
import Fermat.FLT.GaloisRepresentation.BrauerNesbittConjugacy
-- proof-only: complex conjugation as an element of `Γ ℚ`
-- (`complexConj`, `complexConj_mul_self`,
-- `cyclotomicCharacter_complexConj`) — the oddness vocabulary consumed by
-- the H4 Schur stratum below. Its own import cone is pure mathlib, so it
-- cannot close the forbidden Khare–Wintenberger cycle.
import Fermat.FLT.GaloisRepresentation.ComplexConjugation
-- proof-only: the characteristic of a finite field, `ℤ_ℓ`-unit lemmas.
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Padics.RingHoms
-- Krull's height theorem, consumed by the PROVEN Krull glue
-- `exists_isPrime_lt_maximalIdeal_of_mvPowerSeries_presentation`.
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
-- proof-only: the Hilbert-basis instance `IsNoetherianRing R⟦X⟧`, the
-- domain instances for (multivariate) power series.
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
-- proof-only: Nakayama's lemma, the generation step of the Böckle
-- relation-bound assembly.
import Mathlib.RingTheory.Nakayama
-- proof-only: evaluation of multivariate power series at topologically
-- nilpotent elements, and the bridge from `IsAdicComplete` to
-- `CompleteSpace` + `T2Space` in the adic topology — together they give
-- the substitution homomorphism of the de Smit–Lenstra presentation.
import Mathlib.RingTheory.MvPowerSeries.Evaluation
import Mathlib.RingTheory.AdicCompletion.Topology
-- proof-only imports for the topology glue
-- `isModuleTopology_of_isAdic_maximalIdeal`.
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.RingTheory.Noetherian.Basic
-- proof-only: `Ideal.finite_quotient_pow` and `Ideal.Quotient.factor`, the
-- two ingredients of the finiteness glue
-- `finite_quotient_of_maximalIdeal_pow_le`.
import Mathlib.RingTheory.Ideal.Quotient.Index
-- proof-only: charpoly bridges and base-change linear algebra.
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

open GaloisRepresentation Polynomial

namespace GaloisRepresentation

universe u v
/-- The standard rank-2 free module `Fin 2 → O` has rank 2. -/
lemma rank_finTwoFun (O : Type*) [CommRing O] [Nontrivial O] :
    Module.rank O (Fin 2 → O) = 2 := by
  simp

variable {ℓ : ℕ} [Fact ℓ.Prime] (hℓOdd : Odd ℓ)
variable {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]

/-- **A finite field receiving `ℤ_ℓ` has characteristic `ℓ`** (PROVEN,
elementary): the characteristic of the finite field `k` is a prime `p`;
were `p ≠ ℓ`, then `p` would be a unit of `ℤ_ℓ` dying in `k` under the
structure map — impossible in the nontrivial `k`. Stated as the
vanishing of `(ℓ : k)`, the form the completeness bootstrap
`moduleFinite_of_finite_quotient_span` consumes (over `ZMod ℓ` this was
`ZMod.natCast_self`). -/
lemma natCast_self_eq_zero : ((ℓ : ℕ) : k) = 0 := by
  have hp : (ringChar k).Prime :=
    (CharP.char_is_prime_or_zero k (ringChar k)).resolve_right
      (CharP.char_ne_zero_of_finite k (ringChar k))
  by_cases hne : ringChar k = ℓ
  · rw [← hne]
    exact ringChar.Nat.cast_ringChar
  · exfalso
    have hunit : IsUnit ((ringChar k : ℕ) : ℤ_[ℓ]) :=
      PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr
        ((Nat.coprime_primes (Fact.out : ℓ.Prime) hp).mpr
          (fun h => hne h.symm)))
    have hzero : algebraMap ℤ_[ℓ] k ((ringChar k : ℕ) : ℤ_[ℓ]) = 0 := by
      rw [map_natCast]
      exact ringChar.Nat.cast_ringChar
    have hu := hunit.map (algebraMap ℤ_[ℓ] k)
    rw [hzero] at hu
    exact not_isUnit_zero hu

variable [TopologicalSpace k] [DiscreteTopology k]
variable {V : Type v} [AddCommGroup V] [Module k V]
  [Module.Finite k V] [Module.Free k V]
  (hdim : Module.rank k V = 2)
set_option backward.isDefEq.respectTransparency false in
open scoped TensorProduct in
/-- Characteristic-polynomial transport through base change and framing:
the family-membership equation `(τ.baseChange B).conj e = σ_φ` identifies
the characteristic polynomials of the family member with the images of
those of `τ` under the coefficient map. (Ingredient of the proof of
`residual_charFrob_eq_of_family`.) -/
lemma charpoly_baseChange_conj {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] {B : Type*} [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [Algebra A B] [ContinuousSMul A B]
    {W : Type*} [AddCommGroup W] [Module A W] [Module.Finite A W]
    [Module.Free A W] {N : Type*} [AddCommGroup N] [Module B N]
    [Module.Finite B N] [Module.Free B N]
    (τ : GaloisRep ℚ A W) (e : (B ⊗[A] W) ≃ₗ[B] N)
    (g : Field.absoluteGaloisGroup ℚ) :
    (((τ.baseChange B).conj e) g).charpoly =
      ((τ g).charpoly).map (algebraMap A B) := by
  rw [GaloisRep.conj_apply, LinearEquiv.charpoly_conj]
  show ((Module.End.baseChangeHom A B W) (τ g)).charpoly = _
  rw [show (Module.End.baseChangeHom A B W) (τ g) =
    LinearMap.baseChange B (τ g) from rfl, LinearMap.charpoly_baseChange]

/-- A *hardly ramified deformation* of a mod-`ℓ` representation `ρbar`, in
Mazur's category: a coefficient ring `R` — a Noetherian local topological
`ℤ_ℓ`-algebra whose topology is the `𝔪`-adic one (`isAdic`) and which is
`𝔪`-adically complete and separated (`isAdicComplete`) — together with a
hardly ramified framed representation over `R` and a SURJECTIVE reduction
map to the coefficient field `k` matching the characteristic polynomials
of Frobenius of `ρbar` at all good primes.

Unlike `HardlyRamifiedLift`, the ring is *not* required to be a domain,
to be module-finite over `ℤ_ℓ`, or to have characteristic zero: the
universal deformation ring of the hardly ramified problem lives in this
category, and the three sorried strata below
(`exists_universal_hardlyRamifiedDeformation`,
`moduleFinite_of_isUniversal`, `algebraMap_injective_of_isUniversal`) pin
its finer properties down one at a time. The residue field is `k`: `π`
is surjective (`π_surjective` — automatic over `ZMod ℓ`, where the image
is a subring of the prime field, and part of Mazur's category data for
general `k`), so `ker π` is a maximal ideal of the local ring `R`,
necessarily the maximal ideal. -/
structure HardlyRamifiedDeformation (ρbar : GaloisRep ℚ k V) where
  /-- The coefficient ring of the deformation. -/
  R : Type u
  [commRing : CommRing R]
  [topologicalSpace : TopologicalSpace R]
  [isTopologicalRing : IsTopologicalRing R]
  [isLocalRing : IsLocalRing R]
  [algebra : Algebra ℤ_[ℓ] R]
  [isNoetherianRing : IsNoetherianRing R]
  /-- The topology of the coefficient ring is the maximal-adic one. -/
  isAdic : IsAdic (IsLocalRing.maximalIdeal R)
  /-- The coefficient ring is maximal-adically complete and separated. -/
  isAdicComplete : IsAdicComplete (IsLocalRing.maximalIdeal R) R
  /-- The deformation, framed by the standard basis. -/
  ρ : FramedGaloisRep ℚ R (Fin 2)
  /-- The deformation is hardly ramified. -/
  isHardlyRamified : IsHardlyRamified hℓOdd (rank_finTwoFun R) ρ
  /-- The reduction map to the residue characteristic-`ℓ` world. -/
  π : R →+* k
  /-- The reduction map is surjective onto the coefficient field: `k` IS
  the residue field of `R`. Automatic for `k = ZMod ℓ` (the image is a
  subring of the prime field, hence everything —
  `ZMod.ringHom_surjective`); for a general finite `k` it is part of
  Mazur's deformation-category data. -/
  π_surjective : Function.Surjective π
  /-- The deformation reduces to `ρbar`: the characteristic polynomials
  of Frobenius match at every prime `q ∉ {2, ℓ}`. -/
  charFrob_compat : ∀ q (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
    (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
      ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat

/-- A hardly ramified deformation `D` of `ρbar` is *universal* if every
hardly ramified deformation `D'` of `ρbar` receives a **unique**
`ℤ_ℓ`-algebra homomorphism `f : D.R → D'.R` compatible with the two
reduction maps and with the characteristic polynomials of Frobenius at
all good primes.

This is Mazur universality expressed through the trace data rather than
through strict equivalence of representations, which keeps the statement
inside the repository's charpoly vocabulary. Both halves of the `∃!` are
load-bearing:

* *Existence* fails for proper quotients of the universal ring (composing
  `R^{univ} ↠ D.R → R^{univ}` would split the quotient, by uniqueness of
  compatible endomorphisms of `R^{univ}` — Carayol: for `ρbar` absolutely
  irreducible the universal ring is topologically generated by traces of
  Frobenii, which the compatibility clause pins).
* *Uniqueness* fails for inflations of the universal ring: `R^{univ}[[t]]`
  (deformation constant in `t`) maps to `R^{univ}[[t]]/(t²)` compatibly
  via both `t ↦ 0` and `t ↦ t̄`, and the square-zero extension
  `R^{univ} ⊕ 𝔽_ℓ ε` maps to itself compatibly via both `ε ↦ ε` and
  `ε ↦ 0`. Without the uniqueness clause the finiteness stratum
  `moduleFinite_of_isUniversal` below would be *false* (`R^{univ}[[t]]`
  would satisfy the mapping property); with it, any two universal data
  are canonically isomorphic, and any universal datum is isomorphic to
  the genuine universal deformation ring.

(For the truth of the strata below it also matters that divisible
square-zero inflations such as `R^{univ} ⊕ ℚ_ℓ ε` are excluded: there
`ε ↦ 0` *is* the unique compatible map to any Noetherian datum, since a
divisible submodule must die in a finite `ℤ_ℓ`-module — but such a ring
is not Noetherian (`ℓ` acts invertibly on the ideal `ℚ_ℓ ε`, so by
Nakayama it is not finitely generated), so the `isNoetherianRing` field
of `HardlyRamifiedDeformation` already rules it out.) -/
def HardlyRamifiedDeformation.IsUniversal {ρbar : GaloisRep ℚ k V}
    (D : HardlyRamifiedDeformation hℓOdd ρbar) : Prop :=
  letI := D.commRing; letI := D.topologicalSpace; letI := D.isTopologicalRing
  letI := D.isLocalRing; letI := D.algebra
  ∀ D' : HardlyRamifiedDeformation hℓOdd ρbar,
    letI := D'.commRing; letI := D'.topologicalSpace
    letI := D'.isTopologicalRing; letI := D'.isLocalRing; letI := D'.algebra
    ∃! f : D.R →+* D'.R,
      f.comp (algebraMap ℤ_[ℓ] D.R) = algebraMap ℤ_[ℓ] D'.R ∧
      D'.π.comp f = D.π ∧
      ∀ q (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
        (D.ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map f =
          D'.ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat

/-- The **existence half** of `IsUniversal`: every hardly ramified
deformation `D'` of `ρbar` receives at least one `ℤ_ℓ`-algebra
homomorphism from `D` compatible with the reduction maps and the
characteristic polynomials of Frobenius. This is what Mazur-style
representability (the framed functor with the hardly ramified conditions
cut in) produces directly; the uniqueness half is supplied separately by
trace generation (`IsTraceGenerated`) through the purely formal Carayol
argument `isUniversal_of_isWeaklyUniversal_isTraceGenerated` below. Weak
universality alone is strictly weaker than `IsUniversal`: the inflation
`R^{univ}[[t]]` (deformation constant in `t`) is weakly universal but
not universal. -/
def HardlyRamifiedDeformation.IsWeaklyUniversal
    {ρbar : GaloisRep ℚ k V}
    (D : HardlyRamifiedDeformation hℓOdd ρbar) : Prop :=
  letI := D.commRing; letI := D.topologicalSpace; letI := D.isTopologicalRing
  letI := D.isLocalRing; letI := D.algebra
  ∀ D' : HardlyRamifiedDeformation hℓOdd ρbar,
    letI := D'.commRing; letI := D'.topologicalSpace
    letI := D'.isTopologicalRing; letI := D'.isLocalRing; letI := D'.algebra
    ∃ f : D.R →+* D'.R,
      f.comp (algebraMap ℤ_[ℓ] D.R) = algebraMap ℤ_[ℓ] D'.R ∧
      D'.π.comp f = D.π ∧
      ∀ q (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
        (D.ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map f =
          D'.ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat

/-- **Trace generation** (Carayol): the coefficient ring of `D` is
topologically generated, as a `ℤ_ℓ`-algebra, by the coefficients of the
characteristic polynomials of Frobenius at the good primes — the closure
of the subring generated by the image of `ℤ_ℓ` together with all
`charFrob` coefficients is everything. For the genuine universal ring of
an absolutely irreducible `ρbar` this holds by Carayol's theorem (the
universal ring is topologically generated by traces of Frobenii, and the
trace at `Frob_q` is `−(coeff 1)` of the degree-2 `charFrob`); it is
exactly what makes compatible homomorphisms out of `D` unique, turning
weak universality into universality. -/
def HardlyRamifiedDeformation.IsTraceGenerated
    {ρbar : GaloisRep ℚ k V}
    (D : HardlyRamifiedDeformation hℓOdd ρbar) : Prop :=
  letI := D.commRing; letI := D.topologicalSpace; letI := D.isTopologicalRing
  letI := D.algebra
  (Subring.closure (Set.range (algebraMap ℤ_[ℓ] D.R) ∪
      {x : D.R | ∃ q, ∃ hq : q.Prime, q ≠ 2 ∧ q ≠ ℓ ∧ ∃ n : ℕ,
        x = (D.ρ.charFrob
          hq.toHeightOneSpectrumRingOfIntegersRat).coeff n})).topologicalClosure
    = ⊤

/-- The **trace-descent relation** (Carayol): `D'` is a trace-generated
hardly ramified deformation equipped with a ring homomorphism
`ι : D'.R → D.R` compatible with the `ℤ_ℓ`-structure maps, the
reduction maps, and the Frobenius characteristic polynomials —
abstractly, the descended datum over the closed subalgebra of `D.R`
topologically generated by the `charFrob` coefficients, together with
its inclusion. Bundled as a definition (rather than inlined in the
existential of `exists_isTraceGenerated_ringHom`) so that the instance
`letI`s live under plain parameters, following the pattern of
`IsUniversal`/`IsWeaklyUniversal`. -/
def HardlyRamifiedDeformation.IsTraceDescent {ρbar : GaloisRep ℚ k V}
    (D D' : HardlyRamifiedDeformation hℓOdd ρbar) : Prop :=
  letI := D.commRing; letI := D.topologicalSpace
  letI := D.isTopologicalRing; letI := D.isLocalRing; letI := D.algebra
  letI := D'.commRing; letI := D'.topologicalSpace
  letI := D'.isTopologicalRing; letI := D'.isLocalRing; letI := D'.algebra
  D'.IsTraceGenerated ∧
  ∃ ι : D'.R →+* D.R,
    ι.comp (algebraMap ℤ_[ℓ] D'.R) = algebraMap ℤ_[ℓ] D.R ∧
    D.π.comp ι = D'.π ∧
    ∀ q (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (D'.ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map ι =
        D.ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat

/-- An adically-topologized, adically-separated ring is Hausdorff: `{0}`
is the intersection of the closed (open) subgroups `I ^ k`, hence closed
(PROVEN, elementary; extracted from the proof of
`isModuleTopology_of_isAdic_maximalIdeal` below for reuse in the
uniqueness half of universality). -/
lemma t2Space_of_isAdic {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] {I : Ideal R} (hadic : IsAdic I)
    [IsHausdorff I R] : T2Space R := by
  have hclosed : IsClosed ({(0 : R)} : Set R) := by
    have h0 : ({(0 : R)} : Set R) = ⋂ k : ℕ, ((I ^ k : Ideal R) : Set R) := by
      ext x
      simp only [Set.mem_singleton_iff, Set.mem_iInter, SetLike.mem_coe]
      constructor
      · rintro rfl k
        exact Submodule.zero_mem _
      · intro hx
        refine IsHausdorff.haus (inferInstance : IsHausdorff I R) x
          fun k => ?_
        rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
        exact hx k
    rw [h0]
    refine isClosed_iInter fun k => ?_
    exact AddSubgroup.isClosed_of_isOpen (Submodule.toAddSubgroup (I ^ k))
      ((isAdic_iff.mp hadic).1 k)
  haveI := IsTopologicalAddGroup.t1Space R hclosed
  infer_instance

open Topology in
/-- A **local homomorphism between adically-topologized local rings is
continuous** (PROVEN, elementary): if `f` carries the maximal ideal of
`R` into the maximal ideal of `S`, then `f (𝔪_R ^ k) ⊆ 𝔪_S ^ k` for
every `k`, which is continuity at `0`, hence continuity. (Formal
ingredient of the uniqueness half of `IsUniversal`: homomorphisms
compatible with the reduction maps are automatically local, hence
continuous, so agreement on a topologically generating subring forces
agreement everywhere.) -/
lemma continuous_of_map_maximalIdeal_le {R S : Type*} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R] [CommRing S]
    [TopologicalSpace S] [IsTopologicalRing S] [IsLocalRing S]
    (hR : IsAdic (IsLocalRing.maximalIdeal R))
    (hS : IsAdic (IsLocalRing.maximalIdeal S)) (f : R →+* S)
    (hloc : Ideal.map f (IsLocalRing.maximalIdeal R) ≤
      IsLocalRing.maximalIdeal S) :
    Continuous f := by
  apply continuous_of_continuousAt_zero f
  unfold ContinuousAt
  rw [map_zero, hS.hasBasis_nhds_zero.tendsto_right_iff]
  intro k _
  have hmem : ((IsLocalRing.maximalIdeal R ^ k : Ideal R) : Set R) ∈
      𝓝 (0 : R) := hR.hasBasis_nhds_zero.mem_of_mem trivial
  filter_upwards [hmem] with x hx
  have hle : Ideal.map f (IsLocalRing.maximalIdeal R ^ k) ≤
      IsLocalRing.maximalIdeal S ^ k := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono hloc k
  exact hle (Ideal.mem_map_of_mem f hx)

omit [Finite k] [Algebra ℤ_[ℓ] k] [DiscreteTopology k] in
/-- **Uniqueness from trace generation** (the formal Carayol argument,
PROVEN): a weakly universal, trace-generated hardly ramified deformation
is universal. Two compatible homomorphisms `f, f' : D.R → D'.R` agree on
the image of `ℤ_ℓ` (both restrict to the structure map) and on every
Frobenius-charpoly coefficient (both carry the `charFrob` of `D` to that
of `D'`); they are continuous, because compatibility with the reduction
maps makes them local (`ker π` is the maximal ideal on both sides: `π`
is surjective onto the prime field `ℤ/ℓℤ`, so its kernel is maximal) and
local homomorphisms of adic local rings are continuous; and the
equalizer of two continuous ring homomorphisms into a Hausdorff ring
(adic separatedness of `D'.R`) is a closed subring. A closed subring
containing the generating set contains its topological closure, which is
everything by trace generation. -/
theorem isUniversal_of_isWeaklyUniversal_isTraceGenerated
    {ρbar : GaloisRep ℚ k V}
    (D : HardlyRamifiedDeformation hℓOdd ρbar)
    (hw : D.IsWeaklyUniversal) (ht : D.IsTraceGenerated) :
    D.IsUniversal := by
  letI := D.commRing; letI := D.topologicalSpace; letI := D.isTopologicalRing
  letI := D.isLocalRing; letI := D.algebra
  intro D'
  letI := D'.commRing; letI := D'.topologicalSpace
  letI := D'.isTopologicalRing; letI := D'.isLocalRing; letI := D'.algebra
  letI := D'.isAdicComplete
  obtain ⟨f, hf⟩ := hw D'
  refine ⟨f, hf, fun f' hf' => ?_⟩
  -- compatible homomorphisms are local, hence continuous
  have hker : RingHom.ker D.π = IsLocalRing.maximalIdeal D.R :=
    IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective D.π D.π_surjective)
  have hker' : RingHom.ker D'.π = IsLocalRing.maximalIdeal D'.R :=
    IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective D'.π D'.π_surjective)
  have hcont : ∀ g : D.R →+* D'.R, D'.π.comp g = D.π → Continuous g := by
    intro g hg
    refine continuous_of_map_maximalIdeal_le D.isAdic D'.isAdic g ?_
    rw [Ideal.map_le_iff_le_comap, ← hker, ← hker']
    intro x hx
    show D'.π (g x) = 0
    rw [← RingHom.comp_apply, hg]
    exact hx
  -- the equalizer of `f'` and `f` is a closed subring …
  haveI : T2Space D'.R := t2Space_of_isAdic D'.isAdic
  have hclosed : IsClosed ((RingHom.eqLocus f' f : Subring D.R) : Set D.R) :=
    isClosed_eq (hcont f' hf'.2.1) (hcont f hf.2.1)
  -- … containing the trace-generating set
  have hgen : Subring.closure (Set.range (algebraMap ℤ_[ℓ] D.R) ∪
      {x : D.R | ∃ q, ∃ hq : q.Prime, q ≠ 2 ∧ q ≠ ℓ ∧ ∃ n : ℕ,
        x = (D.ρ.charFrob
          hq.toHeightOneSpectrumRingOfIntegersRat).coeff n}) ≤
      RingHom.eqLocus f' f := by
    rw [Subring.closure_le]
    rintro x (⟨c, rfl⟩ | ⟨q, hq, hq2, hqℓ, n, rfl⟩)
    · show f' (algebraMap ℤ_[ℓ] D.R c) = f (algebraMap ℤ_[ℓ] D.R c)
      rw [← RingHom.comp_apply, ← RingHom.comp_apply, hf'.1, hf.1]
    · show f' ((D.ρ.charFrob
          hq.toHeightOneSpectrumRingOfIntegersRat).coeff n) =
        f ((D.ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff n)
      have hcf := (hf'.2.2 q hq hq2 hqℓ).trans (hf.2.2 q hq hq2 hqℓ).symm
      have hcoeff := congrArg (fun p : Polynomial D'.R => p.coeff n) hcf
      simpa [Polynomial.coeff_map] using hcoeff
  have htop : (⊤ : Subring D.R) ≤ RingHom.eqLocus f' f := by
    have hcl : (Subring.closure (Set.range (algebraMap ℤ_[ℓ] D.R) ∪
        {x : D.R | ∃ q, ∃ hq : q.Prime, q ≠ 2 ∧ q ≠ ℓ ∧ ∃ n : ℕ,
          x = (D.ρ.charFrob
            hq.toHeightOneSpectrumRingOfIntegersRat).coeff
              n})).topologicalClosure = ⊤ := ht
    rw [← hcl]
    exact Subring.topologicalClosure_minimal _ hgen hclosed
  exact RingHom.ext fun x => htop (Subring.mem_top x)

omit [Finite k] [Algebra ℤ_[ℓ] k] [DiscreteTopology k] in
/-- **Rigidity of universal data** (PROVEN, formal): any two universal
hardly ramified deformations have canonically isomorphic coefficient
rings, compatibly with the `ℤ_ℓ`-algebra structure. The two `∃!`-clauses
produce homomorphisms in both directions whose composites are compatible
endomorphisms, hence equal to the identity (the identity being the
unique compatible endomorphism). This is what lets the finiteness and
presentation strata, stated for an arbitrary universal datum, be
transported from the constructed universal deformation ring. -/
theorem exists_ringEquiv_of_isUniversal {ρbar : GaloisRep ℚ k V}
    (D D' : HardlyRamifiedDeformation hℓOdd ρbar)
    (hD : D.IsUniversal) (hD' : D'.IsUniversal) :
    letI := D.commRing; letI := D'.commRing
    letI := D.algebra; letI := D'.algebra
    ∃ e : D.R ≃+* D'.R, ∀ c : ℤ_[ℓ],
      e (algebraMap ℤ_[ℓ] D.R c) = algebraMap ℤ_[ℓ] D'.R c := by
  letI := D.commRing; letI := D.topologicalSpace; letI := D.isTopologicalRing
  letI := D.isLocalRing; letI := D.algebra
  letI := D'.commRing; letI := D'.topologicalSpace
  letI := D'.isTopologicalRing; letI := D'.isLocalRing; letI := D'.algebra
  obtain ⟨f, hf, _⟩ := hD D'
  obtain ⟨g, hg, _⟩ := hD' D
  have hgf : g.comp f = RingHom.id D.R := by
    obtain ⟨i, _, hiu⟩ := hD D
    have h1 : g.comp f = i := by
      refine hiu (g.comp f) ⟨?_, ?_, ?_⟩
      · rw [RingHom.comp_assoc, hf.1, hg.1]
      · rw [← RingHom.comp_assoc, hg.2.1, hf.2.1]
      · intro q hq hq2 hqℓ
        rw [← Polynomial.map_map, hf.2.2 q hq hq2 hqℓ,
          hg.2.2 q hq hq2 hqℓ]
    have h2 : RingHom.id D.R = i := by
      refine hiu (RingHom.id D.R) ⟨?_, ?_, ?_⟩
      · rw [RingHom.id_comp]
      · rw [RingHom.comp_id]
      · intro q hq _ _
        exact Polynomial.map_id
    rw [h1, h2]
  have hfg : f.comp g = RingHom.id D'.R := by
    obtain ⟨j, _, hju⟩ := hD' D'
    have h1 : f.comp g = j := by
      refine hju (f.comp g) ⟨?_, ?_, ?_⟩
      · rw [RingHom.comp_assoc, hg.1, hf.1]
      · rw [← RingHom.comp_assoc, hf.2.1, hg.2.1]
      · intro q hq hq2 hqℓ
        rw [← Polynomial.map_map, hg.2.2 q hq hq2 hqℓ,
          hf.2.2 q hq hq2 hqℓ]
    have h2 : RingHom.id D'.R = j := by
      refine hju (RingHom.id D'.R) ⟨?_, ?_, ?_⟩
      · rw [RingHom.id_comp]
      · rw [RingHom.comp_id]
      · intro q hq _ _
        exact Polynomial.map_id
    rw [h1, h2]
  refine ⟨RingEquiv.ofRingHom f g hfg hgf, fun c => ?_⟩
  show f (algebraMap ℤ_[ℓ] D.R c) = algebraMap ℤ_[ℓ] D'.R c
  rw [← RingHom.comp_apply, hf.1]

omit [Finite k] [Algebra ℤ_[ℓ] k] in
/-- **Continuity of the reduction map** (PROVEN, elementary): the
reduction map `π : D'.R → ℤ/ℓℤ` of a hardly ramified deformation is
continuous — its kernel is the maximal ideal (`π` is surjective onto
the prime field), which is open in the maximal-adic topology, so `π`
is locally constant. (Ingredient of the residual-identification
vocabulary below: it makes `ℤ/ℓℤ` a topological `D'.R`-algebra, so the
reduction of `D'.ρ` can be formed by `baseChange`.) -/
lemma HardlyRamifiedDeformation.continuous_pi
    {ρbar : GaloisRep ℚ k V}
    (D' : HardlyRamifiedDeformation hℓOdd ρbar) :
    letI := D'.commRing; letI := D'.topologicalSpace
    letI := D'.isTopologicalRing; letI := D'.isLocalRing
    Continuous D'.π := by
  letI := D'.commRing; letI := D'.topologicalSpace
  letI := D'.isTopologicalRing; letI := D'.isLocalRing
  have hker : RingHom.ker D'.π = IsLocalRing.maximalIdeal D'.R :=
    IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective D'.π D'.π_surjective)
  have hopen : IsOpen ((RingHom.ker D'.π : Ideal D'.R) : Set D'.R) := by
    rw [hker]
    have h1 := (isAdic_iff.mp D'.isAdic).1 1
    rwa [pow_one] at h1
  apply continuous_of_continuousAt_zero D'.π
  unfold ContinuousAt
  rw [map_zero, nhds_discrete k, Filter.tendsto_pure]
  filter_upwards [hopen.mem_nhds (Submodule.zero_mem _)] with x hx
  exact hx

open scoped TensorProduct in
/-- **Residual identification**: the reduction of `D'.ρ` along the
reduction map `D'.π` — the base change of `D'.ρ` to `ℤ/ℓℤ`, a
continuous `D'.R`-algebra via `continuous_pi` — is conjugate to `ρbar`
itself. This is the datum with which Mazur-style strict-deformation
universality can be applied to `D'`: the `HardlyRamifiedDeformation`
category matches `D'` with `ρbar` only through Frobenius characteristic
polynomials (`charFrob_compat`), and the Chebotarev–Brauer–Nesbitt leaf
`exists_conj_of_charFrob_eq` upgrades that matching to an actual
conjugation whenever `ρbar` is irreducible. Bundled as a definition so
the instance `letI`s live under plain parameters (elaborator
constraint, cf. `IsTraceDescent`). -/
def HardlyRamifiedDeformation.IsResidualIdentified
    {ρbar : GaloisRep ℚ k V}
    (D' : HardlyRamifiedDeformation hℓOdd ρbar) : Prop :=
  letI := D'.commRing; letI := D'.topologicalSpace
  letI := D'.isTopologicalRing; letI := D'.isLocalRing; letI := D'.algebra
  letI : Algebra D'.R k := D'.π.toAlgebra
  letI : ContinuousSMul D'.R k :=
    continuousSMul_of_algebraMap D'.R k
      (by rw [RingHom.algebraMap_toAlgebra]; exact D'.continuous_pi)
  ∃ e : (k ⊗[D'.R] (Fin 2 → D'.R)) ≃ₗ[k] V,
    (D'.ρ.baseChange k).conj e = ρbar

/-- **Weak universality on residually identified deformations**: `D`
maps compatibly to every deformation `D'` that comes equipped with a
residual identification. This is what Mazur-style strict-deformation
representability produces directly — the classifying map exists for
deformations whose reduction is identified with `ρbar` — without the
Chebotarev–Brauer–Nesbitt input, which is exactly what upgrades this
property to full `IsWeaklyUniversal` in the assembly
`exists_isWeaklyUniversal`. -/
def HardlyRamifiedDeformation.IsWeaklyUniversalOnIdentified
    {ρbar : GaloisRep ℚ k V}
    (D : HardlyRamifiedDeformation hℓOdd ρbar) : Prop :=
  letI := D.commRing; letI := D.topologicalSpace; letI := D.isTopologicalRing
  letI := D.isLocalRing; letI := D.algebra
  ∀ D' : HardlyRamifiedDeformation hℓOdd ρbar,
    letI := D'.commRing; letI := D'.topologicalSpace
    letI := D'.isTopologicalRing; letI := D'.isLocalRing; letI := D'.algebra
    D'.IsResidualIdentified →
    ∃ f : D.R →+* D'.R,
      f.comp (algebraMap ℤ_[ℓ] D.R) = algebraMap ℤ_[ℓ] D'.R ∧
      D'.π.comp f = D.π ∧
      ∀ q (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
        (D.ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map f =
          D'.ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat

open scoped TensorProduct in
/-- **Weak universality on identified deformations, at the level of the
REPRESENTATIONS** (the shape in which Mazur representability actually
produces its classifying maps): `D` maps to every residually identified
`D'` by a CONTINUOUS `ℤ_ℓ`-algebra homomorphism `f` compatible with the
reduction maps, along which the pushforward of `D.ρ` — its base change
to `D'.R` viewed as a `D.R`-algebra through `f` — is *conjugate* to
`D'.ρ`.

This is strictly stronger than `IsWeaklyUniversalOnIdentified`, whose
`charFrob` clause is the conjugation-invariance shadow of the last
clause (`exists_isWeaklyUniversalOnIdentified` below derives it through
`charpoly_baseChange_conj`). The universal deformation ring's defining
property is the representation-level one: a strict deformation of
`ρbar` over `D'.R` is classified by a map out of `R^{univ}` under which
the universal representation pulls back to it up to the framing
ambiguity — the linear equivalence `e`. Continuity of `f` is bundled
into the existential because it is needed to STATE the base change
(`GaloisRep.baseChange` requires `ContinuousSMul D.R D'.R`); it is in
any case automatic, `f` being local by the reduction-map clause
(`continuous_of_map_maximalIdeal_le`). -/
def HardlyRamifiedDeformation.IsWeaklyUniversalOnIdentifiedFrames
    {ρbar : GaloisRep ℚ k V}
    (D : HardlyRamifiedDeformation hℓOdd ρbar) : Prop :=
  letI := D.commRing; letI := D.topologicalSpace; letI := D.isTopologicalRing
  letI := D.isLocalRing; letI := D.algebra
  ∀ D' : HardlyRamifiedDeformation hℓOdd ρbar,
    letI := D'.commRing; letI := D'.topologicalSpace
    letI := D'.isTopologicalRing; letI := D'.isLocalRing; letI := D'.algebra
    D'.IsResidualIdentified →
    ∃ f : D.R →+* D'.R, ∃ hfc : Continuous f,
      f.comp (algebraMap ℤ_[ℓ] D.R) = algebraMap ℤ_[ℓ] D'.R ∧
      D'.π.comp f = D.π ∧
      letI : Algebra D.R D'.R := f.toAlgebra
      letI : ContinuousSMul D.R D'.R :=
        continuousSMul_of_algebraMap D.R D'.R
          (by rw [RingHom.algebraMap_toAlgebra]; exact hfc)
      ∃ e : (D'.R ⊗[D.R] (Fin 2 → D.R)) ≃ₗ[D'.R] (Fin 2 → D'.R),
        (D.ρ.baseChange D'.R).conj e = D'.ρ

/-- **Chebotarev–Brauer–Nesbitt conjugacy leaf** (PROVEN 2026-07-24 —
the identification half of the Mazur representability stratum): a
continuous mod-`ℓ` representation `τ` of `Gal(ℚ̄/ℚ)` on a 2-dimensional
space whose Frobenius characteristic polynomials at all primes
`q ∉ {2, ℓ}` agree with those of an *irreducible* `ρbar` is conjugate
to `ρbar`.

DERIVED as the `S = {(2), (ℓ)}` instance of the SHARED conjugacy node
`exists_conj_of_charFrob_eq_away` (`BrauerNesbittConjugacy.lean`, which
also discharges `Modularity/Patching.lean`'s identically-named leaf):
Chebotarev density (`dense_conjClasses_globalFrob`) plus continuity
into the discrete endomorphism spaces upgrade the off-`{2, ℓ}` charpoly
agreement to agreement at every group element, and the abstract
dimension-2 Brauer–Nesbitt core over a finite coefficient field —
Kolchin irreducibility transfer plus Jacobson density plus little
Wedderburn/separability, valid in every characteristic — produces the
intertwining conjugation. -/
theorem exists_conj_of_charFrob_eq
    (hdimV : Module.rank k V = 2)
    {W : Type*} [AddCommGroup W] [Module k W]
    [Module.Finite k W] [Module.Free k W]
    (hdimW : Module.rank k W = 2)
    {ρbar : GaloisRep ℚ k V} (hirr : ρbar.IsIrreducible)
    (τ : GaloisRep ℚ k W)
    (hcf : ∀ q (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      τ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat) :
    ∃ e : W ≃ₗ[k] V, τ.conj e = ρbar := by
  classical
  refine exists_conj_of_charFrob_eq_away hdimV hirr hdimW τ
    {Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat,
      (Fact.out : ℓ.Prime).toHeightOneSpectrumRingOfIntegersRat} ?_
  intro q hq hqS
  have hq2 : q ≠ 2 := by
    rintro rfl
    exact hqS (Finset.mem_insert.mpr (Or.inl rfl))
  have hqℓ : q ≠ ℓ := by
    rintro rfl
    exact hqS (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))
  exact hcf q hq hq2 hqℓ

open scoped TensorProduct in
/-- **Strict universality on FINITE framed test objects** — Mazur's
universal property tested against the objects of *Schlessinger's*
category (Artinian — here equivalently finite — local `ℤ_ℓ`-algebras
with residue field `k`), stated at the isomorphism level.

A test object is the raw datum Schlessinger's category consists of: a
FINITE local topological `ℤ_ℓ`-algebra `A`, a hardly ramified
representation `ρA` on the STANDARD FRAME `Fin 2 → A`, a surjective
reduction `πA : A →+* k`, and a residual identification of `ρA ⊗_A k`
with `ρbar`. Continuity of `πA` is taken as a HYPOTHESIS rather than
derived, so that a test object carries no `IsModuleTopology` datum; for
the bundled test objects of `HardlyRamifiedDeformation` it is supplied
by the proven `HardlyRamifiedDeformation.continuous_pi`, which is what
`isWeaklyUniversalOnIdentifiedFramesFinite_of_isStrictlyUniversalOnFiniteFrames`
below does.

The conclusion is the classifying map in its classical strength: a
CONTINUOUS ring homomorphism `ψ : D.R →+* A`, strict (compatible with
the `ℤ_ℓ`-structures and with the two reductions), carrying the
universal representation to `ρA` up to the framing ambiguity — the
linear equivalence `e` — i.e. `D.ρ ⊗_{D.R} A ≅ ρA` as representations.

Interface-side twin: `Modularity/Patching.lean`'s
`IsStrictlyUniversalOnFramedFiniteLifts` (same statement, unbundled
coefficient data, `IsModuleTopology` in place of the continuity
hypothesis). -/
def HardlyRamifiedDeformation.IsStrictlyUniversalOnFiniteFrames
    {ρbar : GaloisRep ℚ k V}
    (D : HardlyRamifiedDeformation hℓOdd ρbar) : Prop :=
  letI := D.commRing; letI := D.topologicalSpace; letI := D.isTopologicalRing
  letI := D.isLocalRing; letI := D.algebra
  ∀ (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLocalRing A] [Algebra ℤ_[ℓ] A] [Finite A]
    (ρA : FramedGaloisRep ℚ A (Fin 2)),
    IsHardlyRamified hℓOdd (rank_finTwoFun A) ρA →
    ∀ πA : A →+* k, Function.Surjective πA → ∀ hπA : Continuous πA,
    (letI : Algebra A k := πA.toAlgebra
     letI : ContinuousSMul A k := continuousSMul_of_algebraMap A k
       (by rw [RingHom.algebraMap_toAlgebra]; exact hπA)
     ∃ e : (k ⊗[A] (Fin 2 → A)) ≃ₗ[k] V, (ρA.baseChange k).conj e = ρbar) →
    ∃ ψ : D.R →+* A, ∃ hψ : Continuous ψ,
      ψ.comp (algebraMap ℤ_[ℓ] D.R) = algebraMap ℤ_[ℓ] A ∧
      πA.comp ψ = D.π ∧
      (letI : Algebra D.R A := ψ.toAlgebra
       letI : ContinuousSMul D.R A := continuousSMul_of_algebraMap D.R A
         (by rw [RingHom.algebraMap_toAlgebra]; exact hψ)
       ∃ e : (A ⊗[D.R] (Fin 2 → D.R)) ≃ₗ[A] (Fin 2 → A),
         (D.ρ.baseChange A).conj e = ρA)

open scoped TensorProduct in
/-- **Weak universality on FINITE residually identified deformations** —
verbatim `IsWeaklyUniversalOnIdentifiedFrames`, but tested only against
deformations whose coefficient ring is FINITE. The hypothesis side of
the pro-finite limit leaf `isWeaklyUniversalOnIdentifiedFrames_of_finite`
below: it is what the Artinian-level representability leaf delivers once
its raw test objects are re-bundled as deformations, and the whole
content of that leaf is the passage from this to the unrestricted
property. -/
def HardlyRamifiedDeformation.IsWeaklyUniversalOnIdentifiedFramesFinite
    {ρbar : GaloisRep ℚ k V}
    (D : HardlyRamifiedDeformation hℓOdd ρbar) : Prop :=
  letI := D.commRing; letI := D.topologicalSpace; letI := D.isTopologicalRing
  letI := D.isLocalRing; letI := D.algebra
  ∀ D' : HardlyRamifiedDeformation hℓOdd ρbar,
    letI := D'.commRing; letI := D'.topologicalSpace
    letI := D'.isTopologicalRing; letI := D'.isLocalRing; letI := D'.algebra
    Finite D'.R →
    D'.IsResidualIdentified →
    ∃ f : D.R →+* D'.R, ∃ hfc : Continuous f,
      f.comp (algebraMap ℤ_[ℓ] D.R) = algebraMap ℤ_[ℓ] D'.R ∧
      D'.π.comp f = D.π ∧
      letI : Algebra D.R D'.R := f.toAlgebra
      letI : ContinuousSMul D.R D'.R :=
        continuousSMul_of_algebraMap D.R D'.R
          (by rw [RingHom.algebraMap_toAlgebra]; exact hfc)
      ∃ e : (D'.R ⊗[D.R] (Fin 2 → D.R)) ≃ₗ[D'.R] (Fin 2 → D'.R),
        (D.ρ.baseChange D'.R).conj e = D'.ρ

omit [Finite k] [Algebra ℤ_[ℓ] k] in
/-- **A finite deformation IS a Schlessinger test object** (PROVEN
2026-07-25 — the re-bundling glue of the Schlessinger cut): a
deformation `D` classifying every finite raw framed test object
classifies every finite deformation of the category.

There is nothing to do but read the structure fields as the raw datum:
a `HardlyRamifiedDeformation` with finite coefficient ring supplies the
ring and its topology (`commRing`, `topologicalSpace`,
`isTopologicalRing`, `isLocalRing`, `algebra`), the framed hardly
ramified representation (`ρ`, `isHardlyRamified`), the surjective
reduction (`π`, `π_surjective`) — CONTINUOUS by the proven
`HardlyRamifiedDeformation.continuous_pi`, which is exactly the datum
the raw form takes as a hypothesis — and the residual identification is
`IsResidualIdentified` itself, whose `letI` block is the raw form's
verbatim. The Noetherian, adic and adic-completeness fields of the
structure are simply not needed by the raw form: they are automatic for
a finite ring, which is why the Artinian-level leaf is stated on raw
test objects and does not have to build them. -/
theorem isWeaklyUniversalOnIdentifiedFramesFinite_of_isStrictlyUniversalOnFiniteFrames
    {ρbar : GaloisRep ℚ k V} (D : HardlyRamifiedDeformation hℓOdd ρbar)
    (hD : D.IsStrictlyUniversalOnFiniteFrames) :
    D.IsWeaklyUniversalOnIdentifiedFramesFinite := by
  letI := D.commRing; letI := D.topologicalSpace; letI := D.isTopologicalRing
  letI := D.isLocalRing; letI := D.algebra
  intro D'
  letI := D'.commRing; letI := D'.topologicalSpace
  letI := D'.isTopologicalRing; letI := D'.isLocalRing; letI := D'.algebra
  intro hfin hid
  letI := hfin
  exact hD D'.R D'.ρ D'.isHardlyRamified D'.π D'.π_surjective
    D'.continuous_pi hid

/-- **Restricted-ramification finiteness — Schlessinger's H3 at every
Artinian level** (sorry node — the arithmetic finiteness stratum of the
2026-07-26 Schlessinger cut of `exists_isStrictlyUniversalOnFiniteFrames`):
over a FINITE discrete local topological `ℤ_ℓ`-algebra `A` there are only
finitely many hardly ramified framed representations of `Γ ℚ` on `A²`.

Mathematical content (Hermite–Minkowski). A hardly ramified `ρ` over `A`
is a continuous homomorphism of `Γ ℚ` into the FINITE discrete monoid
`End_A(A²)`, unramified outside `{2, ℓ}`. Its kernel is therefore an open
normal subgroup of index at most `#End_A(A²)` containing the image of
every local inertia group away from `{2, ℓ}`, and `ρ` is determined by
that kernel together with an injection of the finite quotient into
`End_A(A²)`. The fixed field of such a kernel is a Galois number field of
degree at most `#End_A(A²)` unramified outside `{2, ℓ, ∞}`, so its
discriminant is divisible only by `2` and `ℓ` with exponents bounded in
terms of the degree (Serre, *Corps Locaux* III §6 Prop. 13 for the
different, hence for the discriminant), and Hermite's theorem
(`NumberField.finite_of_discr_bdd`) leaves finitely many such fields;
each carries finitely many quotients and each quotient finitely many
injections. Equivalently: `G_{ℚ,{2,ℓ}}` is a *small* profinite group, so
it admits only finitely many continuous homomorphisms to a fixed finite
monoid.

Consumed at `A = k[ε]`, where the set specialises to the framed tangent
space of the deformation problem — Schlessinger's H3 — and, in the
inverse-limit construction of the hull, at every Artinian level; which is
why it is stated uniformly over a general finite discrete coefficient
ring rather than at the dual numbers only.

DEDUPE NOTE. `Modularity/Patching.lean` PROVES this statement verbatim
(`GaloisRepresentation.Modularity.finite_setOf_isHardlyRamified`, over
`finite_setOf_galoisRep_isUnramifiedAt`,
`finite_setOf_subgroup_inertiaAt_le` and
`finite_setOf_intermediateField_inertiaAt_le`), bottoming out in the
single sharper arithmetic leaf
`exists_discr_factorization_le_of_finrank_le` (the discriminant-exponent
bound by the degree). That chain uses NOTHING from Khare–Wintenberger, so
the honest discharge of this leaf is not a re-proof but the module split
recorded in `~/.flt-design-deformation-patching-dedup.md`: lift the
Hermite–Minkowski block out of `Patching.lean` into a module upstream of
this one and consume it here. It is stated as a leaf rather than moved
because `Patching.lean` has its own concurrent owners.

Both-ways audit: a plain classical finiteness statement about an abstract
finite coefficient ring — true outright as cited, with no
representation-theoretic hypothesis and no vacuity involved.

CIRCULARITY GUARD: as for every leaf of this file — no import from
`Family.lean`, `Lift.lean` or `Modularity/*`, and no discharge through
the odd-prime dichotomy `not_isIrreducible_of_isHardlyRamified_of_five_le`
(which is proven over pillar α, i.e. over this file's cone). Neither is a
temptation here: the statement carries no irreducibility hypothesis. -/
theorem finite_setOf_isHardlyRamified_frames {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLocalRing A]
    [Algebra ℤ_[ℓ] A] [Finite A] [DiscreteTopology A] :
    {ρ : FramedGaloisRep ℚ A (Fin 2) |
      IsHardlyRamified hℓOdd (rank_finTwoFun A) ρ}.Finite :=
  sorry

/-- **Schur plus oddness: `End_{k[Γ]}(ρbar) = k`** (PROVEN 2026-07-26 —
Schlessinger's H4 stratum of the 2026-07-26 cut of
`exists_isStrictlyUniversalOnFiniteFrames`): every `k`-linear
endomorphism of `V` commuting with the whole image of an irreducible
hardly ramified `ρbar` is a scalar. Equivalently `ρbar` is ABSOLUTELY
irreducible; equivalently the framed deformation functor is a torsor
over the unframed one, which is Schlessinger's H4 (`dim_k t_F` finite
and the hull unobstructed by automorphisms).

The missing repository vocabulary — complex conjugation as an element of
`Γ ℚ`, together with the evaluation of `cyclotomicCharacter` at it — is
now `GaloisRepresentation/ComplexConjugation.lean`: `complexConj : Γ ℚ`,
`complexConj_mul_self` (it is an involution) and
`cyclotomicCharacter_complexConj` (the character sends it to `−1` for odd
`p`). Those three facts are exactly what this proof consumes from the
oddness side.

**The proof written here is NOT the Wedderburn route** that this
docstring previously sketched (`End_{k[Γ]}(V)` a division ring, hence by
Wedderburn's little theorem a field extension `k'/k` with
`[k':k] · dim_{k'} V = 2`, then oddness killing `[k':k] = 2`). That route
needs Wedderburn plus a `k'`-module structure on `V`; in dimension two
one can do without both. The argument used instead, with `J := ρbar c`
for `c` complex conjugation:

1. *Schur*, in the only form needed: an endomorphism commuting with the
   whole image of the irreducible `ρbar` is an intertwiner, hence zero or
   bijective (`Representation.IsIrreducible.bijective_or_eq_zero`, through
   `LinearMap.intertwiningMap_of_isIntertwiningMap`).
2. *Oddness*: `J * J = 1` since `c² = 1`, and `det J = −1` by
   `IsHardlyRamified.det` composed with `cyclotomicCharacter_complexConj`;
   `−1 ≠ 1` in `k` because `char k = ℓ` (`natCast_self_eq_zero`) is odd.
   So `J ≠ 1` and `J ≠ −1` (the determinant of `±1` on a rank-two module
   is `1`).
3. *A `+1`-eigenvector exists*: `(J − 1)(J + 1) = J² − 1 = 0`, so if
   `J − 1` were injective then `J + 1 = 0`, i.e. `J = −1`, excluded. Pick
   `w ≠ 0` with `J w = w`.
4. *`f w` is a multiple of `w`*: `f` commutes with `J`, so `J (f w) = f w`
   too. Were `w` and `f w` independent they would be a basis of the
   rank-two `V` (`basisOfLinearIndependentOfCardEqFinrank`), and `J`,
   fixing both, would be `1` — excluded. So `f w = a • w` for some `a`
   (`linearIndependent_fin2`).
5. *Conclude*: `f − a` commutes with the image and kills `w ≠ 0`, so it is
   not injective, so by Schur it is `0`, i.e. `f = a • 1`.

The hypothesis `h : IsHardlyRamified hℓOdd hdim ρbar` is used ONLY
through its `det` field (step 2); `hirr` only through step 1; `hdim` only
to know `finrank k V = 2` (steps 2 and 4).

Both-ways audit: classically this is the standard "odd irreducible
two-dimensional mod-`ℓ` representation is absolutely irreducible", true
outright for `ℓ` odd; abstractly the hypothesis package contains an
irreducible hardly ramified `ρbar`, which the section audit of
`Interface.lean` shows to be classically unsatisfiable, so the statement
holds vacuously as well — but see the circularity guard: that vacuity is
NOT available as a proof route here, and the proof below does not use it.

CIRCULARITY GUARD: `not_isIrreducible_of_isHardlyRamified_of_five_le`
refutes exactly this hypothesis package and is itself proven over pillar
α, which is what this file's cone proves; Lean rejects the cycle. The
proof below imports only `ComplexConjugation.lean`, whose own cone is
pure mathlib. -/
theorem exists_smul_eq_of_commute_of_isIrreducible
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible) (f : Module.End k V)
    (hf : ∀ g, Commute f (ρbar g)) :
    ∃ c : k, f = c • 1 := by
  haveI : Representation.IsIrreducible ρbar.toRepresentation := hirr
  have hfr : Module.finrank k V = 2 := Module.finrank_eq_of_rank_eq (by exact_mod_cast hdim)
  -- **Schur's lemma**: an endomorphism commuting with the whole image is zero or bijective.
  have schur : ∀ e : Module.End k V, (∀ g, Commute e (ρbar g)) →
      e = 0 ∨ Function.Bijective e := by
    intro e he
    have hint : ∀ (g : Field.absoluteGaloisGroup ℚ) (x : V),
        e (ρbar.toRepresentation g x) = ρbar.toRepresentation g (e x) := by
      intro g x
      have h9 := congrArg (fun m : Module.End k V => m x) (he g).eq
      simp only [Module.End.mul_apply] at h9
      exact h9
    have hb := Representation.IsIrreducible.bijective_or_eq_zero
      (LinearMap.intertwiningMap_of_isIntertwiningMap ρbar.toRepresentation
        ρbar.toRepresentation e hint)
    rcases hb with hbij | h0
    · exact Or.inr hbij
    · left
      have h10 := congrArg
        (fun F : Representation.IntertwiningMap ρbar.toRepresentation ρbar.toRepresentation =>
          F.toLinearMap) h0
      simp only [Representation.IntertwiningMap.zero_toLinearMap] at h10
      exact h10
  -- **`−1 ≠ 1` in `k`**, because `char k = ℓ` is odd.
  have hne1 : (-1 : k) ≠ 1 := by
    intro hcon
    have h2 : ((2 : ℕ) : k) = 0 := by
      push_cast
      linear_combination -hcon
    haveI hc : CharP k (ringChar k) := ringChar.charP k
    have hp : (ringChar k).Prime :=
      (CharP.char_is_prime_or_zero k (ringChar k)).resolve_right
        (CharP.char_ne_zero_of_finite k (ringChar k))
    have hd2 : ringChar k ∣ 2 := (CharP.cast_eq_zero_iff k (ringChar k) 2).mp h2
    have hdl : ringChar k ∣ ℓ :=
      (CharP.cast_eq_zero_iff k (ringChar k) ℓ).mp natCast_self_eq_zero
    have hr2 : ringChar k = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd2
    rw [hr2] at hdl
    exact (Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr hdl)) hℓOdd
  -- **Complex conjugation**: an involution of determinant `−1`.
  set J : Module.End k V := ρbar complexConj with hJdef
  have hJJ : J * J = 1 := by
    rw [hJdef, ← map_mul ρbar]
    convert map_one ρbar using 2
    exact complexConj_mul_self
  have hdetJ : LinearMap.det J = -1 := by
    have hd := h.det complexConj
    rw [GaloisRep.det_apply, cyclotomicCharacter_complexConj ℓ hℓOdd] at hd
    rw [hJdef, hd]
    simp
  have hJnot1 : J ≠ 1 := by
    intro hcJ
    rw [hcJ, show LinearMap.det (1 : Module.End k V) = 1 from LinearMap.det_id] at hdetJ
    exact hne1 hdetJ.symm
  have hJnotneg1 : J ≠ -1 := by
    intro hcJ
    have h12 : LinearMap.det J = 1 := by
      rw [hcJ, show (-1 : Module.End k V) = (-1 : k) • 1 by simp,
        LinearMap.det_smul, hfr]
      simp
    rw [h12] at hdetJ
    exact hne1 hdetJ.symm
  -- **A `+1`-eigenvector exists**: otherwise `J − 1` is injective, forcing `J = −1`.
  have hprod : (J - 1) * (J + 1) = 0 := by
    have h13 : (J - 1) * (J + 1) = J * J - 1 := by noncomm_ring
    rw [h13, hJJ, sub_self]
  have hex : ∃ w : V, w ≠ 0 ∧ J w = w := by
    by_contra hcon
    push Not at hcon
    have hinj : Function.Injective ((J - 1 : Module.End k V) : V →ₗ[k] V) := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro x hx
      rw [LinearMap.mem_ker] at hx
      by_contra hx0
      refine hcon x hx0 ?_
      have h14 : J x - x = 0 := by simpa using hx
      linear_combination (norm := module) h14
    have hJ1 : J + 1 = 0 := by
      apply LinearMap.ext
      intro x
      have h15 : (J - 1) ((J + 1) x) = (J - 1) 0 := by
        have h16 := congrArg (fun m : Module.End k V => m x) hprod
        simpa [Module.End.mul_apply] using h16
      simpa using hinj h15
    exact hJnotneg1 (by linear_combination (norm := noncomm_ring) hJ1)
  obtain ⟨w, hw0, hwJ⟩ := hex
  -- `f w` lies in the same eigenspace, `f` commuting with `J`.
  have hfwJ : J (f w) = f w := by
    have h17 := congrArg (fun m : Module.End k V => m w) (hf complexConj).eq
    simp only [Module.End.mul_apply] at h17
    rw [← hJdef] at h17
    rw [← h17, hwJ]
  -- `w` and `f w` cannot be independent: they would span `V` and force `J = 1`.
  have hdep : ¬ LinearIndependent k ![f w, w] := by
    intro hli
    have hcard : Fintype.card (Fin 2) = Module.finrank k V := by simp [hfr]
    refine hJnot1 ?_
    apply (basisOfLinearIndependentOfCardEqFinrank hli hcard).ext
    intro i
    fin_cases i <;>
      simp [coe_basisOfLinearIndependentOfCardEqFinrank, hfwJ, hwJ]
  have hav : ∃ a : k, f w = a • w := by
    rw [linearIndependent_fin2] at hdep
    push Not at hdep
    obtain ⟨a, ha⟩ := hdep hw0
    exact ⟨a, by simpa using ha.symm⟩
  obtain ⟨a, ha⟩ := hav
  -- `f − a` kills `w ≠ 0`, so Schur forces it to vanish.
  refine ⟨a, ?_⟩
  have hcomm : ∀ g, Commute (f - a • (1 : Module.End k V)) (ρbar g) := by
    intro g
    have h18 := (hf g).eq
    unfold Commute SemiconjBy
    rw [sub_mul, mul_sub, h18]
    congr 1
    simp [Algebra.smul_def, Algebra.commutes]
  rcases schur (f - a • 1) hcomm with h0 | hbij
  · linear_combination (norm := noncomm_ring) h0
  · exfalso
    have hzero : (f - a • (1 : Module.End k V)) w = (f - a • (1 : Module.End k V)) 0 := by
      simp [ha]
    exact hw0 (hbij.1 hzero)

open scoped TensorProduct in
/-- **Residual identification of a RAW framed package** — verbatim
`HardlyRamifiedDeformation.IsResidualIdentified`, but on unbundled
coefficient data `(R, ρuniv, πuniv)` with the continuity of the reduction
supplied as a hypothesis rather than derived from the structure fields
(`HardlyRamifiedDeformation.continuous_pi`). This is the shape in which
the Schlessinger core leaf below delivers the identification of the
universal representation with `ρbar`: the hull is constructed before it
is known to be an object of Mazur's category, so the identification
cannot yet be phrased on a bundled deformation.

Bundled as a definition rather than written inline so that the instance
`letI`s live under plain parameters — the same elaborator constraint
recorded on `IsResidualIdentified` and `IsTraceDescent`. -/
def IsResidualIdentifiedFrame {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R]
    (ρbar : GaloisRep ℚ k V) (ρuniv : FramedGaloisRep ℚ R (Fin 2))
    (πuniv : R →+* k) (hπcont : Continuous πuniv) : Prop :=
  letI : Algebra R k := πuniv.toAlgebra
  letI : ContinuousSMul R k := continuousSMul_of_algebraMap R k
    (by rw [RingHom.algebraMap_toAlgebra]; exact hπcont)
  ∃ e : (k ⊗[R] (Fin 2 → R)) ≃ₗ[k] V, (ρuniv.baseChange k).conj e = ρbar

open scoped TensorProduct in
/-- **Strict universality on finite frames, on a RAW package** —
verbatim `HardlyRamifiedDeformation.IsStrictlyUniversalOnFiniteFrames`,
with the bundled deformation `D` replaced by the unbundled data
`(R, ρuniv, πuniv)` it is tested through. The predicate quantifies over
exactly the same raw finite framed test objects, so the two are literally
the same proposition once a bundling is available — which is what the
assembly `exists_isStrictlyUniversalOnFiniteFrames` below exploits: the
Schlessinger core leaf produces the raw package, and the Mazur-category
structure fields (`isNoetherianRing`, `isAdic`, `isAdicComplete`) plus
the `charFrob_compat` shadow of the residual identification are what turn
it into an object of the category. -/
def IsStrictlyUniversalOnFrames
    {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [Algebra ℤ_[ℓ] R] (ρbar : GaloisRep ℚ k V)
    (ρuniv : FramedGaloisRep ℚ R (Fin 2)) (πuniv : R →+* k) : Prop :=
  ∀ (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLocalRing A] [Algebra ℤ_[ℓ] A] [Finite A]
    (ρA : FramedGaloisRep ℚ A (Fin 2)),
    IsHardlyRamified hℓOdd (rank_finTwoFun A) ρA →
    ∀ πA : A →+* k, Function.Surjective πA → ∀ hπA : Continuous πA,
    (letI : Algebra A k := πA.toAlgebra
     letI : ContinuousSMul A k := continuousSMul_of_algebraMap A k
       (by rw [RingHom.algebraMap_toAlgebra]; exact hπA)
     ∃ e : (k ⊗[A] (Fin 2 → A)) ≃ₗ[k] V, (ρA.baseChange k).conj e = ρbar) →
    ∃ ψ : R →+* A, ∃ hψ : Continuous ψ,
      ψ.comp (algebraMap ℤ_[ℓ] R) = algebraMap ℤ_[ℓ] A ∧
      πA.comp ψ = πuniv ∧
      (letI : Algebra R A := ψ.toAlgebra
       letI : ContinuousSMul R A := continuousSMul_of_algebraMap R A
         (by rw [RingHom.algebraMap_toAlgebra]; exact hψ)
       ∃ e : (A ⊗[R] (Fin 2 → R)) ≃ₗ[A] (Fin 2 → A),
         (ρuniv.baseChange A).conj e = ρA)

open scoped TensorProduct in
/-- **Schlessinger's hull for the hardly ramified problem** (sorry node —
the deformation-theoretic core of the 2026-07-26 cut of
`exists_isStrictlyUniversalOnFiniteFrames`, which is now PROVEN over this
leaf, the H3 finiteness leaf `finite_setOf_isHardlyRamified_frames` and
the H4 Schur node `exists_smul_eq_of_commute_of_isIrreducible`, PROVEN
2026-07-26): GIVEN
Schlessinger's H3 (`hfin`, restricted-ramification finiteness at every
Artinian level) and H4 (`hschur`, `End_{k[Γ]}(ρbar) = k`), the hardly
ramified deformation problem of an irreducible hardly ramified `ρbar`
(`ℓ ≥ 5`) has a hull: a complete Noetherian local topological
`ℤ_ℓ`-algebra `R` with the `𝔪`-adic topology, carrying a hardly ramified
framed representation `ρuniv`, a surjective continuous reduction `πuniv`
identifying `ρuniv ⊗_R k` with `ρbar`, which classifies every FINITE raw
framed test object *strictly* — by a continuous `ℤ_ℓ`-algebra map
compatible with the reductions along which `ρuniv` pushes forward to the
test representation up to the framing ambiguity.

WHAT IS AND IS NOT IN THIS LEAF. In: Schlessinger's criteria H1 and H2
on framed lifts, the relative representability of the hardly ramified
local conditions (Ramakrishna's flat condition at `ℓ`, the CDT tame
condition at `2`), the de Smit–Lenstra presentation of the hull and the
Mazur-category ring clauses read off it. Out: (i) H3, the leaf
`finite_setOf_isHardlyRamified_frames`, supplied as `hfin`; (ii) H4, the
now-PROVEN node `exists_smul_eq_of_commute_of_isIrreducible`, supplied
as `hschur`;
(iii) the passage from Artinian test objects to the whole of Mazur's
category — the separate leaf
`isWeaklyUniversalOnIdentifiedFrames_of_finite`, pure commutative algebra
and topology; (iv) the Chebotarev–Brauer–Nesbitt matching that
manufactures the residual identification, supplied by
`exists_conj_of_charFrob_eq` through the proven assembly
`exists_isWeaklyUniversal`; (v) the `charFrob` shadow of the conjugation
clause, discharged by `exists_isWeaklyUniversalOnIdentified` through
`charpoly_baseChange_conj` — and, at this level, by the assembly
`exists_isStrictlyUniversalOnFiniteFrames` below, which is exactly why
this leaf delivers the honest residual identification
(`IsResidualIdentifiedFrame`) and not a `charFrob` clause.

Mathematical content: `hschur` says `End_{k[Γ]}(ρbar) = k`, so the
framing is a torsor and Schlessinger's H4 holds; `hfin` is H3 (the
framed tangent space, a subset of the hardly ramified lifts over the
dual numbers `k[ε]`, is finite). H1 and H2 are formal for the FRAMED
functor — a lift over a fibre product `A₁ ×_{A₀} A₂` of coefficient
rings is exactly a compatible pair of lifts, the frame removing the
gluing ambiguity — and the hardly ramified local conditions are checked
componentwise: cyclotomic determinant and unramifiedness outside
`{2, ℓ}` are limit-stable, flatness at `ℓ` is a deformation condition by
Ramakrishna, and the tame quadratic quotient at `2` is an ordinary-type
condition by Conrad–Diamond–Taylor. Hence by Schlessinger's theorem
(Trans. AMS 130 (1968), Thm. 2.11) and Mazur (§1.2) the functor has a
hull, presented by the de Smit–Lenstra generators-and-relations
construction as `W(k)[[x₁,…,x_g]]/I` with `g = dim_k` of the tangent
space; that quotient is Noetherian, local, `𝔪`-adically complete and
carries the `𝔪`-adic topology — the three Mazur-category clauses of the
conclusion — and the classifying map of a residually identified finite
test object is the required `ψ`.

NOTE ON THE MAZUR-CATEGORY CLAUSES. They are delivered by this leaf
rather than cut out as commutative algebra over the presentation
(`IsNoetherianRing`/`IsAdicComplete` from a surjection
`ℤ_ℓ[[x₁,…,x_g]] ↠ R`, as `Patching.lean` cuts them) because this
file's power-series section — including the PROVEN
`isNoetherianRing_mvPowerSeries` — is declared far BELOW this point and
depends on the currying machinery developed there; separating them here
would mean either moving that section above the deformation-theoretic
section or re-sorrying an already proven lemma. Once the section is
moved, the split is available at no mathematical cost.

PARALLEL COPY, NOT IMPORTABLE. `Modularity/Patching.lean` proves the
same statement (`exists_weaklyUniversalOnIdentified_hardlyRamifiedDeformation`)
over the same finite-tangent/finite-tests cut, its Artinian-level leaf
being `exists_framedStrictlyUniversal_hardlyRamified_finiteTests` (whose
`IsStrictlyUniversalOnFramedFiniteLifts` is the unbundled twin of
`IsStrictlyUniversalOnFiniteFrames` above). It cannot be imported here:
`Patching.lean` imports `Modularity/KhareWintenberger.lean`, which
consumes pillar α — which is what this file proves. See
`~/.flt-design-deformation-patching-dedup.md`: the de-duplication is a
module split of `Patching.lean` into a KW-free upstream module, to be
done when that file is quiet.

CIRCULARITY GUARD. This leaf carries the `IsHardlyRamified` +
`IsIrreducible` + `5 ≤ ℓ` package that the odd-prime dichotomy
`not_isIrreducible_of_isHardlyRamified_of_five_le` refutes, and that
dichotomy is proven over pillar α — which is what this file's cone
proves. Discharging this leaf vacuously through it is circular and Lean
rejects it. Likewise no import from `Family.lean`, `Lift.lean` or
`Modularity/*` may be added to this module.

References: Mazur, *Deforming Galois representations*, MSRI Publ. 16
(1989), §1.2; Ramakrishna, *On a variation of Mazur's deformation
functor*, Compositio 87 (1994); Conrad–Diamond–Taylor, JAMS 12 (1999),
§2; de Smit–Lenstra, *Explicit construction of universal deformation
rings*, Prop. 2.3; Böckle's appendix to Khare's Serre-conjecture
notes. -/
theorem exists_isStrictlyUniversalOnFrames_of_finite_lifts (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible)
    (hschur : ∀ f : Module.End k V, (∀ g, Commute f (ρbar g)) →
      ∃ c : k, f = c • 1)
    (hfin : ∀ (A : Type u) [CommRing A] [TopologicalSpace A]
      [IsTopologicalRing A] [IsLocalRing A] [Algebra ℤ_[ℓ] A] [Finite A]
      [DiscreteTopology A],
      {ρ : FramedGaloisRep ℚ A (Fin 2) |
        IsHardlyRamified hℓOdd (rank_finTwoFun A) ρ}.Finite) :
    ∃ (R : Type u) (_ : CommRing R) (_ : TopologicalSpace R)
      (_ : IsTopologicalRing R) (_ : IsLocalRing R) (_ : Algebra ℤ_[ℓ] R)
      (_ : IsNoetherianRing R) (_ : IsAdic (IsLocalRing.maximalIdeal R))
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal R) R)
      (ρuniv : FramedGaloisRep ℚ R (Fin 2))
      (_ : IsHardlyRamified hℓOdd (rank_finTwoFun R) ρuniv)
      (πuniv : R →+* k) (_ : Function.Surjective πuniv)
      (hπcont : Continuous πuniv),
      IsResidualIdentifiedFrame (ℓ := ℓ) ρbar ρuniv πuniv hπcont ∧
      IsStrictlyUniversalOnFrames hℓOdd ρbar ρuniv πuniv :=
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- **Mazur/Ramakrishna representability at the ARTINIAN level** (PROVEN
2026-07-26 over the Schlessinger cut — the H3 finiteness leaf
`finite_setOf_isHardlyRamified_frames`, the H4 Schur node
`exists_smul_eq_of_commute_of_isIrreducible` (itself PROVEN 2026-07-26)
and the deformation-theoretic
core leaf `exists_isStrictlyUniversalOnFrames_of_finite_lifts`): the hardly
ramified deformation problem of an irreducible hardly ramified `ρbar`
(`ℓ ≥ 5`) admits an object `D` of Mazur's category that classifies every
FINITE residually identified framed test object *strictly* — by a
continuous `ℤ_ℓ`-algebra map compatible with the reductions along which
`D.ρ` pushes forward to the test representation up to the framing
ambiguity.

The glue proven here is the BUNDLING of the raw hull into an object of
this file's deformation category. The core leaf delivers the coefficient
ring with its Mazur-category clauses, the hardly ramified framed
representation, the surjective continuous reduction and the residual
identification `ρuniv ⊗_R k ≅ ρbar`; what the structure
`HardlyRamifiedDeformation` additionally demands is `charFrob_compat`,
the `charFrob` shadow of that identification, and it is exactly
`charpoly_baseChange_conj` evaluated at `globalFrob`: conjugation and
base change carry the characteristic polynomial of `ρuniv` at a
Frobenius onto that of `ρbar` through the coefficient map
`algebraMap R k = πuniv`. The universality clause then transfers with
nothing to do, `IsStrictlyUniversalOnFrames` being the raw transcription
of `IsStrictlyUniversalOnFiniteFrames`.

CIRCULARITY GUARD (inherited by the three leaves): the hypothesis package
is the one `not_isIrreducible_of_isHardlyRamified_of_five_le` refutes, and
that dichotomy is proven over pillar α, i.e. over this file's cone; no
leaf below this node may be discharged vacuously through it. -/
theorem exists_isStrictlyUniversalOnFiniteFrames (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible) :
    ∃ D : HardlyRamifiedDeformation hℓOdd ρbar,
      D.IsStrictlyUniversalOnFiniteFrames := by
  obtain ⟨R, iCR, iTS, iTR, iLR, iAlg, iNoeth, hadic, hcomplete, ρuniv,
      hρuniv, πuniv, hπsurj, hπcont, hident, huniv⟩ :=
    exists_isStrictlyUniversalOnFrames_of_finite_lifts hℓOdd hdim hℓ5 h hirr
      (fun f hf =>
        exists_smul_eq_of_commute_of_isIrreducible hℓOdd hdim h hirr f hf)
      (fun A => finite_setOf_isHardlyRamified_frames hℓOdd)
  refine ⟨{ R := R, isAdic := hadic, isAdicComplete := hcomplete,
            ρ := ρuniv, isHardlyRamified := hρuniv, π := πuniv,
            π_surjective := hπsurj, charFrob_compat := ?_ }, huniv⟩
  intro q hq hq2 hqℓ
  letI : Algebra R k := πuniv.toAlgebra
  letI : ContinuousSMul R k := continuousSMul_of_algebraMap R k
    (by rw [RingHom.algebraMap_toAlgebra]; exact hπcont)
  obtain ⟨e, he⟩ := hident
  have hcp := charpoly_baseChange_conj ρuniv e
    (globalFrob hq.toHeightOneSpectrumRingOfIntegersRat)
  rw [he] at hcp
  rw [GaloisRep.charFrob_eq_charpoly_globalFrob,
    GaloisRep.charFrob_eq_charpoly_globalFrob, hcp,
    RingHom.algebraMap_toAlgebra]

/-- **The pro-finite limit upgrade** (sorry node — the
commutative-algebra half of the 2026-07-25 Schlessinger cut): a
deformation that classifies every FINITE residually identified
deformation classifies every residually identified deformation. No
arithmetic is involved: the hardly ramified conditions enter only
through the fact that they are stable under quotient base change, and
the input and output clauses are identical apart from the finiteness
restriction.

Classical route, in four steps.

1. *Level-`n` test objects.* Let `D'` be residually identified and
   `n : ℕ`. Base change `D'` along the surjection
   `D'.R ↠ D'.R ⧸ 𝔪ⁿ`. The quotient is local (`𝔪ⁿ ≠ ⊤`), Noetherian,
   discrete — `𝔪ⁿ` is open for the adic topology, and the induced adic
   topology is discrete because the maximal ideal is nilpotent there, so
   `IsAdic` and `IsAdicComplete` hold trivially — and FINITE, because
   `D'.R` is Noetherian with the finite residue field `k`
   (`Ideal.finite_quotient_pow`, the route already taken by
   `finite_quotient_of_maximalIdeal_pow_le` LATER IN THIS FILE).
   Hardly-ramifiedness pushes forward along the quotient
   (`isHardlyRamified_baseChange_quotient`, with its ingredients
   `isFlatAt_baseChange_quotient` and `isTameAtTwo_baseChange`), the
   reduction map factors because `𝔪ⁿ ≤ 𝔪 = ker D'.π`, and the residual
   identification of the quotient is that of `D'` transported through
   the tensor cancellation `k ⊗_{D'.R ⧸ 𝔪ⁿ} ((D'.R ⧸ 𝔪ⁿ) ⊗_{D'.R} M)
   ≅ k ⊗_{D'.R} M`. NOTE FOR THE PROVER: those three base-change lemmas
   are stated further down this module; proving this leaf requires
   moving them above this point (they depend on nothing between).
2. *Level-`n` classifying data.* The finite hypothesis applied to the
   level-`n` object gives a pair `(ψₙ, eₙ)` — a strict ring map
   `D.R →+* D'.R ⧸ 𝔪ⁿ` together with a conjugation of the pushforward
   of `D.ρ` onto the reduced representation.
3. *Kőnig.* For fixed `n` there are only FINITELY many such pairs: a
   `ψ` with `π ∘ ψ = D.π` kills `𝔪_{D.R}^c` for a `c` with
   `𝔪ⁿ`-nilpotency, hence factors through the finite ring
   `D.R ⧸ 𝔪_{D.R}^c` (this is `Patching.lean`'s proven
   `finite_setOf_ringHom_comp_eq`, whose own finiteness input is
   `finite_quotient_of_maximalIdeal_pow_le` of this file), and `e` is a
   matrix over a finite ring. The sets are nonempty by step 2 and
   stable under the transition maps `D'.R ⧸ 𝔪ᵐ ↠ D'.R ⧸ 𝔪ⁿ`, so
   `nonempty_sections_of_finite_inverse_system` gives a compatible
   system `(ψₙ, eₙ)ₙ`.
4. *Assembly.* `D'.R` is `𝔪`-adically complete and separated
   (`isAdicComplete`), so the compatible system assembles: `ψ = lim ψₙ`
   is a ring homomorphism, continuous because it is local; the matrix
   `lim eₙ` is invertible because it is invertible modulo `𝔪`; and the
   conjugation equation, holding modulo every `𝔪ⁿ`, holds outright by
   separatedness.

Interface-side twin: `Modularity/Patching.lean`'s PROVEN
`isWeaklyUniversalOnIdentifiedDeformation_of_finiteTests`, which
performs exactly steps 1–4 over the leaves
`exists_ringHom_quotient_of_finiteTests` (step 1),
`finite_quotient_maximalIdeal_pow` (step 3 — dischargeable from this
file's `finite_quotient_of_maximalIdeal_pow_le`) and
`exists_ringHom_of_forall_quotient_mem` (steps 3–4). That proof carries
only the TRACE-level clause through the limit; the extra work here is
that the conjugation datum `e` must be carried through the Kőnig
argument alongside `ψ`, which is why the pairs, not the ring maps
alone, form the inverse system.

WHAT IS ALREADY PROVEN AT THE UN-FRAMED LEVEL, AND WHY IT DOES NOT
TRANSFER (2026-07-25, recorded after a collision in which this leaf and
an un-framed twin were cut simultaneously). Steps 3–4 in their
TRACE-ONLY form are proven, verbatim in the shape

    exists_ringHom_of_forall_quotient_mem
      (I : Ideal A) [IsAdicComplete I A] (X : ∀ n, Set (R →+* A ⧸ I ^ n))
      (finite) (nonempty) (stable under `Ideal.Quotient.factorPow`) :
      ∃ f : R →+* A, ∀ n, (Ideal.Quotient.mk (I ^ n)).comp f ∈ X n

— in `Modularity/Patching.lean` (its identically-stated leaf, discharged
2026-07-25) and in this repository's history at commit `bca1902`. Two
things in that proof are worth reusing here and one is not:

* REUSE: step 4 needs no manual limit construction at all. Mathlib's
  `IsAdicComplete.liftRingHom` (`Mathlib/RingTheory/AdicCompletion/
  RingHom.lean`) is exactly the universal property — a compatible tower
  `f n : R →+* A ⧸ I ^ n` assembles to `f : R →+* A` with
  `mk_comp_liftRingHom : (mk (I ^ n)).comp (liftRingHom I f hf) = f n`.
  "`ψ = lim ψₙ` is a ring homomorphism" above is therefore free.
* REUSE: step 3's finiteness is `finite_setOf_ringHom_comp_eq` (proven
  in `Patching.lean`), whose only nontrivial input is mathlib's
  `Ideal.finite_quotient_pow` — which also discharges that file's
  `finite_quotient_maximalIdeal_pow` outright.
* DOES NOT TRANSFER: the Kőnig step itself. The lemma above quantifies
  over `Set (R →+* A ⧸ I ^ n)` — a NON-dependent family — whereas here
  the second component `e` has a type that depends on the first: the
  algebra structure `Algebra D.R (D'.R ⧸ 𝔪ⁿ)` used to form
  `(D'.R ⧸ 𝔪ⁿ) ⊗_{D.R} (Fin 2 → D.R)` is `ψₙ.toAlgebra`. So the
  inverse system is one of Σ-types and the lemma cannot be applied.
  SUGGESTED FIX for whoever proves this leaf: make the system
  non-dependent first, by transporting `e` across the canonical
  `TensorProduct.piScalarRight` isomorphism
  `B ⊗_{D.R} (Fin 2 → D.R) ≅ (Fin 2 → B)` (already used in
  `exists_hardlyRamified_lift_of_five_le` in this file) so that the
  datum becomes an element of `GL₂(D'.R ⧸ 𝔪ⁿ)` — a type independent of
  `ψₙ` — with the conjugation equation as a side condition. Kőnig then
  applies to the plain product, the ring-map component assembles by
  `IsAdicComplete.liftRingHom`, and the matrix component assembles
  entrywise by `IsPrecomplete`, its invertibility coming from
  invertibility modulo `𝔪` as step 4 already notes.

CIRCULARITY GUARD: as for the Artinian leaf — the hypothesis package is
the one the odd-prime dichotomy refutes, and the dichotomy is proven
over pillar α, so a vacuous discharge through it is circular. -/
theorem isWeaklyUniversalOnIdentifiedFrames_of_finite
    {ρbar : GaloisRep ℚ k V} (D : HardlyRamifiedDeformation hℓOdd ρbar)
    (hD : D.IsWeaklyUniversalOnIdentifiedFramesFinite) :
    D.IsWeaklyUniversalOnIdentifiedFrames :=
  sorry

/-- **Strict Mazur representability** (PROVEN 2026-07-25 over the
Schlessinger cut: the Artinian-level representability leaf
`exists_isStrictlyUniversalOnFiniteFrames`, the pro-finite limit leaf
`isWeaklyUniversalOnIdentifiedFrames_of_finite`, and the re-bundling
glue between them): the hardly ramified deformation problem of an
irreducible hardly ramified `ρbar` (`ℓ ≥ 5`) admits a deformation `D`
that maps to every *residually identified* deformation `D'` — every
`D'` equipped with a conjugation of its reduction onto `ρbar` — by a
continuous `ℤ_ℓ`-algebra homomorphism compatible with the reduction maps
along which `D.ρ` pushes forward to `D'.ρ` up to conjugation.

The cut is the classical architecture of the representability theorem,
and the one `Modularity/Patching.lean` uses for its (non-importable)
parallel copy: Schlessinger's criterion produces a hull against
ARTINIAN test objects only, and the passage to the whole of Mazur's
category is the separate, purely commutative-algebraic pro-finite limit.
The Chebotarev–Brauer–Nesbitt matching is in neither half (it is
supplied by `exists_conj_of_charFrob_eq` through the proven assembly
`exists_isWeaklyUniversal`); this stratum is Mazur/Ramakrishna
representability proper. -/
theorem exists_isWeaklyUniversalOnIdentifiedFrames (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible) :
    ∃ D : HardlyRamifiedDeformation hℓOdd ρbar,
      D.IsWeaklyUniversalOnIdentifiedFrames := by
  obtain ⟨D, hD⟩ :=
    exists_isStrictlyUniversalOnFiniteFrames hℓOdd hdim hℓ5 h hirr
  exact ⟨D, isWeaklyUniversalOnIdentifiedFrames_of_finite hℓOdd D
    (isWeaklyUniversalOnIdentifiedFramesFinite_of_isStrictlyUniversalOnFiniteFrames
      hℓOdd D hD)⟩

/-- **Trace shadow of strict Mazur representability** (PROVEN
2026-07-25, glue over `exists_isWeaklyUniversalOnIdentifiedFrames`):
a deformation classifying every residually identified deformation at
the level of representations classifies it at the level of Frobenius
characteristic polynomials.

The proof is `charpoly_baseChange_conj`: the family-membership equation
`(D.ρ.baseChange D'.R).conj e = D'.ρ` identifies the characteristic
polynomial of `D'.ρ` at each Frobenius with the image under the
coefficient map `algebraMap D.R D'.R = f` of that of `D.ρ` — which is
verbatim the `charFrob` clause of `IsWeaklyUniversalOnIdentified`. The
other two clauses (the `ℤ_ℓ`-structure map and the reduction map) are
carried unchanged. -/
theorem exists_isWeaklyUniversalOnIdentified (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible) :
    ∃ D : HardlyRamifiedDeformation hℓOdd ρbar,
      D.IsWeaklyUniversalOnIdentified := by
  obtain ⟨D, hD⟩ :=
    exists_isWeaklyUniversalOnIdentifiedFrames hℓOdd hdim hℓ5 h hirr
  refine ⟨D, ?_⟩
  letI := D.commRing; letI := D.topologicalSpace; letI := D.isTopologicalRing
  letI := D.isLocalRing; letI := D.algebra
  intro D' hid
  letI := D'.commRing; letI := D'.topologicalSpace
  letI := D'.isTopologicalRing; letI := D'.isLocalRing; letI := D'.algebra
  obtain ⟨f, hfc, hf1, hf2, e, he⟩ := hD D' hid
  letI : Algebra D.R D'.R := f.toAlgebra
  letI : ContinuousSMul D.R D'.R :=
    continuousSMul_of_algebraMap D.R D'.R
      (by rw [RingHom.algebraMap_toAlgebra]; exact hfc)
  refine ⟨f, hf1, hf2, ?_⟩
  intro q hq hq2 hqℓ
  have hcp := charpoly_baseChange_conj D.ρ e
    (globalFrob hq.toHeightOneSpectrumRingOfIntegersRat)
  rw [he] at hcp
  show ((D.ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map f) = _
  rw [GaloisRep.charFrob_eq_charpoly_globalFrob,
    GaloisRep.charFrob_eq_charpoly_globalFrob, hcp,
    RingHom.algebraMap_toAlgebra]

open scoped TensorProduct in
/-- **Mazur representability stratum** (DECOMPOSED 2026-07-23 into the
strict Mazur representability leaf
`exists_isWeaklyUniversalOnIdentified` — the classifying maps for
residually identified deformations — and the Chebotarev–Brauer–Nesbitt
conjugacy leaf `exists_conj_of_charFrob_eq` — which produces the
residual identification from the `charFrob_compat` matching; the
assembly below is proven): the hardly ramified deformation problem of
an irreducible hardly ramified `ρbar` (`ℓ ≥ 5`) admits a *weakly
universal* object — a deformation mapping compatibly to every
deformation. Trace generation is NOT part of this node (it is restored
by the Carayol descent stratum
`exists_isWeaklyUniversal_isTraceGenerated_of_isWeaklyUniversal`
below).

The proven glue: given any deformation `D'`, its reduction — the base
change of `D'.ρ` along the (continuous, by `continuous_pi`) reduction
map `D'.π` — is a 2-dimensional mod-`ℓ` representation
(`Module.rank_baseChange`) whose Frobenius characteristic polynomials
are the reductions of those of `D'.ρ` (`LinearMap.charpoly_baseChange`)
— i.e., by clause `charFrob_compat`, those of `ρbar`. The
Chebotarev–Brauer–Nesbitt leaf turns this matching into a residual
identification, and the strict leaf's classifying map is the required
compatible homomorphism. -/
theorem exists_isWeaklyUniversal (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible) :
    ∃ D : HardlyRamifiedDeformation hℓOdd ρbar, D.IsWeaklyUniversal := by
  obtain ⟨D, hD⟩ :=
    exists_isWeaklyUniversalOnIdentified hℓOdd hdim hℓ5 h hirr
  refine ⟨D, ?_⟩
  letI := D.commRing; letI := D.topologicalSpace; letI := D.isTopologicalRing
  letI := D.isLocalRing; letI := D.algebra
  intro D'
  letI := D'.commRing; letI := D'.topologicalSpace
  letI := D'.isTopologicalRing; letI := D'.isLocalRing; letI := D'.algebra
  letI : Algebra D'.R k := D'.π.toAlgebra
  letI : ContinuousSMul D'.R k :=
    continuousSMul_of_algebraMap D'.R k
      (by rw [RingHom.algebraMap_toAlgebra]; exact D'.continuous_pi)
  -- the reduction is 2-dimensional …
  have hrankW :
      Module.rank k (k ⊗[D'.R] (Fin 2 → D'.R)) = 2 := by
    rw [Module.rank_baseChange, rank_finTwoFun]
    simp
  -- … and its Frobenius characteristic polynomials are those of `ρbar`
  have hcf : ∀ q (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (D'.ρ.baseChange k).charFrob
          hq.toHeightOneSpectrumRingOfIntegersRat =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat := by
    intro q hq hq2 hqℓ
    have hcp : ((D'.ρ.baseChange k)
        (globalFrob hq.toHeightOneSpectrumRingOfIntegersRat)).charpoly =
        ((D'.ρ (globalFrob
          hq.toHeightOneSpectrumRingOfIntegersRat)).charpoly).map
          (algebraMap D'.R k) := by
      show ((Module.End.baseChangeHom D'.R k (Fin 2 → D'.R))
        (D'.ρ (globalFrob
          hq.toHeightOneSpectrumRingOfIntegersRat))).charpoly = _
      rw [show (Module.End.baseChangeHom D'.R k (Fin 2 → D'.R))
          (D'.ρ (globalFrob hq.toHeightOneSpectrumRingOfIntegersRat)) =
        LinearMap.baseChange k
          (D'.ρ (globalFrob hq.toHeightOneSpectrumRingOfIntegersRat))
        from rfl, LinearMap.charpoly_baseChange]
    have hred := D'.charFrob_compat q hq hq2 hqℓ
    show ((D'.ρ.baseChange k)
      (globalFrob hq.toHeightOneSpectrumRingOfIntegersRat)).charpoly = _
    rw [hcp, RingHom.algebraMap_toAlgebra]
    exact hred
  obtain ⟨e, he⟩ := exists_conj_of_charFrob_eq hdim hrankW hirr
    (D'.ρ.baseChange k) hcf
  exact hD D' ⟨e, he⟩

/-- **A subring whose image under a topological embedding is dense in
the ambient subring is everything** (PROVEN 2026-07-25, elementary
topology; the descent half of the Carayol trace-generation glue): let
`C` be a subring of a topological ring `R` carrying the subspace
topology, `T'` a subring of `C` whose image `T = ι(T')` under the
inclusion `ι = C.subtype` satisfies `C = T.topologicalClosure`. Then
`T'` is topologically dense in `C`.

The proof is the inducing-map closure formula
`IsInducing.closure_eq_preimage_closure_image`: the closure of `T'`
inside `C` is the preimage of the closure of `ι '' T' = T` inside `R`,
and every point of `C` lies in that closure by hypothesis. -/
lemma topologicalClosure_eq_top_of_map_eq {R : Type*} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] {C : Subring R}
    {T' : Subring C} {T : Subring R}
    (hmap : T'.map C.subtype = T) (hC : C = T.topologicalClosure) :
    T'.topologicalClosure = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  have hx : (x : R) ∈ T.topologicalClosure := hC ▸ x.2
  have hind : Topology.IsInducing (fun y : C => (y : R)) := ⟨rfl⟩
  have himg : (fun y : C => (y : R)) '' (T' : Set C) = (T : Set R) := by
    rw [← hmap, Subring.coe_map, Subring.coe_subtype]
  show x ∈ closure ((T' : Set C))
  rw [hind.closure_eq_preimage_closure_image, Set.mem_preimage, himg]
  exact hx

/-- **Carayol's trace subring `R'`**: the closed `ℤ_ℓ`-subalgebra of the
coefficient ring topologically generated by the coefficients of the
Frobenius characteristic polynomials at the good primes. This is the
subring appearing in the hypothesis of the Carayol descent leaf below
and, verbatim, the subring whose being everything is
`IsTraceGenerated` — so `D.IsTraceGenerated` is `traceSubring ℓ D.ρ = ⊤`
and the descent produces a deformation whose ring IS `traceSubring ℓ D.ρ`.

The prime `ℓ` is an explicit argument because it is not determined by
`ρ`: it occurs only in the `ℤ_ℓ`-algebra structure and in the
"good prime" condition `q ≠ ℓ`. -/
def traceSubring (ℓ : ℕ) [Fact ℓ.Prime] {R : Type*} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Algebra ℤ_[ℓ] R]
    (ρ : FramedGaloisRep ℚ R (Fin 2)) : Subring R :=
  (Subring.closure (Set.range (algebraMap ℤ_[ℓ] R) ∪
    {x : R | ∃ q, ∃ hq : q.Prime, q ≠ 2 ∧ q ≠ ℓ ∧ ∃ n : ℕ,
      x = (ρ.charFrob
        hq.toHeightOneSpectrumRingOfIntegersRat).coeff n})).topologicalClosure

/-- The trace subring is a `ℤ_ℓ`-algebra: the image of `ℤ_ℓ` is one of
its two generating sets, so the structure map corestricts. -/
noncomputable instance instAlgebraTraceSubring (ℓ : ℕ) [Fact ℓ.Prime]
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Algebra ℤ_[ℓ] R] (ρ : FramedGaloisRep ℚ R (Fin 2)) :
    Algebra ℤ_[ℓ] (traceSubring ℓ ρ) :=
  ((algebraMap ℤ_[ℓ] R).codRestrict (traceSubring ℓ ρ)
    (fun c => Subring.le_topologicalClosure _
      (Subring.subset_closure (Or.inl ⟨c, rfl⟩)))).toAlgebra

/-- Every Frobenius characteristic-polynomial coefficient at a good
prime lies in the trace subring (it is one of its generators). -/
lemma charFrob_coeff_mem_traceSubring (ℓ : ℕ) [Fact ℓ.Prime] {R : Type*}
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Algebra ℤ_[ℓ] R] (ρ : FramedGaloisRep ℚ R (Fin 2))
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqℓ : q ≠ ℓ) (n : ℕ) :
    (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff n ∈
      traceSubring ℓ ρ :=
  Subring.le_topologicalClosure _
    (Subring.subset_closure (Or.inr ⟨q, hq, hq2, hqℓ, n, rfl⟩))

/-- **The descended representation is trace-generated** (PROVEN
2026-07-25 — the *coefficient-ring structure of `R'`* half of Carayol's
Théorème 1): if a framed representation `ρ'` over the trace subring
`R' = traceSubring ℓ ρ` of `ρ` has `ρ`'s Frobenius characteristic
polynomials as the images of its own under the inclusion `R' → R`, then
`R'` is topologically generated by the `ℤ_ℓ`-image together with the
`charFrob` coefficients OF `ρ'` — i.e. `ρ'` is trace-generated as a
coefficient ring in its own right.

This is not a tautology: `R'` is by definition the closure of the
subring `T` generated by the coefficients of `ρ` *inside `R`*, whereas
trace generation of `ρ'` asks for the closure of the subring `T'`
generated by the coefficients of `ρ'` *inside `R'`*, for the subspace
topology. The two are matched because the inclusion `ι : R' → R` is a
topological embedding carrying `T'` isomorphically onto `T`
(`RingHom.map_closure` plus the two generator computations: `ι` carries
the `ℤ_ℓ`-image to the `ℤ_ℓ`-image by construction of the algebra
structure, and the `charFrob` coefficients of `ρ'` to those of `ρ` by
hypothesis), so `closure T ∩ R' = closure_{R'} T'`
(`topologicalClosure_eq_top_of_map_eq`), and `closure T = R'`. -/
lemma traceSubring_eq_top_of_charFrob_map (ℓ : ℕ) [Fact ℓ.Prime]
    {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Algebra ℤ_[ℓ] R] (ρ : FramedGaloisRep ℚ R (Fin 2))
    (ρ' : FramedGaloisRep ℚ (traceSubring ℓ ρ) (Fin 2))
    (hcf : ∀ q (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ'.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map
          (traceSubring ℓ ρ).subtype =
        ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat) :
    traceSubring ℓ ρ' = ⊤ := by
  refine topologicalClosure_eq_top_of_map_eq ?_ rfl
  have h1 : (traceSubring ℓ ρ).subtype ''
      Set.range (algebraMap ℤ_[ℓ] (traceSubring ℓ ρ)) =
      Set.range (algebraMap ℤ_[ℓ] R) := by
    rw [← Set.range_comp]
    rfl
  have h2 : (traceSubring ℓ ρ).subtype ''
      {x : traceSubring ℓ ρ | ∃ q, ∃ hq : q.Prime, q ≠ 2 ∧ q ≠ ℓ ∧ ∃ n : ℕ,
        x = (ρ'.charFrob
          hq.toHeightOneSpectrumRingOfIntegersRat).coeff n} =
      {x : R | ∃ q, ∃ hq : q.Prime, q ≠ 2 ∧ q ≠ ℓ ∧ ∃ n : ℕ,
        x = (ρ.charFrob
          hq.toHeightOneSpectrumRingOfIntegersRat).coeff n} := by
    ext x
    constructor
    · rintro ⟨y, ⟨q, hq, hq2, hqℓ, n, rfl⟩, rfl⟩
      refine ⟨q, hq, hq2, hqℓ, n, ?_⟩
      simp only [← hcf q hq hq2 hqℓ, Polynomial.coeff_map, Subring.coe_subtype]
    · rintro ⟨q, hq, hq2, hqℓ, n, rfl⟩
      refine ⟨(ρ'.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff n,
        ⟨q, hq, hq2, hqℓ, n, rfl⟩, ?_⟩
      simp only [← hcf q hq hq2 hqℓ, Polynomial.coeff_map, Subring.coe_subtype]
  rw [RingHom.map_closure, Set.image_union, h1, h2]

/-- **Coefficient-ring structure of Carayol's trace subring `R'`**
(sorry leaf — the ring-theoretic half of Carayol's Théorème 1, split
off 2026-07-25): the closed `ℤ_ℓ`-subalgebra `R' = traceSubring ℓ D.ρ`
of the coefficient ring of a hardly ramified deformation is itself a
coefficient ring: local, Noetherian, with the subspace topology equal
to its own maximal-adic topology, and maximal-adically complete and
separated.

Mathematical content. Locality and completeness are the soft half: `R'`
is a CLOSED subring of the complete local ring `D.R` (it is a
topological closure by construction), `𝔪' = 𝔪 ∩ R'` is a maximal ideal
of `R'` because `R'` surjects onto the residue field `k` (that
surjectivity is `subring_closure_charFrob_coeff_eq_top` below), and any
`x ∈ R' \ 𝔪'` is invertible already in `R'`: its inverse in `D.R` is
the limit of the geometric series in `1 − x/a` for a lift `a` of the
residue of `x`, and `R'` is closed. Closedness in a complete separated
ring also gives completeness and separatedness for the induced
filtration, and the induced filtration is the `𝔪'`-adic one because
`𝔪'^n ⊆ 𝔪^n ∩ R'` and, in the other direction, Carayol's Lemme 1
bounds `𝔪^n ∩ R'` by a power of `𝔪'`.

NOETHERIANITY is the genuine content and is FALSE for a general closed
subring of a complete Noetherian local ring: it holds here because
Carayol's argument produces a finite set of topological generators of
`𝔪'` (equivalently `𝔪'/(𝔪'^2 + ℓ)` is finite-dimensional over `k`),
after which the complete local ring `R'` with finite residue field is
Noetherian by the Cohen structure theorem — a quotient of a power
series ring `W(k)[[x₁, …, x_g]]`.

The hypotheses of the Carayol package (`hℓ5`, hard ramification,
irreducibility of `ρbar`, and the trace hypothesis `htr`) are carried
even though the soft half does not consume them: they are what Carayol's
Théorème 1 assumes, and the finiteness of the generating set of `𝔪'`
uses them through the absolute irreducibility of the residual
representation.

References: Carayol, *Formes modulaires et représentations galoisiennes
à valeurs dans un anneau local complet* (Contemp. Math. 165), Théorème 1
and Lemme 1; Nyssen, *Pseudo-représentations*; Rouquier,
*Caractérisation des caractères et pseudo-caractères*. -/
theorem exists_isLocalRing_traceSubring (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible)
    (D : HardlyRamifiedDeformation hℓOdd ρbar)
    (htr : letI := D.commRing; letI := D.topologicalSpace
      letI := D.isTopologicalRing; letI := D.algebra
      ∀ g : Field.absoluteGaloisGroup ℚ,
        ((D.ρ g).charpoly).coeff 1 ∈ traceSubring ℓ D.ρ) :
    letI := D.commRing; letI := D.topologicalSpace
    letI := D.isTopologicalRing; letI := D.isLocalRing; letI := D.algebra
    ∃ hloc : IsLocalRing (traceSubring ℓ D.ρ),
      letI := hloc
      IsNoetherianRing (traceSubring ℓ D.ρ) ∧
      IsAdic (IsLocalRing.maximalIdeal (traceSubring ℓ D.ρ)) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (traceSubring ℓ D.ρ))
        (traceSubring ℓ D.ρ) :=
  sorry

/-- **Carayol's Théorème 1 proper: the conjugation into `GL₂(R')`**
(sorry leaf — the representation-theoretic half, split off 2026-07-25):
a hardly ramified deformation whose traces all lie in the closed trace
subring `R'` (hypothesis `htr`, supplied by the Chebotarev density step
`exists_isTraceGenerated_ringHom`) is, after a change of framing,
a representation with coefficients in `R'` — and the descended framed
representation is again hardly ramified and has the SAME Frobenius
characteristic polynomials, read through the inclusion `R' → D.R`.

Mathematical content (Carayol). `ρbar` is absolutely irreducible: it is
odd (its determinant is the mod-`ℓ` cyclotomic character, which sends
complex conjugation to `−1 ≠ 1` for odd `ℓ`) and irreducible over the
finite field `k`, and an odd irreducible 2-dimensional representation
over a finite field of odd characteristic is absolutely irreducible. By
Nakayama the `D.R`-algebra generated by `D.ρ(G)` is therefore all of
`M₂(D.R)`; choose `x, y ∈ G` with `{1, ρ(x), ρ(y), ρ(x)ρ(y)}` a
`D.R`-basis of `M₂(D.R)` (possible because the residues already form a
`k`-basis of `M₂(k)`). The trace form then expresses every matrix
entry of every `ρ(g)`, in the basis dual to that one, as a `ℤ`-linear
combination of traces `tr(ρ(g)·b)` with `b` a product of `ρ(x)`'s and
`ρ(y)`'s — hence, by `htr` applied to those products, an element of
`R'`; equivalently, Rouquier–Nyssen's theorem that a pseudo-character
of dimension 2 over a local ring whose residual representation is
absolutely irreducible is the character of a true representation into
`GL₂` of that ring. Conjugating by the base change matrix is the
required change of framing.

Descent of the hardly ramified conditions along the inclusion: the
determinant condition and unramifiedness outside `{2, ℓ}` transfer
because the inclusion is injective and compatible with the
`ℤ_ℓ`-structure maps; flatness at `ℓ` and the tame condition at `2`
transfer because the open ideals of `R'` are the traces of the open
ideals of `D.R` (the topology being the subspace one) and the finite
flat / triangular data descend along the induced isomorphisms of finite
quotients.

References: Carayol, *Formes modulaires et représentations galoisiennes
à valeurs dans un anneau local complet* (Contemp. Math. 165), Théorème 1;
Nyssen, *Pseudo-représentations* (Math. Ann. 306); Rouquier,
*Caractérisation des caractères et pseudo-caractères* (J. Algebra 180);
Mazur, *Deforming Galois representations*, §1.8. -/
theorem exists_framedGaloisRep_traceSubring (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible)
    (D : HardlyRamifiedDeformation hℓOdd ρbar)
    (htr : letI := D.commRing; letI := D.topologicalSpace
      letI := D.isTopologicalRing; letI := D.algebra
      ∀ g : Field.absoluteGaloisGroup ℚ,
        ((D.ρ g).charpoly).coeff 1 ∈ traceSubring ℓ D.ρ)
    (hloc : letI := D.commRing; letI := D.topologicalSpace
      letI := D.isTopologicalRing; letI := D.algebra
      IsLocalRing (traceSubring ℓ D.ρ)) :
    letI := D.commRing; letI := D.topologicalSpace
    letI := D.isTopologicalRing; letI := D.isLocalRing; letI := D.algebra
    letI := hloc
    ∃ ρ' : FramedGaloisRep ℚ (traceSubring ℓ D.ρ) (Fin 2),
      IsHardlyRamified hℓOdd (rank_finTwoFun (traceSubring ℓ D.ρ)) ρ' ∧
      ∀ q (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
        (ρ'.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map
            (traceSubring ℓ D.ρ).subtype =
          D.ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat :=
  sorry

/-- **The residual trace field is everything** (sorry leaf, isolated
2026-07-25): the coefficient field `k` is generated as a ring by the
coefficients of the Frobenius characteristic polynomials of `ρbar` at
the good primes — equivalently, `k` is the trace field of `ρbar`.

WHY THIS IS NOT AN ARTIFACT OF THE DECOMPOSITION: it is IMPLIED by the
conclusion of `exists_isTraceGenerated_ringHom_of_forall_trace_mem`, so
any proof of that theorem proves this too. Indeed the descended datum
`D'` has a surjective reduction map `D'.π : D'.R ↠ k` which is
continuous (`HardlyRamifiedDeformation.continuous_pi`) into the discrete
`k`; `D'.R` is the closure of the subring generated by the
`ℤ_ℓ`-image and its own `charFrob` coefficients (trace generation), so
`k = D'.π '' D'.R` is the subring generated by `D'.π` of those
generators; and `D'.π` sends the `ℤ_ℓ`-image into the prime field and
the `charFrob` coefficients of `D'.ρ` to those of `ρbar`
(`D'.charFrob_compat`).

It is TRUE and trivial whenever `k` is the prime field `𝔽_ℓ` — the case
of the Frey-curve application, where the deformation development is
consumed at `k = ZMod ℓ` — because any subring of `𝔽_ℓ` containing `1`
is everything, and the generating set is nonempty (the `charFrob` are
monic of degree 2, so `coeff 2 = 1` is in it). For a general finite `k`
it is the statement that `ρbar` is not the scalar extension of a
representation over a proper subfield, which is the standard
normalization of the coefficient field in the deformation-theoretic
literature (one always takes `k` to BE the trace field, `E` in
Khare–Wintenberger's notation) and which the current spelling of
`HardlyRamifiedDeformation` — whose `π_surjective` field demands the
residue field be `k` on the nose — makes a genuine hypothesis rather
than a convention. A future owner of this leaf who cannot prove it in
the general form should instead narrow `k` at the pillar-α interface.

References: Khare–Wintenberger, *Serre's modularity conjecture (I)*, §2
(the coefficient field is the field generated by the traces); Carayol,
*Formes modulaires et représentations galoisiennes à valeurs dans un
anneau local complet*, Théorème 1 (the residue field of the trace
subring is the trace field). -/
theorem subring_closure_charFrob_coeff_eq_top
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible) :
    Subring.closure {x : k | ∃ q, ∃ hq : q.Prime, q ≠ 2 ∧ q ≠ ℓ ∧ ∃ n : ℕ,
      x = (ρbar.charFrob
        hq.toHeightOneSpectrumRingOfIntegersRat).coeff n} = ⊤ :=
  sorry

/-- **Carayol subring-descent stratum** (PROVEN 2026-07-25 as glue over
the three leaves `exists_isLocalRing_traceSubring` (the coefficient-ring
structure of `R'`), `exists_framedGaloisRep_traceSubring` (Carayol's
Théorème 1 proper: the conjugation into `GL₂(R')`) and
`subring_closure_charFrob_coeff_eq_top` (the residual trace field);
DECOMPOSED 2026-07-25 from the earlier single sorry, whose Chebotarev
density step had already been split off into
`exists_isTraceGenerated_ringHom` and enters here as the hypothesis
`htr`): every hardly ramified deformation `D` of an irreducible hardly
ramified `ρbar` (`ℓ ≥ 5`) whose closed trace subring `R'` already
absorbs the trace of `D.ρ` at every group element admits a
*trace-generated* deformation `D'` mapping compatibly INTO it. Weak
universality plays no role here: it is restored formally by the
composition glue in
`exists_isWeaklyUniversal_isTraceGenerated_of_isWeaklyUniversal` below.

The assembly below is proven. The descended datum is built on the
coefficient ring `R' = traceSubring ℓ D.ρ` itself: its ring structure
comes from the first leaf, its representation from the second, its
reduction map is `D.π ∘ ι` for the inclusion `ι = R'.subtype` (whose
surjectivity onto `k` is the third leaf applied to the range of
`D.π ∘ ι`, a subring of `k` containing every `charFrob` coefficient of
`ρbar` by `D.charFrob_compat`), and its `charFrob_compat` is the
factorization `map (D.π ∘ ι) = map D.π ∘ map ι` through the second
leaf's clause. The two clauses of `IsTraceDescent` then hold with
`ι`: trace generation is the PROVEN
`traceSubring_eq_top_of_charFrob_map` — the coefficient-ring statement
that `R'` is topologically generated by the traces of the DESCENDED
representation, not merely by those of `D.ρ` — and the three
compatibilities are, respectively, the definition of the corestricted
`ℤ_ℓ`-structure map, the definition of `D'.π`, and the second leaf's
`charFrob` clause.

References: Carayol, *Formes modulaires et représentations galoisiennes
à valeurs dans un anneau local complet* (Théorème 1 and Lemme 1);
Mazur, *Deforming Galois representations*, §1.8. -/
theorem exists_isTraceGenerated_ringHom_of_forall_trace_mem (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible)
    (D : HardlyRamifiedDeformation hℓOdd ρbar)
    (htr : letI := D.commRing; letI := D.topologicalSpace
      letI := D.isTopologicalRing; letI := D.algebra
      ∀ g : Field.absoluteGaloisGroup ℚ,
        ((D.ρ g).charpoly).coeff 1 ∈
          (Subring.closure (Set.range (algebraMap ℤ_[ℓ] D.R) ∪
            {x : D.R | ∃ q, ∃ hq : q.Prime, q ≠ 2 ∧ q ≠ ℓ ∧ ∃ n : ℕ,
              x = (D.ρ.charFrob
                hq.toHeightOneSpectrumRingOfIntegersRat).coeff
                  n})).topologicalClosure) :
    ∃ D' : HardlyRamifiedDeformation hℓOdd ρbar, D.IsTraceDescent hℓOdd D' := by
  classical
  letI := D.commRing; letI := D.topologicalSpace; letI := D.isTopologicalRing
  letI := D.isLocalRing; letI := D.algebra; letI := D.isNoetherianRing
  obtain ⟨hloc, hnoeth, hadic, hcompl⟩ :=
    exists_isLocalRing_traceSubring hℓOdd hdim hℓ5 h hirr D htr
  letI := hloc
  obtain ⟨ρ', hhr', hcf'⟩ :=
    exists_framedGaloisRep_traceSubring hℓOdd hdim hℓ5 h hirr D htr hloc
  refine ⟨{ R := traceSubring ℓ D.ρ
            isLocalRing := hloc
            isNoetherianRing := hnoeth
            isAdic := hadic
            isAdicComplete := hcompl
            ρ := ρ'
            isHardlyRamified := hhr'
            π := D.π.comp (traceSubring ℓ D.ρ).subtype
            π_surjective := ?_
            charFrob_compat := ?_ }, ?_, (traceSubring ℓ D.ρ).subtype, ?_, rfl,
          hcf'⟩
  · -- surjectivity of the descended reduction map: its range is a
    -- subring of `k` containing every `charFrob` coefficient of `ρbar`
    intro y
    have hmem : y ∈ Subring.closure {x : k | ∃ q, ∃ hq : q.Prime, q ≠ 2 ∧ q ≠ ℓ ∧
        ∃ n : ℕ, x = (ρbar.charFrob
          hq.toHeightOneSpectrumRingOfIntegersRat).coeff n} := by
      rw [subring_closure_charFrob_coeff_eq_top hℓOdd hdim h hirr]
      trivial
    have hle : Subring.closure {x : k | ∃ q, ∃ hq : q.Prime, q ≠ 2 ∧ q ≠ ℓ ∧
        ∃ n : ℕ, x = (ρbar.charFrob
          hq.toHeightOneSpectrumRingOfIntegersRat).coeff n} ≤
        (D.π.comp (traceSubring ℓ D.ρ).subtype).range := by
      rw [Subring.closure_le]
      rintro x ⟨q, hq, hq2, hqℓ, n, rfl⟩
      refine ⟨⟨(D.ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff n,
        charFrob_coeff_mem_traceSubring ℓ D.ρ hq hq2 hqℓ n⟩, ?_⟩
      show D.π ((D.ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff n) =
        (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff n
      rw [← D.charFrob_compat q hq hq2 hqℓ, Polynomial.coeff_map]
    exact hle hmem
  · -- `charFrob` compatibility of the descended datum with `ρbar`
    intro q hq hq2 hqℓ
    rw [← Polynomial.map_map, hcf' q hq hq2 hqℓ]
    exact D.charFrob_compat q hq hq2 hqℓ
  · -- trace generation of the descended datum
    exact traceSubring_eq_top_of_charFrob_map ℓ D.ρ ρ' hcf'
  · -- the `ℤ_ℓ`-structure map of the descended datum
    exact RingHom.ext fun c => rfl

/-- **Chebotarev half of the Carayol descent** (PROVEN 2026-07-25 — the
density step of the route recorded on
`exists_isTraceGenerated_ringHom_of_forall_trace_mem` above): the
closed subring `R'` topologically generated by the `ℤ_ℓ`-image and the
Frobenius characteristic-polynomial coefficients at the good primes
absorbs the trace of `D.ρ` at EVERY element of `Gal(ℚ̄/ℚ)`, so the
hypothesis of the subring-descent leaf is automatic and the descent
leaf discharges `exists_isTraceGenerated_ringHom` outright.

The proof is Carayol's density step, verbatim: the trace function
`g ↦ (charpoly (D.ρ g)).coeff 1 = −tr (D.ρ g)` is continuous (the trace
is a `D.R`-linear functional on `Module.End D.R (Fin 2 → D.R)`, which
carries the module topology by the definition of `GaloisRep`, so
`IsModuleTopology.continuous_of_linearMap` applies), hence its
`R'`-agreement set is closed (`R'` being a topological closure); that
set contains every conjugate of every Frobenius at a prime outside
`{(2), (ℓ)}` by conjugation-invariance of the characteristic
polynomial; and those conjugates are dense by Chebotarev
(`dense_conjClasses_globalFrob`). -/
theorem exists_isTraceGenerated_ringHom (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible)
    (D : HardlyRamifiedDeformation hℓOdd ρbar) :
    ∃ D' : HardlyRamifiedDeformation hℓOdd ρbar,
      D.IsTraceDescent hℓOdd D' := by
  classical
  letI := D.commRing; letI := D.topologicalSpace; letI := D.isTopologicalRing
  letI := D.isLocalRing; letI := D.algebra
  refine exists_isTraceGenerated_ringHom_of_forall_trace_mem hℓOdd hdim hℓ5 h
    hirr D ?_
  set C : Subring D.R :=
    (Subring.closure (Set.range (algebraMap ℤ_[ℓ] D.R) ∪
      {x : D.R | ∃ q, ∃ hq : q.Prime, q ≠ 2 ∧ q ≠ ℓ ∧ ∃ n : ℕ,
        x = (D.ρ.charFrob
          hq.toHeightOneSpectrumRingOfIntegersRat).coeff n})).topologicalClosure
    with hC
  have hCclosed : IsClosed (C : Set D.R) :=
    Subring.isClosed_topologicalClosure _
  -- continuity of the global trace function
  have hFcont : Continuous fun g : Field.absoluteGaloisGroup ℚ =>
      ((D.ρ g).charpoly).coeff 1 := by
    letI := moduleTopology D.R (Module.End D.R (Fin 2 → D.R))
    haveI : IsModuleTopology D.R (Module.End D.R (Fin 2 → D.R)) := ⟨rfl⟩
    have hρc : Continuous fun g : Field.absoluteGaloisGroup ℚ => D.ρ g :=
      ContinuousMonoidHom.continuous_toFun D.ρ
    have htrc : Continuous fun φ : Module.End D.R (Fin 2 → D.R) =>
        LinearMap.trace D.R (Fin 2 → D.R) φ :=
      IsModuleTopology.continuous_of_linearMap _
    have hcoeff : (fun g : Field.absoluteGaloisGroup ℚ =>
        ((D.ρ g).charpoly).coeff 1) =
        fun g => - LinearMap.trace D.R (Fin 2 → D.R) (D.ρ g) := by
      funext g
      have hmt := Matrix.trace_eq_neg_charpoly_coeff
        (LinearMap.toMatrix (Pi.basisFun D.R (Fin 2)) (Pi.basisFun D.R (Fin 2))
          (D.ρ g))
      rw [LinearMap.charpoly_toMatrix] at hmt
      rw [LinearMap.trace_eq_matrix_trace D.R (Pi.basisFun D.R (Fin 2)), hmt]
      norm_num
    rw [hcoeff]
    exact (htrc.comp hρc).neg
  -- the `C`-agreement set of the trace function is closed …
  have hDclosed : IsClosed {g : Field.absoluteGaloisGroup ℚ |
      ((D.ρ g).charpoly).coeff 1 ∈ C} :=
    hCclosed.preimage hFcont
  -- … and contains the Frobenius conjugates away from `{2, ℓ}`
  have hsub : {x : Field.absoluteGaloisGroup ℚ |
      ∃ v : IsDedekindDomain.HeightOneSpectrum
          (NumberField.RingOfIntegers ℚ),
        v ∉ ({Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat,
            (Fact.out : ℓ.Prime).toHeightOneSpectrumRingOfIntegersRat} :
          Finset (IsDedekindDomain.HeightOneSpectrum
            (NumberField.RingOfIntegers ℚ))) ∧
        ∃ hgg : Field.absoluteGaloisGroup ℚ,
          x = hgg * globalFrob v * hgg⁻¹} ⊆
      {g : Field.absoluteGaloisGroup ℚ |
        ((D.ρ g).charpoly).coeff 1 ∈ C} := by
    rintro x ⟨v, hvS, hgg, rfl⟩
    obtain ⟨q, hq, rfl⟩ := exists_prime_toHeightOneSpectrum v
    have hq2 : q ≠ 2 := by
      rintro rfl
      exact hvS (Finset.mem_insert.mpr (Or.inl rfl))
    have hqℓ : q ≠ ℓ := by
      rintro rfl
      exact hvS (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))
    have hgu : (D.ρ hgg).comp (D.ρ hgg⁻¹) = LinearMap.id := by
      have h1 : D.ρ hgg * D.ρ hgg⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel, map_one]
      exact h1
    have hgu' : (D.ρ hgg⁻¹).comp (D.ρ hgg) = LinearMap.id := by
      have h1 : D.ρ hgg⁻¹ * D.ρ hgg = 1 := by
        rw [← map_mul, inv_mul_cancel, map_one]
      exact h1
    have heq : D.ρ (hgg * globalFrob
          hq.toHeightOneSpectrumRingOfIntegersRat * hgg⁻¹) =
        (LinearEquiv.ofLinear (D.ρ hgg) (D.ρ hgg⁻¹) hgu hgu').conj
          (D.ρ (globalFrob hq.toHeightOneSpectrumRingOfIntegersRat)) := by
      ext w
      simp [map_mul, LinearEquiv.conj_apply, Module.End.mul_apply]
    show ((D.ρ (hgg * globalFrob
      hq.toHeightOneSpectrumRingOfIntegersRat * hgg⁻¹)).charpoly).coeff 1 ∈ C
    rw [heq, LinearEquiv.charpoly_conj, hC]
    refine Subring.le_topologicalClosure _ (Subring.subset_closure ?_)
    refine Or.inr ⟨q, hq, hq2, hqℓ, 1, ?_⟩
    rw [GaloisRep.charFrob_eq_charpoly_globalFrob]
  -- Chebotarev density: every trace lies in `C`
  intro g
  have hdense := dense_conjClasses_globalFrob (K := ℚ)
    ({Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat,
      (Fact.out : ℓ.Prime).toHeightOneSpectrumRingOfIntegersRat} :
      Finset (IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers ℚ)))
  have huniv : (Set.univ : Set (Field.absoluteGaloisGroup ℚ)) ⊆ _ :=
    hdense.closure_eq ▸ hDclosed.closure_subset_iff.mpr hsub
  exact huniv (Set.mem_univ g)

/-- **Carayol trace-descent stratum** (DECOMPOSED 2026-07-23 into the
Carayol subring-descent leaf `exists_isTraceGenerated_ringHom` above —
which produces the descended trace-generated datum `D'` *together with*
a compatible ring homomorphism `ι : D'.R → D.R` (the subring
inclusion), and does not mention weak universality at all — plus the
PROVEN composition glue below): a weakly universal hardly ramified
deformation can be replaced by one that is *also* trace-generated.

The glue: `D'` is weakly universal because any deformation `D''`
receives `f : D.R → D''.R` from weak universality of `D`, and
`f ∘ ι` is compatible since every piece of compatibility data — the
`ℤ_ℓ`-structure map, the reduction map, the `charFrob` coefficients —
composes.

References: Carayol, *Formes modulaires et représentations galoisiennes
à valeurs dans un anneau local complet* (Théorème 1 and Lemme 1);
Mazur, *Deforming Galois representations*, §1.8. -/
theorem exists_isWeaklyUniversal_isTraceGenerated_of_isWeaklyUniversal
    (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible)
    (D : HardlyRamifiedDeformation hℓOdd ρbar) (hw : D.IsWeaklyUniversal) :
    ∃ D' : HardlyRamifiedDeformation hℓOdd ρbar,
      D'.IsWeaklyUniversal ∧ D'.IsTraceGenerated := by
  letI := D.commRing; letI := D.topologicalSpace; letI := D.isTopologicalRing
  letI := D.isLocalRing; letI := D.algebra
  obtain ⟨D', hdesc⟩ :=
    exists_isTraceGenerated_ringHom hℓOdd hdim hℓ5 h hirr D
  obtain ⟨ht', ι, hι1, hι2, hι3⟩ := (hdesc : _ ∧ _)
  refine ⟨D', ?_, ht'⟩
  letI := D'.commRing; letI := D'.topologicalSpace
  letI := D'.isTopologicalRing; letI := D'.isLocalRing; letI := D'.algebra
  intro D''
  letI := D''.commRing; letI := D''.topologicalSpace
  letI := D''.isTopologicalRing; letI := D''.isLocalRing; letI := D''.algebra
  obtain ⟨f, hf1, hf2, hf3⟩ := hw D''
  refine ⟨f.comp ι, ?_, ?_, ?_⟩
  · rw [RingHom.comp_assoc, hι1, hf1]
  · rw [← RingHom.comp_assoc, hf2, hι2]
  · intro q hq hq2 hqℓ
    rw [← Polynomial.map_map, hι3 q hq hq2 hqℓ, hf3 q hq hq2 hqℓ]

/-- **Representability leaf** (DECOMPOSED 2026-07-23 into the Mazur
representability leaf `exists_isWeaklyUniversal` — the existence of
compatible maps — and the Carayol trace-descent leaf
`exists_isWeaklyUniversal_isTraceGenerated_of_isWeaklyUniversal` — the
replacement of a weakly universal datum by a trace-generated one; the
assembly below is proven): the hardly ramified deformation problem of an
irreducible hardly ramified `ρbar` (`ℓ ≥ 5`) admits a weakly universal,
trace-generated object. The uniqueness half of universality is NOT part
of this node: it is derived formally in
`isUniversal_of_isWeaklyUniversal_isTraceGenerated`. -/
theorem exists_isWeaklyUniversal_isTraceGenerated (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible) :
    ∃ D : HardlyRamifiedDeformation hℓOdd ρbar,
      D.IsWeaklyUniversal ∧ D.IsTraceGenerated := by
  obtain ⟨D, hw⟩ := exists_isWeaklyUniversal hℓOdd hdim hℓ5 h hirr
  exact exists_isWeaklyUniversal_isTraceGenerated_of_isWeaklyUniversal hℓOdd
    hdim hℓ5 h hirr D hw

/-- **Representability stratum** (DECOMPOSED 2026-07-22 into the
arithmetic leaf `exists_isWeaklyUniversal_isTraceGenerated` — Mazur
representability producing the maps, Carayol trace generation — plus the
PROVEN formal uniqueness argument
`isUniversal_of_isWeaklyUniversal_isTraceGenerated`): the hardly
ramified deformation problem of an irreducible hardly ramified `ρbar`
(`ℓ ≥ 5`) admits a universal object.

The assembly below is proven: the leaf produces a weakly universal,
trace-generated deformation, and the formal Carayol argument upgrades it
to a universal one. -/
theorem exists_universal_hardlyRamifiedDeformation (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible) :
    ∃ D : HardlyRamifiedDeformation hℓOdd ρbar, D.IsUniversal := by
  obtain ⟨D, hw, ht⟩ :=
    exists_isWeaklyUniversal_isTraceGenerated hℓOdd hdim hℓ5 h hirr
  exact ⟨D, isUniversal_of_isWeaklyUniversal_isTraceGenerated hℓOdd D hw ht⟩

/-- **`𝔪`-primarity from a one-point fibre** (PROVEN 2026-07-25, pure
commutative algebra — no arithmetic content): in a Noetherian local
ring, if the maximal ideal is the ONLY prime containing `x`, then some
power of the maximal ideal is contained in `(x)`.

Proof: `radical (x) = ⋂ {p prime, p ∋ x}` (`Ideal.radical_eq_sInf`), and
by hypothesis every such `p` equals `𝔪`, so `𝔪 ≤ radical (x)`; the
radical of an ideal of a Noetherian ring is finitely generated, hence
`radical (x) ^ n ≤ (x)` for some `n` (`Ideal.exists_radical_pow_le_of_fg`),
and `𝔪 ^ n ≤ radical (x) ^ n` by monotonicity of powers.

This is the Noetherian dévissage from the geometric form of "`R ⧸ (x)`
is Artinian" — `Spec (R ⧸ (x))` is the single closed point — to the
ideal-theoretic form. Note that it needs no hypothesis relating `x` to
`𝔪`: if `x` is a unit, `(x) = ⊤` and the conclusion is trivial. -/
theorem exists_maximalIdeal_pow_le_span_of_forall_isPrime {R : Type*}
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (x : R)
    (hx : ∀ p : Ideal R, p.IsPrime → x ∈ p → p = IsLocalRing.maximalIdeal R) :
    ∃ n : ℕ, IsLocalRing.maximalIdeal R ^ n ≤ Ideal.span {x} := by
  obtain ⟨n, hn⟩ :=
    (Ideal.span {x}).exists_radical_pow_le_of_fg (IsNoetherian.noetherian _)
  refine ⟨n, le_trans (pow_le_pow_left' ?_ n) hn⟩
  rw [Ideal.radical_eq_sInf]
  refine le_sInf ?_
  rintro J ⟨hJ1, hJ2⟩
  exact (hx J hJ2 (hJ1 (Ideal.mem_span_singleton_self x))).ge

/-- **Mod-`ℓ` fibre leaf** (sorry node — the arithmetic core of the
finiteness stratum; NARROWED 2026-07-25 from the `𝔪`-primarity form
`∃ n, 𝔪 ^ n ≤ (ℓ)` to this pointwise statement about `Spec`, the
dévissage between the two being the pure commutative algebra
`exists_maximalIdeal_pow_le_span_of_forall_isPrime` just above): in the
weakly universal, trace-generated hardly ramified deformation ring —
i.e. the genuine universal ring, as constructed by
`exists_isWeaklyUniversal_isTraceGenerated` — the maximal ideal is the
ONLY prime of `D.R` containing `ℓ`. Geometrically: the mod-`ℓ` fibre of
`Spec D.R` is a single point.

Equivalently (the ring being Noetherian local with finite residue
field): `(ℓ)` is `𝔪`-primary, `D.R ⧸ (ℓ)` is Artinian, `D.R ⧸ (ℓ)` is
finite — the three forms the statement has had, related by
`exists_maximalIdeal_pow_le_span_of_forall_isPrime` and
`finite_quotient_of_maximalIdeal_pow_le` below. This is verbatim the
literature's "`R/λ` is Artinian", i.e. `dim R ≤ 1` with `ℓ` a system of
parameters, which is what the Taylor–Wiles–Kisin patching argument
produces.

WHY THE POINTWISE FORM: it is the one the repository's *specialization*
machinery consumes. For a prime `p ∋ ℓ` the quotient `D.R ⧸ p` is a
characteristic-`ℓ` local domain over which the deformation remains
hardly ramified — `isFlatAt_baseChange_quotient`, `isTameAtTwo_baseChange`
and `isHardlyRamified_baseChange_quotient` below are stated for exactly
these PRIME quotients — so a proof may work one point of the mod-`ℓ`
fibre at a time (show `D.R ⧸ p` is a field), instead of handling the
whole mod-`ℓ` fibre at once. The dual bound is already available: the
presentation stratum gives a prime strictly below `𝔪`
(`exists_isPrime_lt_maximalIdeal_of_isWeaklyUniversal_isTraceGenerated`,
`dim D.R ≥ 1`), so this leaf is exactly the matching upper bound
`dim D.R ≤ 1` in the fibre-wise form.

This is the potential-modularity / Taylor–Wiles–Kisin input of
Khare–Wintenberger — the single genuinely deep arithmetic node of the
lifting core. The residual-modularity hypothesis is bypassed via
potential modularity (Taylor's Moret-Bailly argument), which after a
solvable base change `F/ℚ` (totally real, in which the deformation
problem's conditions remain balanced) proves an `R = T` theorem by the
Taylor–Wiles–Kisin patching method; `T` is a finite `ℤ_ℓ`-algebra, so
`T/ℓT` — and with it the mod-`ℓ` fibre of the `ℚ`-level ring, by
Khare–Wintenberger's descent — is finite. The mod-`ℓ` form is chosen
over `Module.Finite ℤ_[ℓ] D.R` because it is what the patching
literature produces directly (cf. the Böckle presentation stratum); the
lift back to `ℤ_ℓ`-module finiteness is the pure commutative-algebra
completeness bootstrap `moduleFinite_of_finite_quotient_span` below.
The hypotheses characterize `D` up to canonical isomorphism (weak
universality + trace generation = universality, by
`isUniversal_of_isWeaklyUniversal_isTraceGenerated` and the rigidity
theorem `exists_ringEquiv_of_isUniversal`), so a future proof may
construct its own universal datum, prove ITS mod-`ℓ` fibre a point, and
transport the result along the canonical isomorphism.

WHERE THE PROOF WILL HAVE TO COME FROM (audit, 2026-07-25).
`Fermat/FLT/Modularity/Patching.lean` proves both halves of `R = T` for
its own deformation vocabulary — `surjective_ringHom_of_charFrob_eq`
and `injective_ringHom_of_isWeaklyUniversal`, the latter through the
patched-module engine — but it carries `Module.Finite ℤ_[ℓ] T` as a
HYPOTHESIS on the Hecke side and produces no finiteness of any
deformation ring, so even the Hecke-algebra input is not yet available
in the repository. Nor are its declarations reachable from here:
`Patching.lean` imports `Modularity/KhareWintenberger.lean`, which
imports THIS module, so consuming it would close the dependency cycle
this module's circularity guard exists to prevent. Discharging this
leaf therefore needs either (i) the KW-free module split recorded in
`~/.flt-design-deformation-patching-dedup.md` plus genuine finiteness of
`T`, or (ii) the Hilbert-modular potential-modularity route. CIRCULARITY
GUARD: the odd-prime dichotomy
`not_isIrreducible_of_isHardlyRamified_of_five_le` must NOT be used to
discharge this vacuously — it is itself proven over pillar α, which
this cluster proves.

References: Khare–Wintenberger, *Serre's modularity conjecture (I)*,
Thm. 4.1 and §4, and *(II)*; Taylor, *Remarks on a conjecture of
Fontaine and Mazur* and *On the meromorphic continuation of degree two
L-functions*; Kisin, *Moduli of finite flat group schemes, and
modularity*; Buzzard's 2026 EPSRC course, Lecture 4. -/
theorem eq_maximalIdeal_of_isPrime_of_isWeaklyUniversal_isTraceGenerated
    (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible)
    (D : HardlyRamifiedDeformation hℓOdd ρbar)
    (hw : D.IsWeaklyUniversal) (ht : D.IsTraceGenerated) :
    letI := D.commRing; letI := D.isLocalRing
    ∀ p : Ideal D.R, p.IsPrime → (ℓ : D.R) ∈ p →
      p = IsLocalRing.maximalIdeal D.R :=
  sorry

/-- **Mod-`ℓ` `𝔪`-primarity stratum** (PROVEN 2026-07-25 over the
mod-`ℓ` fibre leaf
`eq_maximalIdeal_of_isPrime_of_isWeaklyUniversal_isTraceGenerated` and
the pure commutative algebra
`exists_maximalIdeal_pow_le_span_of_forall_isPrime`): in the weakly
universal, trace-generated hardly ramified deformation ring the ideal
`(ℓ)` is `𝔪`-PRIMARY — some power of the maximal ideal is contained in
`(ℓ)`. This is the ideal-theoretic face of "`R/λ` is Artinian"; the
finiteness face is
`finite_quotient_span_of_isWeaklyUniversal_isTraceGenerated` below. -/
theorem exists_maximalIdeal_pow_le_span_of_isWeaklyUniversal_isTraceGenerated
    (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible)
    (D : HardlyRamifiedDeformation hℓOdd ρbar)
    (hw : D.IsWeaklyUniversal) (ht : D.IsTraceGenerated) :
    letI := D.commRing; letI := D.isLocalRing
    ∃ n : ℕ, IsLocalRing.maximalIdeal D.R ^ n ≤ Ideal.span {(ℓ : D.R)} := by
  letI := D.commRing; letI := D.isLocalRing
  haveI := D.isNoetherianRing
  exact exists_maximalIdeal_pow_le_span_of_forall_isPrime (ℓ : D.R)
    (eq_maximalIdeal_of_isPrime_of_isWeaklyUniversal_isTraceGenerated hℓOdd
      hdim hℓ5 h hirr D hw ht)

omit [TopologicalSpace k] [DiscreteTopology k] [Algebra ℤ_[ℓ] k] in
/-- **Finiteness from `𝔪`-primarity** (PROVEN 2026-07-25, pure
commutative algebra — no arithmetic content): a Noetherian local ring
`R` with FINITE residue field `k` (it maps onto `k`) has finite
quotient by any ideal `I` containing a power of the maximal ideal.

Proof: `ker π` is the maximal ideal (`π` surjective onto a field), so
`R ⧸ 𝔪 ≃ k` is finite; `𝔪` is finitely generated (Noetherian), so
`R ⧸ 𝔪 ^ n` is finite for every `n` (`Ideal.finite_quotient_pow`,
the successive-quotients dévissage); and `R ⧸ I` is a quotient of
`R ⧸ 𝔪 ^ n` once `𝔪 ^ n ≤ I` (`Ideal.Quotient.factor`).

This is the "Artinian ⇒ finite over a finite residue field" step of
the finiteness stratum: for a Noetherian local ring, `∃ n, 𝔪 ^ n ≤ I`
says exactly that `R ⧸ I` has Krull dimension `0`, i.e. is Artinian
(`isArtinianRing_iff_isNoetherianRing_krullDimLE_zero`). -/
theorem finite_quotient_of_maximalIdeal_pow_le {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] {I : Ideal R}
    (π : R →+* k) (hπsurj : Function.Surjective π)
    (hn : ∃ n : ℕ, IsLocalRing.maximalIdeal R ^ n ≤ I) :
    Finite (R ⧸ I) := by
  obtain ⟨n, hnle⟩ := hn
  have hker : RingHom.ker π = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective π hπsurj)
  haveI : Finite (R ⧸ IsLocalRing.maximalIdeal R) := by
    rw [← hker]
    exact Finite.of_equiv k
      (RingHom.quotientKerEquivOfSurjective hπsurj).symm.toEquiv
  haveI : Finite (R ⧸ IsLocalRing.maximalIdeal R ^ n) :=
    Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n
  exact Finite.of_surjective (Ideal.Quotient.factor hnle)
    (Ideal.Quotient.factor_surjective hnle)

/-- **Mod-`ℓ` finiteness stratum** (PROVEN 2026-07-25 over the
`𝔪`-primarity stratum
`exists_maximalIdeal_pow_le_span_of_isWeaklyUniversal_isTraceGenerated`
— itself proven over the mod-`ℓ` fibre leaf
`eq_maximalIdeal_of_isPrime_of_isWeaklyUniversal_isTraceGenerated` —
and the pure commutative algebra `finite_quotient_of_maximalIdeal_pow_le`):
the weakly universal, trace-generated hardly ramified deformation ring
is finite modulo `ℓ`. The deformation ring is Noetherian local with
finite residue field `k` (structure fields `isNoetherianRing`,
`isLocalRing`, `π_surjective`), so mod-`ℓ` finiteness is *equivalent*
to the `𝔪`-primarity of `(ℓ)` isolated in the leaf. -/
theorem finite_quotient_span_of_isWeaklyUniversal_isTraceGenerated
    (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible)
    (D : HardlyRamifiedDeformation hℓOdd ρbar)
    (hw : D.IsWeaklyUniversal) (ht : D.IsTraceGenerated) :
    letI := D.commRing
    Finite (D.R ⧸ Ideal.span {(ℓ : D.R)}) := by
  letI := D.commRing; letI := D.isLocalRing
  haveI := D.isNoetherianRing
  exact finite_quotient_of_maximalIdeal_pow_le D.π D.π_surjective
    (exists_maximalIdeal_pow_le_span_of_isWeaklyUniversal_isTraceGenerated
      hℓOdd hdim hℓ5 h hirr D hw ht)

omit [TopologicalSpace k] [DiscreteTopology k] in
/-- **Completeness bootstrap** (PROVEN 2026-07-23, pure commutative
algebra — no arithmetic content): a Noetherian local `ℤ_ℓ`-algebra `R`,
separated for its maximal-adic topology, with residue field `k` (it
maps ONTO the finite field `k`, of characteristic `ℓ` by
`natCast_self_eq_zero`) and finite modulo `ℓ`, is finite as a
`ℤ_ℓ`-module.

Proof (standard: Mazur, *Deforming Galois representations*, §1.1;
Matsumura, Thm. 8.4): `ℓ` lies in the maximal ideal (it dies under the
reduction map, whose kernel is the maximal ideal of the local ring, `π`
being surjective onto `k`), so `ℓ^t R ⊆ 𝔪^t`.
Choose representatives `x₁, …, x_s ∈ R` of the finitely many classes of
`R/(ℓ)`; every `r ∈ R` unwinds as `r = Σ_j ℓ^j a_j` with each `a_j`
among the `xᵢ`, the coordinatewise partial sums of the resulting
`ℤ_ℓ`-coefficients converge in the complete `ℤ_ℓ` (`IsPrecomplete`,
purely algebraically), and adic separatedness identifies `r` with the
limit combination — so the `xᵢ` generate `R` as a `ℤ_ℓ`-module.

(The `IsNoetherianRing` hypothesis is DELIBERATELY retained although
this proof does not consume it: it keeps the statement aligned with the
literature form of the bootstrap, and its sole use site — the
finiteness-stratum assembly `moduleFinite_of_isWeaklyUniversal_...`
below — discharges it with the `isNoetherianRing` field of
`HardlyRamifiedDeformation`, which keeps that structure field inside
the root theorem's dependency cone. Do not remove it.) -/
theorem moduleFinite_of_finite_quotient_span {R : Type*} [CommRing R]
    [IsLocalRing R] [Algebra ℤ_[ℓ] R] [IsNoetherianRing R]
    [IsHausdorff (IsLocalRing.maximalIdeal R) R]
    (π : R →+* k) (hπsurj : Function.Surjective π)
    (hfin : Finite (R ⧸ Ideal.span {(ℓ : R)})) :
    Module.Finite ℤ_[ℓ] R := by
  classical
  -- `ℓ` lies in the maximal ideal: it dies under the reduction map (the
  -- target `k` has characteristic `ℓ`), whose kernel is the maximal ideal
  have hker : RingHom.ker π = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective π hπsurj)
  have hℓm : (ℓ : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [← hker, RingHom.mem_ker, map_natCast]
    exact natCast_self_eq_zero
  haveI := hfin
  haveI : Fintype (R ⧸ Ideal.span {(ℓ : R)}) := Fintype.ofFinite _
  -- a set-theoretic section of the reduction onto the finite quotient
  let s : (R ⧸ Ideal.span {(ℓ : R)}) → R :=
    Function.surjInv Ideal.Quotient.mk_surjective
  have hs : ∀ q, Ideal.Quotient.mk (Ideal.span {(ℓ : R)}) (s q) = q :=
    fun q => Function.surjInv_eq Ideal.Quotient.mk_surjective q
  -- division step: subtracting the representative of the class leaves a
  -- multiple of `ℓ`
  have hstep : ∀ x : R, ∃ c : R,
      x - s (Ideal.Quotient.mk (Ideal.span {(ℓ : R)}) x) = (ℓ : R) * c := by
    intro x
    have hx : x - s (Ideal.Quotient.mk (Ideal.span {(ℓ : R)}) x) ∈
        Ideal.span {(ℓ : R)} := by
      rw [← Ideal.Quotient.eq]
      exact (hs _).symm
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hx
    exact ⟨c, by rw [← hc, mul_comm]⟩
  choose step hstepEq using hstep
  -- the `ℤ_ℓ`-span of the representatives is everything: unwind an
  -- arbitrary element into `ℓ`-adic digits, converge the coefficients in
  -- the complete `ℤ_ℓ`, and identify by adic separatedness
  have hspan : Submodule.span ℤ_[ℓ] (Set.range s) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro r
    -- remainders of the iterated division
    let rem : ℕ → R := fun t =>
      Nat.rec (motive := fun _ => R) r (fun _ prev => step prev) t
    have hremS : ∀ t, rem (t + 1) = step (rem t) := fun _ => rfl
    -- partial coefficient sums, one per representative
    set c : ℕ → (R ⧸ Ideal.span {(ℓ : R)}) → ℤ_[ℓ] := fun t q =>
      ∑ j ∈ Finset.range t,
        if Ideal.Quotient.mk (Ideal.span {(ℓ : R)}) (rem j) = q
        then (ℓ : ℤ_[ℓ]) ^ j else 0 with hcdef
    -- the partial sums are Cauchy for the `ℓ`-adic filtration of `ℤ_ℓ`
    have hcauchy : ∀ q, ∀ {a b : ℕ}, a ≤ b →
        c a q ≡ c b q [SMOD
          (IsLocalRing.maximalIdeal ℤ_[ℓ] ^ a • ⊤ :
            Submodule ℤ_[ℓ] ℤ_[ℓ])] := by
      intro q a b hab
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      have hsplit : c b q - c a q = ∑ j ∈ Finset.Ico a b,
          (if Ideal.Quotient.mk (Ideal.span {(ℓ : R)}) (rem j) = q
           then (ℓ : ℤ_[ℓ]) ^ j else 0) := by
        simp only [hcdef]
        rw [← Finset.sum_range_add_sum_Ico _ hab]
        ring
      have hmem : ∑ j ∈ Finset.Ico a b,
          (if Ideal.Quotient.mk (Ideal.span {(ℓ : R)}) (rem j) = q
           then (ℓ : ℤ_[ℓ]) ^ j else 0) ∈
          (IsLocalRing.maximalIdeal ℤ_[ℓ] ^ a : Ideal ℤ_[ℓ]) := by
        refine Submodule.sum_mem _ fun j hj => ?_
        rw [Finset.mem_Ico] at hj
        rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow]
        split_ifs
        · exact Ideal.mem_span_singleton.mpr (pow_dvd_pow _ hj.1)
        · exact Submodule.zero_mem _
      have hflip : c a q - c b q = -(c b q - c a q) := by ring
      rw [hflip, hsplit]
      exact neg_mem hmem
    -- converge the coefficients in the complete `ℤ_ℓ`
    have hex : ∀ q, ∃ Lq : ℤ_[ℓ], ∀ t, c t q ≡ Lq [SMOD
        (IsLocalRing.maximalIdeal ℤ_[ℓ] ^ t • ⊤ :
          Submodule ℤ_[ℓ] ℤ_[ℓ])] :=
      fun q => IsPrecomplete.prec inferInstance
        (fun {a b} hab => hcauchy q hab)
    choose L hL using hex
    -- the finite-stage identity: `r` is the digit combination plus an
    -- `ℓ^t`-divisible remainder
    have hA : ∀ t, r = (∑ j ∈ Finset.range t, (ℓ : R) ^ j *
        s (Ideal.Quotient.mk (Ideal.span {(ℓ : R)}) (rem j))) +
        (ℓ : R) ^ t * rem t := by
      intro t
      induction t with
      | zero =>
        rw [Finset.sum_range_zero, pow_zero, one_mul, zero_add]
        rfl
      | succ t ih =>
        have hdiv : rem t =
            s (Ideal.Quotient.mk (Ideal.span {(ℓ : R)}) (rem t)) +
              (ℓ : R) * rem (t + 1) := by
          have h1 := hstepEq (rem t)
          rw [← hremS t] at h1
          rw [← h1]
          ring
        calc r = (∑ j ∈ Finset.range t, (ℓ : R) ^ j *
              s (Ideal.Quotient.mk (Ideal.span {(ℓ : R)}) (rem j))) +
              (ℓ : R) ^ t * rem t := ih
          _ = (∑ j ∈ Finset.range (t + 1), (ℓ : R) ^ j *
              s (Ideal.Quotient.mk (Ideal.span {(ℓ : R)}) (rem j))) +
              (ℓ : R) ^ (t + 1) * rem (t + 1) := by
            conv_lhs => rw [hdiv]
            rw [Finset.sum_range_succ]
            ring
    -- regroup the digit combination by representative
    have hB : ∀ t, (∑ j ∈ Finset.range t, (ℓ : R) ^ j *
        s (Ideal.Quotient.mk (Ideal.span {(ℓ : R)}) (rem j))) =
        ∑ q, algebraMap ℤ_[ℓ] R (c t q) * s q := by
      intro t
      have hterm : ∀ q, algebraMap ℤ_[ℓ] R (c t q) * s q =
          ∑ j ∈ Finset.range t,
            (if Ideal.Quotient.mk (Ideal.span {(ℓ : R)}) (rem j) = q
             then (ℓ : R) ^ j * s q else 0) := by
        intro q
        simp only [hcdef]
        rw [map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs
        · rw [map_pow, map_natCast]
        · rw [map_zero, zero_mul]
      refine Eq.symm ?_
      calc ∑ q, algebraMap ℤ_[ℓ] R (c t q) * s q
          = ∑ q, ∑ j ∈ Finset.range t,
              (if Ideal.Quotient.mk (Ideal.span {(ℓ : R)}) (rem j) = q
               then (ℓ : R) ^ j * s q else 0) :=
            Finset.sum_congr rfl fun q _ => hterm q
        _ = ∑ j ∈ Finset.range t, ∑ q,
              (if Ideal.Quotient.mk (Ideal.span {(ℓ : R)}) (rem j) = q
               then (ℓ : R) ^ j * s q else 0) :=
            Finset.sum_comm
        _ = ∑ j ∈ Finset.range t, (ℓ : R) ^ j *
              s (Ideal.Quotient.mk (Ideal.span {(ℓ : R)}) (rem j)) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.sum_ite_eq]
            simp
    -- the limit combination differs from `r` by an element of every power
    -- of the maximal ideal …
    have hsmul : ∑ q, L q • s q = ∑ q, algebraMap ℤ_[ℓ] R (L q) * s q :=
      Finset.sum_congr rfl fun q _ => Algebra.smul_def _ _
    have hmemt : ∀ t : ℕ, r - ∑ q, L q • s q ∈
        (IsLocalRing.maximalIdeal R ^ t : Ideal R) := by
      intro t
      have hsub : r - ∑ q, L q • s q =
          (ℓ : R) ^ t * rem t +
          ∑ q, algebraMap ℤ_[ℓ] R (c t q - L q) * s q := by
        calc r - ∑ q, L q • s q
            = ((∑ q, algebraMap ℤ_[ℓ] R (c t q) * s q) +
                (ℓ : R) ^ t * rem t) -
                ∑ q, algebraMap ℤ_[ℓ] R (L q) * s q := by
              rw [← hB t, ← hA t, hsmul]
          _ = (ℓ : R) ^ t * rem t +
              ∑ q, (algebraMap ℤ_[ℓ] R (c t q) * s q -
                algebraMap ℤ_[ℓ] R (L q) * s q) := by
              rw [Finset.sum_sub_distrib]
              ring
          _ = (ℓ : R) ^ t * rem t +
              ∑ q, algebraMap ℤ_[ℓ] R (c t q - L q) * s q := by
              refine congrArg (fun z => (ℓ : R) ^ t * rem t + z) ?_
              exact Finset.sum_congr rfl fun q _ => by
                rw [map_sub, sub_mul]
      rw [hsub]
      refine Submodule.add_mem _ ?_ ?_
      · exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hℓm t)
      · refine Submodule.sum_mem _ fun q _ => ?_
        have hLqt := hL q t
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top,
          PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow,
          Ideal.mem_span_singleton] at hLqt
        obtain ⟨d, hd⟩ := hLqt
        rw [hd, map_mul, map_pow, map_natCast, mul_assoc]
        exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hℓm t)
    -- … hence vanishes by adic separatedness
    have hzero : r - ∑ q, L q • s q = 0 := by
      refine IsHausdorff.haus (inferInstance :
        IsHausdorff (IsLocalRing.maximalIdeal R) R) _ fun t => ?_
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
      exact hmemt t
    rw [sub_eq_zero.mp hzero]
    exact Submodule.sum_mem _ fun q _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)
  -- conclude module finiteness from the finite generating set
  exact Module.finite_def.mpr
    ⟨(Set.finite_range s).toFinset, by
      rw [Set.Finite.coe_toFinset]; exact hspan⟩

/-- **Finiteness stratum** (DECOMPOSED 2026-07-23 into the mod-`ℓ`
finiteness stratum `finite_quotient_span_of_isWeaklyUniversal_isTraceGenerated`
— the potential-modularity / Taylor–Wiles–Kisin content, producing
finiteness of `D.R ⧸ (ℓ)` — plus the pure commutative-algebra
completeness bootstrap `moduleFinite_of_finite_quotient_span`; the
assembly below is proven): the weakly universal, trace-generated hardly
ramified deformation ring is finite as a `ℤ_ℓ`-module. -/
theorem moduleFinite_of_isWeaklyUniversal_isTraceGenerated (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible)
    (D : HardlyRamifiedDeformation hℓOdd ρbar)
    (hw : D.IsWeaklyUniversal) (ht : D.IsTraceGenerated) :
    letI := D.commRing; letI := D.algebra
    Module.Finite ℤ_[ℓ] D.R := by
  letI := D.commRing; letI := D.isLocalRing; letI := D.algebra
  haveI := D.isNoetherianRing
  haveI : IsHausdorff (IsLocalRing.maximalIdeal D.R) D.R :=
    (D.isAdicComplete).toIsHausdorff
  have hfin : Finite (D.R ⧸ Ideal.span {(ℓ : D.R)}) :=
    finite_quotient_span_of_isWeaklyUniversal_isTraceGenerated hℓOdd hdim
      hℓ5 h hirr D hw ht
  exact moduleFinite_of_finite_quotient_span D.π D.π_surjective hfin

/-- **Finiteness stratum** (DECOMPOSED 2026-07-22 into the arithmetic
leaf `moduleFinite_of_isWeaklyUniversal_isTraceGenerated` — potential
modularity / Taylor–Wiles–Kisin — plus PROVEN formal transport): the
universal hardly ramified deformation ring is finite as a `ℤ_ℓ`-module.
The assembly below is proven: any universal `D` is canonically
isomorphic, as a `ℤ_ℓ`-algebra, to the trace-generated weakly universal
datum produced by the representability leaf
(`exists_ringEquiv_of_isUniversal`), whose finiteness is the leaf; the
isomorphism upgrades to a `ℤ_ℓ`-linear equivalence and finiteness
transfers along it. -/
theorem moduleFinite_of_isUniversal (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible)
    (D : HardlyRamifiedDeformation hℓOdd ρbar) (hD : D.IsUniversal) :
    letI := D.commRing; letI := D.algebra
    Module.Finite ℤ_[ℓ] D.R := by
  letI := D.commRing; letI := D.algebra
  obtain ⟨D₀, hw₀, ht₀⟩ :=
    exists_isWeaklyUniversal_isTraceGenerated hℓOdd hdim hℓ5 h hirr
  letI := D₀.commRing; letI := D₀.algebra
  have hD₀ : D₀.IsUniversal :=
    isUniversal_of_isWeaklyUniversal_isTraceGenerated hℓOdd D₀ hw₀ ht₀
  obtain ⟨e, he⟩ := exists_ringEquiv_of_isUniversal hℓOdd D₀ D hD₀ hD
  have hfin₀ : Module.Finite ℤ_[ℓ] D₀.R :=
    moduleFinite_of_isWeaklyUniversal_isTraceGenerated hℓOdd hdim hℓ5 h hirr
      D₀ hw₀ ht₀
  letI := hfin₀
  let elin : D₀.R ≃ₗ[ℤ_[ℓ]] D.R :=
    { e.toAddEquiv with
      map_smul' := fun c x => by
        show e (c • x) = c • e x
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, he c] }
  exact Module.Finite.equiv elin

/-- Auxiliary for the variable-splitting isomorphism: `Finsupp.tail` is
additive. -/
lemma finsupp_tail_add {n : ℕ} (p q : Fin (n + 1) →₀ ℕ) :
    Finsupp.tail (p + q) = Finsupp.tail p + Finsupp.tail q :=
  Finsupp.ext fun i => by simp [Finsupp.tail_apply]

/-- Auxiliary for the variable-splitting isomorphism: `Finsupp.cons` is
additive. -/
lemma finsupp_cons_add_cons {n : ℕ} (a b : ℕ) (s t : Fin n →₀ ℕ) :
    Finsupp.cons a s + Finsupp.cons b t = Finsupp.cons (a + b) (s + t) :=
  Finsupp.ext fun i => by
    induction i using Fin.cases with
    | zero => simp
    | succ j => simp

/-- Auxiliary for the variable-splitting isomorphism: a sum over the
antidiagonal of `Finsupp.cons k m` is an iterated sum over the
antidiagonals of `k` and of `m` — the monomial-splitting rearrangement
underlying the Cauchy-product compatibility. -/
lemma sum_antidiagonal_cons {S : Type*} [AddCommMonoid S] {n : ℕ} (k : ℕ)
    (m : Fin n →₀ ℕ)
    (F : (Fin (n + 1) →₀ ℕ) × (Fin (n + 1) →₀ ℕ) → S) :
    ∑ p ∈ Finset.antidiagonal (Finsupp.cons k m), F p =
      ∑ ij ∈ Finset.antidiagonal k, ∑ ab ∈ Finset.antidiagonal m,
        F (Finsupp.cons ij.1 ab.1, Finsupp.cons ij.2 ab.2) := by
  calc ∑ p ∈ Finset.antidiagonal (Finsupp.cons k m), F p
      = ∑ x ∈ Finset.antidiagonal k ×ˢ Finset.antidiagonal m,
          F (Finsupp.cons x.1.1 x.2.1, Finsupp.cons x.1.2 x.2.2) := ?_
    _ = ∑ ij ∈ Finset.antidiagonal k, ∑ ab ∈ Finset.antidiagonal m,
          F (Finsupp.cons ij.1 ab.1, Finsupp.cons ij.2 ab.2) :=
        Finset.sum_product' (Finset.antidiagonal k) (Finset.antidiagonal m)
          (fun ij ab => F (Finsupp.cons ij.1 ab.1, Finsupp.cons ij.2 ab.2))
  refine Finset.sum_nbij'
    (i := fun p => ((p.1 0, p.2 0), (Finsupp.tail p.1, Finsupp.tail p.2)))
    (j := fun x => (Finsupp.cons x.1.1 x.2.1, Finsupp.cons x.1.2 x.2.2))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨p, q⟩ hp
    rw [Finset.mem_antidiagonal] at hp
    rw [Finset.mem_product, Finset.mem_antidiagonal, Finset.mem_antidiagonal]
    refine ⟨?_, ?_⟩
    · have h0 := DFunLike.congr_fun hp 0
      simpa using h0
    · rw [← finsupp_tail_add, hp, Finsupp.tail_cons]
  · rintro ⟨⟨i, j⟩, a, b⟩ hx
    rw [Finset.mem_product, Finset.mem_antidiagonal,
      Finset.mem_antidiagonal] at hx
    rw [Finset.mem_antidiagonal]
    show Finsupp.cons i a + Finsupp.cons j b = Finsupp.cons k m
    rw [finsupp_cons_add_cons, hx.1, hx.2]
  · rintro ⟨p, q⟩ -
    simp
  · rintro ⟨⟨i, j⟩, a, b⟩ -
    simp
  · rintro ⟨p, q⟩ -
    simp

/-- Auxiliary for the variable-splitting isomorphism: the splitting map
itself, carrying `f ∈ R[[x₀,…,x_n]]` to the single-variable power series
in `x₀` whose `k`-th coefficient is the `n`-variable series of
`x₀`-degree-`k` coefficients of `f`. -/
noncomputable def mvPowerSeriesSplit {R : Type*} [CommRing R] (n : ℕ)
    (f : MvPowerSeries (Fin (n + 1)) R) :
    PowerSeries (MvPowerSeries (Fin n) R) :=
  PowerSeries.mk fun k =>
    (fun m => MvPowerSeries.coeff (Finsupp.cons k m) f :
      MvPowerSeries (Fin n) R)

/-- Auxiliary: coefficient formula for `mvPowerSeriesSplit`. -/
lemma coeff_coeff_mvPowerSeriesSplit {R : Type*} [CommRing R] (n : ℕ)
    (f : MvPowerSeries (Fin (n + 1)) R) (k : ℕ) (m : Fin n →₀ ℕ) :
    MvPowerSeries.coeff m (PowerSeries.coeff k (mvPowerSeriesSplit n f)) =
      MvPowerSeries.coeff (Finsupp.cons k m) f := by
  rw [mvPowerSeriesSplit, PowerSeries.coeff_mk]
  rfl

/-- Auxiliary for the variable-splitting isomorphism: the merging map,
inverse to `mvPowerSeriesSplit`. -/
noncomputable def mvPowerSeriesUnsplit {R : Type*} [CommRing R] (n : ℕ)
    (G : PowerSeries (MvPowerSeries (Fin n) R)) :
    MvPowerSeries (Fin (n + 1)) R :=
  (fun p => MvPowerSeries.coeff (Finsupp.tail p)
      (PowerSeries.coeff (p 0) G) :
    MvPowerSeries (Fin (n + 1)) R)

/-- Auxiliary: coefficient formula for `mvPowerSeriesUnsplit`. -/
lemma coeff_mvPowerSeriesUnsplit {R : Type*} [CommRing R] (n : ℕ)
    (G : PowerSeries (MvPowerSeries (Fin n) R)) (p : Fin (n + 1) →₀ ℕ) :
    MvPowerSeries.coeff p (mvPowerSeriesUnsplit n G) =
      MvPowerSeries.coeff (Finsupp.tail p) (PowerSeries.coeff (p 0) G) :=
  rfl

/-- **Variable-splitting isomorphism for power series** (PROVEN
2026-07-23, pure commutative algebra — the missing mathlib bridge
between multivariate power series in `n + 1` variables and
single-variable power series over multivariate power series in `n`
variables): separating one variable. Proven by reindexing coefficients
along `Finsupp.cons`/`Finsupp.tail` (split off the exponent of `x₀`),
multiplicativity being the Cauchy-product rearrangement of the
convolution over split monomials (`sum_antidiagonal_cons`). Stated over
an arbitrary commutative base ring: both consumers below induct with a
changing base. (MOVED 2026-07-25 above the presentation stratum: the
Böckle relation-bound assembly needs `isNoetherianRing_mvPowerSeries`,
and so does the sibling leaf `isNoetherianRing_of_mvPowerSeries_presentation`
of `Modularity/Patching.lean`, whose docstring asks for exactly this
move.) -/
theorem nonempty_ringEquiv_mvPowerSeries_powerSeries {R : Type*}
    [CommRing R] (n : ℕ) :
    Nonempty (MvPowerSeries (Fin (n + 1)) R ≃+*
      PowerSeries (MvPowerSeries (Fin n) R)) := by
  refine ⟨{
    toFun := mvPowerSeriesSplit n
    invFun := mvPowerSeriesUnsplit n
    left_inv := fun f => ?_
    right_inv := fun G => ?_
    map_mul' := fun f g => ?_
    map_add' := fun f g => ?_ }⟩
  · -- left inverse: recombine the split exponents
    refine MvPowerSeries.ext fun p => ?_
    rw [coeff_mvPowerSeriesUnsplit, coeff_coeff_mvPowerSeriesSplit,
      Finsupp.cons_tail]
  · -- right inverse: split the recombined exponents
    refine PowerSeries.ext fun k => ?_
    refine MvPowerSeries.ext fun m => ?_
    rw [coeff_coeff_mvPowerSeriesSplit, coeff_mvPowerSeriesUnsplit,
      Finsupp.tail_cons, Finsupp.cons_zero]
  · -- multiplicativity: the Cauchy product rearranges over split monomials
    classical
    refine PowerSeries.ext fun k => ?_
    refine MvPowerSeries.ext fun m => ?_
    rw [coeff_coeff_mvPowerSeriesSplit, MvPowerSeries.coeff_mul,
      PowerSeries.coeff_mul, map_sum]
    simp only [MvPowerSeries.coeff_mul, coeff_coeff_mvPowerSeriesSplit]
    exact sum_antidiagonal_cons k m fun p =>
      MvPowerSeries.coeff p.1 f * MvPowerSeries.coeff p.2 g
  · -- additivity: coefficientwise
    refine PowerSeries.ext fun k => ?_
    refine MvPowerSeries.ext fun m => ?_
    rw [coeff_coeff_mvPowerSeriesSplit, map_add, map_add, map_add,
      coeff_coeff_mvPowerSeriesSplit, coeff_coeff_mvPowerSeriesSplit]

/-- **Noetherianness of multivariate power series** (PROVEN 2026-07-23
modulo the variable-splitting leaf above — a mathlib gap: the
single-variable instance `IsNoetherianRing R⟦X⟧` exists in the pin, the
finitely-many-variables version does not): power series in finitely
many variables over a Noetherian commutative ring form a Noetherian
ring, by induction on the number of variables along the splitting
isomorphism, the single-variable step being mathlib's
Hilbert-basis-style instance and the base case the constants
isomorphism `MvPowerSeries (Fin 0) R ≅ R`. Stated over an arbitrary
Noetherian base (rather than `ℤ_ℓ`) because the induction changes the
base at every step. -/
theorem isNoetherianRing_mvPowerSeries {R : Type*} [CommRing R]
    [IsNoetherianRing R] (g : ℕ) :
    IsNoetherianRing (MvPowerSeries (Fin g) R) := by
  induction g with
  | zero =>
    exact isNoetherianRing_of_ringEquiv R (RingEquiv.ofBijective
      (MvPowerSeries.C : R →+* MvPowerSeries (Fin 0) R)
      ⟨MvPowerSeries.C_injective, MvPowerSeries.C_surjective⟩)
  | succ n ih =>
    obtain ⟨e⟩ := nonempty_ringEquiv_mvPowerSeries_powerSeries (R := R) n
    haveI := ih
    exact isNoetherianRing_of_ringEquiv _ e.symm

/-- **Minimal generating family of `𝔪` modulo an ideal** (PROVEN
2026-07-25 — pure commutative algebra; the Lean-friendly substitute for
"choose a BASIS of the finite-dimensional cotangent space"): in a
Noetherian local ring, for every ideal `J ≤ 𝔪` there is a family
`t : Fin g → 𝔪` with `𝔪 = (t) ⊔ J` whose length `g` is MINIMAL among all
such families.

Proven by well-ordering: Noetherianness makes `𝔪` finitely generated
(`Submodule.fg_iff_exists_fin_generating_family`), so some `n` admits
such a family — `𝔪 = 𝔪 ⊔ J` because `J ≤ 𝔪` — and `Nat.find` picks the
least one.

At `J = 𝔪² ⊔ (ℓ)` the conclusion is exactly the de Smit–Lenstra choice
of a basis of the mod-`ℓ` cotangent space `𝔪/(𝔪² + ℓ)`: minimality of
the CARDINALITY replaces linear independence, and is the form the
kernel bound `ker_le_of_minimal_mvPowerSeries_ringHom` consumes — a
relation with a unit coefficient would let one member of the family be
dropped, producing a shorter family and contradicting minimality. The
cardinality formulation avoids having to build the residue-field
vector-space structure on the cotangent quotient. -/
theorem exists_minimal_span_sup_of_isNoetherianRing {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (J : Ideal R)
    (hJ : J ≤ IsLocalRing.maximalIdeal R) :
    ∃ (g : ℕ) (t : Fin g → R), (∀ i, t i ∈ IsLocalRing.maximalIdeal R) ∧
      IsLocalRing.maximalIdeal R = Ideal.span (Set.range t) ⊔ J ∧
      ∀ (n : ℕ) (s : Fin n → R), (∀ i, s i ∈ IsLocalRing.maximalIdeal R) →
        IsLocalRing.maximalIdeal R = Ideal.span (Set.range s) ⊔ J → g ≤ n := by
  classical
  have hex : ∃ n : ℕ, ∃ s : Fin n → R,
      (∀ i, s i ∈ IsLocalRing.maximalIdeal R) ∧
      IsLocalRing.maximalIdeal R = Ideal.span (Set.range s) ⊔ J := by
    obtain ⟨n, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
      (IsNoetherian.noetherian (IsLocalRing.maximalIdeal R))
    refine ⟨n, s, fun i => ?_, ?_⟩
    · rw [← hs]; exact Ideal.subset_span ⟨i, rfl⟩
    · rw [show Ideal.span (Set.range s) = IsLocalRing.maximalIdeal R from hs]
      exact (sup_eq_left.mpr hJ).symm
  obtain ⟨t, ht, hspan⟩ := Nat.find_spec hex
  exact ⟨Nat.find hex, t, ht, hspan,
    fun n s hs hspans => Nat.find_le ⟨s, hs, hspans⟩⟩

/-- **Cohen coefficient-ring leaf** (sorry node — pure commutative
algebra, the first of the four strata into which the minimal
presentation of `exists_minimal_mvPowerSeries_presentation` was
DECOMPOSED 2026-07-25): a complete Noetherian local `ℤ_ℓ`-algebra `R`
with residue field `k` (it maps ONTO `k`) receives a compatible
COEFFICIENT RING `Λ` — an unramified complete local domain,
module-finite over `ℤ_ℓ`, with maximal ideal `(ℓ)`, mapping to `R` by a
`ℤ_ℓ`-algebra map `ι` that is onto the residue field.

Classically `Λ = W(k)`, the Witt vectors of the finite field `k` (just
`ℤ_ℓ` when `k = 𝔽_ℓ`). CAVEAT (2026-07-25): the clauses do NOT by
themselves pin `Λ ≅ W(k)` — a FINITE FIELD satisfies every one of them
(local Noetherian domain, module-finite over `ℤ_ℓ`, and
`𝔪_Λ = (ℓ) = ⊥` when `ℓ = 0` in `Λ`), so `dim Λ` is not pinned to `1`
by this clause set. Downstream that unit of dimension is load-bearing,
and it is now carried explicitly by the relation-count leaf
`exists_relations_lt_le_smul_of_minimal_mvPowerSeries_presentation`,
which concludes `(ℓ : Λ) ≠ 0`. A proof of the present leaf that
produces `Λ = W(k)` gives that for free; whoever proves it may find it
cleaner to ADD `(ℓ : Λ) ≠ 0` to the conclusion here and let the
arithmetic leaf drop it. Two
distinct pieces of content: (a) `W(k)` itself — mathlib has
`WittVector p k`, its `IsDiscreteValuationRing` instance and
`WittVector.equiv : 𝕎 (ZMod p) ≃+* ℤ_[p]`, so `Algebra ℤ_[ℓ] (𝕎 k)` is
assembled from `WittVector.map` applied to `ZMod ℓ →+* k`; what is NOT
in the pin is `Module.Finite ℤ_[ℓ] (𝕎 k)` (freeness of rank `[k : 𝔽_ℓ]`)
and `maximalIdeal (𝕎 k) = (ℓ)` (read off `WittVector.irreducible` in
the DVR); (b) the lift `ι : Λ →+* R`, which is the coefficient-ring
half of the COHEN STRUCTURE THEOREM: `W(k)/ℤ_ℓ` is formally étale, so
the residue map `R ↠ k` lifts uniquely through the `ℓ`-adically
complete `R` — concretely by Teichmüller representatives, using
`IsAdicComplete` to sum the lifting series.

References: de Smit–Lenstra, *Explicit construction of universal
deformation rings*, Prop. 2.3 (App. to Cornell–Silverman–Stevens);
Matsumura, *Commutative Ring Theory*, §29 (Cohen structure theorem);
Serre, *Local Fields*, II §5 (Witt vectors as the unramified complete
DVR with residue field `k`). -/
theorem exists_coefficientRing_ringHom {R : Type*} [CommRing R]
    [IsLocalRing R] [Algebra ℤ_[ℓ] R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (π : R →+* k) (hπsurj : Function.Surjective π) :
    ∃ (Λ : Type u) (_ : CommRing Λ) (_ : IsDomain Λ) (_ : IsLocalRing Λ)
      (_ : IsNoetherianRing Λ) (_ : Algebra ℤ_[ℓ] Λ)
      (_ : Module.Finite ℤ_[ℓ] Λ),
      IsLocalRing.maximalIdeal Λ = Ideal.span {(ℓ : Λ)} ∧
      ∃ ι : Λ →+* R,
        ι.comp (algebraMap ℤ_[ℓ] Λ) = algebraMap ℤ_[ℓ] R ∧
        Function.Surjective (π.comp ι) :=
  sorry

open Filter Topology in
/-- **Convergent-substitution stratum** (PROVEN 2026-07-25 — pure
commutative algebra, the second stratum of the same-day decomposition of
`exists_minimal_mvPowerSeries_presentation`): substituting
topologically nilpotent elements into a power series converges in a
complete local ring. Given a coefficient map `ι : Λ →+* R` into a local
ring that is `𝔪`-adically complete and separated, and elements
`t₁, …, t_g ∈ 𝔪_R`, there is a ring homomorphism
`φ : Λ[[x₁, …, x_g]] →+* R` with `φ ∘ C = ι` and `φ xᵢ = tᵢ`.

Proven through mathlib's `MvPowerSeries.eval₂Hom`, which builds
`f ↦ ∑_m ι(coeff m f) · t^m` by density from polynomials over a
complete separated linearly topologized ring. Supplying its hypotheses
is the whole proof, and each is a one-liner in the right vocabulary:
`WithIdeal R := ⟨𝔪_R⟩` installs the `𝔪`-adic topology together with its
uniformity, `IsUniformAddGroup` and `IsLinearTopology` instances;
`IsAdic.isAdicComplete_iff` converts the ALGEBRAIC hypothesis
`IsAdicComplete 𝔪 R` into `CompleteSpace R ∧ T2Space R` for exactly
that topology; `WithIdeal Λ := ⟨⊥⟩` makes `Λ` discrete, so `ι` is
continuous by `WithIdeal.uniformContinuous_of_map_le` (`⊥.map ι = ⊥`);
and `HasEval t` holds because `tᵢ ∈ 𝔪_R` gives `tᵢ^n ∈ 𝔪_R^n → 0`
(topological nilpotence) while `Fin g` is finite, so the cofinite
filter is `⊥` and the vanishing-at-infinity clause is vacuous. The two
conclusions are then `MvPowerSeries.eval₂_C` and
`MvPowerSeries.eval₂_X`. -/
theorem exists_mvPowerSeries_ringHom_of_mem_maximalIdeal {R : Type*}
    [CommRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    {Λ : Type*} [CommRing Λ] (ι : Λ →+* R) {g : ℕ} (t : Fin g → R)
    (ht : ∀ i, t i ∈ IsLocalRing.maximalIdeal R) :
    ∃ φ : MvPowerSeries (Fin g) Λ →+* R,
      φ.comp (MvPowerSeries.C : Λ →+* MvPowerSeries (Fin g) Λ) = ι ∧
      ∀ i, φ (MvPowerSeries.X i) = t i := by
  -- the `𝔪`-adic topology on `R`, the discrete one on `Λ`
  letI : WithIdeal Λ := ⟨⊥⟩
  letI : WithIdeal R := ⟨IsLocalRing.maximalIdeal R⟩
  have hIadic : IsAdic (IsLocalRing.maximalIdeal R) := rfl
  obtain ⟨hcomplete, hT2⟩ := hIadic.isAdicComplete_iff.mp inferInstance
  letI := hcomplete
  letI := hT2
  have hι : Continuous ι :=
    (WithIdeal.uniformContinuous_of_map_le (f := ι)
      (by show Ideal.map ι ⊥ ≤ IsLocalRing.maximalIdeal R
          rw [Ideal.map_bot]
          exact bot_le)).continuous
  -- the `tᵢ` are topologically nilpotent, and there are finitely many of them
  have hteval : MvPowerSeries.HasEval t := by
    refine ⟨fun i => ?_, ?_⟩
    · rw [IsTopologicallyNilpotent,
        (IsLocalRing.maximalIdeal R).hasBasis_nhds_zero_adic.tendsto_right_iff]
      intro n _
      filter_upwards [eventually_ge_atTop n] with m hm
      exact Ideal.pow_le_pow_right hm (Ideal.pow_mem_pow (ht i) m)
    · rw [Filter.cofinite_eq_bot]
      exact tendsto_bot
  refine ⟨MvPowerSeries.eval₂Hom hι hteval, ?_, fun i => ?_⟩
  · refine RingHom.ext fun r => ?_
    rw [RingHom.comp_apply, MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_C]
  · rw [MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_X]

/-- **Surjectivity leaf of the de Smit–Lenstra presentation** (sorry
node — pure commutative algebra, the third stratum of the 2026-07-25
decomposition of `exists_minimal_mvPowerSeries_presentation`): the
substitution map `φ : Λ[[x₁, …, x_g]] → R` of
`exists_mvPowerSeries_ringHom_of_mem_maximalIdeal` is SURJECTIVE as
soon as `Λ` covers the residue field (`π ∘ ι` onto) and the `tᵢ`
generate `𝔪_R` modulo `𝔪_R² + ℓR`.

Proof (successive approximation): let `A` be the image of `φ`, a
subring containing `ι(Λ)` and every `tᵢ`. Residue surjectivity gives
`R = ι(Λ) + 𝔪_R`; the spanning hypothesis plus `ℓ = ι(ℓ) ∈ A` and
`𝔪_Λ = (ℓ)` give `𝔪_R ⊆ A·𝔪_R + 𝔪_R²`, so by induction
`R = A + 𝔪_R^n` for every `n`. For `r ∈ R` this produces a sequence
`a_n ∈ A` with `r − a_n ∈ 𝔪_R^n` and `a_{n+1} − a_n ∈ 𝔪_R^n`; lifting
the increments through `φ` and summing them in the COMPLETE power
series ring `Λ[[x₁, …, x_g]]` (the increments lie in `𝔪_S^n`, so the
sum converges coefficientwise) gives a preimage of `r` — `IsHausdorff`
turning "agrees modulo every `𝔪_R^n`" into equality. Classically
phrased: the image of a complete ring is closed, and it is dense by the
generation hypothesis. -/
theorem surjective_of_mvPowerSeries_ringHom {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    {Λ : Type*} [CommRing Λ] [IsLocalRing Λ]
    (hΛℓ : IsLocalRing.maximalIdeal Λ = Ideal.span {(ℓ : Λ)})
    (π : R →+* k) (ι : Λ →+* R) (hι : Function.Surjective (π.comp ι))
    {g : ℕ} (t : Fin g → R)
    (hspan : IsLocalRing.maximalIdeal R = Ideal.span (Set.range t) ⊔
      (IsLocalRing.maximalIdeal R ^ 2 ⊔ Ideal.span {(ℓ : R)}))
    (φ : MvPowerSeries (Fin g) Λ →+* R)
    (hφC : φ.comp (MvPowerSeries.C : Λ →+* MvPowerSeries (Fin g) Λ) = ι)
    (hφX : ∀ i, φ (MvPowerSeries.X i) = t i) :
    Function.Surjective φ :=
  sorry

/-- **Minimality (kernel-bound) leaf of the de Smit–Lenstra
presentation** (sorry node — pure commutative algebra, the fourth
stratum of the 2026-07-25 decomposition of
`exists_minimal_mvPowerSeries_presentation`): when the `tᵢ` are a
MINIMAL family generating `𝔪_R` modulo `𝔪_R² + ℓR` — the length `g` is
least among all such families, as produced by
`exists_minimal_span_sup_of_isNoetherianRing` — the substitution map
`φ` has `ker φ ≤ 𝔪_S² + (ℓ)`, i.e. `φ` is an isomorphism on mod-`ℓ`
cotangent spaces and the presentation is minimal.

Proof: `𝔪_Λ = (ℓ)` makes `𝔪_S = (ℓ, x₁, …, x_g)`, so
`𝔪_S² + (ℓ) = (ℓ) + (xᵢxⱼ)` and every `f ∈ S` decomposes as
`f = C c + ∑ᵢ C aᵢ · xᵢ + h` with `h ∈ 𝔪_S²` — the power-series
ingredient being that a series with vanishing constant term is
`∑ᵢ xᵢ gᵢ` (split each monomial off its least variable of positive
exponent), applied twice. Now let `f ∈ ker φ` and suppose
`f ∉ 𝔪_S² + (ℓ)`; then some `aⱼ` is a unit of `Λ` (all `aᵢ ∈ (ℓ)` and
`c ∈ (ℓ)` would put `f` back inside). Applying `φ` gives
`ι(c) + ∑ᵢ ι(aᵢ) tᵢ ∈ 𝔪_R²`, and `ι(c) ∈ 𝔪_R² + ℓR` since `c ∈ 𝔪_Λ` is
forced by `φ(f) = 0` and `tᵢ ∈ 𝔪_R`; multiplying by `ι(aⱼ)⁻¹` exhibits
`tⱼ ∈ span {tᵢ : i ≠ j} ⊔ (𝔪_R² ⊔ ℓR)`. Hence the family with `tⱼ`
deleted still generates `𝔪_R` modulo `𝔪_R² + ℓR`, contradicting
minimality of `g` (`hmin` applied at `g − 1`). -/
theorem ker_le_of_minimal_mvPowerSeries_ringHom {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] {Λ : Type*} [CommRing Λ]
    [IsLocalRing Λ]
    (hΛℓ : IsLocalRing.maximalIdeal Λ = Ideal.span {(ℓ : Λ)})
    (ι : Λ →+* R) {g : ℕ} (t : Fin g → R)
    (ht : ∀ i, t i ∈ IsLocalRing.maximalIdeal R)
    (hspan : IsLocalRing.maximalIdeal R = Ideal.span (Set.range t) ⊔
      (IsLocalRing.maximalIdeal R ^ 2 ⊔ Ideal.span {(ℓ : R)}))
    (hmin : ∀ (n : ℕ) (s : Fin n → R),
      (∀ i, s i ∈ IsLocalRing.maximalIdeal R) →
      IsLocalRing.maximalIdeal R = Ideal.span (Set.range s) ⊔
        (IsLocalRing.maximalIdeal R ^ 2 ⊔ Ideal.span {(ℓ : R)}) → g ≤ n)
    (φ : MvPowerSeries (Fin g) Λ →+* R) (hφsurj : Function.Surjective φ)
    (hφC : φ.comp (MvPowerSeries.C : Λ →+* MvPowerSeries (Fin g) Λ) = ι)
    (hφX : ∀ i, φ (MvPowerSeries.X i) = t i) :
    RingHom.ker φ ≤
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin g) Λ) ^ 2 ⊔
        Ideal.span {(ℓ : MvPowerSeries (Fin g) Λ)} :=
  sorry

/-- **Minimal-presentation stratum** (DECOMPOSED 2026-07-25 into the
four commutative-algebra leaves `exists_coefficientRing_ringHom`
(Cohen/Witt coefficient ring),
`exists_mvPowerSeries_ringHom_of_mem_maximalIdeal` (convergent
substitution), `surjective_of_mvPowerSeries_ringHom` (successive
approximation) and `ker_le_of_minimal_mvPowerSeries_ringHom`
(minimality), over the PROVEN choice of a minimal generating family
`exists_minimal_span_sup_of_isNoetherianRing`; the assembly below is
proven): every Noetherian local `ℤ_ℓ`-algebra which is
maximal-adically complete and separated and has finite residue field
`k` (it maps ONTO `k`) admits a *minimal* presentation by a power
series ring over a coefficient ring `Λ`: a compatible surjection
`φ : Λ[[x₁,…,x_g]] ↠ R` whose kernel lies in `𝔪² + (ℓ)` — i.e. `φ`
induces an isomorphism of mod-`ℓ` cotangent spaces
`𝔪_S/(𝔪_S² + ℓ) ≅ 𝔪_R/(𝔪_R² + ℓ)`, so `g` is the mod-`ℓ` cotangent
dimension of `R`.

The coefficient ring `Λ` is classically the Witt vectors `W(k)` — for
`k = ZMod ℓ` just `ℤ_ℓ` itself — and the clauses nearly pin it up to
isomorphism: a local domain, Noetherian, module-finite over `ℤ_ℓ`
(hence complete), with maximal ideal `(ℓ)` (unramified over `ℤ_ℓ`); its
residue field is then forced to be `k` by the surjection `φ` onto the
local ring `R` with residue field `k`. (CAVEAT, 2026-07-25: "nearly" —
the clauses admit `ℓ = 0` in `Λ`, i.e. a finite field, for which
`dim Λ[[x₁,…,x_g]] = g` rather than `g + 1`; the missing
`(ℓ : Λ) ≠ 0` is supplied downstream by the relation-count leaf, see
`exists_coefficientRing_ringHom`.) (`k`-GENERALIZATION NOTE,
2026-07-24: over `ZMod ℓ` this leaf fixed `Λ = ℤ_ℓ`; the abstract `Λ`
is the correct base for a general finite residue field, since a
quotient of `ℤ_ℓ[[x₁,…,x_g]]` has residue field `𝔽_ℓ`.)

The assembly proven here is the de Smit–Lenstra skeleton (*Explicit
construction of universal deformation rings*, Prop. 2.3; Matsumura
§29): the surjection `π : R ↠ k` onto a field has `ker π = 𝔪_R`
(`IsLocalRing.ker_eq_maximalIdeal`), so `ℓ ∈ 𝔪_R` because `k` has
characteristic `ℓ` (`natCast_self_eq_zero`) and therefore
`J := 𝔪_R² + ℓR` is a proper ideal; a MINIMAL family `t₁, …, t_g ∈ 𝔪_R`
generating `𝔪_R` modulo `J` exists by Noetherianness
(`exists_minimal_span_sup_of_isNoetherianRing`) — this is the
"finite-dimensional mod-`ℓ` cotangent space, choose a basis" step; the
coefficient-ring leaf supplies `Λ = W(k)` and the formally étale lift
`ι` (`R` becomes a `Λ`-algebra); the substitution leaf turns
`xᵢ ↦ tᵢ` into `φ` — convergent because the `tᵢ` are topologically
nilpotent and `R` is complete — whose `ℤ_ℓ`-compatibility is
`φ ∘ C = ι` composed with `ι ∘ algebraMap = algebraMap`
(`MvPowerSeries.algebraMap_apply`); and the last two leaves are its
surjectivity (the image is a closed subring, dense by the generation
hypothesis) and its kernel bound (which restates the choice of a
*minimal* family, not merely a spanning one). -/
theorem exists_minimal_mvPowerSeries_presentation {R : Type*} [CommRing R]
    [IsLocalRing R] [Algebra ℤ_[ℓ] R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (π : R →+* k) (hπsurj : Function.Surjective π) :
    ∃ (Λ : Type u) (_ : CommRing Λ) (_ : IsDomain Λ) (_ : IsLocalRing Λ)
      (_ : IsNoetherianRing Λ) (_ : Algebra ℤ_[ℓ] Λ)
      (_ : Module.Finite ℤ_[ℓ] Λ),
      IsLocalRing.maximalIdeal Λ = Ideal.span {(ℓ : Λ)} ∧
      ∃ (g : ℕ) (φ : MvPowerSeries (Fin g) Λ →+* R),
        Function.Surjective φ ∧
        φ.comp (algebraMap ℤ_[ℓ] (MvPowerSeries (Fin g) Λ)) =
          algebraMap ℤ_[ℓ] R ∧
        RingHom.ker φ ≤
          IsLocalRing.maximalIdeal (MvPowerSeries (Fin g) Λ) ^ 2 ⊔
            Ideal.span {(ℓ : MvPowerSeries (Fin g) Λ)} := by
  -- `ker π = 𝔪_R`, so `ℓ ∈ 𝔪_R` and the mod-`ℓ` cotangent ideal is proper
  have hkerπ : RingHom.ker π = IsLocalRing.maximalIdeal R :=
    IsLocalRing.ker_eq_maximalIdeal π hπsurj
  have hℓmem : (ℓ : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [← hkerπ, RingHom.mem_ker, map_natCast]
    exact natCast_self_eq_zero
  have hJ : (IsLocalRing.maximalIdeal R ^ 2 ⊔ Ideal.span {(ℓ : R)}) ≤
      IsLocalRing.maximalIdeal R :=
    sup_le (Ideal.pow_le_self two_ne_zero)
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hℓmem))
  -- a minimal family generating `𝔪_R` modulo `𝔪_R² + ℓR`
  obtain ⟨g, t, ht, hspan, hmin⟩ :=
    exists_minimal_span_sup_of_isNoetherianRing _ hJ
  -- the coefficient ring and the substitution map
  obtain ⟨Λ, iCR, iDom, iLoc, iNoeth, iAlg, iFin, hΛℓ, ι, hιcomp, hιsurj⟩ :=
    exists_coefficientRing_ringHom (ℓ := ℓ) (k := k) π hπsurj
  letI := iCR; letI := iDom; letI := iLoc; letI := iNoeth; letI := iAlg
  letI := iFin
  obtain ⟨φ, hφC, hφX⟩ :=
    exists_mvPowerSeries_ringHom_of_mem_maximalIdeal ι t ht
  have hφsurj : Function.Surjective φ :=
    surjective_of_mvPowerSeries_ringHom hΛℓ π ι hιsurj t hspan φ hφC hφX
  refine ⟨Λ, iCR, iDom, iLoc, iNoeth, iAlg, iFin, hΛℓ, g, φ, hφsurj, ?_,
    ker_le_of_minimal_mvPowerSeries_ringHom hΛℓ ι t ht hspan hmin φ hφsurj
      hφC hφX⟩
  -- `ℤ_ℓ`-compatibility: `algebraMap` into `Λ[[x]]` is `C ∘ algebraMap`
  refine RingHom.ext fun r => ?_
  rw [RingHom.comp_apply, MvPowerSeries.algebraMap_apply,
    show φ ((MvPowerSeries.C : Λ →+* MvPowerSeries (Fin g) Λ)
        (algebraMap ℤ_[ℓ] Λ r)) = ι (algebraMap ℤ_[ℓ] Λ r) from
      RingHom.congr_fun hφC _,
    ← RingHom.comp_apply, hιcomp]

/-- **Böckle relation-count leaf** (sorry node — the arithmetic core of
the presentation stratum, isolated 2026-07-25 by peeling off the
Nakayama step; **RESTATED the same day: the previous conclusion `r < g`
was FALSE**, see the refutation below): for EVERY minimal presentation
`φ : Λ[[x₁,…,x_g]] ↠ D.R` of the weakly universal, trace-generated
hardly ramified deformation ring, over ANY unramified coefficient ring
`Λ` (local Noetherian domain, module-finite over `ℤ_ℓ`, maximal ideal
`(ℓ)`; minimal means `ker φ ⊆ 𝔪² + (ℓ)`, so that `g` is the mod-`ℓ`
tangent dimension `dim H¹_{HR}(G_{ℚ,S}, ad⁰ ρbar)` of the deformation
functor), the coefficient ring has `ℓ ≠ 0` and the kernel is generated
by *at most `g`* power series MODULO `𝔪_S · ker φ`.

**Why `r < g` was wrong (2026-07-25).** Two independent defects, both
fixed here and in the Krull glue below.

1. *The bound.* Obstruction theory bounds `r` by `dim H²_{HR}`, and the
   Greenberg–Wiles/Poitou–Tate Euler characteristic compares that to
   `g = dim H¹_{HR}` term by term over `S = {2, ℓ, ∞}` — for the FIXED
   determinant problem (`IsHardlyRamified.det` pins `det ρ` to the
   cyclotomic character, so the relevant module is `ad⁰`, of dimension
   `3`, not `ad`):
   `dim H¹_L − dim H¹_{L^⊥} = h⁰(ℚ, ad⁰) − h⁰(ℚ, ad⁰(1))`
   `+ Σ_{v ∈ S} (dim L_v − h⁰(ℚ_v, ad⁰))`. Absolute irreducibility kills
   the two global terms; the local terms are `0` at `2` (the tame
   condition is balanced), `+1` at `ℓ` (flat/Fontaine–Laffaille:
   `dim H¹_f = h⁰ + dim ad⁰/Fil⁰ = h⁰ + 1`) and `−1` at `∞` (`ρbar` odd,
   so `h⁰(ℝ, ad⁰) = 1` and `L_∞ = 0` as `ℓ` is odd). The total is `0`,
   NOT `1`: the honest conclusion is `r ≤ g`, which is exactly the
   classical statement (`R ≅ Λ[[x₁,…,x_g]]/(f₁,…,f_r)` with
   `r ≤ dim H²`, whence `dim R ≥ 1 + g − r ≥ 1`). The `+1` in that
   dimension count is `dim Λ = 1`, i.e. it comes from the COEFFICIENT
   RING, not from a strict inequality between `r` and `g`; the old
   statement had moved it into the relation count.
2. *Refutation, not merely a gap.* With `Λ` of characteristic `0` (as
   `Λ ≅ W(k)` is), `r < g` CONTRADICTS this module's own finiteness
   stratum: `dim Λ[[x₁,…,x_g]] = g + 1`, so `r ≤ g − 1` relations would
   give `dim D.R ≥ 2`, while
   `moduleFinite_of_isWeaklyUniversal_isTraceGenerated` makes `D.R`
   module-finite over `ℤ_ℓ`, hence of Krull dimension `≤ 1`. The
   expected situation is `r = g` exactly (`R ≅ T` finite flat over
   `W(k)`, of dimension `1`), and `g = r = 0` (`R ≅ W(k)`, a rigid
   deformation problem) is not excluded by any hypothesis — there the
   old statement asserted `r < 0`. The old `g = 0` worry was therefore
   not an isolated edge case but the visible corner of a wrong bound.

**Why the new conjunct `(ℓ : Λ) ≠ 0`.** With `r ≤ g` the `+1` has to be
supplied by `dim Λ = 1`, and the `Λ`-clauses do NOT supply it: a finite
field `Λ = k` satisfies every one of them (local Noetherian domain,
module-finite over `ℤ_ℓ`, `𝔪_Λ = (ℓ) = ⊥`), and then
`dim Λ[[x₁,…,x_g]] = g`, so `r ≤ g` would say nothing. The docstrings
claiming these clauses "pin `Λ ≅ W(k)`" were wrong for the same reason.
`(ℓ : Λ) ≠ 0` is what pins it, and it is genuine arithmetic, which is
why it is a conclusion of this leaf rather than a hypothesis: if
`ℓ = 0` in `Λ` then `ℓ = 0` in `D.R` (the presentation is
`ℤ_ℓ`-compatible), so `D.R` would be a `ℤ_ℓ`-module-finite `𝔽_ℓ`-algebra,
hence FINITE — contradicting the characteristic-zero point that Böckle's
count produces. Downstream,
`exists_isPrime_lt_maximalIdeal_of_mvPowerSeries_presentation` consumes
it as `𝔪_Λ ≠ ⊥` through `succ_le_height_maximalIdeal_mvPowerSeries`.

What obstruction theory delivers, and nothing more (Böckle;
Khare–Wintenberger §4): the minimal relation space is the `k`-vector
space `ker φ/(𝔪_S · ker φ)`, whose dual embeds into
`H²_{HR}(G_{ℚ,S}, ad⁰ ρbar)`, so `r ≤ dim H²` elements of `ker φ` span
it modulo `𝔪_S · ker φ`. The passage from "spans modulo `𝔪_S · ker φ`"
to "generates" is Nakayama's lemma, PROVEN in the assembly
`exists_relations_lt_of_minimal_mvPowerSeries_presentation` below, so no
completeness or closedness argument is needed here.

As with the finiteness leaf, the hypotheses pin `D` down up to
canonical isomorphism, so a future proof may construct its own
universal datum and transport along `exists_ringEquiv_of_isUniversal`
(minimality of a presentation is preserved by composition with a
`ℤ_ℓ`-algebra isomorphism).

(The name keeps its historical `_lt_` — now a misnomer for `r ≤ g` —
so that every reference, queued task and sibling docstring stays valid.)

References: Böckle, *Presentations of universal deformation rings*
(and his appendix to Khare's Serre-conjecture notes);
Khare–Wintenberger, *Serre's modularity conjecture (I)*, §4;
Darmon–Diamond–Taylor, *Fermat's Last Theorem*, §2.6–2.7 (the `r ≤ g`
count and `dim R ≥ 1 + g − r`); Mazur, *Deforming Galois
representations*, §1.6–1.7. -/
theorem exists_relations_lt_le_smul_of_minimal_mvPowerSeries_presentation
    (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible)
    (D : HardlyRamifiedDeformation hℓOdd ρbar)
    (hw : D.IsWeaklyUniversal) (ht : D.IsTraceGenerated) :
    letI := D.commRing; letI := D.algebra
    ∀ (Λ : Type u) (_ : CommRing Λ) (_ : IsDomain Λ) (_ : IsLocalRing Λ)
      (_ : IsNoetherianRing Λ) (_ : Algebra ℤ_[ℓ] Λ)
      (_ : Module.Finite ℤ_[ℓ] Λ),
      IsLocalRing.maximalIdeal Λ = Ideal.span {(ℓ : Λ)} →
      ∀ (g : ℕ) (φ : MvPowerSeries (Fin g) Λ →+* D.R),
        Function.Surjective φ →
        φ.comp (algebraMap ℤ_[ℓ] (MvPowerSeries (Fin g) Λ)) =
          algebraMap ℤ_[ℓ] D.R →
        RingHom.ker φ ≤
          IsLocalRing.maximalIdeal (MvPowerSeries (Fin g) Λ) ^ 2 ⊔
            Ideal.span {(ℓ : MvPowerSeries (Fin g) Λ)} →
        ∃ (r : ℕ) (f : Fin r → MvPowerSeries (Fin g) Λ),
          (ℓ : Λ) ≠ 0 ∧ r ≤ g ∧ (∀ i, f i ∈ RingHom.ker φ) ∧
          RingHom.ker φ ≤ Ideal.span (Set.range f) ⊔
            IsLocalRing.maximalIdeal (MvPowerSeries (Fin g) Λ) •
              RingHom.ker φ :=
  sorry

/-- **Böckle relation-bound stratum** (DECOMPOSED 2026-07-25 into the
arithmetic leaf
`exists_relations_lt_le_smul_of_minimal_mvPowerSeries_presentation` —
the Galois-cohomological count `r ≤ g` for the minimal relation space
`ker φ/(𝔪_S · ker φ)`, together with `ℓ ≠ 0` in `Λ` — plus the PROVEN
Nakayama step below; the count was `r < g` until the same day, when it
was refuted, see the leaf's docstring): for EVERY minimal presentation
`φ : Λ[[x₁,…,x_g]] ↠ D.R` of the weakly universal, trace-generated
hardly ramified deformation ring, over ANY unramified coefficient ring
`Λ`, the kernel is generated by *at most `g`* power series, over a
coefficient ring of characteristic `0`.

The assembly proven here is Nakayama's lemma in the form
`Submodule.le_of_le_smul_of_le_jacobson_bot`: `Λ[[x₁,…,x_g]]` is
Noetherian (`isNoetherianRing_mvPowerSeries`, proven in this module),
so `ker φ` is finitely generated, and `𝔪_S` lies in its Jacobson
radical (`IsLocalRing.maximalIdeal_le_jacobson`); hence elements of
`ker φ` spanning it modulo `𝔪_S · ker φ` already span it. This is also
what makes the *span* (rather than its closure) the correct statement:
finitely generated ideals of a Noetherian complete local ring are
closed. -/
theorem exists_relations_lt_of_minimal_mvPowerSeries_presentation
    (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible)
    (D : HardlyRamifiedDeformation hℓOdd ρbar)
    (hw : D.IsWeaklyUniversal) (ht : D.IsTraceGenerated) :
    letI := D.commRing; letI := D.algebra
    ∀ (Λ : Type u) (_ : CommRing Λ) (_ : IsDomain Λ) (_ : IsLocalRing Λ)
      (_ : IsNoetherianRing Λ) (_ : Algebra ℤ_[ℓ] Λ)
      (_ : Module.Finite ℤ_[ℓ] Λ),
      IsLocalRing.maximalIdeal Λ = Ideal.span {(ℓ : Λ)} →
      ∀ (g : ℕ) (φ : MvPowerSeries (Fin g) Λ →+* D.R),
        Function.Surjective φ →
        φ.comp (algebraMap ℤ_[ℓ] (MvPowerSeries (Fin g) Λ)) =
          algebraMap ℤ_[ℓ] D.R →
        RingHom.ker φ ≤
          IsLocalRing.maximalIdeal (MvPowerSeries (Fin g) Λ) ^ 2 ⊔
            Ideal.span {(ℓ : MvPowerSeries (Fin g) Λ)} →
        ∃ (r : ℕ) (f : Fin r → MvPowerSeries (Fin g) Λ),
          (ℓ : Λ) ≠ 0 ∧ r ≤ g ∧
          RingHom.ker φ = Ideal.span (Set.range f) := by
  letI := D.commRing; letI := D.algebra
  intro Λ iCR iDom iLoc iNoeth iAlg iFin hΛℓ g φ hφs hφc hφmin
  letI := iCR; letI := iDom; letI := iLoc; letI := iNoeth; letI := iAlg
  letI := iFin
  obtain ⟨r, f, hℓΛ, hrg, hfmem, hle⟩ :=
    exists_relations_lt_le_smul_of_minimal_mvPowerSeries_presentation hℓOdd
      hdim hℓ5 h hirr D hw ht Λ iCR iDom iLoc iNoeth iAlg iFin hΛℓ g φ hφs
      hφc hφmin
  haveI : IsNoetherianRing (MvPowerSeries (Fin g) Λ) :=
    isNoetherianRing_mvPowerSeries g
  refine ⟨r, f, hℓΛ, hrg, le_antisymm ?_ ?_⟩
  · exact Submodule.le_of_le_smul_of_le_jacobson_bot
      (IsNoetherian.noetherian (RingHom.ker φ))
      (IsLocalRing.maximalIdeal_le_jacobson ⊥) hle
  · exact Ideal.span_le.mpr (Set.range_subset_iff.mpr hfmem)

/-- **Böckle presentation leaf** (DECOMPOSED 2026-07-23 into the
minimal-presentation leaf `exists_minimal_mvPowerSeries_presentation` —
pure commutative algebra: every complete Noetherian local `ℤ_ℓ`-algebra
with finite residue field `k` is minimally presented by a power series
ring over the unramified coefficient ring `Λ ≅ W(k)` — and the Böckle
relation-bound leaf
`exists_relations_lt_of_minimal_mvPowerSeries_presentation` — the
Galois-cohomological count `r ≤ g` for minimal presentations; the
assembly below is proven): the weakly universal, trace-generated hardly
ramified deformation ring admits a presentation
`D.R ≅ Λ[[x₁,…,x_g]]/(f₁,…,f_r)` with at most as many relations as
generators, `r ≤ g`, compatibly with the `ℤ_ℓ`-structures, over a local
Noetherian domain `Λ` module-finite over `ℤ_ℓ` which is NOT a field
(`𝔪_Λ ≠ ⊥`, i.e. `Λ` is of characteristic `0`).

The count was `r < g` until 2026-07-25, when it was refuted (see the
relation-count leaf's docstring); the missing unit of dimension is
`dim Λ = 1`, which is why `𝔪_Λ ≠ ⊥` is exported here — the Krull glue
needs it to turn `r ≤ g` into `dim D.R ≥ 1`. -/
theorem exists_mvPowerSeries_presentation_of_isWeaklyUniversal_isTraceGenerated
    (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible)
    (D : HardlyRamifiedDeformation hℓOdd ρbar)
    (hw : D.IsWeaklyUniversal) (ht : D.IsTraceGenerated) :
    letI := D.commRing; letI := D.algebra
    ∃ (Λ : Type u) (_ : CommRing Λ) (_ : IsDomain Λ) (_ : IsLocalRing Λ)
      (_ : IsNoetherianRing Λ) (_ : Algebra ℤ_[ℓ] Λ)
      (_ : Module.Finite ℤ_[ℓ] Λ)
      (g r : ℕ) (φ : MvPowerSeries (Fin g) Λ →+* D.R)
      (f : Fin r → MvPowerSeries (Fin g) Λ),
      IsLocalRing.maximalIdeal Λ ≠ ⊥ ∧ r ≤ g ∧ Function.Surjective φ ∧
      φ.comp (algebraMap ℤ_[ℓ] (MvPowerSeries (Fin g) Λ)) =
        algebraMap ℤ_[ℓ] D.R ∧
      RingHom.ker φ = Ideal.span (Set.range f) := by
  letI := D.commRing; letI := D.isLocalRing; letI := D.algebra
  haveI := D.isNoetherianRing
  haveI := D.isAdicComplete
  obtain ⟨Λ, iΛ1, iΛ2, iΛ3, iΛ4, iΛ5, iΛ6, hΛℓ, g, φ, hφs, hφc, hφmin⟩ :=
    exists_minimal_mvPowerSeries_presentation (ℓ := ℓ) D.π D.π_surjective
  obtain ⟨r, f, hℓΛ, hrg, hker⟩ :=
    exists_relations_lt_of_minimal_mvPowerSeries_presentation hℓOdd hdim hℓ5
      h hirr D hw ht Λ iΛ1 iΛ2 iΛ3 iΛ4 iΛ5 iΛ6 hΛℓ g φ hφs hφc hφmin
  -- `𝔪_Λ = (ℓ)` is nonzero exactly because `ℓ ≠ 0` in `Λ`
  have hΛbot : IsLocalRing.maximalIdeal Λ ≠ ⊥ := by
    rw [hΛℓ]
    exact fun hbot => hℓΛ (Ideal.span_singleton_eq_bot.mp hbot)
  exact ⟨Λ, iΛ1, iΛ2, iΛ3, iΛ4, iΛ5, iΛ6, g, r, φ, f, hΛbot, hrg, hφs, hφc,
    hker⟩

/-- **Prime chain in `Λ[[x₁,…,x_g]]`, `Λ` a local domain** (PROVEN
2026-07-23 modulo the
variable-splitting leaf `nonempty_ringEquiv_mvPowerSeries_powerSeries`):
a strictly increasing chain of `g + 1` primes inside the maximal ideal
— morally `(0) ⊂ (x_g) ⊂ (x_{g−1}, x_g) ⊂ ⋯ ⊂ (x₁,…,x_g)`.

Proof, by induction on `g`: for `g = 0` the constant chain `(⊥)` works
(the ring is a domain by `MvPowerSeries`' `NoZeroDivisors` instance).
For the step, split off one variable: pull the chain of the `n`-variable
ring back along the (surjective) constant-coefficient map of the
single-variable power series ring over it — pullback along a surjection
is strictly monotone and preserves primality — and prepend `⊥` (prime:
power series over a domain form a domain; strictly below the pullback
of the bottom link, which contains `X` while `⊥` does not); transport
the resulting chain along the splitting isomorphism; the top link stays
inside the maximal ideal because a power series with non-unit constant
coefficient is a non-unit. -/
theorem exists_isPrime_chain_mvPowerSeries (Λ : Type*) [CommRing Λ]
    [IsDomain Λ] [IsLocalRing Λ] (g : ℕ) :
    ∃ c : Fin (g + 1) → Ideal (MvPowerSeries (Fin g) Λ),
      StrictMono c ∧ (∀ i, (c i).IsPrime) ∧
      c (Fin.last g) ≤
        IsLocalRing.maximalIdeal (MvPowerSeries (Fin g) Λ) := by
  induction g with
  | zero =>
    haveI : IsDomain (MvPowerSeries (Fin 0) Λ) :=
      NoZeroDivisors.to_isDomain _
    exact ⟨fun _ => ⊥, fun i j hij => (hij.ne (Fin.ext (by omega))).elim,
      fun _ => Ideal.isPrime_bot, bot_le⟩
  | succ n ih =>
    obtain ⟨c, hmono, hprime, hle⟩ := ih
    obtain ⟨e⟩ :=
      nonempty_ringEquiv_mvPowerSeries_powerSeries (R := Λ) n
    haveI : IsDomain (MvPowerSeries (Fin n) Λ) :=
      NoZeroDivisors.to_isDomain _
    -- the pulled-back chain over the split ring, with `⊥` prepended
    let c' : Fin (n + 1 + 1) →
        Ideal (PowerSeries (MvPowerSeries (Fin n) Λ)) :=
      Fin.cases ⊥ fun i => (c i).comap
        (PowerSeries.constantCoeff (R := MvPowerSeries (Fin n) Λ))
    have hc'zero : c' 0 = ⊥ := rfl
    have hc'succ : ∀ i : Fin (n + 1), c' i.succ = (c i).comap
        (PowerSeries.constantCoeff (R := MvPowerSeries (Fin n) Λ)) :=
      fun i => rfl
    -- pulling back along the (surjective) constant-coefficient map is
    -- strictly monotone
    have hccSM : StrictMono
        fun I : Ideal (MvPowerSeries (Fin n) Λ) => I.comap
          (PowerSeries.constantCoeff (R := MvPowerSeries (Fin n) Λ)) :=
      Monotone.strictMono_of_injective (fun _ _ h => Ideal.comap_mono h)
        (Ideal.comap_injective_of_surjective _
          PowerSeries.constantCoeff_surj)
    have hSM : StrictMono c' := by
      rw [Fin.strictMono_iff_lt_succ]
      intro i
      induction i using Fin.induction with
      | zero =>
        rw [Fin.castSucc_zero, hc'zero, hc'succ 0]
        refine bot_lt_iff_ne_bot.mpr fun hbot => ?_
        have hX : PowerSeries.X ∈ (c 0).comap
            (PowerSeries.constantCoeff (R := MvPowerSeries (Fin n) Λ)) := by
          show PowerSeries.constantCoeff (R := MvPowerSeries (Fin n) Λ)
            PowerSeries.X ∈ c 0
          rw [PowerSeries.constantCoeff_X]
          exact (c 0).zero_mem
        rw [hbot] at hX
        exact PowerSeries.X_ne_zero (Ideal.mem_bot.mp hX)
      | succ j _ =>
        rw [← Fin.succ_castSucc, hc'succ j.castSucc, hc'succ j.succ]
        exact hccSM (hmono (Fin.castSucc_lt_succ (i := j)))
    -- primality along the pulled-back chain
    have hprime' : ∀ i, (c' i).IsPrime := by
      intro i
      induction i using Fin.induction with
      | zero =>
        rw [hc'zero]
        exact Ideal.isPrime_bot
      | succ j _ =>
        rw [hc'succ j]
        haveI := hprime j
        exact Ideal.IsPrime.comap _
    -- transport along the splitting isomorphism
    have heSM : StrictMono
        fun I : Ideal (PowerSeries (MvPowerSeries (Fin n) Λ)) =>
          I.comap (e : MvPowerSeries (Fin (n + 1)) Λ →+*
            PowerSeries (MvPowerSeries (Fin n) Λ)) :=
      Monotone.strictMono_of_injective (fun _ _ h => Ideal.comap_mono h)
        (Ideal.comap_injective_of_surjective _ e.surjective)
    refine ⟨fun i => (c' i).comap
      (e : MvPowerSeries (Fin (n + 1)) Λ →+*
        PowerSeries (MvPowerSeries (Fin n) Λ)),
      heSM.comp hSM, fun i => ?_, ?_⟩
    · haveI := hprime' i
      exact Ideal.IsPrime.comap _
    · intro x hx
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have hx' : PowerSeries.constantCoeff (R := MvPowerSeries (Fin n) Λ)
          (e x) ∈ c (Fin.last n) := by
        have hmem : e x ∈ c' (Fin.last (n + 1)) := hx
        rw [← Fin.succ_last, hc'succ (Fin.last n)] at hmem
        exact hmem
      have hnonu := hle hx'
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hnonu
      exact hnonu ((hu.map e).map
        (PowerSeries.constantCoeff (R := MvPowerSeries (Fin n) Λ)))

/-- **Height from a prime chain** (PROVEN, elementary): a strictly
increasing chain of `n + 1` primes ending inside `J` forces
`n ≤ height J`. Walking up the chain raises the height by at least one
per strict link (`Ideal.height_add_one_le_of_lt_of_isPrime`), and the
height is monotone in the ideal (`Ideal.height_mono`). -/
theorem le_height_of_isPrime_chain {A : Type*} [CommRing A] {n : ℕ}
    {c : Fin (n + 1) → Ideal A} (hmono : StrictMono c)
    (hprime : ∀ i, (c i).IsPrime) {J : Ideal A}
    (hle : c (Fin.last n) ≤ J) : (n : ℕ∞) ≤ J.height := by
  have hstep : ∀ i : Fin (n + 1), ((i : ℕ) : ℕ∞) ≤ (c i).height := by
    intro i
    induction i using Fin.induction with
    | zero => simp
    | succ j ih =>
      haveI := hprime j.castSucc
      haveI := hprime j.succ
      have hlt := Ideal.height_add_one_le_of_lt_of_isPrime
        (hmono (Fin.castSucc_lt_succ (i := j)))
      have hcast : ((j.succ : ℕ) : ℕ∞) = ((j.castSucc : ℕ) : ℕ∞) + 1 := by
        simp
      rw [hcast]
      exact le_trans (add_le_add ih le_rfl) hlt
  have hlast := hstep (Fin.last n)
  rw [Fin.val_last] at hlast
  exact hlast.trans (Ideal.height_mono hle)

/-- Coefficientwise surjectivity of the coefficient map on power series
(mathlib has `PowerSeries.map_surjective`, but not the multivariate
version). -/
theorem mvPowerSeries_map_surjective {σ : Type*} {Λ Γ : Type*} [CommRing Λ]
    [CommRing Γ] (f : Λ →+* Γ) (hf : Function.Surjective f) :
    Function.Surjective (MvPowerSeries.map (σ := σ) f) := by
  classical
  intro t
  refine ⟨fun m => Function.surjInv hf (MvPowerSeries.coeff m t),
    MvPowerSeries.ext fun m => ?_⟩
  show f (Function.surjInv hf (MvPowerSeries.coeff m t)) = _
  exact Function.surjInv_eq hf _

/-- **Height of the maximal ideal of `Λ[[x₁,…,x_g]]`, `Λ` a local domain
which is NOT a field** (PROVEN 2026-07-23 modulo the prime-chain leaf
above; STRENGTHENED from `g` to `g + 1` on 2026-07-25, see the
relation-count leaf's docstring): at least `g + 1`.

The `+ 1` is `dim Λ ≥ 1` and it is load-bearing, not cosmetic: it is the
only reason a presentation with `r ≤ g` relations — which is all
Poitou–Tate delivers, `r < g` being FALSE — still forces
`dim R ≥ 1`. Classically `Λ = W(k)` is a complete DVR and
`dim Λ[[x₁,…,x_g]] = g + 1`; the hypothesis `𝔪_Λ ≠ ⊥` is exactly "Λ is
not a field", i.e. `ℓ ≠ 0` in `Λ` once `𝔪_Λ = (ℓ)`.

Proof: reduce the coefficients modulo `𝔪_Λ`. The chain lemma above,
applied to the residue FIELD of `Λ`, gives `g + 1` primes of
`k(Λ)[[x₁,…,x_g]]` inside its maximal ideal; pulling them back along
the (surjective, local) reduction map `Λ[[x]] ↠ k(Λ)[[x]]` keeps them
prime and strictly increasing, all of them containing the kernel — and
`⊥` prepends strictly below, because the kernel is nonzero (it contains
`C a` for any `0 ≠ a ∈ 𝔪_Λ`) while `Λ[[x]]` is a domain. That is a
chain of `g + 2` primes inside the maximal ideal. -/
theorem succ_le_height_maximalIdeal_mvPowerSeries (Λ : Type*) [CommRing Λ]
    [IsDomain Λ] [IsLocalRing Λ]
    (hΛ : IsLocalRing.maximalIdeal Λ ≠ ⊥) (g : ℕ) :
    ((g + 1 : ℕ) : ℕ∞) ≤
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin g) Λ)).height := by
  classical
  obtain ⟨c, hmono, hprime, hle⟩ :=
    exists_isPrime_chain_mvPowerSeries (IsLocalRing.ResidueField Λ) g
  haveI : IsDomain (MvPowerSeries (Fin g) Λ) := NoZeroDivisors.to_isDomain _
  -- reduction of the coefficients modulo the maximal ideal of `Λ`
  let Ψ : MvPowerSeries (Fin g) Λ →+*
      MvPowerSeries (Fin g) (IsLocalRing.ResidueField Λ) :=
    MvPowerSeries.map (IsLocalRing.residue Λ)
  have hΨsurj : Function.Surjective Ψ :=
    mvPowerSeries_map_surjective _ Ideal.Quotient.mk_surjective
  have hcSM : StrictMono fun I : Ideal (MvPowerSeries (Fin g)
      (IsLocalRing.ResidueField Λ)) => I.comap Ψ :=
    Monotone.strictMono_of_injective (fun _ _ h => Ideal.comap_mono h)
      (Ideal.comap_injective_of_surjective _ hΨsurj)
  -- the chain pulled back to `Λ[[x]]`, with `⊥` prepended
  let c' : Fin (g + 1 + 1) → Ideal (MvPowerSeries (Fin g) Λ) :=
    Fin.cases ⊥ fun i => (c i).comap Ψ
  have hc'zero : c' 0 = ⊥ := rfl
  have hc'succ : ∀ i : Fin (g + 1), c' i.succ = (c i).comap Ψ := fun _ => rfl
  -- the prepended link is strict: the kernel of `Ψ` is nonzero
  obtain ⟨a, hamem, hane⟩ := Submodule.ne_bot_iff _ |>.mp hΛ
  have hker : (MvPowerSeries.C a : MvPowerSeries (Fin g) Λ) ∈
      (c 0).comap Ψ := by
    show Ψ (MvPowerSeries.C a) ∈ c 0
    have hzero : Ψ (MvPowerSeries.C a) = 0 := by
      show MvPowerSeries.map (IsLocalRing.residue Λ) (MvPowerSeries.C a) = 0
      rw [MvPowerSeries.map_C]
      have hres : IsLocalRing.residue Λ a = 0 := by
        rw [← RingHom.mem_ker, IsLocalRing.ker_residue]; exact hamem
      rw [hres, map_zero]
    rw [hzero]
    exact (c 0).zero_mem
  have hSM : StrictMono c' := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    induction i using Fin.induction with
    | zero =>
      rw [Fin.castSucc_zero, hc'zero, hc'succ 0]
      refine bot_lt_iff_ne_bot.mpr fun hbot => ?_
      rw [hbot] at hker
      exact (MvPowerSeries.C_injective (σ := Fin g) (R := Λ)).ne hane
        (by simpa using Ideal.mem_bot.mp hker) |>.elim
    | succ j _ =>
      rw [← Fin.succ_castSucc, hc'succ j.castSucc, hc'succ j.succ]
      exact hcSM (hmono (Fin.castSucc_lt_succ (i := j)))
  have hprime' : ∀ i, (c' i).IsPrime := by
    intro i
    induction i using Fin.induction with
    | zero => rw [hc'zero]; exact Ideal.isPrime_bot
    | succ j _ =>
      rw [hc'succ j]
      haveI := hprime j
      exact Ideal.IsPrime.comap _
  refine le_height_of_isPrime_chain hSM hprime' ?_
  rw [← Fin.succ_last, hc'succ (Fin.last g)]
  intro x hx
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have hΨx : Ψ x ∈
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin g)
        (IsLocalRing.ResidueField Λ)) := hle hx
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hΨx
  exact hΨx (hu.map Ψ)

/-- **Krull glue for the presentation stratum** (PROVEN 2026-07-23
modulo the two commutative-algebra leaves above — no arithmetic
content; RESTATED 2026-07-25 with `r ≤ g` in place of `r < g`, at the
price of the hypothesis `𝔪_Λ ≠ ⊥`, because `r < g` is false — see the
relation-count leaf's docstring): a local ring presented as a quotient
of `Λ[[x₁,…,x_g]]` — `Λ` a Noetherian local domain which is not a
field — by an ideal generated by `r ≤ g` elements has a prime strictly
below its maximal ideal.

Proof: if not, every prime of `R` equals the maximal ideal, so — the
prime correspondence along the surjection `φ` being elementary — the
maximal ideal of the power series ring is a *minimal* prime over
`ker φ`; Krull's height theorem
(`Ideal.height_le_card_of_mem_minimalPrimes_span`) then bounds its
height by `r`, contradicting the height lower bound `g + 1 > r`
(`succ_le_height_maximalIdeal_mvPowerSeries`, where the `+1` is
`dim Λ ≥ 1`). -/
theorem exists_isPrime_lt_maximalIdeal_of_mvPowerSeries_presentation
    {Λ : Type*} [CommRing Λ] [IsDomain Λ] [IsLocalRing Λ]
    [IsNoetherianRing Λ] (hΛ : IsLocalRing.maximalIdeal Λ ≠ ⊥)
    {R : Type*} [CommRing R] [IsLocalRing R] {g r : ℕ} (hrg : r ≤ g)
    (φ : MvPowerSeries (Fin g) Λ →+* R) (hφ : Function.Surjective φ)
    (f : Fin r → MvPowerSeries (Fin g) Λ)
    (hker : RingHom.ker φ = Ideal.span (Set.range f)) :
    ∃ P : Ideal R, P.IsPrime ∧ P < IsLocalRing.maximalIdeal R := by
  classical
  by_contra hcon
  push Not at hcon
  haveI : IsNoetherianRing (MvPowerSeries (Fin g) Λ) :=
    isNoetherianRing_mvPowerSeries g
  -- the kernel is proper, hence contained in the maximal ideal
  have hKtop : RingHom.ker φ ≠ ⊤ := by
    intro htop
    have h1 : (1 : MvPowerSeries (Fin g) Λ) ∈ RingHom.ker φ :=
      htop ▸ Submodule.mem_top
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  have hKle : RingHom.ker φ ≤
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin g) Λ) :=
    IsLocalRing.le_maximalIdeal hKtop
  -- were there no prime strictly below the maximal ideal of `R`, the
  -- maximal ideal of the power series ring would be a MINIMAL prime
  -- over the kernel
  have hmin : IsLocalRing.maximalIdeal (MvPowerSeries (Fin g) Λ) ∈
      (RingHom.ker φ).minimalPrimes := by
    refine ⟨⟨(IsLocalRing.maximalIdeal.isMaximal _).isPrime, hKle⟩, ?_⟩
    rintro Q ⟨hQp, hKQ⟩ _
    haveI := hQp
    -- the image of `Q` is a prime of `R` not strictly below the maximal
    -- ideal, hence equal to it
    have hmapP : (Q.map φ).IsPrime := Ideal.map_isPrime_of_surjective hφ hKQ
    have hmaple : Q.map φ ≤ IsLocalRing.maximalIdeal R :=
      IsLocalRing.le_maximalIdeal hmapP.ne_top
    have hmapeq : Q.map φ = IsLocalRing.maximalIdeal R :=
      (eq_or_lt_of_le hmaple).resolve_right (hcon _ hmapP)
    -- the surjection is local: the maximal ideal lands in the maximal
    -- ideal (else a preimage of the inverse of a unit value writes `1`
    -- as an element of the maximal ideal)
    have hloc : IsLocalRing.maximalIdeal (MvPowerSeries (Fin g) Λ) ≤
        (IsLocalRing.maximalIdeal R).comap φ := by
      intro x hx
      show φ x ∈ IsLocalRing.maximalIdeal R
      by_contra hu
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hu
      obtain ⟨y, hy⟩ := hφ (↑hu.unit⁻¹)
      have hxy : x * y - 1 ∈ RingHom.ker φ := by
        rw [RingHom.mem_ker, map_sub, map_mul, hy, map_one, hu.mul_val_inv,
          sub_self]
      have h1 : (1 : MvPowerSeries (Fin g) Λ) ∈
          IsLocalRing.maximalIdeal (MvPowerSeries (Fin g) Λ) := by
        have hsub := sub_mem (Ideal.mul_mem_right y _ hx) (hKle hxy)
        rwa [sub_sub_cancel] at hsub
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
        ((Ideal.eq_top_iff_one _).mpr h1)
    -- and the pullback of the image of `Q` is `Q` itself
    have hpull : (IsLocalRing.maximalIdeal R).comap φ = Q := by
      rw [← hmapeq, Ideal.comap_map_of_surjective φ hφ,
        ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hKQ]
    exact hloc.trans hpull.le
  -- Krull's height theorem bounds the height of the maximal ideal by
  -- the number of generators of the kernel …
  rw [hker] at hmin
  have hkr := Ideal.height_le_card_of_mem_minimalPrimes_span
    (Set.finite_range f) hmin
  have hcard : (Set.range f).ncard ≤ r := by
    have himg := Set.ncard_image_le (f := f) (s := (Set.univ : Set (Fin r)))
      Set.finite_univ
    rw [Set.image_univ] at himg
    simpa [Set.ncard_univ] using himg
  -- … contradicting the height lower bound `g + 1 > r`
  have hgr : ((g + 1 : ℕ) : ℕ∞) ≤ (r : ℕ∞) :=
    (succ_le_height_maximalIdeal_mvPowerSeries Λ hΛ g).trans
      (hkr.trans (Nat.cast_le.mpr hcard))
  exact absurd (Nat.cast_le.mp hgr) (by omega)

/-- **Dimension leaf** (DECOMPOSED 2026-07-23 into the Böckle
presentation leaf
`exists_mvPowerSeries_presentation_of_isWeaklyUniversal_isTraceGenerated`
— the Galois-cohomological generators-and-relations count `g − r ≥ 0`
over a coefficient ring of characteristic `0` — plus the Krull glue
`exists_isPrime_lt_maximalIdeal_of_mvPowerSeries_presentation`, itself
proven modulo the two pure commutative-algebra leaves
`isNoetherianRing_mvPowerSeries` and
`succ_le_height_maximalIdeal_mvPowerSeries`; the assembly below is
proven): the weakly universal, trace-generated hardly ramified
deformation ring has Krull dimension `≥ 1` — some prime lies strictly
below the maximal ideal. The unit of dimension comes from
`dim Λ = 1` (`𝔪_Λ ≠ ⊥`), not from a strict inequality `r < g`, which
was refuted 2026-07-25. -/
theorem exists_isPrime_lt_maximalIdeal_of_isWeaklyUniversal_isTraceGenerated
    (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible)
    (D : HardlyRamifiedDeformation hℓOdd ρbar)
    (hw : D.IsWeaklyUniversal) (ht : D.IsTraceGenerated) :
    letI := D.commRing; letI := D.isLocalRing
    ∃ P : Ideal D.R, P.IsPrime ∧ P < IsLocalRing.maximalIdeal D.R := by
  letI := D.commRing; letI := D.isLocalRing; letI := D.algebra
  obtain ⟨Λ, iΛ1, iΛ2, iΛ3, iΛ4, iΛ5, iΛ6, g, r, φ, f, hΛbot, hrg, hφ, -,
    hker⟩ :=
    exists_mvPowerSeries_presentation_of_isWeaklyUniversal_isTraceGenerated
      hℓOdd hdim hℓ5 h hirr D hw ht
  letI := iΛ1; letI := iΛ2; letI := iΛ3; letI := iΛ4
  exact exists_isPrime_lt_maximalIdeal_of_mvPowerSeries_presentation hΛbot hrg
    φ hφ f hker

/-- **A local ring of Krull dimension `≥ 1` is infinite** (PROVEN,
elementary): were `R` finite, the quotient by a prime `P` strictly below
the maximal ideal would be a finite integral domain, hence a field,
making `P` maximal — but the only maximal ideal of a local ring is the
maximal ideal, contradicting strictness. -/
lemma infinite_of_isPrime_lt_maximalIdeal {R : Type*} [CommRing R]
    [IsLocalRing R] {P : Ideal R} (hP : P.IsPrime)
    (hlt : P < IsLocalRing.maximalIdeal R) : Infinite R := by
  by_contra hinf
  rw [not_infinite_iff_finite] at hinf
  haveI := hinf
  haveI := hP
  haveI : Finite (R ⧸ P) :=
    Finite.of_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  have hmax : P.IsMaximal :=
    Ideal.Quotient.maximal_of_isField P (Finite.isField_of_domain (R ⧸ P))
  exact absurd (IsLocalRing.eq_maximalIdeal hmax) (ne_of_lt hlt)

/-- **Kernel dichotomy for module-finite `ℤ_ℓ`-algebras** (PROVEN,
elementary): a `ℤ_ℓ`-algebra that is finite as a `ℤ_ℓ`-module and
infinite as a set has characteristic zero — the structure map is
injective. If some `x ≠ 0` died in `R`, then so would `ℓ ^ v(x)` (every
nonzero element of `ℤ_ℓ` is a unit times a power of `ℓ`), and reducing
the coordinates of the finitely many module generators mod `ℓ ^ v(x)`
would exhibit `R` as the image of the finite set `(ℤ/ℓ^{v(x)})^k`. -/
lemma algebraMap_injective_of_moduleFinite_of_infinite {R : Type*}
    [CommRing R] [Algebra ℤ_[ℓ] R] (hfin : Module.Finite ℤ_[ℓ] R)
    (hinf : Infinite R) : Function.Injective (algebraMap ℤ_[ℓ] R) := by
  classical
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  by_contra hx0
  -- `ℓ ^ v(x)` is a unit multiple of `x`, hence also dies in `R`
  have hℓn : algebraMap ℤ_[ℓ] R ((ℓ : ℤ_[ℓ]) ^ x.valuation) = 0 := by
    have hprod : algebraMap ℤ_[ℓ] R ((PadicInt.unitCoeff hx0 : ℤ_[ℓ])) *
        algebraMap ℤ_[ℓ] R ((ℓ : ℤ_[ℓ]) ^ x.valuation) = 0 := by
      rw [← map_mul, ← PadicInt.unitCoeff_spec hx0, hx]
    exact ((PadicInt.unitCoeff hx0).isUnit.map
      (algebraMap ℤ_[ℓ] R)).mul_right_eq_zero.mp hprod
  -- so `R` is covered by a finite set: reduce coordinates mod `ℓ ^ v(x)`
  haveI := hfin
  haveI := hinf
  haveI : NeZero (ℓ ^ x.valuation) :=
    ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  obtain ⟨k, φ, hφ⟩ := Module.Finite.exists_fin' ℤ_[ℓ] R
  have hsurj : Function.Surjective
      fun c : Fin k → ZMod (ℓ ^ x.valuation) =>
        φ fun i => ((c i).val : ℤ_[ℓ]) := by
    intro r
    obtain ⟨c, rfl⟩ := hφ r
    refine ⟨fun i => PadicInt.toZModPow x.valuation (c i), ?_⟩
    have hker : ∀ i, c i -
        (((PadicInt.toZModPow x.valuation (c i)).val : ℤ_[ℓ])) ∈
        Ideal.span {(ℓ : ℤ_[ℓ]) ^ x.valuation} := by
      intro i
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast,
        ZMod.natCast_val, ZMod.cast_id, sub_self]
    choose d hd using fun i => Ideal.mem_span_singleton'.mp (hker i)
    have hvec : (c - fun i =>
        (((PadicInt.toZModPow x.valuation (c i)).val : ℤ_[ℓ]))) =
        ((ℓ : ℤ_[ℓ]) ^ x.valuation) • d := by
      funext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [← hd i, mul_comm]
    have hφd : φ c - φ (fun i =>
        (((PadicInt.toZModPow x.valuation (c i)).val : ℤ_[ℓ]))) = 0 := by
      rw [← map_sub, hvec, map_smul, Algebra.smul_def, hℓn, zero_mul]
    exact (sub_eq_zero.mp hφd).symm
  haveI := Finite.of_surjective _ hsurj
  exact not_finite R

/-- **Presentation stratum** (DECOMPOSED 2026-07-22 into the arithmetic
leaf `exists_isPrime_lt_maximalIdeal_of_isWeaklyUniversal_isTraceGenerated`
— Böckle's presentation bound `g − r ≥ 1` giving Krull dimension `≥ 1` —
plus PROVEN formal glue): the universal hardly ramified deformation ring
has characteristic zero — `ℤ_ℓ` embeds.

The assembly below is proven: dimension `≥ 1` makes the constructed
universal ring infinite (`infinite_of_isPrime_lt_maximalIdeal`);
infiniteness transports to `D.R` along the canonical isomorphism of
universal data; and an infinite module-finite `ℤ_ℓ`-algebra (finiteness
by `moduleFinite_of_isUniversal`) has injective structure map
(`algebraMap_injective_of_moduleFinite_of_infinite` — a nonzero kernel
`(ℓ^n)` would make `R` a quotient of a finite set). -/
theorem algebraMap_injective_of_isUniversal (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible)
    (D : HardlyRamifiedDeformation hℓOdd ρbar) (hD : D.IsUniversal) :
    letI := D.commRing; letI := D.algebra
    Function.Injective (algebraMap ℤ_[ℓ] D.R) := by
  letI := D.commRing; letI := D.algebra
  have hfin : Module.Finite ℤ_[ℓ] D.R :=
    moduleFinite_of_isUniversal hℓOdd hdim hℓ5 h hirr D hD
  obtain ⟨D₀, hw₀, ht₀⟩ :=
    exists_isWeaklyUniversal_isTraceGenerated hℓOdd hdim hℓ5 h hirr
  letI := D₀.commRing; letI := D₀.isLocalRing; letI := D₀.algebra
  have hD₀ : D₀.IsUniversal :=
    isUniversal_of_isWeaklyUniversal_isTraceGenerated hℓOdd D₀ hw₀ ht₀
  obtain ⟨P, hP, hlt⟩ :=
    exists_isPrime_lt_maximalIdeal_of_isWeaklyUniversal_isTraceGenerated
      hℓOdd hdim hℓ5 h hirr D₀ hw₀ ht₀
  have hinf₀ : Infinite D₀.R := infinite_of_isPrime_lt_maximalIdeal hP hlt
  obtain ⟨e, _⟩ := exists_ringEquiv_of_isUniversal hℓOdd D₀ D hD₀ hD
  have hinf : Infinite D.R := @Infinite.of_injective _ _ hinf₀ e e.injective
  exact algebraMap_injective_of_moduleFinite_of_infinite hfin hinf

open IsLocalRing Topology in
/-- **Topology glue** (PROVEN 2026-07-22, elementary — no arithmetic
content): on a module-finite local `ℤ_ℓ`-algebra whose topology is the
maximal-adic one and which is adically complete and separated, the
topology is the `ℤ_ℓ`-module topology.

Proof: (1) `ℓ` lands in the maximal ideal — otherwise the span chain of
the powers of its inverse violates Noetherian stabilization (morally:
`ℚ_ℓ` would embed as a finitely generated `ℤ_ℓ`-submodule); hence the
structure map `ℤ_ℓ → R` is continuous (`ℓ^k`-balls land in `𝔪^k`) and
`R` is a topological `ℤ_ℓ`-module, giving `moduleTopology ≤ τ_R` for
free (`moduleTopology_le`). (2) For the converse, the module topology is
compact — it is the coinduced topology along a surjection
`ℤ_ℓ^n ↠ R` from a compact space
(`ModuleTopology.eq_coinduced_of_surjective`) — while `τ_R` is Hausdorff
(adic separatedness: `{0} = ⋂ 𝔪^k` is an intersection of closed open
subgroups), so the continuous identity from the module topology to
`τ_R` is a homeomorphism (`Continuous.homeoOfEquivCompactToT2`), and
the two topologies agree (`IsModuleTopology.of_continuous_id`). -/
theorem isModuleTopology_of_isAdic_maximalIdeal {R : Type u} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    [Algebra ℤ_[ℓ] R] [Module.Finite ℤ_[ℓ] R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (hadic : IsAdic (IsLocalRing.maximalIdeal R)) :
    IsModuleTopology ℤ_[ℓ] R := by
  classical
  -- Step 1: `ℓ` lands in the maximal ideal (else `ℚ_ℓ` would embed as a
  -- finitely generated `ℤ_ℓ`-submodule).
  have hℓm : algebraMap ℤ_[ℓ] R (ℓ : ℤ_[ℓ]) ∈ maximalIdeal R := by
    by_contra hu
    rw [mem_maximalIdeal, mem_nonunits_iff, not_not] at hu
    obtain ⟨u, hu⟩ := hu
    haveI : IsNoetherian ℤ_[ℓ] R :=
      isNoetherian_of_isNoetherianRing_of_finite ℤ_[ℓ] R
    have hvu : ((u⁻¹ : Rˣ) : R) * (u : R) = 1 := u.inv_mul
    -- the ascending chain of spans of powers of the inverse stabilizes
    have hmono : Monotone fun n : ℕ =>
        Submodule.span ℤ_[ℓ] {((u⁻¹ : Rˣ) : R) ^ n} := by
      apply monotone_nat_of_le_succ
      intro n
      rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
        Submodule.mem_span_singleton]
      refine ⟨(ℓ : ℤ_[ℓ]), ?_⟩
      calc (ℓ : ℤ_[ℓ]) • ((u⁻¹ : Rˣ) : R) ^ (n + 1)
          = (((u⁻¹ : Rˣ) : R) * (u : R)) * ((u⁻¹ : Rˣ) : R) ^ n := by
            rw [Algebra.smul_def, ← hu]; ring
        _ = ((u⁻¹ : Rˣ) : R) ^ n := by rw [hvu, one_mul]
    obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr
      (inferInstance : IsNoetherian ℤ_[ℓ] R) ⟨_, hmono⟩
    have heq : Submodule.span ℤ_[ℓ] {((u⁻¹ : Rˣ) : R) ^ n} =
        Submodule.span ℤ_[ℓ] {((u⁻¹ : Rˣ) : R) ^ (n + 1)} :=
      hn (n + 1) (Nat.le_succ n)
    have hmem : ((u⁻¹ : Rˣ) : R) ^ (n + 1) ∈
        Submodule.span ℤ_[ℓ] {((u⁻¹ : Rˣ) : R) ^ n} := by
      rw [heq]
      exact Submodule.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    -- multiply by `u^(n+1)`: `algebraMap (c * ℓ) = 1`
    have h1 : algebraMap ℤ_[ℓ] R (c * ℓ) = 1 := by
      have h := congrArg (· * ((u : R)) ^ (n + 1)) hc
      simp only [Algebra.smul_def] at h
      have hpow : ((u⁻¹ : Rˣ) : R) ^ n * ((u : R)) ^ (n + 1) = (u : R) := by
        calc ((u⁻¹ : Rˣ) : R) ^ n * ((u : R)) ^ (n + 1)
            = (((u⁻¹ : Rˣ) : R) * (u : R)) ^ n * (u : R) := by ring
          _ = (u : R) := by rw [hvu, one_pow, one_mul]
      rw [map_mul, ← hu]
      calc algebraMap ℤ_[ℓ] R c * (u : R)
          = algebraMap ℤ_[ℓ] R c * ((u⁻¹ : Rˣ) : R) ^ n *
              ((u : R)) ^ (n + 1) := by rw [mul_assoc, hpow]
        _ = ((u⁻¹ : Rˣ) : R) ^ (n + 1) * ((u : R)) ^ (n + 1) := h
        _ = (((u⁻¹ : Rˣ) : R) * (u : R)) ^ (n + 1) := by rw [mul_pow]
        _ = 1 := by rw [hvu, one_pow]
    -- but `1 - c * ℓ` is a unit of `ℤ_ℓ` in the kernel of `algebraMap`
    have hker : algebraMap ℤ_[ℓ] R (1 - c * ℓ) = 0 := by
      rw [map_sub, map_one, h1, sub_self]
    have hkne : RingHom.ker (algebraMap ℤ_[ℓ] R) ≠ ⊤ := by
      intro htop
      have h1mem : (1 : ℤ_[ℓ]) ∈ RingHom.ker (algebraMap ℤ_[ℓ] R) :=
        htop ▸ Submodule.mem_top
      rw [RingHom.mem_ker, map_one] at h1mem
      exact one_ne_zero h1mem
    have hcl : c * (ℓ : ℤ_[ℓ]) ∈ maximalIdeal ℤ_[ℓ] := by
      rw [PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.mem_span_singleton.mpr ⟨c, mul_comm c _⟩
    have hone : (1 : ℤ_[ℓ]) ∈ maximalIdeal ℤ_[ℓ] := by
      have h := add_mem (IsLocalRing.le_maximalIdeal hkne
        (RingHom.mem_ker.mpr hker)) hcl
      rwa [sub_add_cancel] at h
    exact (IsLocalRing.maximalIdeal.isMaximal ℤ_[ℓ]).ne_top
      ((Ideal.eq_top_iff_one _).mpr hone)
  -- Step 2: the structure map is continuous, so `R` is a topological
  -- `ℤ_ℓ`-module for its given topology.
  have hcont : Continuous (algebraMap ℤ_[ℓ] R) := by
    apply continuous_of_continuousAt_zero (algebraMap ℤ_[ℓ] R)
    unfold ContinuousAt
    rw [map_zero, hadic.hasBasis_nhds_zero.tendsto_right_iff]
    intro k _
    have hball : Metric.closedBall (0 : ℤ_[ℓ]) ((ℓ : ℝ) ^ (-(k : ℤ))) ∈
        𝓝 (0 : ℤ_[ℓ]) := by
      refine Metric.closedBall_mem_nhds 0 ?_
      exact zpow_pos (Nat.cast_pos.mpr (Fact.out : ℓ.Prime).pos) _
    filter_upwards [hball] with x hx
    have hx' : x ∈ Ideal.span {((ℓ : ℤ_[ℓ])) ^ k} := by
      rw [← PadicInt.norm_le_pow_iff_mem_span_pow]
      simpa [Metric.mem_closedBall, dist_zero_right] using hx
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hx'
    show algebraMap ℤ_[ℓ] R x ∈ ((maximalIdeal R ^ k : Ideal R) : Set R)
    rw [← hd, map_mul, map_pow]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hℓm k)
  haveI hsmul : ContinuousSMul ℤ_[ℓ] R :=
    continuousSMul_of_algebraMap ℤ_[ℓ] R hcont
  -- Step 3: the given topology is Hausdorff (adic separatedness).
  haveI ht2 : T2Space R := by
    have hclosed : IsClosed ({(0 : R)} : Set R) := by
      have h0 : ({(0 : R)} : Set R) =
          ⋂ k : ℕ, ((maximalIdeal R ^ k : Ideal R) : Set R) := by
        ext x
        simp only [Set.mem_singleton_iff, Set.mem_iInter, SetLike.mem_coe]
        constructor
        · rintro rfl k
          exact Submodule.zero_mem _
        · intro hx
          refine IsHausdorff.haus
            (inferInstance : IsHausdorff (maximalIdeal R) R) x fun k => ?_
          rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
          exact hx k
      rw [h0]
      refine isClosed_iInter fun k => ?_
      exact AddSubgroup.isClosed_of_isOpen
        (Submodule.toAddSubgroup (maximalIdeal R ^ k))
        ((isAdic_iff.mp hadic).1 k)
    haveI := IsTopologicalAddGroup.t1Space R hclosed
    infer_instance
  -- Step 4: the module topology is compact (continuous surjective image of
  -- `ℤ_ℓⁿ`) …
  obtain ⟨n, φ, hφ⟩ := Module.Finite.exists_fin' ℤ_[ℓ] R
  have hcoind : moduleTopology ℤ_[ℓ] R =
      TopologicalSpace.coinduced φ inferInstance :=
    ModuleTopology.eq_coinduced_of_surjective hφ
  have hφc : @Continuous (Fin n → ℤ_[ℓ]) R _ (moduleTopology ℤ_[ℓ] R) φ :=
    continuous_iff_coinduced_le.mpr (le_of_eq hcoind.symm)
  have hcompact : @CompactSpace R (moduleTopology ℤ_[ℓ] R) :=
    @Function.Surjective.compactSpace _ _ _ (moduleTopology ℤ_[ℓ] R) _ hφc
      inferInstance hφ
  -- … so the continuous identity from the (compact) module topology to the
  -- (Hausdorff) given topology is a homeomorphism, and the two agree.
  have hid : @Continuous R R (moduleTopology ℤ_[ℓ] R) _ id :=
    continuous_id_iff_le.mpr (moduleTopology_le ℤ_[ℓ] R)
  exact IsModuleTopology.of_continuous_id
    (@Homeomorph.continuous_symm R R (moduleTopology ℤ_[ℓ] R) _
      (@Continuous.homeoOfEquivCompactToT2 R R
        (moduleTopology ℤ_[ℓ] R) _ hcompact ht2 (Equiv.refl R) hid))

/-- **B6a-core**: the Khare–Wintenberger-style lifting core.
An irreducible hardly ramified mod-`ℓ` representation with `ℓ ≥ 5` lifts to
a hardly ramified representation over *some* coefficient ring `R` — a local
topological `ℤ_ℓ`-algebra, finite as a `ℤ_ℓ`-module, carrying the
`ℤ_ℓ`-module topology, of characteristic zero (`ℤ_ℓ` embeds) — with a
reduction map matching the characteristic polynomials of Frobenius of
`ρbar` at all good primes. `R` is *not* required to be a domain.

DECOMPOSED (2026-07-22) along the standard deformation-theoretic proof
into the three strata above — representability
(`exists_universal_hardlyRamifiedDeformation`: Mazur/Ramakrishna/Carayol),
`ℤ_ℓ`-module finiteness of the universal ring
(`moduleFinite_of_isUniversal`: potential modularity, Taylor–Wiles–Kisin,
Khare–Wintenberger), characteristic zero
(`algebraMap_injective_of_isUniversal`: Böckle's presentation bound
`g − r ≥ 1`) — plus the elementary topology glue
(`isModuleTopology_of_isAdic_maximalIdeal`). The assembly below is
proven: it takes the universal datum and repackages it with the three
pinned-down properties.

References: Khare–Wintenberger, *Serre's modularity conjecture (I)*,
Thm. 4.1 and §4; Böckle's appendix to Khare's *Serre's conjecture* notes;
Buzzard's 2026 EPSRC course, Lecture 4. -/
theorem exists_finite_lift (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible) :
    ∃ (R : Type u) (_ : CommRing R) (_ : TopologicalSpace R)
      (_ : IsTopologicalRing R) (_ : IsLocalRing R) (_ : Algebra ℤ_[ℓ] R)
      (_ : Module.Finite ℤ_[ℓ] R) (_ : IsModuleTopology ℤ_[ℓ] R),
      Function.Injective (algebraMap ℤ_[ℓ] R) ∧
      ∃ ρ : FramedGaloisRep ℚ R (Fin 2),
        IsHardlyRamified hℓOdd (rank_finTwoFun R) ρ ∧
        ∃ π : R →+* k, Function.Surjective π ∧
          ∀ q (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
          (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
            ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat := by
  obtain ⟨D, hD⟩ :=
    exists_universal_hardlyRamifiedDeformation hℓOdd hdim hℓ5 h hirr
  letI := D.commRing; letI := D.topologicalSpace; letI := D.isTopologicalRing
  letI := D.isLocalRing; letI := D.algebra; letI := D.isNoetherianRing
  letI := D.isAdicComplete
  have hfin : Module.Finite ℤ_[ℓ] D.R :=
    moduleFinite_of_isUniversal hℓOdd hdim hℓ5 h hirr D hD
  letI := hfin
  have hmt : IsModuleTopology ℤ_[ℓ] D.R :=
    isModuleTopology_of_isAdic_maximalIdeal D.isAdic
  have hinj : Function.Injective (algebraMap ℤ_[ℓ] D.R) :=
    algebraMap_injective_of_isUniversal hℓOdd hdim hℓ5 h hirr D hD
  exact ⟨D.R, D.commRing, D.topologicalSpace, D.isTopologicalRing,
    D.isLocalRing, D.algebra, hfin, hmt, hinj, D.ρ, D.isHardlyRamified,
    D.π, D.π_surjective, D.charFrob_compat⟩

set_option backward.isDefEq.respectTransparency false in
open scoped TensorProduct in
/-- **Flatness transfers along quotient specialization** (PROVEN
2026-07-22, mirroring the residue-field transfer
`IsHardlyRamified.isFlatAt_baseChange_residue` of `Threeadic.lean`): if
`ρ` is flat at `ℓ`, so is its base change to a quotient `R ⧸ P` of the
coefficient ring. The open ideals of `R ⧸ P` correspond to the open
ideals `J ⊇ P` of `R` (preimages along the continuous quotient map are
open), the double base change `((R ⧸ P) ⧸ I) ⊗ ((R ⧸ P) ⊗ M)` collapses
equivariantly to `(R ⧸ J) ⊗ M` (tensor cancellation
`AlgebraTensorModule.cancelBaseChange` plus the double-quotient
isomorphism `DoubleQuot.quotQuotEquivQuotOfLE` along
`I = J.map (Ideal.Quotient.mk P)`), and
`HasFlatProlongationAt.of_equiv` transports the Hopf-algebra witness. -/
theorem isFlatAt_baseChange_quotient {R : Type u} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Free R M]
    (P : Ideal R) [P.IsPrime] [IsLocalRing (R ⧸ P)]
    {ρ : GaloisRep ℚ R M}
    (hflat : ρ.IsFlatAt
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : ℓ.Prime))) :
    (ρ.baseChange (R ⧸ P)).IsFlatAt
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : ℓ.Prime)) := by
  constructor
  intro I hI
  -- the corresponding open ideal of `R`, lying over `P`
  let J : Ideal R := I.comap (Ideal.Quotient.mk P)
  have hPJ : P ≤ J := fun x hx => by
    show Ideal.Quotient.mk P x ∈ I
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact I.zero_mem
  have hImap : I = J.map (Ideal.Quotient.mk P) :=
    (Ideal.map_comap_of_surjective (Ideal.Quotient.mk P)
      Ideal.Quotient.mk_surjective I).symm
  have hJopen : IsOpen (J : Set R) := by
    have hpre : (J : Set R) =
        (Ideal.Quotient.mk P) ⁻¹' (I : Set (R ⧸ P)) := rfl
    rw [hpre]
    exact hI.preimage (QuotientRing.isOpenQuotientMap_mk P).continuous
  -- the coefficient identification `((R ⧸ P) ⧸ I) ≃+* R ⧸ J`
  let φ : ((R ⧸ P) ⧸ I) ≃+* (R ⧸ J) :=
    (Ideal.quotEquivOfEq hImap).trans (DoubleQuot.quotQuotEquivQuotOfLE hPJ)
  have hφalg : ∀ r : R,
      φ (algebraMap R ((R ⧸ P) ⧸ I) r) = algebraMap R (R ⧸ J) r := by
    intro r
    show (DoubleQuot.quotQuotEquivQuotOfLE hPJ)
        ((Ideal.quotEquivOfEq hImap)
          (Ideal.Quotient.mk I (Ideal.Quotient.mk P r))) =
      Ideal.Quotient.mk J r
    rw [Ideal.quotEquivOfEq_mk]
    exact DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk r hPJ
  -- its `R`-linear form
  let φlin : ((R ⧸ P) ⧸ I) ≃ₗ[R] (R ⧸ J) :=
    { φ.toAddEquiv with
      map_smul' := fun r x => by
        show φ (r • x) = r • φ x
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, hφalg] }
  -- assemble: cancel the middle base change, then transport coefficients
  let e₁ := TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ P)
    ((R ⧸ P) ⧸ I) ((R ⧸ P) ⧸ I) M
  let e₂ := TensorProduct.congr φlin (LinearEquiv.refl R M)
  let eSp : ((((ρ.baseChange (R ⧸ P)).baseChange ((R ⧸ P) ⧸ I)).toLocal
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
          (Fact.out : ℓ.Prime))).Space ≃+
      ((ρ.baseChange (R ⧸ J)).toLocal
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
          (Fact.out : ℓ.Prime))).Space) :=
    e₁.toAddEquiv.trans e₂.toAddEquiv
  have he : ∀ (g : Field.absoluteGaloisGroup
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
          (Fact.out : ℓ.Prime))))
      (x : (((ρ.baseChange (R ⧸ P)).baseChange ((R ⧸ P) ⧸ I)).toLocal
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
          (Fact.out : ℓ.Prime))).Space),
      eSp (g • x) = g • eSp x := by
    intro g x
    show (e₁.toAddEquiv.trans e₂.toAddEquiv)
        ((((ρ.baseChange (R ⧸ P)).baseChange ((R ⧸ P) ⧸ I)).toLocal
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
            (Fact.out : ℓ.Prime)) g) x) =
      ((ρ.baseChange (R ⧸ J)).toLocal
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
            (Fact.out : ℓ.Prime)) g)
        ((e₁.toAddEquiv.trans e₂.toAddEquiv) x)
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul c y =>
      induction y using TensorProduct.induction_on with
      | zero =>
        rw [show (c ⊗ₜ[R ⧸ P] (0 : (R ⧸ P) ⊗[R] M)) =
          (0 : ((R ⧸ P) ⧸ I) ⊗[R ⧸ P] ((R ⧸ P) ⊗[R] M)) from
          TensorProduct.tmul_zero _ _]
        simp
      | add a b ha hb =>
        rw [TensorProduct.tmul_add]
        simp only [map_add, ha, hb]
      | tmul d m => rfl
  refine (hflat.cond J hJopen).of_equiv _ eSp.symm ?_
  intro g x
  apply eSp.injective
  rw [AddEquiv.apply_symm_apply, he, AddEquiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
open scoped TensorProduct in
/-- **Tameness at `2` transfers along base change** (generalization of the
proven residue-field transfer `IsHardlyRamified.isTameAtTwo_baseChange_residue`
in `Threeadic.lean` from finite residue fields to arbitrary topological
coefficient algebras `B`, same proof): the rank-1 tame quadratic quotient
`(π, δ)` of `ρ` at `2` base-changes to `(rid ∘ (π ⊗ 1), (δ ⊗ 1)ᵉ)` for
`ρ ⊗ B`. -/
lemma isTameAtTwo_baseChange {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Free R M]
    (B : Type*) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [Algebra R B] [ContinuousSMul R B]
    {ρ : GaloisRep ℚ R M}
    (htame : ∃ (π : M →ₗ[R] R) (_ : Function.Surjective π)
      (δ : GaloisRep ℚ_[2] R R),
      ∀ g : Field.absoluteGaloisGroup ℚ_[2], ∀ v : M,
        π (ρ.map (algebraMap ℚ ℚ_[2]) g v) = δ g (π v) ∧
        (AddSubgroup.inertia
          ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup :
            AddSubgroup Z2bar) (Field.absoluteGaloisGroup ℚ_[2]) ≤ δ.ker) ∧
        (∀ g' : Field.absoluteGaloisGroup ℚ_[2], δ g' * δ g' = 1)) :
    ∃ (π : (B ⊗[R] M) →ₗ[B] B) (_ : Function.Surjective π)
      (δ : GaloisRep ℚ_[2] B B),
      ∀ g : Field.absoluteGaloisGroup ℚ_[2], ∀ v : B ⊗[R] M,
        π ((ρ.baseChange B).map (algebraMap ℚ ℚ_[2]) g v) = δ g (π v) ∧
        (AddSubgroup.inertia
          ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup :
            AddSubgroup Z2bar) (Field.absoluteGaloisGroup ℚ_[2]) ≤ δ.ker) ∧
        (∀ g' : Field.absoluteGaloisGroup ℚ_[2], δ g' * δ g' = 1) := by
  obtain ⟨π, hπsurj, δ, h⟩ := htame
  -- the canonical identification `B ⊗[R] R ≃ₗ[B] B`
  let e : (B ⊗[R] R) ≃ₗ[B] B := TensorProduct.AlgebraTensorModule.rid R B B
  -- the base-changed projection and character
  refine ⟨e.toLinearMap ∘ₗ LinearMap.baseChange B π, ?_,
    (δ.baseChange B).conj e, ?_⟩
  · -- surjectivity: hit `c` with `c ⊗ v₀` for a preimage `v₀` of `1`
    intro c
    obtain ⟨v₀, hv₀⟩ := hπsurj 1
    refine ⟨c ⊗ₜ v₀, ?_⟩
    simp [e, LinearMap.baseChange_tmul, hv₀,
      TensorProduct.AlgebraTensorModule.rid_tmul]
  · intro g w
    refine ⟨?_, ?_, ?_⟩
    · -- equivariance, by linearity on simple tensors
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul c v =>
        have h1 := (h g v).1
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
        rw [show ((ρ.baseChange B).map (algebraMap ℚ ℚ_[2])) g (c ⊗ₜ v) =
          c ⊗ₜ ((ρ.map (algebraMap ℚ ℚ_[2])) g v) from rfl,
          LinearMap.baseChange_tmul, h1,
          GaloisRep.conj_apply, LinearMap.baseChange_tmul]
        rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply,
          LinearEquiv.coe_coe, LinearEquiv.coe_coe,
          TensorProduct.AlgebraTensorModule.rid_symm_apply,
          show ((δ.baseChange B) g : Module.End B (B ⊗[R] R)) =
            LinearMap.baseChange B (δ g) from rfl,
          LinearMap.baseChange_tmul,
          TensorProduct.AlgebraTensorModule.rid_tmul]
        rw [show (δ g) (π v) = π v • (δ g) 1 from by
          conv_lhs => rw [show (π v : R) = π v • (1 : R) from by
            rw [smul_eq_mul, mul_one]]
          rw [map_smul]]
        simp [e, TensorProduct.AlgebraTensorModule.rid_tmul, smul_smul,
          mul_comm]
      | add x y hx hy =>
        simp only [map_add, hx, hy]
    · -- unramifiedness: the kernel only grows under base change + conj
      intro σ hσ
      have hδσ : δ σ = 1 := (h 1 0).2.1 hσ
      have : (δ.baseChange B).conj e σ = 1 := by
        rw [GaloisRep.conj_apply]
        rw [show (δ.baseChange B) σ =
          LinearMap.baseChange B (δ σ) from rfl, hδσ]
        refine LinearMap.ext fun c => ?_
        simp
      exact this
    · -- the quadratic condition transfers through the monoid hom
      intro g'
      have hsq : δ g' * δ g' = 1 := (h 1 0).2.2 g'
      calc (δ.baseChange B).conj e g' * (δ.baseChange B).conj e g'
          = (δ.baseChange B).conj e (g' * g') := (map_mul _ _ _).symm
        _ = 1 := by
            rw [GaloisRep.conj_apply]
            rw [show (δ.baseChange B) (g' * g') =
              LinearMap.baseChange B (δ (g' * g')) from rfl,
              map_mul δ, hsq]
            refine LinearMap.ext fun c => ?_
            simp

set_option backward.isDefEq.respectTransparency false in
open scoped TensorProduct in
/-- **Hardly-ramifiedness transfers along quotient specialization of the
coefficients** (DERIVED 2026-07-22, mirroring the proven residue-field
transfer `exists_residual_isHardlyRamified` of `Threeadic.lean`): the
determinant condition maps along `R → R ⧸ P` (`LinearMap.det_baseChange`),
unramifiedness passes to any base change (existing instance), tameness at
`2` and flatness at `ℓ` by the proven transfers above. -/
lemma isHardlyRamified_baseChange_quotient {R : Type u} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    [Algebra ℤ_[ℓ] R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Free R M] {hdimM : Module.rank R M = 2}
    (P : Ideal R) [P.IsPrime] [IsLocalRing (R ⧸ P)]
    (hdimQ : Module.rank (R ⧸ P) ((R ⧸ P) ⊗[R] M) = 2)
    {ρ : GaloisRep ℚ R M} (h : IsHardlyRamified hℓOdd hdimM ρ) :
    IsHardlyRamified hℓOdd hdimQ (ρ.baseChange (R ⧸ P)) := by
  constructor
  · -- the determinant condition maps along the quotient map
    intro g
    have hdet : (ρ.baseChange (R ⧸ P)).det g =
        algebraMap R (R ⧸ P) (ρ.det g) := by
      show LinearMap.det ((ρ.baseChange (R ⧸ P)) g) = _
      rw [show ((ρ.baseChange (R ⧸ P)) g :
          Module.End (R ⧸ P) ((R ⧸ P) ⊗[R] M)) =
        LinearMap.baseChange (R ⧸ P) (ρ g) from rfl,
        LinearMap.det_baseChange]
      rfl
    rw [hdet, h.det g, ← IsScalarTower.algebraMap_apply]
  · -- unramifiedness passes to the base change (existing instance)
    intro p hp hpp
    letI : ρ.IsUnramifiedAt hp.toHeightOneSpectrumRingOfIntegersRat :=
      h.isUnramified p hp hpp
    infer_instance
  · -- flatness at ℓ (sorried transfer leaf)
    exact isFlatAt_baseChange_quotient P h.isFlat
  · -- tameness at 2 (proven transfer)
    exact isTameAtTwo_baseChange (R ⧸ P) h.isTameAtTwo

set_option backward.isDefEq.respectTransparency false in
open scoped TensorProduct in
/-- **Hardly-ramifiedness transfers along conjugation** by a linear
isomorphism of the representation space (PROVEN 2026-07-22): the
determinant is conjugation-invariant, the kernels of the local
representations only grow, flatness transports through
`HasFlatProlongationAt.of_equiv` along the base-changed isomorphism, and
the tame quadratic quotient is composed with the inverse isomorphism. -/
lemma isHardlyRamified_conj {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Free R M]
    {N : Type v} [AddCommGroup N] [Module R N] [Module.Finite R N]
    [Module.Free R N]
    {hdimM : Module.rank R M = 2} (hdimN : Module.rank R N = 2)
    {ρ : GaloisRep ℚ R M} (h : IsHardlyRamified hℓOdd hdimM ρ)
    (e : M ≃ₗ[R] N) :
    IsHardlyRamified hℓOdd hdimN (ρ.conj e) := by
  constructor
  · -- determinant: conjugation-invariant
    intro g
    rw [GaloisRep.det_apply, GaloisRep.conj_apply, LinearEquiv.conj_apply,
      LinearMap.comp_assoc, LinearMap.det_conj]
    exact h.det g
  · -- unramifiedness: the kernel of the local representation only grows
    intro p hp hpp
    have hun := h.isUnramified p hp hpp
    refine ⟨le_trans hun.localInertiaGroup_le ?_⟩
    intro σ hσ
    have h1 : ρ.toLocal hp.toHeightOneSpectrumRingOfIntegersRat σ = 1 := hσ
    show (ρ.conj e).toLocal hp.toHeightOneSpectrumRingOfIntegersRat σ = 1
    rw [GaloisRep.toLocal_apply, GaloisRep.conj_apply,
      ← GaloisRep.toLocal_apply, h1]
    refine LinearMap.ext fun w => ?_
    simp
  · -- flatness: transport along the base-changed equivariant isomorphism
    constructor
    intro I hI
    refine (h.isFlat.cond I hI).of_equiv _
      (LinearEquiv.baseChange R (R ⧸ I) M N e).toAddEquiv ?_
    intro g x
    show (LinearEquiv.baseChange R (R ⧸ I) M N e)
        (((ρ.baseChange (R ⧸ I)).toLocal
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
            (Fact.out : ℓ.Prime)) g) x) =
      (((ρ.conj e).baseChange (R ⧸ I)).toLocal
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
            (Fact.out : ℓ.Prime)) g)
        ((LinearEquiv.baseChange R (R ⧸ I) M N e) x)
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul c m =>
      simp only [GaloisRep.toLocal_apply, GaloisRep.baseChange_tmul,
        LinearEquiv.baseChange_tmul, GaloisRep.conj_apply,
        LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  · -- tameness at 2: compose the quotient with the inverse isomorphism
    obtain ⟨π, hπsurj, δ, hδ⟩ := h.isTameAtTwo
    refine ⟨π.comp (e.symm : N →ₗ[R] M), ?_, δ, ?_⟩
    · intro r
      obtain ⟨m, hm⟩ := hπsurj r
      exact ⟨e m, by simp [hm]⟩
    · intro g w
      refine ⟨?_, (hδ 1 0).2.1, (hδ 1 0).2.2⟩
      have h1 := (hδ g (e.symm w)).1
      show π (e.symm ((ρ.conj e).map (algebraMap ℚ ℚ_[2]) g w)) =
        δ g (π (e.symm w))
      rw [GaloisRep.map_apply, GaloisRep.conj_apply,
        LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply,
        ← GaloisRep.map_apply, h1]

set_option backward.isDefEq.respectTransparency false in
open scoped TensorProduct in
/-- **The Khare–Wintenberger lift, packaged** (generalized B6a): an
irreducible hardly ramified mod-`ℓ` representation over the finite
coefficient field `k`, `ℓ ≥ 5`, admits a hardly ramified `ℓ`-adic lift
over a characteristic-zero local topological domain `O` finite over
`ℤ_ℓ` with the `ℤ_ℓ`-module topology, together with a surjective
reduction `π : O →+* k` matching the Frobenius characteristic
polynomials at every prime `q ∉ {2, ℓ}`.

DERIVED from the Khare–Wintenberger core `exists_finite_lift` by
commutative algebra (this is the historical derivation of `Lift.lean`'s
`exists_hardlyRamifiedLift`, which now delegates here): `ℓ` is not
nilpotent in `R` (characteristic-zero injectivity), so some prime `P`
of `R` avoids it, and — every nonzero element of `ℤ_ℓ` being a unit
times a power of `ℓ` — `P` lies over `(0) ⊆ ℤ_ℓ`. The quotient
`O := R ⧸ P` is a characteristic-zero local topological domain, finite
over `ℤ_ℓ` with the `ℤ_ℓ`-module topology; the reduction map factors
through it (`P ⊆ 𝔪 = ker π`, the kernel being maximal because
`R/ker π` is a finite domain), and the characteristic polynomials of
Frobenius transport through the specialization by
`charpoly_baseChange_conj`. Hardly-ramifiedness specializes by
`isHardlyRamified_baseChange_quotient` + `isHardlyRamified_conj`.

This statement mirrors VERBATIM pillar α of
`Modularity/KhareWintenberger.lean`
(`exists_hardlyRamified_lift_residual_of_five_le`), which it
discharges; it lives here — in a module importing neither `Family.lean`
nor the modularity interface — so that both `Lift.lean` (at
`k = ZMod ℓ`) and the Khare–Wintenberger cut consume the SAME
deformation development without closing the interface's forbidden
cycle. -/
theorem exists_hardlyRamified_lift_of_five_le (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible) :
    ∃ (O : Type u) (_ : CommRing O) (_ : IsDomain O) (_ : TopologicalSpace O)
      (_ : IsTopologicalRing O) (_ : Algebra ℤ_[ℓ] O) (_ : IsLocalRing O)
      (_ : Module.Finite ℤ_[ℓ] O) (_ : IsModuleTopology ℤ_[ℓ] O)
      (_ : Function.Injective (algebraMap ℤ_[ℓ] O))
      (ρ : GaloisRep ℚ O (Fin 2 → O))
      (hrank : Module.rank O (Fin 2 → O) = 2)
      (_ : IsHardlyRamified hℓOdd hrank ρ)
      (π : O →+* k) (_ : Function.Surjective π),
      ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
        (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
          ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat := by
  classical
  obtain ⟨R, iR1, iR2, iR3, iR4, iR5, iR6, iR7, hinj, ρR, hρR, πR, hπRs,
    hπR⟩ := exists_finite_lift hℓOdd hdim hℓ5 h hirr
  letI := iR1; letI := iR2; letI := iR3; letI := iR4; letI := iR5
  letI := iR6; letI := iR7
  -- Step 1: a prime of `R` lying over `(0) ⊆ ℤ_ℓ`.
  obtain ⟨P, hPp, hP0⟩ : ∃ P : Ideal R, P.IsPrime ∧
      ∀ x : ℤ_[ℓ], algebraMap ℤ_[ℓ] R x ∈ P → x = 0 := by
    have hℓR : algebraMap ℤ_[ℓ] R (ℓ : ℤ_[ℓ]) ∉ nilradical R := by
      rw [mem_nilradical]
      rintro ⟨n, hn⟩
      rw [← map_pow] at hn
      exact pow_ne_zero n
        (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero)
        (hinj (hn.trans (map_zero (algebraMap ℤ_[ℓ] R)).symm))
    obtain ⟨P, hPp, hℓP⟩ : ∃ P : Ideal R, Ideal.IsPrime P ∧
        algebraMap ℤ_[ℓ] R (ℓ : ℤ_[ℓ]) ∉ P := by
      by_contra hcon
      push Not at hcon
      refine hℓR ?_
      rw [nilradical_eq_sInf]
      exact Submodule.mem_sInf.mpr fun J hJ => hcon J hJ
    refine ⟨P, hPp, fun x hx => by_contra fun hx0 => ?_⟩
    rw [PadicInt.unitCoeff_spec hx0, map_mul, map_pow] at hx
    rcases hPp.mem_or_mem hx with hu | hpow
    · exact hPp.ne_top (Ideal.eq_top_of_isUnit_mem P hu
        (IsUnit.map (algebraMap ℤ_[ℓ] R) (PadicInt.unitCoeff hx0).isUnit))
    · exact hℓP (hPp.mem_of_pow_mem _ hpow)
  haveI := hPp
  -- Step 2: `O := R ⧸ P` is a local topological domain of characteristic
  -- zero, finite over `ℤ_ℓ` with the `ℤ_ℓ`-module topology.
  have hloc : IsLocalRing (R ⧸ P) :=
    .of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  letI := hloc
  have hfin : Module.Finite ℤ_[ℓ] (R ⧸ P) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ_[ℓ] P).toLinearMap
      (Ideal.Quotient.mkₐ_surjective ℤ_[ℓ] P)
  letI := hfin
  have hmt : IsModuleTopology ℤ_[ℓ] (R ⧸ P) := by
    constructor
    have hquot :=
      (QuotientRing.isOpenQuotientMap_mk P).isQuotientMap.eq_coinduced
    have hmod := ModuleTopology.eq_coinduced_of_surjective
      (φ := (Ideal.Quotient.mkₐ ℤ_[ℓ] P).toLinearMap)
      (Ideal.Quotient.mkₐ_surjective ℤ_[ℓ] P)
    rw [hquot, hmod]
    rfl
  letI := hmt
  have hinjO : Function.Injective (algebraMap ℤ_[ℓ] (R ⧸ P)) := by
    refine (injective_iff_map_eq_zero _).mpr fun x hx => hP0 x ?_
    rwa [IsScalarTower.algebraMap_apply ℤ_[ℓ] R (R ⧸ P),
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at hx
  -- Step 3: specialize the framed representation along `R → R ⧸ P`.
  let e : (R ⧸ P) ⊗[R] (Fin 2 → R) ≃ₗ[R ⧸ P] (Fin 2 → R ⧸ P) :=
    TensorProduct.piScalarRight R (R ⧸ P) (R ⧸ P) (Fin 2)
  let ρO : FramedGaloisRep ℚ (R ⧸ P) (Fin 2) := (ρR.baseChange (R ⧸ P)).conj e
  have hrankQ : Module.rank (R ⧸ P) ((R ⧸ P) ⊗[R] (Fin 2 → R)) = 2 := by
    rw [Module.rank_baseChange, rank_finTwoFun]
    simp
  have hHRO : IsHardlyRamified hℓOdd (rank_finTwoFun (R ⧸ P)) ρO :=
    isHardlyRamified_conj hℓOdd (rank_finTwoFun (R ⧸ P))
      (isHardlyRamified_baseChange_quotient hℓOdd P hrankQ hρR) e
  -- Step 4: the reduction map factors through the quotient: `ker πR` is
  -- maximal (its quotient is a finite domain, hence a field), so it is the
  -- maximal ideal of the local ring `R`, which contains the prime `P`.
  have hPle : P ≤ RingHom.ker πR := by
    haveI : (RingHom.ker πR).IsPrime := RingHom.ker_isPrime πR
    haveI : Finite (R ⧸ RingHom.ker πR) :=
      Finite.of_equiv _ (RingHom.quotientKerEquivRange πR).symm.toEquiv
    calc P ≤ IsLocalRing.maximalIdeal R :=
          IsLocalRing.le_maximalIdeal hPp.ne_top
      _ = RingHom.ker πR := (IsLocalRing.eq_maximalIdeal
          (Ideal.Quotient.maximal_of_isField _
            (Finite.isField_of_domain (R ⧸ RingHom.ker πR)))).symm
  let πO : R ⧸ P →+* k :=
    Ideal.Quotient.lift P πR fun a ha => by
      rw [← RingHom.mem_ker]
      exact hPle ha
  have hπOs : Function.Surjective πO := by
    intro y
    obtain ⟨x, hx⟩ := hπRs y
    refine ⟨Ideal.Quotient.mk P x, ?_⟩
    rw [show πO (Ideal.Quotient.mk P x) = πR x from
      Ideal.Quotient.lift_mk P πR _]
    exact hx
  -- Step 5: assemble; the characteristic polynomials of Frobenius
  -- transport through the specialization.
  have hcompat : ∀ q (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρO.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map πO =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat := by
    intro q hq hq2 hqℓ
    have hcf : ρO.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
        (ρR.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map
          (algebraMap R (R ⧸ P)) :=
      charpoly_baseChange_conj ρR e
        (globalFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    have hπcomp : πO.comp (algebraMap R (R ⧸ P)) = πR := by
      ext a
      rw [RingHom.comp_apply, Ideal.Quotient.algebraMap_eq]
      exact Ideal.Quotient.lift_mk P πR _
    rw [hcf, Polynomial.map_map, hπcomp]
    exact hπR q hq hq2 hqℓ
  exact ⟨R ⧸ P, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hloc, hfin, hmt, hinjO, ρO, rank_finTwoFun (R ⧸ P),
    hHRO, πO, hπOs, hcompat⟩

end GaloisRepresentation
