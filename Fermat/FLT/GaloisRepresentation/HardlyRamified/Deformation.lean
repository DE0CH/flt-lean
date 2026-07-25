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
- `exists_isStrictlyUniversalOnFrames_of_deformationCondition`
- `hasFlatProlongationAt_of_pi_surjection`
- `isFlatAt_of_fibreProduct`
- `isTameAtTwo_of_fibreProduct`
- `finite_setOf_isHardlyRamified_frames_of_discreteTopology`
- `isTameAtTwo_of_forall_isOpen_quotient`
- `exists_ringHom_matrix_quotient_of_finite`
- `exists_pow_comap_le_pow_maximalIdeal_traceSubring`
- `fg_comap_maximalIdeal_traceSubring`
- `exists_framedGaloisRep_traceSubring`
- `subring_closure_charFrob_coeff_eq_top`
- `exists_finiteIndex_isIntegral_charpolyCoeff_quotient_of_isWeaklyUniversal_isTraceGenerated`
- `exists_relations_lt_le_smul_of_minimal_mvPowerSeries_presentation`

Both former strata above them were narrowed on 2026-07-25 into those
leaves, and every statement they replace is now PROVEN here — including
the surjectivity and minimality strata of the minimal presentation,
`surjective_of_mvPowerSeries_ringHom` and
`ker_le_of_minimal_mvPowerSeries_ringHom`, PROVEN the same day.

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
  commutative-algebra/topology pro-finite limit — PROVEN 2026-07-25,
  leaving only its level step `exists_ringHom_matrix_quotient_of_finite`);
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
  sends it to `−1`) — leaving H3 and the deformation-theoretic core as
  the two leaves of that cut; the core has since been proven as well (the
  next item), so **H3 is the only leaf of the 2026-07-26 cut still open**.
* That deformation-theoretic core was CUT AGAIN (2026-07-25) along the
  seam between Schlessinger's abstract machine and the arithmetic, and is
  now PROVEN as an assembly. Everything specific to the hardly ramified
  problem enters an application of Schlessinger's theorem through the
  statement that the four local conditions form a DEFORMATION CONDITION
  (Mazur §§18–23, Conrad–Diamond–Taylor §2): closed under pushforward
  along maps of Artinian coefficient rings, under gluing along fibre
  products (H1, H2), and under passage to the pro-limit. So the core
  became the arithmetic-free
  `exists_isStrictlyUniversalOnFrames_of_deformationCondition` plus those
  three clauses — the first of which is PROVEN here, as
  `isHardlyRamified_pushforwardFrame` over the single flatness leaf
  `isFlatAt_baseChange` (this needed the base-change transfer block,
  formerly ~2900 lines below, to be hoisted; the hoist is a separate
  commit) — plus `finite_setOf_isHardlyRamified_frames_of_discreteTopology`,
  which closes a genuine gap: the raw test objects of
  `IsStrictlyUniversalOnFrames` carry an ARBITRARY finite ring topology,
  while the H3 leaf is stated for the discrete one, and a finite local
  ring does admit strictly coarser ring topologies.
* The two PRESENTATION leaves became proven assemblies over the four
  commutative-algebra strata of the minimal presentation and the
  arithmetic relation count: `exists_minimal_mvPowerSeries_presentation`
  is PROVEN over the Cohen coefficient ring
  `exists_coefficientRing_ringHom` (itself PROVEN 2026-07-25, WITHOUT
  Witt vectors — the residue field is finite, hence monogenic, so the
  unramified lift is an `AdjoinRoot`; see its docstring), the convergent
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
  That geometric form was itself PROVEN on 2026-07-25, over the TRACE
  form `isIntegral_charFrobCoeff_quotient_of_isWeaklyUniversal_isTraceGenerated`
  (the Frobenius traces of the mod-`ℓ` specialization are algebraic over
  `𝔽_ℓ`) and the pure commutative algebra
  `eq_maximalIdeal_of_isPrime_of_isIntegral_quotient`. The TRACE form was
  in turn PROVEN on 2026-07-26 over the potential-modularity leaf
  `exists_finiteIndex_isIntegral_charpolyCoeff_quotient_of_isWeaklyUniversal_isTraceGenerated`
  (there is a FINITE-INDEX `H ≤ G_ℚ` — the Galois group of the totally
  real field over which potential modularity gives `R = T` with `T` a
  finite `ℤ_ℓ`-algebra — on which all traces are already integral), the
  Khare–Wintenberger descent from `H` back to `ℚ` being the elementary
  `isIntegral_trace_of_isIntegral_trace_pow` (the Dickson identity
  `tr(Mᵐ) = Dₘ(tr M, det M)` with `Dₘ` monic of degree `m`) together with
  `exists_pow_mem_of_finiteIndex`; the determinant coefficient is a
  cyclotomic value, and the remaining coefficients are `1` and `0`.

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
  `k = 𝔽_ℓ` (the Frey-curve consumer in `Lift.lean`).

  AUDITED 2026-07-25, VERDICT ON THAT LEAF: it is NOT dischargeable and
  no proof effort should be dispatched at it. Quantified over `k` it is
  EQUIVALENT to the ch. 4 headline
  `not_isIrreducible_of_isHardlyRamified_of_five_le`, because every
  hypothesis it carries is stable under extension of the coefficient
  field while its conclusion is not; and the consuming cone does not
  force `k = 𝔽_ℓ` (`Modularity/Interface.lean` consumes pillar α at the
  residue field of an arbitrary local coefficient ring). The fix is an
  interface change, not a proof: take `traceSubring` and
  `IsTraceGenerated` over the Cohen coefficient ring `Λ ≅ W(k)` that
  this module's own `exists_coefficientRing_ringHom` already produces,
  rather than over `ℤ_ℓ`, whereupon the descended datum's
  `π_surjective` is free and this leaf disappears. See the leaf's
  docstring for the full argument and the second, costlier route
  (descend `ρbar` to its trace field, lift, base change back up).

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
-- proof-only: the Stacks 05GH / Matsumura 8.4 commutative-algebra node
-- "complete local + `𝔪` finitely generated ⟹ Noetherian", split into its
-- own module (it is pure commutative algebra over mathlib alone, and this
-- file is already 15k lines, so it elaborates on its own core).
import Fermat.FLT.GaloisRepresentation.HardlyRamified.CompleteLocalNoetherian
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
-- proof-only: Krull's INTERSECTION theorem `Ideal.iInf_pow_eq_bot_of_isDomain`
-- and the `ZMod ℓ`-algebra structure of a characteristic-`ℓ` ring — the two
-- ingredients of the mod-`ℓ` fibre glue
-- `eq_maximalIdeal_of_isPrime_of_isIntegral_quotient`.
import Mathlib.RingTheory.Filtration
import Mathlib.Algebra.Algebra.ZMod
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
-- proof-only: the two ingredients of the PROVEN surjectivity stratum
-- `surjective_of_mvPowerSeries_ringHom` — mathlib's complete-Nakayama
-- criterion `surjective_of_mk_map_comp_surjective` (Functoriality), the
-- `(x₁,…,x_g)`-adic completeness of `MvPowerSeries` over a finite
-- variable set (Completeness), and Hausdorffness of a proper ideal in a
-- Noetherian local ring (Noetherian); plus `IsLocalHom.of_surjective`
-- and `map_nonunit`, used by both presentation strata.
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.LocalRing.RingHom.Basic
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
-- proof-only: `mul_neg_geom_sum`, the geometric series that inverts a
-- unit of a CLOSED subring inside the ambient local ring
-- (`isUnit_of_isClosed_of_notMem_maximalIdeal`).
import Mathlib.Algebra.Ring.GeomSum
-- proof-only: charpoly bridges and base-change linear algebra.
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Dimension.Constructions
-- `Subgroup.FiniteIndex` and `LinearMap.charpoly`: both appear in the
-- exposed statement of the potential-modularity leaf
-- `exists_finiteIndex_isIntegral_charpolyCoeff_quotient_of_isWeaklyUniversal_isTraceGenerated`.
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Charpoly.Basic
-- the Dickson recursion `tr(Mⁿ) = Dₙ(tr M, det M)` and the 2×2 charpoly
-- coefficient dictionary, the two ingredients of the descent glue
-- `isIntegral_trace_of_isIntegral_trace_pow`; and integral transitivity
-- through `integralClosure`. All three are exposed in the statements of
-- that glue and of the Dickson lemmas it rests on.
public import Mathlib.RingTheory.Polynomial.Dickson
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
-- proof-only: the Cohen coefficient ring `exists_coefficientRing_ringHom`
-- is built as `AdjoinRoot` of a monic `ℤ_ℓ`-lift of the minimal
-- polynomial of a generator of `kˣ`, so it needs the `AdjoinRoot`
-- package (power basis, `lift`, domain-from-prime), the coefficientwise
-- lifting of polynomials along the surjection `ℤ_[ℓ] ↠ ZMod ℓ`, the
-- reduction criterion for irreducibility, the `ZMod ℓ`-algebra structure
-- on a ring of characteristic `ℓ`, separability over the perfect field
-- `ZMod ℓ`, Hensel's lemma in the `𝔪`-adically complete `R`, going-up
-- for the integral extension `ℤ_[ℓ] → Λ`, and `Shrink` to move the
-- resulting `Type 0` ring into `k`'s universe.
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.Algebra.Algebra.Shrink
-- proof-only: the pro-finite limit machinery of
-- `isWeaklyUniversalOnIdentifiedFrames_of_finite` — the tower of quotients
-- `R ⧸ 𝔪ⁿ` with its transition maps (`Ideal.Quotient.factorPow`), Kőnig's
-- lemma for inverse systems of nonempty finite sets
-- (`nonempty_sections_of_finite_inverse_system`), the universal property of
-- adic completeness for ring homomorphisms (`IsAdicComplete.liftRingHom`),
-- the polynomial ring that carries the conjugating matrix through that
-- universal property, and the matrix/linear-equivalence dictionary.
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

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
    (P : Ideal R) [IsLocalRing (R ⧸ P)]
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
    (P : Ideal R) [IsLocalRing (R ⧸ P)]
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

open scoped TensorProduct in
/-- **Pushforward of a framed representation along a continuous ring
homomorphism**: base change along `ψ.toAlgebra`, followed by the standard
identification `A ⊗_B (Fin 2 → B) ≅ (Fin 2 → A)`
(`TensorProduct.piScalarRight`) — concretely, "apply `ψ` to the matrix
entries of `ρ`".

Bundled as a definition rather than written inline because the base
change needs an `Algebra B A` and a `ContinuousSMul B A` in scope, so the
inline form drags a `letI` block into every statement that mentions it
(the elaborator constraint already recorded on `IsResidualIdentified` and
`IsStrictlyUniversalOnFrames`). Every leaf of the deformation-condition
cut below is phrased through it, which is what lets the assembly
`exists_isStrictlyUniversalOnFrames_of_finite_lifts` discharge the
hypotheses of its core leaf by name.

This is the CANONICAL pushforward, carrying no framing ambiguity; the
universality predicates deliberately quantify over an arbitrary framing
`e` instead, because a classifying map only ever determines the
pushforward up to the choice of frame. -/
noncomputable def pushforwardFrame {B : Type u} [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] (ψ : B →+* A)
    (hψ : Continuous ψ) (ρ : FramedGaloisRep ℚ B (Fin 2)) :
    FramedGaloisRep ℚ A (Fin 2) :=
  letI : Algebra B A := ψ.toAlgebra
  letI : ContinuousSMul B A := continuousSMul_of_algebraMap B A
    (by rw [RingHom.algebraMap_toAlgebra]; exact hψ)
  (ρ.baseChange A).conj (TensorProduct.piScalarRight B A A (Fin 2))

/-- **Raynaud closure for flat prolongations, in surjection-from-a-finite-power
form** (sorry node, cut 2026-07-25 out of `isFlatAt_baseChange` below): if the
local space of `ρ₁` is the geometric-point group of a finite flat group scheme
over `𝒪ᵥ`, then so is every `Γ Kᵥ`-equivariant additive QUOTIENT of a finite
POWER of it.

This is the only genuinely deep input to `isFlatAt_baseChange`: everything else
in that proof is tensor plumbing, carried out below. Mathematically it is the
statement that the essential image of the generic-fibre functor
(finite flat group schemes over the DVR `𝒪ᵥ`) ⟶ (finite `Γ Kᵥ`-modules)
is closed under finite products and under equivariant quotients. Products are
represented by the tensor product of the Hopf algebras; quotients come from the
schematic-closure construction — an equivariant surjection of point groups is
induced by a surjection of the finite étale generic-fibre Hopf algebras, and the
image of a Hopf order under a surjective bialgebra map is again a Hopf order.
Note that the EXISTENCE direction used here needs no `e < ℓ − 1` bound; Raynaud's
bound enters only for the UNIQUENESS of the prolongation, which is not asserted.

DUPLICATION / HOME AUDIT (please read before restating this anywhere). Two
other copies of this content already exist in the tree, both import-unreachable
from this module:
* `IsFlatPointsGroupAt.of_surjective` in `Modularity/Interface.lean`, a PROVEN
  assembly over the single leaf `exists_etale_subBialgebra_of_points_surjective`
  — together with `IsFlatPointsGroupAt.pi` it is exactly this statement;
* `hasFlatProlongationAt_of_surjective` in `Modularity/KhareWintenberger.lean`,
  a `sorry` in the `n = 1` special case of this one.
Both live ABOVE this module (`Interface` imports `KhareWintenberger`, which
imports this file), so neither can be consumed here — the circularity guard at
the head of this module forbids importing `Modularity/*`. The declaration below
is therefore the LOWEST home for the content and strictly generalizes
KhareWintenberger's copy (take `n = 1`); whoever unifies them should redirect
both upward copies at this one — or move this one further down still, into
`Deformations/RepresentationTheory/FlatProlongation.lean`, which is the neutral
home KhareWintenberger's own audit nominates — rather than adding a fourth.

References: Raynaud, *Schémas en groupes de type `(p,…,p)`*, Bull. SMF 102
(1974), §3; Tate–Oort, *A classification of group schemes of order p*, Ann.
Sci. ÉNS 3 (1970). -/
theorem hasFlatProlongationAt_of_pi_surjection
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    {A₁ : Type*} [CommRing A₁] [TopologicalSpace A₁]
    {M₁ : Type*} [AddCommGroup M₁] [Module A₁ M₁]
    {A₂ : Type*} [CommRing A₂] [TopologicalSpace A₂]
    {M₂ : Type*} [AddCommGroup M₂] [Module A₂ M₂]
    {ρ₁ : GaloisRep ℚ A₁ M₁} {ρ₂ : GaloisRep ℚ A₂ M₂} (n : ℕ)
    (h : ρ₁.HasFlatProlongationAt w)
    (π : (Fin n → (ρ₁.toLocal w).Space) →+ (ρ₂.toLocal w).Space)
    (hsurj : Function.Surjective π)
    (hequiv : ∀ (g : Field.absoluteGaloisGroup
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ w))
        (x : Fin n → (ρ₁.toLocal w).Space), π (g • x) = g • π x) :
    ρ₂.HasFlatProlongationAt w :=
  sorry

set_option backward.isDefEq.respectTransparency false in
open scoped TensorProduct in
/-- **Flatness at `ℓ` transfers along an arbitrary base change to a
FINITE coefficient algebra** (PROVEN 2026-07-25 over the single Raynaud
leaf `hasFlatProlongationAt_of_pi_surjection` above — Ramakrishna's half
of "the hardly ramified conditions form a deformation condition"; the
QUOTIENT case is the PROVEN `isFlatAt_baseChange_quotient` just above,
and this is the general-coefficient-map form that the Schlessinger cut
below needs).

Route (the quotient proof does NOT cover this: it identifies
`((R ⧸ P) ⧸ I)` with a quotient `R ⧸ J` of `R` itself, which is exactly
what a general coefficient map does not give you). Let `I` be an open
ideal of `B` and put `J := (algebraMap R B)⁻¹ I`, an open ideal of `R`
because the structure map is continuous (`ContinuousSMul R B`, whence
`continuous_algebraMap`). `hflat` then supplies a finite flat
prolongation of `(R ⧸ J) ⊗_R M`, and what remains is that the
prolongation survives the COEFFICIENT EXTENSION `R ⧸ J → B ⧸ I` of
finite rings.

That is done as an explicit equivariant SURJECTION rather than through a
second tensor cancellation, which is what keeps the cut shallow: `B ⧸ I`
is finite, so enumerating it as `b₀, …, b_{n−1}` gives an additive
surjection
`(Fin n → (R ⧸ J) ⊗_R M) ↠ (B ⧸ I) ⊗_R M`, `(xᵢ) ↦ Σᵢ bᵢ • ι(xᵢ)`,
where `ι` is `id ⊗ (R ⧸ J → B ⧸ I)`; surjectivity holds already on the
generators `c ⊗ m = b_{e(c)} • (1 ⊗ m)`, and `Γ Kᵥ`-equivariance holds
because the Galois action lives on the `M`-factor while both `bᵢ • −`
and `ι` act on the coefficient factor. Composing with the inverse of
`TensorProduct.AlgebraTensorModule.cancelBaseChange`, which identifies
`(B ⧸ I) ⊗_B (B ⊗_R M)` — the space actually named by the goal — with
`(B ⧸ I) ⊗_R M`, this is exactly the hypothesis of
`hasFlatProlongationAt_of_pi_surjection`. Crucially this route needs NO
`(R ⧸ J)`-algebra structure on `B ⧸ I`, and in particular neither
`IsScalarTower R (R ⧸ J) (B ⧸ I)` nor `ContinuousSMul (R ⧸ J) (B ⧸ I)`,
neither of which is available as an instance.

WHY `[Finite B]` IS PART OF THE STATEMENT AND NOT A CONVENIENCE (found
2026-07-25 while cutting this leaf; the unrestricted form is FALSE).
`GaloisRep.HasFlatProlongationAt` demands a Hopf algebra `G` that is
`Module.Finite` and `Module.Flat` over `𝒪ᵥ` together with a BIJECTION
from its geometric points onto the space of the local representation.
A finite flat `𝒪ᵥ`-algebra has only finitely many geometric points, so
`HasFlatProlongationAt` forces the space to be FINITE — hence `IsFlatAt`
forces `(B ⧸ I) ⊗_R M` to be finite for every open ideal `I` of `B`.
Dropping `[Finite B]` therefore makes the conclusion fail for, say, `B`
an infinite discrete `𝔽_ℓ`-algebra over `R = 𝔽_ℓ`, where the source
`ρ` is flat and the target space is infinite. Every consumer of this
lemma lives in the Artinian (equivalently finite) category, so the
restriction costs nothing.

References: Ramakrishna, *On a variation of Mazur's deformation
functor*, Compositio 87 (1994), §1; Raynaud, *Schémas en groupes de type
`(p,…,p)`*, Bull. SMF 102 (1974), Thm. 3.3.1; Conrad–Diamond–Taylor,
JAMS 12 (1999), §2. -/
theorem isFlatAt_baseChange {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Free R M]
    (B : Type*) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLocalRing B] [Finite B] [Algebra R B] [ContinuousSMul R B]
    {ρ : GaloisRep ℚ R M}
    (hflat : ρ.IsFlatAt
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : ℓ.Prime))) :
    (ρ.baseChange B).IsFlatAt
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : ℓ.Prime)) := by
  classical
  set w := Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : ℓ.Prime)
  constructor
  intro I hI
  -- the contracted open ideal of `R`
  set J : Ideal R := I.comap (algebraMap R B)
  have hJopen : IsOpen (J : Set R) := hI.preimage (continuous_algebraMap R B)
  have hflatJ : (ρ.baseChange (R ⧸ J)).HasFlatProlongationAt w := hflat.cond J hJopen
  -- an enumeration of the finite ring `B ⧸ I`
  haveI : Finite (B ⧸ I) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨n, ⟨enum⟩⟩ := Finite.exists_equiv_fin (B ⧸ I)
  -- the coefficient map `R ⧸ J → B ⧸ I`, `R`-linearly
  let cmap : (R ⧸ J) →ₗ[R] (B ⧸ I) :=
    Submodule.liftQ J (Algebra.linearMap R (B ⧸ I)) (by
      intro r hr
      show algebraMap R (B ⧸ I) r = 0
      rw [IsScalarTower.algebraMap_apply R B (B ⧸ I)]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hr)
  have hcmap : ∀ r : R, cmap (Ideal.Quotient.mk J r) = algebraMap R (B ⧸ I) r :=
    fun _ => rfl
  let ι : ((R ⧸ J) ⊗[R] M) →ₗ[R] ((B ⧸ I) ⊗[R] M) := LinearMap.rTensor M cmap
  let can := TensorProduct.AlgebraTensorModule.cancelBaseChange R B (B ⧸ I) (B ⧸ I) M
  -- the equivariant surjection out of a finite power of `(R ⧸ J) ⊗ M`
  let π₀ : (Fin n → ((R ⧸ J) ⊗[R] M)) →+ ((B ⧸ I) ⊗[R] M) :=
    { toFun := fun x => ∑ i, (enum.symm i) • ι (x i)
      map_zero' := by simp
      map_add' := fun x y => by simp [smul_add, Finset.sum_add_distrib] }
  let π : (Fin n → ((ρ.baseChange (R ⧸ J)).toLocal w).Space) →+
      (((ρ.baseChange B).baseChange (B ⧸ I)).toLocal w).Space :=
    (can.symm.toAddEquiv.toAddMonoidHom).comp π₀
  refine hasFlatProlongationAt_of_pi_surjection w n hflatJ π ?_ ?_
  · -- surjectivity: already on the generators `c ⊗ m = b_{e c} • (1 ⊗ m)`
    have hsurj0 : Function.Surjective π₀ := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => exact ⟨0, map_zero _⟩
      | tmul c m =>
        refine ⟨(Pi.single (enum c) ((1 : R ⧸ J) ⊗ₜ[R] m) :
          Fin n → ((R ⧸ J) ⊗[R] M)), ?_⟩
        show ∑ i, (enum.symm i) • ι ((Pi.single (enum c) ((1 : R ⧸ J) ⊗ₜ[R] m) :
          Fin n → ((R ⧸ J) ⊗[R] M)) i) = c ⊗ₜ[R] m
        rw [Finset.sum_eq_single_of_mem (enum c) (Finset.mem_univ _)]
        · rw [Pi.single_eq_same]
          show (enum.symm (enum c)) • (cmap 1 ⊗ₜ[R] m) = c ⊗ₜ[R] m
          rw [Equiv.symm_apply_apply,
            show cmap 1 = 1 from (hcmap 1).trans (map_one _)]
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        · intro i _ hne
          rw [Pi.single_eq_of_ne hne]
          simp
      | add a b ha hb =>
        obtain ⟨u, hu⟩ := ha
        obtain ⟨t, ht⟩ := hb
        exact ⟨u + t, by rw [map_add, hu, ht]⟩
    exact can.symm.surjective.comp hsurj0
  · -- `Γ Kᵥ`-equivariance: the action is on the `M`-factor throughout
    intro g x
    have key : ∀ (i : Fin n) (y : (R ⧸ J) ⊗[R] M),
        can.symm ((enum.symm i) • ι (((ρ.baseChange (R ⧸ J)).toLocal w) g y))
          = (((ρ.baseChange B).baseChange (B ⧸ I)).toLocal w) g
              (can.symm ((enum.symm i) • ι y)) := by
      intro i y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [map_add, smul_add, ha, hb]
      | tmul a m => rfl
    show can.symm (∑ i, (enum.symm i) • ι (((ρ.baseChange (R ⧸ J)).toLocal w) g (x i)))
        = (((ρ.baseChange B).baseChange (B ⧸ I)).toLocal w) g
            (can.symm (∑ i, (enum.symm i) • ι (x i)))
    rw [map_sum, map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => key i (x i)

set_option backward.isDefEq.respectTransparency false in
open scoped TensorProduct in
/-- **Hardly-ramifiedness transfers along an arbitrary base change to a
FINITE coefficient algebra** (PROVEN 2026-07-25 over the single leaf
`isFlatAt_baseChange`, everything else being already available in this
module): the general-coefficient-map form of
`isHardlyRamified_baseChange_quotient`, which is the shape Schlessinger's
functoriality needs — the deformation functor must push a lift forward
along EVERY map of Artinian coefficient rings, not only along
surjections.

Same four clauses, same proofs: the determinant maps along the structure
morphism (`LinearMap.det_baseChange`, then `IsScalarTower` for the
`ℤ_ℓ`-compatibility — which is the substitute for the quotient case's
`IsScalarTower.algebraMap_apply`), unramifiedness passes to any base
change by the existing instance, tameness at `2` is the already general
`isTameAtTwo_baseChange`, and flatness at `ℓ` is the one genuinely open
clause, isolated as `isFlatAt_baseChange` above. -/
lemma isHardlyRamified_baseChange {R : Type u} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    [Algebra ℤ_[ℓ] R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Free R M] {hdimM : Module.rank R M = 2}
    (B : Type u) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLocalRing B] [Finite B] [Algebra ℤ_[ℓ] B] [Algebra R B]
    [ContinuousSMul R B] [IsScalarTower ℤ_[ℓ] R B]
    (hdimB : Module.rank B (B ⊗[R] M) = 2)
    {ρ : GaloisRep ℚ R M} (h : IsHardlyRamified hℓOdd hdimM ρ) :
    IsHardlyRamified hℓOdd hdimB (ρ.baseChange B) := by
  constructor
  · -- the determinant maps along the structure morphism
    intro g
    have hdet : (ρ.baseChange B).det g = algebraMap R B (ρ.det g) := by
      show LinearMap.det ((ρ.baseChange B) g) = _
      rw [show ((ρ.baseChange B) g : Module.End B (B ⊗[R] M)) =
        LinearMap.baseChange B (ρ g) from rfl, LinearMap.det_baseChange]
      rfl
    rw [hdet, h.det g, ← IsScalarTower.algebraMap_apply]
  · -- unramifiedness passes to the base change (existing instance)
    intro p hp hpp
    letI : ρ.IsUnramifiedAt hp.toHeightOneSpectrumRingOfIntegersRat :=
      h.isUnramified p hp hpp
    infer_instance
  · -- flatness at `ℓ` (the sorried transfer leaf)
    exact isFlatAt_baseChange B h.isFlat
  · -- tameness at `2` (proven transfer)
    exact isTameAtTwo_baseChange B h.isTameAtTwo

set_option backward.isDefEq.respectTransparency false in
open scoped TensorProduct in
/-- **Hardly-ramifiedness of a pushed-forward frame** (PROVEN 2026-07-25):
`pushforwardFrame` applied to a hardly ramified framed representation is
hardly ramified, provided the pushforward map is a `ℤ_ℓ`-algebra map
(`halg`) and the target is finite.

This is `isHardlyRamified_baseChange` (which supplies the base change)
composed with `isHardlyRamified_conj` (which absorbs the framing
identification `A ⊗_B (Fin 2 → B) ≅ (Fin 2 → A)`), exactly the two-step
pattern of `exists_hardlyRamified_lift_of_five_le`'s specialization step.
`halg` is what manufactures the `IsScalarTower ℤ_[ℓ] B A` instance, the
`ℤ_ℓ`-structure being what the cyclotomic determinant condition is
stated against.

It is Schlessinger's functoriality clause: the framed hardly ramified
lifts form a FUNCTOR on the Artinian category, which is the hypothesis
`hbase` of the core leaf below. -/
theorem isHardlyRamified_pushforwardFrame
    {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLocalRing B] [Algebra ℤ_[ℓ] B]
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLocalRing A] [Finite A] [Algebra ℤ_[ℓ] A]
    (ψ : B →+* A) (hψ : Continuous ψ)
    (halg : ψ.comp (algebraMap ℤ_[ℓ] B) = algebraMap ℤ_[ℓ] A)
    {ρ : FramedGaloisRep ℚ B (Fin 2)}
    (hρ : IsHardlyRamified hℓOdd (rank_finTwoFun B) ρ) :
    IsHardlyRamified hℓOdd (rank_finTwoFun A) (pushforwardFrame ψ hψ ρ) := by
  letI : Algebra B A := ψ.toAlgebra
  letI : ContinuousSMul B A := continuousSMul_of_algebraMap B A
    (by rw [RingHom.algebraMap_toAlgebra]; exact hψ)
  letI : IsScalarTower ℤ_[ℓ] B A := IsScalarTower.of_algebraMap_eq' (by
    rw [RingHom.algebraMap_toAlgebra]
    exact halg.symm)
  have hrank : Module.rank A (A ⊗[B] (Fin 2 → B)) = 2 := by
    rw [Module.rank_baseChange, rank_finTwoFun]
    simp
  exact isHardlyRamified_conj hℓOdd (rank_finTwoFun A)
    (isHardlyRamified_baseChange hℓOdd A hrank hρ)
    (TensorProduct.piScalarRight B A A (Fin 2))

open scoped TensorProduct in
/-- **`pushforwardFrame` computed on the image of a `B`-vector** (PROVEN
2026-07-25): `pushforwardFrame ψ hψ ρ` carries `ψ ∘ v` to `ψ ∘ (ρ g v)`
— i.e. it really is "apply `ψ` to the matrix entries of `ρ`", stated in
the one form that needs no inverse of the framing identification.

`(1 : A) ⊗ₜ v` is a preimage of `ψ ∘ v` under
`TensorProduct.piScalarRight`, so `LinearEquiv.conj_apply_apply` moves
the conjugation out of the way and `GaloisRep.baseChange_tmul` finishes;
nothing has to be said about `piScalarRight.symm` on a general element,
which is a sum.

This is the handle that lets a fibre-product argument compare `ρ g` with
`1` ENTRYWISE — which is the shape the injectivity of `b ↦ (p₁ b, p₂ b)`
can act on. -/
lemma pushforwardFrame_apply_map {B : Type u} [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] (ψ : B →+* A)
    (hψ : Continuous ψ) (ρ : FramedGaloisRep ℚ B (Fin 2))
    (g : Field.absoluteGaloisGroup ℚ) (v : Fin 2 → B) (i : Fin 2) :
    pushforwardFrame ψ hψ ρ g (fun j => ψ (v j)) i = ψ (ρ g v i) := by
  letI : Algebra B A := ψ.toAlgebra
  letI : ContinuousSMul B A := continuousSMul_of_algebraMap B A
    (by rw [RingHom.algebraMap_toAlgebra]; exact hψ)
  have hsmul : ∀ (b : B) (a : A), b • a = ψ b * a := fun _ _ => rfl
  have h1 : (fun j => ψ (v j)) =
      (TensorProduct.piScalarRight B A A (Fin 2)) ((1 : A) ⊗ₜ[B] v) := by
    funext j
    rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
    simp [hsmul]
  show (((ρ.baseChange A).conj (TensorProduct.piScalarRight B A A (Fin 2))) g)
      (fun j => ψ (v j)) i = _
  rw [h1, GaloisRep.conj_apply, LinearEquiv.conj_apply_apply,
    LinearEquiv.symm_apply_apply, GaloisRep.baseChange_tmul,
    TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  simp [hsmul]

open scoped TensorProduct in
/-- **`det` commutes with `pushforwardFrame`** (PROVEN 2026-07-25):
`LinearMap.det_conj` absorbs the framing identification and
`LinearMap.det_baseChange` turns the base-changed determinant into
`algebraMap B A` of the original, which is `ψ` by
`RingHom.algebraMap_toAlgebra`.

This is the direction `isHardlyRamified_pushforwardFrame` does not need
but a fibre-product argument does: it lets a determinant identity be
REFLECTED BACK from the two projections to `B`. -/
lemma det_pushforwardFrame {B : Type u} [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] (ψ : B →+* A)
    (hψ : Continuous ψ) (ρ : FramedGaloisRep ℚ B (Fin 2))
    (g : Field.absoluteGaloisGroup ℚ) :
    (pushforwardFrame ψ hψ ρ).det g = ψ (ρ.det g) := by
  letI : Algebra B A := ψ.toAlgebra
  letI : ContinuousSMul B A := continuousSMul_of_algebraMap B A
    (by rw [RingHom.algebraMap_toAlgebra]; exact hψ)
  show LinearMap.det
    ((((ρ.baseChange A).conj (TensorProduct.piScalarRight B A A (Fin 2))) g)) = _
  rw [GaloisRep.conj_apply, LinearEquiv.conj_apply, LinearMap.comp_assoc,
    LinearMap.det_conj]
  show LinearMap.det (LinearMap.baseChange A (ρ g)) = _
  rw [LinearMap.det_baseChange, RingHom.algebraMap_toAlgebra]
  rfl

/-- **Flatness at `ℓ` glues along a fibre product** (sorry node, cut
2026-07-25 out of `isHardlyRamified_of_fibreProduct` — Ramakrishna's half
of Schlessinger's H1/H2 for the hardly ramified problem).

`B` is the fibre product `A₁ ×_{A₀} A₂` presented by its universal
property (`hcart`: every compatible pair comes from `B`; `hemb`: `B`
injects and carries the induced topology). Given that both projections of
a framed `ρ` over `B` are flat at `ℓ`, so is `ρ`.

WHY THIS IS NOT FORMAL. `GaloisRep.IsFlatAt` quantifies over the OPEN
IDEALS of the coefficient ring, and the open ideals of a fibre product
are not pullbacks of open ideals of the factors: for an ideal `I ⊆ B` the
induced `B ⧸ I → (A₁ ⧸ p₁(I)A₁) × (A₂ ⧸ p₂(I)A₂)` need NOT be injective,
so the prolongation of `ρ ⊗ B ⧸ I` cannot simply be cut out of the two
given ones. The argument is Ramakrishna's: `ℤ_ℓ` is absolutely
unramified, so `e = 1 < ℓ − 1` for odd `ℓ`, and by Raynaud a finite flat
prolongation of a given generic fibre is UNIQUE. Uniqueness is what makes
the two prolongations agree over `A₀` and hence glue over `B`; Raynaud's
closure of the category under subobjects and quotients then descends the
glued object along `B ↪ A₁ × A₂`.

`hodd` IS LOAD-BEARING — `ℓ = 2` IS A GENUINE EXCLUSION, NOT TIDINESS. At
`ℓ = 2` one has `e = 1 = ℓ − 1`, exactly the boundary at which Raynaud's
uniqueness fails: `μ_2` and `ℤ/2` are non-isomorphic finite flat group
schemes over `ℤ_2` with the SAME generic fibre (`−1 ∈ ℚ_2`), so two
prolongations agreeing generically need not agree, and the gluing has no
reason to hold. It is passed explicitly rather than left to a comment
because a prover cannot use a hypothesis that is not in the statement.

References: Ramakrishna, *On a variation of Mazur's deformation functor*,
Compositio 87 (1994), §1; Raynaud, *Schémas en groupes de type
`(p,…,p)`*, Bull. SMF 102 (1974), Thm. 3.3.1; Conrad–Diamond–Taylor,
JAMS 12 (1999), §2. -/
theorem isFlatAt_of_fibreProduct (hodd : Odd ℓ)
    {A₀ : Type u} [CommRing A₀] [TopologicalSpace A₀] [IsTopologicalRing A₀]
    [IsLocalRing A₀] [Algebra ℤ_[ℓ] A₀] [Finite A₀]
    {A₁ : Type u} [CommRing A₁] [TopologicalSpace A₁] [IsTopologicalRing A₁]
    [IsLocalRing A₁] [Algebra ℤ_[ℓ] A₁] [Finite A₁]
    {A₂ : Type u} [CommRing A₂] [TopologicalSpace A₂] [IsTopologicalRing A₂]
    [IsLocalRing A₂] [Algebra ℤ_[ℓ] A₂] [Finite A₂]
    {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLocalRing B] [Algebra ℤ_[ℓ] B] [Finite B]
    (f₁ : A₁ →+* A₀) (f₂ : A₂ →+* A₀) (hf₂ : Function.Surjective f₂)
    (p₁ : B →+* A₁) (p₂ : B →+* A₂) (hp₁ : Continuous p₁) (hp₂ : Continuous p₂)
    (hcomm : f₁.comp p₁ = f₂.comp p₂)
    (hemb : Topology.IsEmbedding fun b : B => (p₁ b, p₂ b))
    (hcart : ∀ (a₁ : A₁) (a₂ : A₂), f₁ a₁ = f₂ a₂ → ∃ b : B, p₁ b = a₁ ∧ p₂ b = a₂)
    {ρ : FramedGaloisRep ℚ B (Fin 2)}
    (h₁ : (pushforwardFrame p₁ hp₁ ρ).IsFlatAt
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : ℓ.Prime)))
    (h₂ : (pushforwardFrame p₂ hp₂ ρ).IsFlatAt
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : ℓ.Prime))) :
    ρ.IsFlatAt
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : ℓ.Prime)) :=
  sorry

/-- **The tame quadratic quotient at `2` glues along a fibre product**
(sorry node, cut 2026-07-25 out of `isHardlyRamified_of_fibreProduct` —
the Conrad–Diamond–Taylor half of Schlessinger's H1/H2).

WHY IT IS NOT FORMAL. `IsHardlyRamified` states tameness at `2` as an
EXISTENTIAL — SOME surjection `π : V ↠ R` and SOME unramified quadratic
`δ`. So `h₁` and `h₂` hand you a line over `A₁` and a line over `A₂` with
no compatibility whatever over `A₀`, and a line over the fibre product is
exactly a compatible PAIR of lines. Everything therefore turns on a
uniqueness statement forcing the two given choices to agree over `A₀`.

THE UNIQUENESS INPUT, MADE EXPLICIT (2026-07-25; this is why `hdet` is a
hypothesis). Write `ρ̄` for the residual representation of `ρ`. Two facts
follow from `hdet` ALONE:

* `χ_ℓ` is UNRAMIFIED on `G_{ℚ_2}` with `χ_ℓ(Frob_2) = 2`, because `ℓ` is
  odd, so `ℚ_2(μ_{ℓⁿ})/ℚ_2` is unramified and Frobenius is the
  `2`-power map on `ℓⁿ`-th roots of unity;
* the image of `2` is never `1` in a residue field — `2 = 1` gives
  `1 = 0`.

Hence `ρ̄|_{G_2}` is NEVER SCALAR: were it `δ̄ · 1`, then `δ̄² = 1` would
give `det ρ̄|_{G_2} = 1`, forcing the image of `2` to be `1`. For the same
reason the two Jordan–Hölder characters of `ρ̄|_{G_2}`, namely `χ̄δ̄` (sub)
and `δ̄` (quotient), are always DISTINCT — they differ by `χ̄|_{G_2}`,
which is nontrivial on `Frob_2`. That distinctness is the uniqueness
engine: a non-split `ρ̄|_{G_2}` has exactly ONE stable line, the given
lines reduce to it, they agree over `A₀`, and they glue.

THE SHARP EDGE IS `ℓ = 3`, AND ITS PROVER MUST NOT IGNORE IT. Uniqueness
can fail only when `ρ̄|_{G_2}` SPLITS as `χ̄δ̄ ⊕ δ̄`. Then there are exactly
two stable lines, with quotients `δ̄` and `χ̄δ̄`; both are unramified, and
the second is also QUADRATIC precisely when `χ̄² = 1` on `G_2`, i.e. when
`4 = 1` in the residue field, i.e. when `ℓ = 3`. So:

* for `ℓ ≥ 5` the line with unramified quadratic quotient is UNIQUE and
  the gluing is unconditional;
* at `ℓ = 3` and split, BOTH lines satisfy the clause, the two
  projections may select lines with different reductions to `A₀`, and
  then there is nothing over `B` to glue them into.

This statement carries only `hodd : Odd ℓ`, inherited from
`isHardlyRamified_of_fibreProduct`, which inherits it from
`IsHardlyRamified`. Its ONLY consumer chain —
`exists_isStrictlyUniversalOnFrames_of_finite_lifts` and
`exists_isStrictlyUniversalOnFrames_of_deformationCondition` — DOES carry
`hℓ5 : 5 ≤ ℓ`. So if the `ℓ = 3` split case proves intractable, the
correct repair is to thread `5 ≤ ℓ` down that chain (edits to other
owners' declarations, deliberately not made here), NOT to weaken this
statement. And do not discharge this leaf by assuming `ρ̄|_{G_2}` is
non-split: nothing in the hypotheses supplies that.

References: Conrad–Diamond–Taylor, JAMS 12 (1999), §2; Mazur, *Deforming
Galois representations*, MSRI Publ. 16 (1989), §§18–23; Schlessinger,
Trans. AMS 130 (1968), Thm. 2.11. -/
theorem isTameAtTwo_of_fibreProduct (hodd : Odd ℓ)
    {A₀ : Type u} [CommRing A₀] [TopologicalSpace A₀] [IsTopologicalRing A₀]
    [IsLocalRing A₀] [Algebra ℤ_[ℓ] A₀] [Finite A₀]
    {A₁ : Type u} [CommRing A₁] [TopologicalSpace A₁] [IsTopologicalRing A₁]
    [IsLocalRing A₁] [Algebra ℤ_[ℓ] A₁] [Finite A₁]
    {A₂ : Type u} [CommRing A₂] [TopologicalSpace A₂] [IsTopologicalRing A₂]
    [IsLocalRing A₂] [Algebra ℤ_[ℓ] A₂] [Finite A₂]
    {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLocalRing B] [Algebra ℤ_[ℓ] B] [Finite B]
    (f₁ : A₁ →+* A₀) (f₂ : A₂ →+* A₀) (hf₂ : Function.Surjective f₂)
    (p₁ : B →+* A₁) (p₂ : B →+* A₂) (hp₁ : Continuous p₁) (hp₂ : Continuous p₂)
    (hcomm : f₁.comp p₁ = f₂.comp p₂)
    (hemb : Topology.IsEmbedding fun b : B => (p₁ b, p₂ b))
    (hcart : ∀ (a₁ : A₁) (a₂ : A₂), f₁ a₁ = f₂ a₂ → ∃ b : B, p₁ b = a₁ ∧ p₂ b = a₂)
    {ρ : FramedGaloisRep ℚ B (Fin 2)}
    (hdet : ∀ g, ρ.det g = algebraMap ℤ_[ℓ] B
      (cyclotomicCharacter (AlgebraicClosure ℚ) ℓ g.toRingEquiv))
    (h₁ : ∃ (π : (Fin 2 → A₁) →ₗ[A₁] A₁) (_ : Function.Surjective π)
      (δ : GaloisRep ℚ_[2] A₁ A₁),
      ∀ g : Field.absoluteGaloisGroup ℚ_[2], ∀ v : Fin 2 → A₁,
        π ((pushforwardFrame p₁ hp₁ ρ).map (algebraMap ℚ ℚ_[2]) g v) = δ g (π v) ∧
        (AddSubgroup.inertia
          ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup :
            AddSubgroup Z2bar) (Field.absoluteGaloisGroup ℚ_[2]) ≤ δ.ker) ∧
        (∀ g' : Field.absoluteGaloisGroup ℚ_[2], δ g' * δ g' = 1))
    (h₂ : ∃ (π : (Fin 2 → A₂) →ₗ[A₂] A₂) (_ : Function.Surjective π)
      (δ : GaloisRep ℚ_[2] A₂ A₂),
      ∀ g : Field.absoluteGaloisGroup ℚ_[2], ∀ v : Fin 2 → A₂,
        π ((pushforwardFrame p₂ hp₂ ρ).map (algebraMap ℚ ℚ_[2]) g v) = δ g (π v) ∧
        (AddSubgroup.inertia
          ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup :
            AddSubgroup Z2bar) (Field.absoluteGaloisGroup ℚ_[2]) ≤ δ.ker) ∧
        (∀ g' : Field.absoluteGaloisGroup ℚ_[2], δ g' * δ g' = 1)) :
    ∃ (π : (Fin 2 → B) →ₗ[B] B) (_ : Function.Surjective π)
      (δ : GaloisRep ℚ_[2] B B),
      ∀ g : Field.absoluteGaloisGroup ℚ_[2], ∀ v : Fin 2 → B,
        π (ρ.map (algebraMap ℚ ℚ_[2]) g v) = δ g (π v) ∧
        (AddSubgroup.inertia
          ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup :
            AddSubgroup Z2bar) (Field.absoluteGaloisGroup ℚ_[2]) ≤ δ.ker) ∧
        (∀ g' : Field.absoluteGaloisGroup ℚ_[2], δ g' * δ g' = 1) :=
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- **Schlessinger's H1/H2 for the hardly ramified problem: the local
conditions are checked componentwise on a fibre product** (PROVEN
2026-07-25 over the two ARITHMETIC leaves `isFlatAt_of_fibreProduct` and
`isTameAtTwo_of_fibreProduct` cut immediately above — the gluing half of
"the hardly ramified conditions form a deformation condition", the
arithmetic input of the Schlessinger core leaf below).

`B` is the fibre product `A₁ ×_{A₀} A₂` of finite local `ℤ_ℓ`-algebras
along a SURJECTION `f₂` — presented not as a construction but by its
universal property: `hcart` says every compatible pair `(a₁, a₂)` comes
from `B`, and `hemb` says `B` carries the induced topology and injects,
so `B` really is the fibre product AS A TOPOLOGICAL RING. The claim is
that a framed representation over `B` whose two projections are hardly
ramified is itself hardly ramified.

WHY THIS IS THE WHOLE OF H1 AND H2. For the FRAMED functor the gluing
map `F(A₁ ×_{A₀} A₂) → F(A₁) ×_{F(A₀)} F(A₂)` is bijective on the
underlying representations for free: a homomorphism into
`GL₂(A₁ ×_{A₀} A₂) = GL₂(A₁) ×_{GL₂(A₀)} GL₂(A₂)` is exactly a
compatible pair, the frame removing the conjugation ambiguity that makes
the unframed functor only *versal*. So the only content is that the four
hardly ramified clauses descend, which is this statement.

WHAT EACH CLAUSE COSTS — the measurement that produced the cut. The four
clauses split exactly two and two.

The determinant clause is FORMAL and is proven here: `det` commutes with
`pushforwardFrame` (`det_pushforwardFrame`, above), so
`p_i (det ρ g) = p_i (algebraMap ℤ_ℓ B (χ g))` for `i = 1, 2` by
`halg₁`/`halg₂`, and injectivity of `b ↦ (p₁ b, p₂ b)` concludes.
Unramifiedness is FORMAL for the same reason and is also proven here: by
`pushforwardFrame_apply_map` an endomorphism of `Fin 2 → B` whose two
projections are the identity is the identity, entry by entry — note that
this is a statement about VALUES, which is exactly the kind of thing that
descends along an injection.

The two local conditions are the REAL content and are the two leaves cut
above: flatness at `ℓ` glues by Ramakrishna and Raynaud
(`isFlatAt_of_fibreProduct`), and the tame quadratic quotient at `2`
glues by Conrad–Diamond–Taylor (`isTameAtTwo_of_fibreProduct`). Neither
is a reformulation of the hypotheses: the first has to cope with open
ideals of `B` that are not pullbacks from the factors, and the second
with an EXISTENTIAL that hands the two projections uncoordinated lines.
See those two docstrings — in particular the `ℓ = 3` sharpness recorded
on the tame leaf, which is the one place this node's `Odd ℓ` may be too
weak and where `5 ≤ ℓ` would have to be threaded down from the consumer.

References: Schlessinger, *Functors of Artin rings*, Trans. AMS 130
(1968), Thm. 2.11 (H1, H2); Mazur, *Deforming Galois representations*,
MSRI Publ. 16 (1989), §§18–23 (deformation conditions); Ramakrishna,
Compositio 87 (1994), §1; Conrad–Diamond–Taylor, JAMS 12 (1999), §2. -/
theorem isHardlyRamified_of_fibreProduct
    {A₀ : Type u} [CommRing A₀] [TopologicalSpace A₀] [IsTopologicalRing A₀]
    [IsLocalRing A₀] [Algebra ℤ_[ℓ] A₀] [Finite A₀]
    {A₁ : Type u} [CommRing A₁] [TopologicalSpace A₁] [IsTopologicalRing A₁]
    [IsLocalRing A₁] [Algebra ℤ_[ℓ] A₁] [Finite A₁]
    {A₂ : Type u} [CommRing A₂] [TopologicalSpace A₂] [IsTopologicalRing A₂]
    [IsLocalRing A₂] [Algebra ℤ_[ℓ] A₂] [Finite A₂]
    {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLocalRing B] [Algebra ℤ_[ℓ] B] [Finite B]
    (f₁ : A₁ →+* A₀) (f₂ : A₂ →+* A₀) (hf₂ : Function.Surjective f₂)
    (p₁ : B →+* A₁) (p₂ : B →+* A₂) (hp₁ : Continuous p₁) (hp₂ : Continuous p₂)
    (halg₁ : p₁.comp (algebraMap ℤ_[ℓ] B) = algebraMap ℤ_[ℓ] A₁)
    (halg₂ : p₂.comp (algebraMap ℤ_[ℓ] B) = algebraMap ℤ_[ℓ] A₂)
    (hcomm : f₁.comp p₁ = f₂.comp p₂)
    (hemb : Topology.IsEmbedding fun b : B => (p₁ b, p₂ b))
    (hcart : ∀ (a₁ : A₁) (a₂ : A₂), f₁ a₁ = f₂ a₂ → ∃ b : B, p₁ b = a₁ ∧ p₂ b = a₂)
    {ρ : FramedGaloisRep ℚ B (Fin 2)}
    (h₁ : IsHardlyRamified hℓOdd (rank_finTwoFun A₁) (pushforwardFrame p₁ hp₁ ρ))
    (h₂ : IsHardlyRamified hℓOdd (rank_finTwoFun A₂) (pushforwardFrame p₂ hp₂ ρ)) :
    IsHardlyRamified hℓOdd (rank_finTwoFun B) ρ := by
  -- An element of `B` is determined by its two projections: this is the
  -- only consequence of `hemb` the two formal clauses need.
  have hinj : ∀ b b' : B, p₁ b = p₁ b' → p₂ b = p₂ b' → b = b' := by
    intro b b' hb₁ hb₂
    exact hemb.injective (by simp only [Prod.mk.injEq]; exact ⟨hb₁, hb₂⟩)
  -- The determinant identity, reflected back from the two projections.
  -- Used twice: as the `det` clause, and as `hdet` for the tame leaf.
  have hdet : ∀ g, ρ.det g = algebraMap ℤ_[ℓ] B
      (cyclotomicCharacter (AlgebraicClosure ℚ) ℓ g.toRingEquiv) := by
    intro g
    refine hinj _ _ ?_ ?_
    · have hcompat : p₁ (algebraMap ℤ_[ℓ] B
          (cyclotomicCharacter (AlgebraicClosure ℚ) ℓ g.toRingEquiv)) =
          algebraMap ℤ_[ℓ] A₁
            (cyclotomicCharacter (AlgebraicClosure ℚ) ℓ g.toRingEquiv) := by
        rw [← halg₁]; rfl
      rw [← det_pushforwardFrame p₁ hp₁ ρ g, h₁.det g, hcompat]
    · have hcompat : p₂ (algebraMap ℤ_[ℓ] B
          (cyclotomicCharacter (AlgebraicClosure ℚ) ℓ g.toRingEquiv)) =
          algebraMap ℤ_[ℓ] A₂
            (cyclotomicCharacter (AlgebraicClosure ℚ) ℓ g.toRingEquiv) := by
        rw [← halg₂]; rfl
      rw [← det_pushforwardFrame p₂ hp₂ ρ g, h₂.det g, hcompat]
  constructor
  · -- DETERMINANT: formal, proven above.
    exact hdet
  · -- UNRAMIFIEDNESS: formal. An endomorphism of `Fin 2 → B` killed by
    -- both projections is the identity, entrywise.
    intro p hp hpp
    -- an element of `Γ ℚ` acting trivially through both projections acts
    -- trivially: `pushforwardFrame_apply_map` makes this an entrywise
    -- statement about VALUES, which `hinj` settles
    have key : ∀ g : Field.absoluteGaloisGroup ℚ,
        (pushforwardFrame p₁ hp₁ ρ) g = 1 → (pushforwardFrame p₂ hp₂ ρ) g = 1 →
        ρ g = 1 := by
      intro g hg₁ hg₂
      refine LinearMap.ext fun w => funext fun i => ?_
      refine hinj _ _ ?_ ?_
      · have hw := pushforwardFrame_apply_map p₁ hp₁ ρ g w i
        rw [hg₁] at hw
        simpa using hw.symm
      · have hw := pushforwardFrame_apply_map p₂ hp₂ ρ g w i
        rw [hg₂] at hw
        simpa using hw.symm
    refine ⟨?_⟩
    intro σ hσ
    have e₁ : (pushforwardFrame p₁ hp₁ ρ).toLocal
        hp.toHeightOneSpectrumRingOfIntegersRat σ = 1 :=
      (h₁.isUnramified p hp hpp).localInertiaGroup_le hσ
    have e₂ : (pushforwardFrame p₂ hp₂ ρ).toLocal
        hp.toHeightOneSpectrumRingOfIntegersRat σ = 1 :=
      (h₂.isUnramified p hp hpp).localInertiaGroup_le hσ
    show ρ.toLocal hp.toHeightOneSpectrumRingOfIntegersRat σ = 1
    rw [GaloisRep.toLocal_apply] at e₁ e₂ ⊢
    exact key _ e₁ e₂
  · -- FLATNESS at `ℓ`: Ramakrishna/Raynaud, the first arithmetic leaf.
    exact isFlatAt_of_fibreProduct hℓOdd f₁ f₂ hf₂ p₁ p₂ hp₁ hp₂ hcomm hemb
      hcart h₁.isFlat h₂.isFlat
  · -- TAMENESS at `2`: Conrad–Diamond–Taylor, the second arithmetic leaf.
    exact isTameAtTwo_of_fibreProduct hℓOdd f₁ f₂ hf₂ p₁ p₂ hp₁ hp₂ hcomm hemb
      hcart hdet h₁.isTameAtTwo h₂.isTameAtTwo

/-- **Restricted-ramification finiteness across arbitrary FINITE ring
topologies — Schlessinger's H3 as the Artinian category actually needs
it** (sorry node, cut 2026-07-25: a genuine gap between the H3 leaf
`finite_setOf_isHardlyRamified_frames` and its consumers, found while
decomposing the Schlessinger core).

**REFUTED 2026-07-26. THIS STATEMENT IS FALSE AS STATED — do not attempt
to prove it, and do not build anything on it.** An explicit infinite
family of counterexamples is given in the REFUTATION section below. The
repair is the one this docstring already anticipated in its last
paragraph, and it is UPSTREAM of this leaf: `[DiscreteTopology A]` must
be added to the test objects of `IsStrictlyUniversalOnFrames` and
`HardlyRamifiedDeformation.IsStrictlyUniversalOnFiniteFrames`, after
which this leaf collapses to `finite_setOf_isHardlyRamified_frames` and
disappears. The paragraph `WHY IT IS NEVERTHELESS TRUE` below is
retained, struck through by the refutation that follows it, because
naming the precise step that fails is the whole content of the finding.

THE GAP. `finite_setOf_isHardlyRamified_frames` is stated for `A` with
the DISCRETE topology, which is the only sensible topology on an Artinian
object of Mazur's category — the maximal ideal is nilpotent, so the adic
topology is discrete. But `IsStrictlyUniversalOnFrames` and
`HardlyRamifiedDeformation.IsStrictlyUniversalOnFiniteFrames` quantify
over RAW test objects: a finite local topological `ℤ_ℓ`-algebra with NO
`IsAdic` clause, deliberately, so that a test object carries no
`IsModuleTopology` datum. A finite ring can carry a strictly coarser ring
topology: for `A = k[ε]` the topology whose opens are the unions of
cosets of `(ε)` — the preimage of the discrete topology of `k` — is a
ring topology, `A` is local and finite, and the reduction `A ↠ k` is
continuous, so `A` is a legitimate test object that is NOT discrete.
Over such an `A` continuity of a framed representation only constrains it
modulo `(ε)`, so a priori there are far more hardly ramified lifts than
the discrete count, and H3 as stated says nothing about them. The gap is
unavoidable: Schlessinger's tangent-space step applies H3 to the dual
numbers with the topology INDUCED FROM THE TEST OBJECT, not with the
discrete one.

WHY IT IS NEVERTHELESS TRUE (the route this leaf records). A hardly
ramified `ρ` over such an `A` is unramified outside `{2, ℓ}`, so it kills
every inertia subgroup away from `{2, ℓ}` and hence factors — as an
ABSTRACT homomorphism — through the Galois group `G_S` of the maximal
extension unramified outside `S = {2, ℓ, ∞}`. `G_S` is topologically
finitely generated (Hermite–Minkowski: only finitely many number fields
of bounded degree are unramified outside `S`), and by the
Nikolov–Segal theorem every finite-index subgroup of a topologically
finitely generated profinite group is OPEN. So every abstract
homomorphism from `G_S` to a finite group is automatically continuous:
the kernel of `ρ` is open, `ρ` is continuous for the DISCRETE topology on
`A`, and the discrete count of `hdisc` bounds the coarse one. Formally
the conclusion is a `Set.Finite` for the coarse-topology type, into which
the discrete-topology set injects; what has to be produced is the reverse
inclusion, i.e. exactly the automatic continuity.

REFUTATION (2026-07-26). The paragraph above fails at its FIRST step,
in exactly the way its own escape clause below predicted: an abstract
homomorphism killing every individual inertia subgroup does NOT factor
through `G_S`. It factors through `Γ / N` with `N` the ABSTRACT normal
closure of the inertia subgroups, and `N` is strictly smaller than its
closure `N̄ = ker (Γ ↠ G_S)`. Nikolov–Segal is a theorem about `G_S`,
which this homomorphism never reaches, so it never applies.

THE WITNESS. Take `A = ZMod ℓ` carrying the INDISCRETE topology `⊤`
(only `∅` and `A` open). It is a legal test object for every quantifier
in this statement: `IsTopologicalRing` extends only `ContinuousAdd`,
`ContinuousMul` and `ContinuousNeg` — there is no separation axiom — and
every map into an indiscrete space is continuous; `A` is a field, hence
`IsLocalRing`; it is `Finite`; and it is a `ℤ_[ℓ]`-algebra. Since
`moduleTopology A A` is `A`'s own topology
(`IsTopologicalSemiring.toIsModuleTopology`) and the module topology of a
finite product is the product topology (`IsModuleTopology.instPi`), the
module topology on `Module.End A (Fin 2 → A) ≃ₗ[A] A⁴` is again
indiscrete. So `FramedGaloisRep ℚ A (Fin 2)` is the set of ALL abstract
monoid homomorphisms `Γ ℚ → Module.End A (Fin 2 → A)`: over this `A`,
continuity is no constraint whatsoever.

THE FAMILY. Let `q : Γ ℚ ↠ Ẑˣ = ∏_p ℤ_pˣ` be the abelianisation
(Kronecker–Weber). For each prime `p` the image `q (I_p)` lies in the
`p`-th factor alone, because `ℚ (μ_m) / ℚ` is unramified at `p` for
`p ∤ m`. Compose with `Ẑˣ ↠ P := ∏_{p odd} ℤ_pˣ / (ℤ_pˣ)²  ≅ ∏_{p odd}
𝔽₂`, and let `D := ⊕_{p odd} 𝔽₂ ⊆ P` be the direct sum. Every `q (I_p)`
lands in `D` — including `p = 2` and `p = ℓ`, whose images die in `P`
entirely (`p = 2`) or occupy one coordinate (`p = ℓ`). Now `P / D ≠ 0`
(the all-ones vector is not in `D`) and in fact `dim_{𝔽₂} (P / D) = 𝔠`,
so there are infinitely many nonzero `𝔽₂`-linear functionals
`f : P / D → 𝔽₂`. Each gives `ψ_f : Γ ℚ ↠ {±1} ⊆ Aˣ`, an abstract
character which kills EVERY inertia subgroup at EVERY finite place, and
which is DISCONTINUOUS: were `ker ψ_f` open, `ψ_f` would cut out a
quadratic field unramified at every finite prime, and Minkowski forbids
one. Distinct `f` give distinct `ψ_f`. This is the ⊕-versus-∏ failure
predicted below, made explicit.

Set `ρ_f := diag (ψ_f, χ̄ · ψ_f)` with `χ̄` the mod-`ℓ` cyclotomic
character. All four clauses of `IsHardlyRamified` hold:
* `det`: `ψ_f · χ̄ · ψ_f = χ̄ · ψ_f² = χ̄`, since `ψ_f² = 1`.
* `isUnramified` away from `{2, ℓ}`: `ψ_f` kills all inertia and `χ̄` is
  unramified outside `ℓ`.
* `isFlat` at `ℓ`: `GaloisRep.IsFlatAt.cond` quantifies over the OPEN
  ideals of `A`, and the only open ideal of an indiscrete ring is `⊤`
  (an ideal contains `0`, so it is not `∅`). The quotient `A ⧸ ⊤` is the
  zero ring, its `Space` is a singleton, and
  `GaloisRep.HasFlatProlongationAt` is witnessed by the trivial group
  scheme `G = 𝒪ᵥ`: `Kᵥ ⊗[𝒪ᵥ] 𝒪ᵥ = Kᵥ` has exactly one `Kᵥ`-algebra map
  to `Kᵥᵃˡᵍ`, so both sides are singletons. Flatness is therefore VACUOUS
  over an indiscrete test object.
* `isTameAtTwo`: take `π` the first coordinate projection and
  `δ := ψ_f` restricted along `Γ ℚ_[2] → Γ ℚ`; `δ` is a `GaloisRep`
  because continuity is free here, it is unramified because `ψ_f` kills
  `I_2`, and `δ² = 1`.

So the set in the conclusion is INFINITE while `hdisc` — the genuine H3,
true by Hermite–Minkowski — is unaffected. The implication is false.

TWO INDEPENDENT DEFECTS, and the second one matters for the repair. (i)
Automatic continuity fails, as above. (ii) Even for CONTINUOUS `ρ`,
`hdisc` cannot bound this set, because over an indiscrete (or any coarse)
`A` the flatness clause is weakened — the open-ideal quantifier sees
fewer ideals — so the coarse hardly-ramified set is not contained in the
image of any discrete one. Bounding it needs Hermite–Minkowski applied
directly (topological finite generation of `G_S`), which `hdisc` does not
supply. Hence NO hypothesis short of discreteness of `A` rescues this
statement, and in particular strengthening `hdisc` is not the repair.

THE REPAIR IS ONE SEPARATION AXIOM, AND IT IS FREE. For a FINITE
topological ring the whole phenomenon is non-separation, and nothing
else. In a finite topological group the intersection `U` of all open
neighbourhoods of `0` is itself open, is a subgroup (from continuity of
`+` at `(0,0)`, using minimality of `U`), is an ideal (from continuity of
`x ↦ a * x`), equals `closure {0}`, and the topology is exactly the coset
topology of `U` — i.e. the pullback of the discrete topology of `A ⧸ U`.
Hence for a finite topological ring

    DiscreteTopology A  ⟺  T0Space A  ⟺  T2Space A  ⟺  closure {0} = 0.

The motivating example of THE GAP above, `k[ε]` with the `(ε)`-coset
topology, is not a subtle intermediate case: `0` and `ε` are
topologically indistinguishable in it, so it is not even `T0`. So the
raw test objects that this leaf was cut to cover are precisely the
NON-HAUSDORFF ones, and every test object anyone actually constructs —
a finite quotient of an `IsAdic` complete local ring, the dual numbers
with their adic topology — is Hausdorff and therefore discrete. Adding
`[T0Space A]` (equivalently `[DiscreteTopology A]`) to the raw test
objects costs the consumers nothing and closes the gap completely.

THE FIX IS UPSTREAM, NOT HERE (unchanged from the original cut, now
mandatory rather than conditional). `IsStrictlyUniversalOnFrames` and
`HardlyRamifiedDeformation.IsStrictlyUniversalOnFiniteFrames` are
themselves too strong and must be narrowed by adding
`[DiscreteTopology A]` to their test objects — which costs their
consumers nothing, since the bundled deformations they are applied to are
`IsAdic` and finite, hence discrete. This leaf was stated so that the
question would be confronted once, in one place, rather than rediscovered
inside a representability proof; that is what happened.

References: Nikolov–Segal, *On finitely generated profinite groups I*,
Ann. of Math. 165 (2007) (the theorem that does NOT apply here); Serre,
*Galois cohomology*, I §4.2 (Hermite–Minkowski and the finite generation
of `G_S`); Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*,
§I.1 and §X.3 (`Ẑˣ` as the abelianisation, inertia in `ℚ (μ_∞)`);
Minkowski's discriminant bound for the everywhere-unramified step. -/
theorem finite_setOf_isHardlyRamified_frames_of_discreteTopology
    (hdisc : ∀ (A : Type u) [CommRing A] [TopologicalSpace A]
      [IsTopologicalRing A] [IsLocalRing A] [Algebra ℤ_[ℓ] A] [Finite A]
      [DiscreteTopology A],
      {ρ : FramedGaloisRep ℚ A (Fin 2) |
        IsHardlyRamified hℓOdd (rank_finTwoFun A) ρ}.Finite)
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLocalRing A] [Algebra ℤ_[ℓ] A] [Finite A] :
    {ρ : FramedGaloisRep ℚ A (Fin 2) |
      IsHardlyRamified hℓOdd (rank_finTwoFun A) ρ}.Finite :=
  sorry

set_option backward.isDefEq.respectTransparency false in
open scoped TensorProduct in
/-- **Matrix entries of a pushed-forward frame** (PROVEN, elementary):
`pushforwardFrame ψ` is "apply `ψ` to the matrix entries", so on a vector
already in the image of `ψ` it acts entrywise through `ψ`. This is the
dictionary that lets a statement about `pushforwardFrame` over `R ⧸ I` be
read back as a congruence in `R`, and it is what the descent clauses of
`isHardlyRamified_of_forall_isOpen_quotient` below run on. -/
lemma pushforwardFrame_apply {B : Type u} [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (ψ : B →+* A) (hψ : Continuous ψ)
    (ρ : FramedGaloisRep ℚ B (Fin 2)) (g : Field.absoluteGaloisGroup ℚ)
    (x : Fin 2 → B) :
    (pushforwardFrame ψ hψ ρ) g (fun i => ψ (x i)) = fun j => ψ (ρ g x j) := by
  letI : Algebra B A := ψ.toAlgebra
  letI : ContinuousSMul B A := continuousSMul_of_algebraMap B A
    (by rw [RingHom.algebraMap_toAlgebra]; exact hψ)
  have hsm : ∀ b : B, b • (1 : A) = ψ b := by
    intro b
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_one]
  have hx : (fun i => ψ (x i)) =
      (TensorProduct.piScalarRight B A A (Fin 2)) ((1 : A) ⊗ₜ[B] x) := by
    funext i
    rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
    exact (hsm (x i)).symm
  show ((ρ.baseChange A).conj (TensorProduct.piScalarRight B A A (Fin 2))) g _ = _
  rw [hx, GaloisRep.conj_apply, LinearEquiv.conj_apply_apply,
    LinearEquiv.symm_apply_apply, GaloisRep.baseChange_tmul]
  funext j
  rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  exact hsm _

set_option backward.isDefEq.respectTransparency false in
open scoped TensorProduct in
/-- **The determinant of a pushed-forward frame is the image of the
determinant** (PROVEN): `LinearMap.det_baseChange` for the base change,
`LinearMap.det_conj` for the framing identification. Same two steps as
`isHardlyRamified_pushforwardFrame`'s determinant clause, isolated
because the descent below needs the equation itself and not just its
consequence. -/
lemma det_pushforwardFrame {B : Type u} [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (ψ : B →+* A) (hψ : Continuous ψ)
    (ρ : FramedGaloisRep ℚ B (Fin 2)) (g : Field.absoluteGaloisGroup ℚ) :
    (pushforwardFrame ψ hψ ρ).det g = ψ (ρ.det g) := by
  letI : Algebra B A := ψ.toAlgebra
  letI : ContinuousSMul B A := continuousSMul_of_algebraMap B A
    (by rw [RingHom.algebraMap_toAlgebra]; exact hψ)
  show ((ρ.baseChange A).conj (TensorProduct.piScalarRight B A A (Fin 2))).det g = _
  rw [GaloisRep.det_apply, GaloisRep.conj_apply, LinearEquiv.conj_apply,
    LinearMap.comp_assoc, LinearMap.det_conj]
  show LinearMap.det ((ρ.baseChange A) g) = _
  rw [show ((ρ.baseChange A) g : Module.End A (A ⊗[B] (Fin 2 → B))) =
    LinearMap.baseChange A (ρ g) from rfl, LinearMap.det_baseChange]
  rfl

open scoped TensorProduct in
/-- **A flat prolongation descends through the base change to `A ⧸ ⊥`**
(PROVEN): `A ⧸ ⊥ ≃ A` is `Submodule.quotEquivOfEqBot`, and tensoring it
with the identity collapses `(A ⧸ ⊥) ⊗_A N` onto `N` equivariantly —
the Galois action on the base change is `g ⊗ 1`, so the transport is
`map_smul`. This is the step that turns the flatness clause of the
level-`I` datum (which quantifies over the open ideals of `R ⧸ I`,
evaluated at `⊥`) back into a statement about `ρ.baseChange (R ⧸ I)`. -/
lemma hasFlatProlongationAt_of_baseChange_bot {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A]
    {N : Type v} [AddCommGroup N] [Module A N] [Module.Finite A N]
    [Module.Free A N] (τ : GaloisRep ℚ A N)
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (h : (τ.baseChange (A ⧸ (⊥ : Ideal A))).HasFlatProlongationAt w) :
    τ.HasFlatProlongationAt w := by
  let φ : (A ⧸ (⊥ : Ideal A)) ≃ₗ[A] A := Submodule.quotEquivOfEqBot _ rfl
  let E : ((A ⧸ (⊥ : Ideal A)) ⊗[A] N) ≃ₗ[A] N :=
    (TensorProduct.congr φ (LinearEquiv.refl A N)).trans (TensorProduct.lid A N)
  refine h.of_equiv _ E.toAddEquiv ?_
  intro g x
  show E (((τ.baseChange (A ⧸ (⊥ : Ideal A))).toLocal w g) x) =
    (τ.toLocal w g) (E x)
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul c y =>
    show E (c ⊗ₜ[A] (τ.toLocal w g) y) = (τ.toLocal w g) (E (c ⊗ₜ[A] y))
    show φ c • ((τ.toLocal w g) y) = (τ.toLocal w g) (φ c • y)
    rw [map_smul]

/-- **A flat prolongation descends through conjugation** (PROVEN): the
inverse of the conjugating isomorphism is itself equivariant, so
`HasFlatProlongationAt.of_equiv` transports the Hopf-algebra witness
back. The converse direction of the transport already used inside
`isHardlyRamified_conj`. -/
lemma hasFlatProlongationAt_of_conj {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A]
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type v} [AddCommGroup N] [Module A N] (τ : GaloisRep ℚ A M)
    (e : M ≃ₗ[A] N)
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (h : (τ.conj e).HasFlatProlongationAt w) :
    τ.HasFlatProlongationAt w := by
  refine h.of_equiv _ e.symm.toAddEquiv ?_
  intro g x
  show e.symm (((τ.conj e).toLocal w g) x) = (τ.toLocal w g) (e.symm x)
  rw [GaloisRep.toLocal_apply, GaloisRep.conj_apply, LinearEquiv.conj_apply_apply,
    LinearEquiv.symm_apply_apply, GaloisRep.toLocal_apply]

/-- **A flat prolongation is inherited by any representation on a
subsingleton space** (PROVEN): the Hopf-algebra witness is reused and the
geometric-points identification is composed with the unique additive
isomorphism of one-element groups, every side condition being
`Subsingleton.elim`. This is what discharges the `I = ⊤` case of
`IsFlatAt`, whose quantifier runs over ALL open ideals — including the
unit ideal, at which the coefficient ring is trivial and no level datum
is available, since `IsLocalRing (R ⧸ ⊤)` is false. -/
lemma hasFlatProlongationAt_of_subsingleton {A : Type u} [CommRing A]
    [TopologicalSpace A] {M : Type v} [AddCommGroup M] [Module A M]
    [Subsingleton M] {A' : Type u} [CommRing A'] [TopologicalSpace A']
    {M' : Type v} [AddCommGroup M'] [Module A' M'] [Subsingleton M']
    {τ₁ : GaloisRep ℚ A M} (τ₂ : GaloisRep ℚ A' M')
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (h : τ₁.HasFlatProlongationAt w) :
    τ₂.HasFlatProlongationAt w := by
  haveI : Subsingleton (τ₁.toLocal w).Space := inferInstanceAs (Subsingleton M)
  haveI : Subsingleton (τ₂.toLocal w).Space := inferInstanceAs (Subsingleton M')
  exact h.of_equiv _ ⟨⟨fun _ => 0, fun _ => 0, fun _ => Subsingleton.elim _ _,
    fun _ => Subsingleton.elim _ _⟩, fun _ _ => Subsingleton.elim _ _⟩
    fun _ _ => Subsingleton.elim _ _

open scoped TensorProduct in
/-- A tensor product with a subsingleton left factor is a subsingleton
(PROVEN, elementary: every pure tensor is `0 ⊗ₜ y = 0`). -/
lemma subsingleton_tensorProduct_of_left {A : Type u} [CommRing A]
    {X : Type v} [AddCommGroup X] [Module A X] [Subsingleton X]
    {N : Type v} [AddCommGroup N] [Module A N] : Subsingleton (X ⊗[A] N) := by
  have hall : ∀ z : X ⊗[A] N, z = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | add a b ha hb => rw [ha, hb, add_zero]
    | tmul c y => rw [Subsingleton.elim c 0, TensorProduct.zero_tmul]
  exact ⟨fun a b => by rw [hall a, hall b]⟩

/-- **The tame quotient at `2` is detected on the finite levels** (sorry
node — the ONE clause of `isHardlyRamified_of_forall_isOpen_quotient`
below that is a genuine pro-limit statement rather than a congruence, cut
out 2026-07-25 when the other three clauses were PROVEN).

WHY THE OTHER THREE CLAUSES ARE NOT HERE. The determinant condition is an
equality in `R`, unramifiedness is the vanishing of `ρ(σ) − 1`, and both
are read off the levels by `𝔪`-adic separatedness
(`IsAdicComplete → IsHausdorff`); flatness at `ℓ` is *literally* a
condition on the reductions, so it transfers by re-indexing. Only the
tame quotient asks for the EXISTENCE of an object over `R` — a rank-one
free quotient — and existence is exactly what does not descend from a
compatible system for free.

THE STATEMENT. `hq` supplies, for every proper open ideal, a surjection
`π_I : (R ⧸ I)² ↠ R ⧸ I` and an unramified quadratic character `δ_I`
through which `ρ|_{G_2}` acts on the quotient. Wanted: one such pair over
`R` itself. The `π_I` supplied at different levels are UNRELATED — `hq`
is a family of independent existence statements, not a compatible system
— so the whole content is manufacturing compatibility.

THE ROUTE (worked out 2026-07-25; it is not the Kőnig argument the
consumer's docstring sketches, and the difference matters).

1. *The character is `±1`-valued, hence rigid.* `δ_I(g)² = 1` in the
   local ring `R ⧸ I`, whose residue characteristic is `ℓ`, odd, so `2`
   is a unit and `(x−1)(x+1) = 0` forces `x = ±1`. Therefore `δ_I` is the
   image of a homomorphism `ε : Γ ℚ_2 → {±1} ⊆ ℤ`, and `ε` is determined
   by `δ_I mod 𝔪` — reduction is injective on `{±1}`.

2. *Only finitely many characters can occur.* Let `D_n` be the set of
   `ε`'s realised at level `𝔪ⁿ`. A level-`m` datum reduces to a level-`n`
   datum with the SAME `ε` for `m ≥ n`, so `D_n` is decreasing. And `D_1`
   is finite: a quotient character of a rank-two representation over the
   field `k` is a Jordan–Hölder factor, of which there are at most two —
   three distinct stable lines `L₁, L₂, L₃` give `V = L₁ ⊕ L₃`, hence
   `V/L₃ ≅ L₁`, collapsing the third character onto one of the first two.
   A decreasing chain of nonempty subsets of a finite set has nonempty
   intersection: fix `ε` in it.

3. *With `ε` FIXED the fibres are MODULES, not merely sets.* Put
   `N := {π : R² →ₗ[R] R | ∀ g, π ∘ ρ(g)|_{G_2} = ε(g) · π}`, an
   `R`-submodule of `R²` (a `π` is its pair of values on the standard
   basis), and `N_n` likewise over `R ⧸ 𝔪ⁿ`. This linearity is the crux,
   and it is why the statement is TRUE WITHOUT a finiteness hypothesis on
   the residue field — a hypothesis this leaf does not have, and which
   the Kőnig/`nonempty_sections_of_finite_inverse_system` route would
   need.

4. *Mittag-Leffler comes free from Artinian-ness.* `R ⧸ 𝔪ⁿ` is Noetherian
   local with nilpotent maximal ideal, hence ARTINIAN, so the descending
   chain of images `im(N_m → N_n)` stabilises; the stabilised images have
   surjective transition maps, so their inverse limit is nonempty. And
   `N = lim N_n`, because `R² = lim (R ⧸ 𝔪ⁿ)²` by completeness and the
   defining equations are closed conditions.

5. *Surjectivity survives the limit.* `π ∈ N ⊆ R²` is surjective iff it
   is unimodular iff its image in `k²` is nonzero (`R` is local). Each
   level supplies a surjective `π_n`, so `im(N_m → N_1)` contains a
   nonzero element for every `m`; the chain stabilises, so the stabilised
   `N_1` contains a nonzero `u`. Lift `u` through the surjective tower and
   assemble by `𝔪`-adic completeness: the result is unimodular, hence the
   wanted surjection, and `δ := ε` is continuous because it is locally
   constant (it factors through the discrete `k`).

CAUTION FOR WHOEVER TAKES THIS. The inertia quantifier is inside `δ.ker`
and must stay there: `δ` is unramified, NOT trivial, and widening the
quantifier from `AddSubgroup.inertia …` to all of `Γ ℚ_2` makes the
statement false for every unramified quadratic twist. Note also that step
1 is the only place the oddness of `ℓ` is used, and it is used
essentially.

References: Mazur, *Deforming Galois representations*, MSRI Publ. 16
(1989), §1.2 (pro-representability and the passage to the limit);
Conrad–Diamond–Taylor, JAMS 12 (1999), §2 (the deformation-condition
axioms); Grothendieck, EGA III 5.4.1 (the same statement read
geometrically: sections of a proper `R`-scheme over a complete local `R`
are the compatible systems of sections over the Artinian truncations). -/
theorem isTameAtTwo_of_forall_isOpen_quotient
    {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [Algebra ℤ_[ℓ] R] [IsNoetherianRing R]
    (hadic : IsAdic (IsLocalRing.maximalIdeal R))
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal R) R)
    {ρ : FramedGaloisRep ℚ R (Fin 2)}
    (hq : ∀ (I : Ideal R), IsOpen (I : Set R) → ∀ [IsLocalRing (R ⧸ I)]
      (hmk : Continuous (Ideal.Quotient.mk I)),
      IsHardlyRamified hℓOdd (rank_finTwoFun (R ⧸ I))
        (pushforwardFrame (Ideal.Quotient.mk I) hmk ρ)) :
    ∃ (π : (Fin 2 → R) →ₗ[R] R) (_ : Function.Surjective π)
      (δ : GaloisRep ℚ_[2] R R),
      ∀ g : Field.absoluteGaloisGroup ℚ_[2], ∀ v : Fin 2 → R,
      π (ρ.map (algebraMap ℚ ℚ_[2]) g v) = δ g (π v) ∧
      (AddSubgroup.inertia
        ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup : AddSubgroup Z2bar)
        (Field.absoluteGaloisGroup ℚ_[2]) ≤ δ.ker) ∧
      (∀ g : Field.absoluteGaloisGroup ℚ_[2], δ g * δ g = 1) :=
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- **Hardly-ramifiedness is detected on the finite levels** (PROVEN
2026-07-25 over the single residual leaf
`isTameAtTwo_of_forall_isOpen_quotient` — the pro-limit clause of the
deformation-condition package, and the one place where the Schlessinger
core has to leave the Artinian category).

A framed representation over a complete Noetherian local `ℤ_ℓ`-algebra
`R` with the `𝔪`-adic topology, all of whose reductions modulo the open
ideals are hardly ramified, is hardly ramified. This is what produces the
clause `IsHardlyRamified hℓOdd (rank_finTwoFun R) ρuniv` of the hull:
Schlessinger's construction only ever produces the Artinian truncations
`ρ_n` over `R ⧸ 𝔪ⁿ`, and hardly-ramifiedness of the limit is a separate
(easy but nonempty) statement about them.

Clause by clause. The determinant condition and the unramifiedness
condition are equalities in `R` respectively kernel containments, and `R`
is `𝔪`-adically SEPARATED (`IsAdicComplete`), so holding modulo every
`𝔪ⁿ` gives them outright. Flatness at `ℓ` is *literally* a condition on
the reductions modulo open ideals (`GaloisRep.IsFlatAt.cond` quantifies
over open ideals of the coefficient ring), so it transfers with a
re-indexing — the open ideals of `R ⧸ I` are the images of the open
ideals of `R` above `I`. The tame quotient at `2` is the only clause
needing a limit: the pairs `(π_n, δ_n)` over `R ⧸ 𝔪ⁿ` form an inverse
system of nonempty finite sets (`R ⧸ 𝔪ⁿ` is finite, `R` being Noetherian
with finite residue field), so `nonempty_sections_of_finite_inverse_system`
produces a compatible system and completeness assembles it — the same
Kőnig step as in `isWeaklyUniversalOnIdentifiedFrames_of_finite`, one
level simpler because no conjugation datum rides along.

The hypothesis is stated over ALL open ideals rather than over the powers
`𝔪ⁿ` because that is the form `IsFlatAt` consumes; `hadic` makes the two
interchangeable — and note that `IsFlatAt`'s quantifier includes the UNIT
ideal, at which no level datum exists (`R ⧸ ⊤` is not local); that case
is discharged separately through
`hasFlatProlongationAt_of_subsingleton`. -/
theorem isHardlyRamified_of_forall_isOpen_quotient
    {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [Algebra ℤ_[ℓ] R] [IsNoetherianRing R]
    (hadic : IsAdic (IsLocalRing.maximalIdeal R))
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal R) R)
    {ρ : FramedGaloisRep ℚ R (Fin 2)}
    (hq : ∀ (I : Ideal R), IsOpen (I : Set R) → ∀ [IsLocalRing (R ⧸ I)]
      (hmk : Continuous (Ideal.Quotient.mk I)),
      IsHardlyRamified hℓOdd (rank_finTwoFun (R ⧸ I))
        (pushforwardFrame (Ideal.Quotient.mk I) hmk ρ)) :
    IsHardlyRamified hℓOdd (rank_finTwoFun R) ρ := by
  classical
  haveI := hcomplete
  have hcont : ∀ J : Ideal R, Continuous (Ideal.Quotient.mk J) :=
    fun _ => continuous_quot_mk
  -- separation: the topology is `𝔪`-adic and `R` is `𝔪`-adically separated
  have hsep : ∀ x y : R,
      (∀ n : ℕ, x - y ∈ (IsLocalRing.maximalIdeal R ^ (n + 1) : Ideal R)) → x = y := by
    intro x y hxy
    have h0 : x - y = 0 := by
      refine IsHausdorff.haus
        (inferInstance : IsHausdorff (IsLocalRing.maximalIdeal R) R) _ fun n => ?_
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
      cases n with
      | zero => simp
      | succ m => exact hxy m
    exact sub_eq_zero.mp h0
  have hpow : ∀ n : ℕ, IsOpen ((IsLocalRing.maximalIdeal R ^ n : Ideal R) : Set R) :=
    (isAdic_iff.mp hadic).1
  have hnetop : ∀ n : ℕ, (IsLocalRing.maximalIdeal R ^ (n + 1) : Ideal R) ≠ ⊤ := by
    intro n htop
    have hle : (IsLocalRing.maximalIdeal R ^ (n + 1) : Ideal R) ≤
        IsLocalRing.maximalIdeal R := Ideal.pow_le_self (Nat.succ_ne_zero n)
    rw [htop, top_le_iff] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top hle
  -- a proper ideal of a local ring has local quotient
  have hlocal : ∀ J : Ideal R, J ≠ ⊤ → IsLocalRing (R ⧸ J) := by
    intro J hJt
    haveI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJt
    exact IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the cyclotomic determinant, level by level
    intro g
    refine hsep _ _ fun n => ?_
    haveI := hlocal _ (hnetop n)
    have hd := (hq _ (hpow (n + 1)) (hcont _)).det g
    rw [det_pushforwardFrame,
      IsScalarTower.algebraMap_apply ℤ_[ℓ] R (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))] at hd
    exact Ideal.Quotient.eq.mp hd
  · -- unramifiedness outside `{2, ℓ}`: the entries of `ρ(σ) − 1` die at every level
    intro p hp hpp
    refine ⟨fun σ hσ => ?_⟩
    show (ρ.toLocal hp.toHeightOneSpectrumRingOfIntegersRat) σ = 1
    refine LinearMap.ext fun x => funext fun j => ?_
    show (ρ.toLocal hp.toHeightOneSpectrumRingOfIntegersRat) σ x j = x j
    rw [GaloisRep.toLocal_apply]
    refine hsep _ _ fun n => ?_
    set J : Ideal R := IsLocalRing.maximalIdeal R ^ (n + 1)
    haveI := hlocal J (hnetop n)
    have h1 : (pushforwardFrame (Ideal.Quotient.mk J) (hcont J) ρ).toLocal
        hp.toHeightOneSpectrumRingOfIntegersRat σ = 1 :=
      ((hq J (hpow (n + 1)) (hcont J)).isUnramified p hp hpp).localInertiaGroup_le hσ
    have h2 : (pushforwardFrame (Ideal.Quotient.mk J) (hcont J) ρ).toLocal
        hp.toHeightOneSpectrumRingOfIntegersRat σ
        (fun i => Ideal.Quotient.mk J (x i)) = fun i => Ideal.Quotient.mk J (x i) := by
      rw [h1]
      rfl
    rw [GaloisRep.toLocal_apply, pushforwardFrame_apply] at h2
    exact Ideal.Quotient.eq.mp (congrFun h2 j)
  · -- flatness at `ℓ`: literally a condition on the levels, re-indexed
    constructor
    intro I hI
    by_cases hIt : I = ⊤
    · -- the unit ideal carries no level datum; both spaces are trivial
      subst hIt
      have hmtop : IsOpen ((⊤ : Ideal (R ⧸ IsLocalRing.maximalIdeal R ^ 1)) :
          Set (R ⧸ IsLocalRing.maximalIdeal R ^ 1)) := by
        rw [Submodule.top_coe]
        exact isOpen_univ
      haveI := hlocal _ (hnetop 0)
      have h1 := (hq _ (hpow 1) (hcont _)).isFlat.cond ⊤ hmtop
      haveI : Subsingleton ((R ⧸ IsLocalRing.maximalIdeal R ^ 1) ⧸
          (⊤ : Ideal (R ⧸ IsLocalRing.maximalIdeal R ^ 1))) :=
        Ideal.Quotient.subsingleton_iff.mpr rfl
      haveI : Subsingleton (R ⧸ (⊤ : Ideal R)) :=
        Ideal.Quotient.subsingleton_iff.mpr rfl
      haveI := subsingleton_tensorProduct_of_left
        (A := R ⧸ IsLocalRing.maximalIdeal R ^ 1)
        (X := (R ⧸ IsLocalRing.maximalIdeal R ^ 1) ⧸
          (⊤ : Ideal (R ⧸ IsLocalRing.maximalIdeal R ^ 1)))
        (N := Fin 2 → (R ⧸ IsLocalRing.maximalIdeal R ^ 1))
      haveI := subsingleton_tensorProduct_of_left (A := R)
        (X := R ⧸ (⊤ : Ideal R)) (N := Fin 2 → R)
      exact hasFlatProlongationAt_of_subsingleton _ _ h1
    · haveI := hlocal I hIt
      have hbot : IsOpen (((⊥ : Ideal (R ⧸ I))) : Set (R ⧸ I)) := by
        have hqm : Topology.IsQuotientMap (Ideal.Quotient.mk I) :=
          (QuotientRing.isOpenQuotientMap_mk I).isQuotientMap
        have hpre : (Ideal.Quotient.mk I) ⁻¹' ((⊥ : Ideal (R ⧸ I)) : Set (R ⧸ I)) =
            (I : Set R) := by
          ext z
          simp [Ideal.Quotient.eq_zero_iff_mem]
        rw [← hqm.isOpen_preimage, hpre]
        exact hI
      have h1 := (hq I hI (hcont I)).isFlat.cond ⊥ hbot
      have h2 := hasFlatProlongationAt_of_baseChange_bot _ _ h1
      exact hasFlatProlongationAt_of_conj _
        (TensorProduct.piScalarRight R (R ⧸ I) (R ⧸ I) (Fin 2)) _ h2
  · -- the tame quotient at `2`: the one genuine pro-limit clause
    exact isTameAtTwo_of_forall_isOpen_quotient hℓOdd hadic hcomplete hq

open scoped TensorProduct in
/-- **Schlessinger's hull for the hardly ramified problem, over the
deformation-condition package** (sorry node — the FORMAL core of the
2026-07-25 cut of `exists_isStrictlyUniversalOnFrames_of_finite_lifts`,
which is now PROVEN over this leaf and the four arithmetic leaves it
takes as hypotheses).

GIVEN Schlessinger's H4 (`hschur`, `End_{k[Γ]}(ρbar) = k`), H3 (`hfin`,
restricted-ramification finiteness at every Artinian level and for every
ring topology on it), and the three clauses that say the hardly ramified
conditions form a DEFORMATION CONDITION — functoriality (`hbase`),
gluing along fibre products, i.e. H1 and H2 (`hglue`), and detection on
the finite levels (`hlim`) — the hardly ramified deformation problem of
an irreducible hardly ramified `ρbar` (`ℓ ≥ 5`) has a hull: a complete
Noetherian local topological `ℤ_ℓ`-algebra `R` with the `𝔪`-adic
topology, carrying a hardly ramified framed representation `ρuniv`, a
surjective continuous reduction `πuniv` identifying `ρuniv ⊗_R k` with
`ρbar`, which classifies every FINITE raw framed test object *strictly*
— by a continuous `ℤ_ℓ`-algebra map compatible with the reductions along
which `ρuniv` pushes forward to the test representation up to the framing
ambiguity.

WHAT IS AND IS NOT IN THIS LEAF. This leaf contains NO ARITHMETIC. In:
the construction of the hull — Schlessinger's inductive small-extension
argument over H1–H4, the de Smit–Lenstra generators-and-relations
presentation `W(k)[[x₁,…,x_g]] ↠ R` with `g` the dimension of the framed
tangent space, and the Mazur-category ring clauses read off it. Out:
(i) H4, the now-PROVEN node `exists_smul_eq_of_commute_of_isIrreducible`
(2026-07-26), supplied
as `hschur`; (ii) H3, the leaf `finite_setOf_isHardlyRamified_frames`
through `finite_setOf_isHardlyRamified_frames_of_discreteTopology`,
supplied as `hfin`; (iii) the deformation-condition clauses — the PROVEN
`isHardlyRamified_pushforwardFrame` (whose own residue is the flatness
leaf `isFlatAt_baseChange`), the leaf
`isHardlyRamified_of_fibreProduct` and the leaf
`isHardlyRamified_of_forall_isOpen_quotient` — supplied as `hbase`,
`hglue` and `hlim`; (iv) the passage from Artinian test objects to the
whole of Mazur's category, the separate leaf
`isWeaklyUniversalOnIdentifiedFrames_of_finite`; (v) the
Chebotarev–Brauer–Nesbitt matching that manufactures the residual
identification, supplied by `exists_conj_of_charFrob_eq` through the
proven assembly `exists_isWeaklyUniversal`; (vi) the `charFrob` shadow of
the conjugation clause, discharged by
`exists_isStrictlyUniversalOnFiniteFrames` through
`charpoly_baseChange_conj` — which is exactly why this leaf delivers the
honest residual identification (`IsResidualIdentifiedFrame`) and not a
`charFrob` clause.

Mathematical content. `hschur` says `End_{k[Γ]}(ρbar) = k`, so the
framing is a torsor and Schlessinger's H4 holds; `hfin` is H3, the framed
tangent space (a subset of the hardly ramified lifts over the dual
numbers `k[ε]`) being finite; `hglue` is H1 and H2, which for the FRAMED
functor reduce to the componentwise character of the local conditions
because a homomorphism into `GL₂` of a fibre product is exactly a
compatible pair. Hence by Schlessinger's theorem (Trans. AMS 130 (1968),
Thm. 2.11) and Mazur (§1.2) the functor has a hull, presented by the de
Smit–Lenstra construction as `W(k)[[x₁,…,x_g]]/I`; that quotient is
Noetherian, local, `𝔪`-adically complete and carries the `𝔪`-adic
topology — the three Mazur-category clauses of the conclusion — the
classifying map of a residually identified finite test object is the
required `ψ`, and `hlim` upgrades the compatible system of Artinian
truncations of `ρuniv` to a hardly ramified representation over `R`
itself.

NOTE ON THE MAZUR-CATEGORY CLAUSES. They are delivered by this leaf
rather than cut out as commutative algebra over the presentation
(`IsNoetherianRing`/`IsAdicComplete` from a surjection
`ℤ_ℓ[[x₁,…,x_g]] ↠ R`, as `Patching.lean` cuts them) because this file's
power-series section — including the PROVEN
`isNoetherianRing_mvPowerSeries` — is declared far BELOW this point and
depends on the currying machinery developed there; separating them here
would mean either moving that section above the deformation-theoretic
section or re-sorrying an already proven lemma. Once the section is
moved, the split is available at no mathematical cost. (The base-change
transfer block WAS hoisted, 2026-07-25, which is what turns the
functoriality clause `hbase` from a leaf into the proven
`isHardlyRamified_pushforwardFrame`.)

PARALLEL COPY, NOT IMPORTABLE. `Modularity/Patching.lean` proves the same
statement (`exists_weaklyUniversalOnIdentified_hardlyRamifiedDeformation`)
over the same finite-tangent/finite-tests cut, its Artinian-level leaf
being `exists_framedStrictlyUniversal_hardlyRamified_finiteTests` (whose
`IsStrictlyUniversalOnFramedFiniteLifts` is the unbundled twin of
`IsStrictlyUniversalOnFiniteFrames` above). It cannot be imported here:
`Patching.lean` imports `Modularity/KhareWintenberger.lean`, which
consumes pillar α — which is what this file proves. See
`~/.flt-design-deformation-patching-dedup.md`.

CIRCULARITY GUARD. This leaf carries the `IsHardlyRamified` +
`IsIrreducible` + `5 ≤ ℓ` package that the odd-prime dichotomy
`not_isIrreducible_of_isHardlyRamified_of_five_le` refutes, and that
dichotomy is proven over pillar α — which is what this file's cone
proves. Discharging this leaf vacuously through it is circular and Lean
rejects it. Likewise no import from `Family.lean`, `Lift.lean` or
`Modularity/*` may be added to this module.

References: Schlessinger, *Functors of Artin rings*, Trans. AMS 130
(1968), Thm. 2.11; Mazur, *Deforming Galois representations*, MSRI Publ.
16 (1989), §1.2; de Smit–Lenstra, *Explicit construction of universal
deformation rings*, Prop. 2.3; Böckle's appendix to Khare's
Serre-conjecture notes. -/
theorem exists_isStrictlyUniversalOnFrames_of_deformationCondition (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible)
    (hschur : ∀ f : Module.End k V, (∀ g, Commute f (ρbar g)) →
      ∃ c : k, f = c • 1)
    (hfin : ∀ (A : Type u) [CommRing A] [TopologicalSpace A]
      [IsTopologicalRing A] [IsLocalRing A] [Algebra ℤ_[ℓ] A] [Finite A],
      {ρ : FramedGaloisRep ℚ A (Fin 2) |
        IsHardlyRamified hℓOdd (rank_finTwoFun A) ρ}.Finite)
    (hbase : ∀ {B : Type u} [CommRing B] [TopologicalSpace B]
      [IsTopologicalRing B] [IsLocalRing B] [Algebra ℤ_[ℓ] B]
      {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [IsLocalRing A] [Finite A] [Algebra ℤ_[ℓ] A]
      (ψ : B →+* A) (hψ : Continuous ψ),
      ψ.comp (algebraMap ℤ_[ℓ] B) = algebraMap ℤ_[ℓ] A →
      ∀ {ρ : FramedGaloisRep ℚ B (Fin 2)},
      IsHardlyRamified hℓOdd (rank_finTwoFun B) ρ →
      IsHardlyRamified hℓOdd (rank_finTwoFun A) (pushforwardFrame ψ hψ ρ))
    (hglue : ∀ {A₀ : Type u} [CommRing A₀] [TopologicalSpace A₀]
      [IsTopologicalRing A₀] [IsLocalRing A₀] [Algebra ℤ_[ℓ] A₀] [Finite A₀]
      {A₁ : Type u} [CommRing A₁] [TopologicalSpace A₁] [IsTopologicalRing A₁]
      [IsLocalRing A₁] [Algebra ℤ_[ℓ] A₁] [Finite A₁]
      {A₂ : Type u} [CommRing A₂] [TopologicalSpace A₂] [IsTopologicalRing A₂]
      [IsLocalRing A₂] [Algebra ℤ_[ℓ] A₂] [Finite A₂]
      {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [IsLocalRing B] [Algebra ℤ_[ℓ] B] [Finite B]
      (f₁ : A₁ →+* A₀) (f₂ : A₂ →+* A₀), Function.Surjective f₂ →
      ∀ (p₁ : B →+* A₁) (p₂ : B →+* A₂) (hp₁ : Continuous p₁)
        (hp₂ : Continuous p₂),
      p₁.comp (algebraMap ℤ_[ℓ] B) = algebraMap ℤ_[ℓ] A₁ →
      p₂.comp (algebraMap ℤ_[ℓ] B) = algebraMap ℤ_[ℓ] A₂ →
      f₁.comp p₁ = f₂.comp p₂ →
      Topology.IsEmbedding (fun b : B => (p₁ b, p₂ b)) →
      (∀ (a₁ : A₁) (a₂ : A₂), f₁ a₁ = f₂ a₂ → ∃ b : B, p₁ b = a₁ ∧ p₂ b = a₂) →
      ∀ {ρ : FramedGaloisRep ℚ B (Fin 2)},
      IsHardlyRamified hℓOdd (rank_finTwoFun A₁) (pushforwardFrame p₁ hp₁ ρ) →
      IsHardlyRamified hℓOdd (rank_finTwoFun A₂) (pushforwardFrame p₂ hp₂ ρ) →
      IsHardlyRamified hℓOdd (rank_finTwoFun B) ρ)
    (hlim : ∀ {R : Type u} [CommRing R] [TopologicalSpace R]
      [IsTopologicalRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R]
      [IsNoetherianRing R],
      IsAdic (IsLocalRing.maximalIdeal R) →
      IsAdicComplete (IsLocalRing.maximalIdeal R) R →
      ∀ {ρ : FramedGaloisRep ℚ R (Fin 2)},
      (∀ (I : Ideal R), IsOpen (I : Set R) → ∀ [IsLocalRing (R ⧸ I)]
        (hmk : Continuous (Ideal.Quotient.mk I)),
        IsHardlyRamified hℓOdd (rank_finTwoFun (R ⧸ I))
          (pushforwardFrame (Ideal.Quotient.mk I) hmk ρ)) →
      IsHardlyRamified hℓOdd (rank_finTwoFun R) ρ) :
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

open scoped TensorProduct in
/-- **Schlessinger's hull for the hardly ramified problem** (PROVEN
2026-07-25 over the deformation-condition cut — the statement is
unchanged and its consumer `exists_isStrictlyUniversalOnFiniteFrames`
below is untouched; what changed is that the node is now an ASSEMBLY):
GIVEN Schlessinger's H3 (`hfin`, restricted-ramification finiteness at
every Artinian level) and H4 (`hschur`, `End_{k[Γ]}(ρbar) = k`), the
hardly ramified deformation problem of an irreducible hardly ramified
`ρbar` (`ℓ ≥ 5`) has a hull: a complete Noetherian local topological
`ℤ_ℓ`-algebra `R` with the `𝔪`-adic topology, carrying a hardly ramified
framed representation `ρuniv`, a surjective continuous reduction `πuniv`
identifying `ρuniv ⊗_R k` with `ρbar`, which classifies every FINITE raw
framed test object *strictly* — by a continuous `ℤ_ℓ`-algebra map
compatible with the reductions along which `ρuniv` pushes forward to the
test representation up to the framing ambiguity.

THE CUT: ARITHMETIC OUT OF THE ABSTRACT MACHINE. Schlessinger's theorem
takes a functor on Artinian rings satisfying H1–H4 and returns a hull;
everything specific to the hardly ramified problem enters through the
statement that the four local conditions form a DEFORMATION CONDITION,
in the sense of Mazur §§18–23 and Conrad–Diamond–Taylor §2 — a subfunctor
closed under (i) pushforward along maps of Artinian coefficient rings,
(ii) gluing along fibre products, and (iii) passage to the pro-limit. The
cut splits the node exactly along that seam:

* `exists_isStrictlyUniversalOnFrames_of_deformationCondition` — the
  FORMAL core (Schlessinger's induction, the de Smit–Lenstra
  presentation, the Mazur-category ring clauses), carrying NO arithmetic;
* `isHardlyRamified_pushforwardFrame` — clause (i), PROVEN above, its
  only residue being the flatness leaf `isFlatAt_baseChange`
  (Ramakrishna, Raynaud);
* `isHardlyRamified_of_fibreProduct` — clause (ii), i.e. H1 and H2, whose
  content is Ramakrishna at `ℓ` and Conrad–Diamond–Taylor at `2`;
* `isHardlyRamified_of_forall_isOpen_quotient` — clause (iii);
* `finite_setOf_isHardlyRamified_frames_of_discreteTopology` — H3 for the
  ARBITRARY finite ring topologies that the raw test objects of
  `IsStrictlyUniversalOnFrames` allow, a gap between the H3 leaf
  `finite_setOf_isHardlyRamified_frames` (stated for discrete `A`) and
  this statement's quantifier; see that leaf for why it is not vacuous.

Each of those leaves carries its own docstring; the proof below is
nothing but the application.

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

CIRCULARITY GUARD (inherited by all five leaves of the cut). This node
carries the `IsHardlyRamified` + `IsIrreducible` + `5 ≤ ℓ` package that
the odd-prime dichotomy
`not_isIrreducible_of_isHardlyRamified_of_five_le` refutes, and that
dichotomy is proven over pillar α — which is what this file's cone
proves. Discharging any leaf below it vacuously through that dichotomy is
circular and Lean rejects it. Likewise no import from `Family.lean`,
`Lift.lean` or `Modularity/*` may be added to this module.

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
      IsStrictlyUniversalOnFrames hℓOdd ρbar ρuniv πuniv := by
  refine exists_isStrictlyUniversalOnFrames_of_deformationCondition hℓOdd hdim
    hℓ5 h hirr hschur ?_ ?_ ?_ ?_
  · -- H3, across arbitrary finite ring topologies
    exact finite_setOf_isHardlyRamified_frames_of_discreteTopology hℓOdd hfin
  · -- functoriality of the deformation condition
    intro B _ _ _ _ _ A _ _ _ _ _ _ ψ hψ halg ρ hρ
    exact isHardlyRamified_pushforwardFrame hℓOdd ψ hψ halg hρ
  · -- H1 and H2: gluing along a fibre product
    intro A₀ _ _ _ _ _ _ A₁ _ _ _ _ _ _ A₂ _ _ _ _ _ _ B _ _ _ _ _ _
      f₁ f₂ hf₂ p₁ p₂ hp₁ hp₂ halg₁ halg₂ hcomm hemb hcart ρ h₁ h₂
    exact isHardlyRamified_of_fibreProduct hℓOdd f₁ f₂ hf₂ p₁ p₂ hp₁ hp₂
      halg₁ halg₂ hcomm hemb hcart h₁ h₂
  · -- detection on the finite levels
    intro R _ _ _ _ _ _ hadic hcomplete ρ hq
    exact isHardlyRamified_of_forall_isOpen_quotient hℓOdd hadic hcomplete hq

set_option backward.isDefEq.respectTransparency false in
/-- **Mazur/Ramakrishna representability at the ARTINIAN level** (PROVEN
2026-07-26 over the Schlessinger cut — the H3 finiteness leaf
`finite_setOf_isHardlyRamified_frames`, the H4 Schur node
`exists_smul_eq_of_commute_of_isIrreducible` (itself PROVEN 2026-07-26)
and the deformation-theoretic core
`exists_isStrictlyUniversalOnFrames_of_finite_lifts` (itself PROVEN
2026-07-25 over the deformation-condition cut)): the hardly
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

open scoped Matrix in
open scoped TensorProduct in
/-- **The matrix form of a framed conjugation** (PROVEN 2026-07-25 — the
linear-algebra dictionary of the pro-finite limit
`isWeaklyUniversalOnIdentifiedFrames_of_finite`): a conjugating matrix
`E ∈ GL₂(B)` intertwining the `ψ`-image of a standard-framed
representation `ρ` over `R` with a standard-framed representation `σ`
over `B` produces the linear equivalence
`e : B ⊗_R R² ≃ₗ[B] B²` with `(ρ ⊗ B)ᵉ = σ` that the deformation
vocabulary asks for.

This is what lets the pro-finite limit be taken over PAIRS living in a
type INDEPENDENT of the ring map: the conjugation datum of
`IsWeaklyUniversalOnIdentifiedFrames` is a `≃ₗ` whose very type depends
on the algebra structure induced by `ψ`, so a tower of such data is a
tower over dependent types and does not form an inverse system of sets;
its matrix avatar `(ψ, E) : (R →+* B) × Matrix (Fin 2) (Fin 2) B` does.
(The naive transfer of `Modularity/Patching.lean`'s
`isWeaklyUniversalOnIdentifiedDeformation_of_finiteTests` fails exactly
here: that proof carries only the TRACE-level clause through the limit,
so its inverse system is one of ring maps alone.)

Proof: `e` is the canonical `B ⊗_R R² ≅ B²` (`TensorProduct.piScalarRight`)
followed by the automorphism of `B²` given by `E`
(`Matrix.toLinearEquiv'`, `E` being invertible since its determinant is
a unit). On a simple tensor `b ⊗ w` the base-changed representation acts
as `b ⊗ ρ(g)w`, whose image is `b • (E *ᵥ ψ∘(ρ(g)w))`; entrywise
`ψ∘(ρ(g)w) = (ψ(ρ(g)) *ᵥ ψ∘w)` because `ψ` is a ring homomorphism
(`RingHom.map_mulVec`), so the two sides of the required identity are
`b • ((E * ψ(ρ(g))) *ᵥ ψ∘w)` and `b • ((σ(g) * E) *ᵥ ψ∘w)`. -/
theorem exists_conj_baseChange_of_matrix
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (ψ : R →+* B) (hψ : Continuous ψ)
    (ρ : FramedGaloisRep ℚ R (Fin 2)) (σ : FramedGaloisRep ℚ B (Fin 2))
    (E : Matrix (Fin 2) (Fin 2) B) (hE : IsUnit E.det)
    (hconj : ∀ g : Field.absoluteGaloisGroup ℚ,
      E * (LinearMap.toMatrix' (ρ g)).map ⇑ψ =
        (LinearMap.toMatrix' (σ g)) * E) :
    letI : Algebra R B := ψ.toAlgebra
    letI : ContinuousSMul R B := continuousSMul_of_algebraMap R B
      (by rw [RingHom.algebraMap_toAlgebra]; exact hψ)
    ∃ e : (B ⊗[R] (Fin 2 → R)) ≃ₗ[B] (Fin 2 → B),
      (ρ.baseChange B).conj e = σ := by
  letI : Algebra R B := ψ.toAlgebra
  letI : ContinuousSMul R B := continuousSMul_of_algebraMap R B
    (by rw [RingHom.algebraMap_toAlgebra]; exact hψ)
  haveI : Invertible E := Matrix.invertibleOfIsUnitDet E hE
  set e : (B ⊗[R] (Fin 2 → R)) ≃ₗ[B] (Fin 2 → B) :=
    (TensorProduct.piScalarRight R B B (Fin 2)).trans
      (Matrix.toLinearEquiv' E inferInstance) with he
  -- the scalar action of `R` on `B` is `ψ`
  have hsmul : ∀ (r : R) (b : B), r • b = ψ r * b := fun r b => by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  -- `e` on a simple tensor is `E` applied to the `ψ`-image, scaled by `b`
  have hetmul : ∀ (b : B) (w : Fin 2 → R),
      e (b ⊗ₜ[R] w) = b • (E *ᵥ (fun j => ψ (w j))) := by
    intro b w
    rw [he]
    show E *ᵥ (TensorProduct.piScalarRight R B B (Fin 2) (b ⊗ₜ[R] w)) = _
    rw [TensorProduct.piScalarRight_apply,
      TensorProduct.piScalarRightHom_tmul]
    rw [show (fun j => w j • b) = b • (fun j => ψ (w j)) from by
      funext j
      rw [hsmul]
      show ψ (w j) * b = b * ψ (w j)
      rw [mul_comm]]
    exact Matrix.mulVec_smul E b _
  refine ⟨e, GaloisRep.ext fun g => ?_⟩
  rw [GaloisRep.conj_apply]
  refine LinearMap.ext fun v => ?_
  rw [LinearEquiv.conj_apply_apply]
  -- the identity on simple tensors, extended by linearity
  have key : ∀ x : B ⊗[R] (Fin 2 → R),
      e ((ρ.baseChange B) g x) = σ g (e x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul b w =>
      rw [GaloisRep.baseChange_tmul, hetmul, hetmul]
      have hmap : (fun j => ψ ((ρ g w) j)) =
          (LinearMap.toMatrix' (ρ g)).map ⇑ψ *ᵥ (fun j => ψ (w j)) := by
        funext i
        rw [show (ρ g w) = LinearMap.toMatrix' (ρ g) *ᵥ w from
          (LinearMap.toMatrix'_mulVec (ρ g) w).symm]
        exact RingHom.map_mulVec ψ (LinearMap.toMatrix' (ρ g)) w i
      rw [hmap, Matrix.mulVec_mulVec]
      rw [show σ g (b • (E *ᵥ (fun j => ψ (w j)))) =
          b • (LinearMap.toMatrix' (σ g) *ᵥ (E *ᵥ (fun j => ψ (w j)))) from by
        rw [map_smul, ← LinearMap.toMatrix'_mulVec (σ g)]]
      rw [Matrix.mulVec_mulVec, hconj g]
  rw [key (e.symm v), LinearEquiv.apply_symm_apply]

open CategoryTheory in
/-- **Kőnig's lemma plus adic assembly, for PAIRS** (PROVEN 2026-07-25 —
steps 3 and 4 of the pro-finite limit
`isWeaklyUniversalOnIdentifiedFrames_of_finite`, pure commutative
algebra): let `A` be `I`-adically complete and separated and let `X n`
be, for each `n`, a NONEMPTY FINITE set of pairs — a ring homomorphism
`R →+* A ⧸ Iⁿ` together with a square matrix over `A ⧸ Iⁿ` — that is
STABLE under the transition maps `A ⧸ Iᵐ →+* A ⧸ Iⁿ` (`n ≤ m`), applied
to the ring map by postcomposition and to the matrix entrywise. Then
there is a single pair `(ψ, E)` over `A` all of whose level-`n`
reductions lie in `X n`.

Why PAIRS and not ring maps alone: the conjugation datum that
representation-level universality carries through the limit is a linear
equivalence whose TYPE depends on the ring map, so the tower is one of
dependent pairs; `exists_conj_baseChange_of_matrix` above replaces the
equivalence by its matrix, which lives in a type independent of the ring
map, and this lemma is then the ordinary inverse-limit statement for the
resulting product type. `Modularity/Patching.lean`'s
`exists_ringHom_of_forall_quotient_mem` is the ring-map-only shadow of
this statement (and is still a sorry node there).

Proof: the `X n` with the postcomposition transitions form an inverse
system of nonempty finite sets over `ℕᵒᵖ`, so its limit is nonempty by
Kőnig's lemma (`nonempty_sections_of_finite_inverse_system`;
functoriality of the system is `Ideal.Quotient.factor_mk` twice over).
A section gives compatible families `(ψₙ, Eₙ)`. Both are assembled at
once by a single application of the universal property of adic
completeness for ring maps (`IsAdicComplete.liftRingHom`), applied not
to `R` but to the polynomial ring `R[Xᵢⱼ]`: the level-`n` ring map
`R[Xᵢⱼ] →+* A ⧸ Iⁿ` is `ψₙ` on constants and `Xᵢⱼ ↦ (Eₙ)ᵢⱼ`, the family
is compatible because it is so on constants and on variables
(`MvPolynomial.ringHom_ext`), and the lift restricted to constants is
`ψ` while its values on the variables are the entries of `E`. -/
theorem exists_ringHom_matrix_of_forall_quotient_mem
    {A : Type*} [CommRing A] (I : Ideal A) [IsAdicComplete I A]
    {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : ∀ n : ℕ, Set ((R →+* A ⧸ I ^ n) × Matrix ι ι (A ⧸ I ^ n)))
    (hfin : ∀ n : ℕ, (X n).Finite) (hne : ∀ n : ℕ, (X n).Nonempty)
    (hstab : ∀ (m n : ℕ) (hmn : n ≤ m)
        (p : (R →+* A ⧸ I ^ m) × Matrix ι ι (A ⧸ I ^ m)), p ∈ X m →
      ((Ideal.Quotient.factorPow I hmn).comp p.1,
        p.2.map ⇑(Ideal.Quotient.factorPow I hmn)) ∈ X n) :
    ∃ (ψ : R →+* A) (E : Matrix ι ι A), ∀ n : ℕ,
      ((Ideal.Quotient.mk (I ^ n)).comp ψ,
        E.map ⇑(Ideal.Quotient.mk (I ^ n))) ∈ X n := by
  classical
  -- functoriality of the transition maps
  have hfacComp : ∀ {a b c : ℕ} (h1 : a ≤ b) (h2 : b ≤ c) (y : A ⧸ I ^ c),
      Ideal.Quotient.factorPow I h1 (Ideal.Quotient.factorPow I h2 y) =
        Ideal.Quotient.factorPow I (h1.trans h2) y := by
    intro a b c h1 h2 y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk,
      Ideal.Quotient.factor_mk]
  -- the inverse system of nonempty finite sets of pairs
  let F : ℕᵒᵖ ⥤ Type _ :=
    { obj := fun j => ↥(X j.unop)
      map := fun {j j'} f =>
        ↾(fun p : ↥(X j.unop) =>
          (⟨((Ideal.Quotient.factorPow I (leOfHom f.unop)).comp p.1.1,
              p.1.2.map ⇑(Ideal.Quotient.factorPow I (leOfHom f.unop))),
            hstab j.unop j'.unop (leOfHom f.unop) p.1 p.2⟩ : ↥(X j'.unop)))
      map_id := fun j => by
        ext p <;> simp
      map_comp := fun {j₁ j₂ j₃} f g => by
        ext p <;> simp [hfacComp] }
  haveI : ∀ j : ℕᵒᵖ, Finite (F.obj j) := fun j => (hfin j.unop).to_subtype
  haveI : ∀ j : ℕᵒᵖ, Nonempty (F.obj j) := fun j => (hne j.unop).to_subtype
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_inverse_system F
  -- the level-`n` data extracted from the section
  set f : ∀ n : ℕ, (R →+* A ⧸ I ^ n) × Matrix ι ι (A ⧸ I ^ n) :=
    fun n => (s (Opposite.op n)).1 with hf
  have hcompat : ∀ (m n : ℕ) (hmn : n ≤ m),
      ((Ideal.Quotient.factorPow I hmn).comp (f m).1,
        (f m).2.map ⇑(Ideal.Quotient.factorPow I hmn)) = f n := by
    intro m n hmn
    have hsec := hs (homOfLE hmn).op
    exact congrArg Subtype.val hsec
  -- both data at once, as a single family of ring maps out of a polynomial ring
  set G : ∀ n : ℕ, MvPolynomial (ι × ι) R →+* A ⧸ I ^ n :=
    fun n => MvPolynomial.eval₂Hom (f n).1 (fun q => (f n).2 q.1 q.2) with hG
  have hGcompat : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow I hle).comp (G n) = G m := by
    intro m n hle
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun q => ?_)
    · have h1 := congrArg (fun t => t.1) (hcompat n m hle)
      have h2 := RingHom.congr_fun h1 r
      simpa [hG] using h2
    · have h1 := congrArg (fun t => t.2) (hcompat n m hle)
      have h2 := congrFun (congrFun h1 q.1) q.2
      simpa [hG] using h2
  -- assemble by adic completeness
  set Ghat : MvPolynomial (ι × ι) R →+* A :=
    IsAdicComplete.liftRingHom I G hGcompat with hGhat
  refine ⟨Ghat.comp MvPolynomial.C,
    Matrix.of fun i i' => Ghat (MvPolynomial.X (i, i')), fun n => ?_⟩
  have hlvl : ((Ideal.Quotient.mk (I ^ n)).comp (Ghat.comp MvPolynomial.C),
      (Matrix.of fun i i' => Ghat (MvPolynomial.X (i, i'))).map
        ⇑(Ideal.Quotient.mk (I ^ n))) = f n := by
    refine Prod.ext (RingHom.ext fun r => ?_) (Matrix.ext fun i i' => ?_)
    · have := RingHom.congr_fun
        (IsAdicComplete.mk_comp_liftRingHom I G hGcompat n) (MvPolynomial.C r)
      simpa [hGhat, hG] using this
    · have := RingHom.congr_fun
        (IsAdicComplete.mk_comp_liftRingHom I G hGcompat n)
        (MvPolynomial.X (i, i'))
      simpa [hGhat, hG] using this
  rw [hlvl, hf]
  exact (s (Opposite.op n)).2

/-- **The maximal ideal of a FINITE local ring is nilpotent** (PROVEN
2026-07-25, pure commutative algebra): a finite ring is Artinian, and the
Jacobson radical of a commutative Artinian ring is nilpotent
(`IsArtinianRing.isNilpotent_jacobson_bot`); over a local ring that
radical IS the maximal ideal (`IsLocalRing.jacobson_eq_maximalIdeal`).

The workhorse of the quotient-deformation construction inside
`exists_ringHom_matrix_quotient_of_finite`: it is what makes the finite
quotient `D'.R ⧸ I` an object of Mazur's category at all, supplying in
one stroke its discreteness, its `IsAdic` clause and its
`IsAdicComplete` clause (the three lemmas below). -/
theorem exists_maximalIdeal_pow_eq_bot (A : Type*) [CommRing A] [Finite A]
    [IsLocalRing A] : ∃ N : ℕ, IsLocalRing.maximalIdeal A ^ N = ⊥ := by
  haveI : IsArtinianRing A := isArtinian_of_finite
  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  refine ⟨N, ?_⟩
  rwa [IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal A) bot_ne_top,
    Ideal.zero_eq_bot] at hN

/-- **A nilpotent ideal is adically complete** (PROVEN 2026-07-25, pure
commutative algebra): if `J ^ N = ⊥` the `J`-adic filtration is
eventually zero, so the ring is `J`-adically separated (anything
congruent to `0` modulo `J ^ N` IS `0`) and precomplete (a compatible
sequence is constant from level `N` on, and its `N`-th term is a
limit). -/
theorem isAdicComplete_of_pow_eq_bot {A : Type*} [CommRing A] {J : Ideal A}
    {N : ℕ} (hJ : J ^ N = ⊥) : IsAdicComplete J A := by
  haveI : IsHausdorff J A := by
    constructor
    intro x hx
    have h := hx N
    rw [hJ] at h
    simpa using h
  haveI : IsPrecomplete J A := by
    constructor
    intro f hf
    refine ⟨f N, fun n => ?_⟩
    rcases le_total n N with hle | hle
    · exact hf hle
    · have h := hf hle
      rw [hJ] at h
      simp only [Submodule.bot_smul, SModEq.bot] at h
      rw [h]
  constructor

/-- **On a DISCRETE ring a nilpotent ideal is adic** (PROVEN 2026-07-25):
in the discrete topology every set is open, and `J ^ N = ⊥ = {0}` sits
inside every neighbourhood of `0`, which is exactly the two clauses of
`isAdic_iff`. (The `⊥`-case of this is mathlib's `is_bot_adic_iff`; what
is needed here is the nilpotent case, `J` being the maximal ideal of a
finite local ring rather than `⊥`.) -/
theorem isAdic_of_pow_eq_bot {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A] {J : Ideal A} {N : ℕ}
    (hJ : J ^ N = ⊥) : IsAdic J := by
  rw [isAdic_iff]
  refine ⟨fun n => isOpen_discrete _, fun s hs => ⟨N, ?_⟩⟩
  rw [hJ]
  intro x hx
  have hx0 : x = 0 := by simpa using hx
  subst hx0
  exact mem_of_mem_nhds hs

/-- **A proper ideal with FINITE quotient is open** (PROVEN 2026-07-25,
pure commutative algebra): in a local ring carrying the `𝔪`-adic
topology, an ideal `I ≠ ⊤` whose quotient is finite contains a power of
`𝔪`, hence is a union of cosets of an open ideal and is open.

The power is produced by `exists_maximalIdeal_pow_eq_bot` applied to the
finite local ring `A ⧸ I`: its maximal ideal `𝔫` satisfies `𝔫 ^ N = ⊥`,
the quotient map is local (`isLocalHom_of_le_jacobson_bot`, `I` lying
inside `𝔪 = jacobson ⊥`) so `𝔪` maps into `𝔫`, and `(𝔪 ^ N).map = ⊥`
says exactly `𝔪 ^ N ≤ I`. `Ideal.isOpen_of_isOpen_subideal` finishes.

This is the converse direction of the proven
`finite_quotient_of_maximalIdeal_pow_le` above, and it is what makes the
quotient topology on `D'.R ⧸ I` DISCRETE. -/
theorem isOpen_of_ne_top_of_finite_quotient {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLocalRing A]
    (hadic : IsAdic (IsLocalRing.maximalIdeal A)) (I : Ideal A)
    (hItop : I ≠ ⊤) (hfin : Finite (A ⧸ I)) : IsOpen (I : Set A) := by
  haveI := hfin
  haveI : Nontrivial (A ⧸ I) := by
    rw [← not_subsingleton_iff_nontrivial, Ideal.Quotient.subsingleton_iff]
    exact hItop
  haveI : IsLocalRing (A ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk I) :=
    isLocalHom_of_le_jacobson_bot I (by
      rw [IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal A) bot_ne_top]
      exact IsLocalRing.le_maximalIdeal hItop)
  obtain ⟨N, hN⟩ := exists_maximalIdeal_pow_eq_bot (A ⧸ I)
  have hmapmono : (IsLocalRing.maximalIdeal A).map (Ideal.Quotient.mk I) ≤
      IsLocalRing.maximalIdeal (A ⧸ I) := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    show Ideal.Quotient.mk I y ∈ IsLocalRing.maximalIdeal (A ⧸ I)
    rw [IsLocalRing.mem_maximalIdeal] at hy ⊢
    exact fun hu => hy (isUnit_of_map_unit (Ideal.Quotient.mk I) y hu)
  have hmono : ∀ n : ℕ,
      ((IsLocalRing.maximalIdeal A).map (Ideal.Quotient.mk I)) ^ n ≤
        IsLocalRing.maximalIdeal (A ⧸ I) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ m ih => rw [pow_succ, pow_succ]; exact Ideal.mul_mono ih hmapmono
  have hle : IsLocalRing.maximalIdeal A ^ N ≤ I := by
    have hpow : ((IsLocalRing.maximalIdeal A) ^ N).map (Ideal.Quotient.mk I) = ⊥ := by
      rw [Ideal.map_pow, ← le_bot_iff, ← hN]
      exact hmono N
    rwa [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at hpow
  exact Ideal.isOpen_of_isOpen_subideal hle ((isAdic_iff.mp hadic).1 N)

open scoped Matrix in
open scoped TensorProduct in
/-- **The canonical framing turns a base change into a matrix image**
(PROVEN 2026-07-25 — the computational core shared by
`toMatrix'_pushforwardFrame` and the matrix dictionary
`exists_matrix_of_conj_baseChange` below): under the identification
`B ⊗_R R² ≅ B²` of `TensorProduct.piScalarRight`, the base change of a
standard-framed `ρ` along `ψ : R →+* B` acts as multiplication by the
matrix `ψ(ρ(g))` obtained by applying `ψ` entrywise.

On a simple tensor `b ⊗ w` both sides are `b • (ψ(ρ(g)) *ᵥ ψ∘w)`: the
framing sends `b ⊗ w` to `b • ψ∘w`, and `ψ∘(ρ(g)w) = ψ(ρ(g)) *ᵥ ψ∘w`
because `ψ` is a ring homomorphism (`RingHom.map_mulVec`). -/
theorem piScalarRight_baseChange_apply {R : Type u} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R]
    {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (ψ : R →+* B) (hψ : Continuous ψ) (ρ : FramedGaloisRep ℚ R (Fin 2))
    (g : Field.absoluteGaloisGroup ℚ) :
    letI : Algebra R B := ψ.toAlgebra
    letI : ContinuousSMul R B := continuousSMul_of_algebraMap R B
      (by rw [RingHom.algebraMap_toAlgebra]; exact hψ)
    ∀ x : B ⊗[R] (Fin 2 → R),
      TensorProduct.piScalarRight R B B (Fin 2) ((ρ.baseChange B) g x) =
        ((LinearMap.toMatrix' (ρ g)).map ⇑ψ) *ᵥ
          (TensorProduct.piScalarRight R B B (Fin 2) x) := by
  letI : Algebra R B := ψ.toAlgebra
  letI : ContinuousSMul R B := continuousSMul_of_algebraMap R B
    (by rw [RingHom.algebraMap_toAlgebra]; exact hψ)
  have hsmul : ∀ (r : R) (b : B), r • b = ψ r * b := fun r b => by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  have hptmul : ∀ (b : B) (w : Fin 2 → R),
      TensorProduct.piScalarRight R B B (Fin 2) (b ⊗ₜ[R] w) =
        b • (fun j => ψ (w j)) := by
    intro b w
    rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
    rw [show (fun j => w j • b) = b • (fun j => ψ (w j)) from by
      funext j
      rw [hsmul]
      show ψ (w j) * b = b * ψ (w j)
      rw [mul_comm]]
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb, Matrix.mulVec_add]
  | tmul b w =>
    rw [GaloisRep.baseChange_tmul, hptmul, hptmul]
    have hmap : (fun j => ψ ((ρ g w) j)) =
        (LinearMap.toMatrix' (ρ g)).map ⇑ψ *ᵥ (fun j => ψ (w j)) := by
      funext i
      rw [show (ρ g w) = LinearMap.toMatrix' (ρ g) *ᵥ w from
        (LinearMap.toMatrix'_mulVec (ρ g) w).symm]
      exact RingHom.map_mulVec ψ (LinearMap.toMatrix' (ρ g)) w i
    rw [hmap, Matrix.mulVec_smul]

open scoped Matrix in
/-- **The matrix of a pushed-forward frame is the entrywise image**
(PROVEN 2026-07-25): `pushforwardFrame ψ hψ ρ` really is "apply `ψ` to
the matrix entries of `ρ`", which is what its docstring promises and what
makes it usable as the level-`n` datum of an inverse system of
MATRICES. -/
theorem toMatrix'_pushforwardFrame {B : Type u} [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] (ψ : B →+* A)
    (hψ : Continuous ψ) (ρ : FramedGaloisRep ℚ B (Fin 2))
    (g : Field.absoluteGaloisGroup ℚ) :
    LinearMap.toMatrix' (pushforwardFrame ψ hψ ρ g) =
      (LinearMap.toMatrix' (ρ g)).map ⇑ψ := by
  letI : Algebra B A := ψ.toAlgebra
  letI : ContinuousSMul B A := continuousSMul_of_algebraMap B A
    (by rw [RingHom.algebraMap_toAlgebra]; exact hψ)
  have happ : ∀ w : Fin 2 → A,
      (pushforwardFrame ψ hψ ρ) g w =
        ((LinearMap.toMatrix' (ρ g)).map ⇑ψ) *ᵥ w := by
    intro w
    rw [show (pushforwardFrame ψ hψ ρ) g =
      (TensorProduct.piScalarRight B A A (Fin 2)).conj ((ρ.baseChange A) g)
      from rfl, LinearEquiv.conj_apply_apply,
      piScalarRight_baseChange_apply ψ hψ ρ g, LinearEquiv.apply_symm_apply]
  have hlin : (pushforwardFrame ψ hψ ρ g : (Fin 2 → A) →ₗ[A] (Fin 2 → A)) =
      Matrix.toLin' ((LinearMap.toMatrix' (ρ g)).map ⇑ψ) := by
    refine LinearMap.ext fun w => ?_
    rw [Matrix.toLin'_apply, happ]
  rw [hlin, LinearMap.toMatrix'_toLin']

/-- **Pushforward depends only on the ring map** (PROVEN 2026-07-25):
the continuity witness is a proof, so equal maps give equal pushforwards.
Needed because `pushforwardFrame` takes its continuity proof as an
explicit argument, which makes the map argument occur in a
dependently-typed position and blocks a plain `rw`. -/
theorem pushforwardFrame_congr {B : Type u} [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] {ψ χ : B →+* A} (hψ : Continuous ψ)
    (hχ : Continuous χ) (h : ψ = χ) (ρ : FramedGaloisRep ℚ B (Fin 2)) :
    pushforwardFrame ψ hψ ρ = pushforwardFrame χ hχ ρ := by
  subst h
  rfl

/-- **Pushforward is functorial** (PROVEN 2026-07-25): pushing forward
along `ψ` and then along `χ` is pushing forward along `χ ∘ ψ`. Read on
matrices (`toMatrix'_pushforwardFrame`) this is just
`Matrix.map_map`. -/
theorem pushforwardFrame_comp {B : Type u} [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] {C : Type u} [CommRing C] [TopologicalSpace C]
    [IsTopologicalRing C] (ψ : B →+* A) (hψ : Continuous ψ) (χ : A →+* C)
    (hχ : Continuous χ) (hcomp : Continuous ⇑(χ.comp ψ))
    (ρ : FramedGaloisRep ℚ B (Fin 2)) :
    pushforwardFrame χ hχ (pushforwardFrame ψ hψ ρ) =
      pushforwardFrame (χ.comp ψ) hcomp ρ := by
  refine GaloisRep.ext fun g => ?_
  refine LinearMap.toMatrix'.injective ?_
  rw [toMatrix'_pushforwardFrame χ hχ (pushforwardFrame ψ hψ ρ) g,
    toMatrix'_pushforwardFrame ψ hψ ρ g,
    toMatrix'_pushforwardFrame (χ.comp ψ) hcomp ρ g, Matrix.map_map]
  rfl

/-- **Conjugation composes** (PROVEN 2026-07-25): conjugating by `a` then
by `b` is conjugating by `a.trans b`. Consumed by the residual-identity
transport inside `exists_ringHom_matrix_quotient_of_finite`, which has to
move an identification stated against a tensor product onto the standard
frame. -/
theorem GaloisRep.conj_trans {A : Type*} [CommRing A] [TopologicalSpace A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Free A M]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
    [Module.Free A N]
    {P : Type*} [AddCommGroup P] [Module A P] [Module.Finite A P]
    [Module.Free A P]
    (ρ : GaloisRep ℚ A M) (a : M ≃ₗ[A] N) (b : N ≃ₗ[A] P) :
    (ρ.conj a).conj b = ρ.conj (a.trans b) := by
  refine GaloisRep.ext fun g => ?_
  refine LinearMap.ext fun x => ?_
  simp only [GaloisRep.conj_apply, LinearEquiv.conj_apply_apply,
    LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply]

/-- **Characteristic polynomials push forward by coefficient extension**
(PROVEN 2026-07-25): the `pushforwardFrame` specialization of
`charpoly_baseChange_conj`, with the algebra map read back as `ψ`. -/
theorem charpoly_pushforwardFrame {B : Type u} [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] (ψ : B →+* A)
    (hψ : Continuous ψ) (ρ : FramedGaloisRep ℚ B (Fin 2))
    (g : Field.absoluteGaloisGroup ℚ) :
    ((pushforwardFrame ψ hψ ρ) g).charpoly = ((ρ g).charpoly).map ψ := by
  letI : Algebra B A := ψ.toAlgebra
  letI : ContinuousSMul B A := continuousSMul_of_algebraMap B A
    (by rw [RingHom.algebraMap_toAlgebra]; exact hψ)
  have h := charpoly_baseChange_conj ρ
    (TensorProduct.piScalarRight B A A (Fin 2)) g
  rwa [RingHom.algebraMap_toAlgebra] at h

open scoped Matrix in
open scoped TensorProduct in
/-- **The matrix form of a framed conjugation, CONVERSE direction**
(PROVEN 2026-07-25 — the reading of `exists_conj_baseChange_of_matrix`
that the level leaf actually needs): a linear equivalence
`e : B ⊗_R R² ≃ₗ[B] B²` conjugating the `ψ`-pushforward of `ρ` onto `σ`
is a conjugating MATRIX `E ∈ GL₂(B)`.

`E` is the matrix of `u := piScalarRight⁻¹ ≫ e`, a `B`-linear
automorphism of `B²`; its determinant is a unit because
`toMatrix' u * toMatrix' u⁻¹ = 1` (`Matrix.isUnit_det_of_right_inverse`).
The intertwining identity is `piScalarRight_baseChange_apply` read
through `u`: `p` carries the base-changed action onto multiplication by
`ψ(ρ(g))`, so `u ∘ ψ(ρ(g)) = σ(g) ∘ u` as linear maps, and
`LinearMap.toMatrix'_comp` turns that into `E · ψ(ρ(g)) = σ(g) · E`.

Deformation-theoretically this is the step that removes the DEPENDENT
type: `e` lives in a type that depends on the algebra structure `ψ`
induces, `E` does not — which is what lets the pro-finite limit above be
taken over honest pairs. -/
theorem exists_matrix_of_conj_baseChange
    {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (ψ : R →+* B) (hψ : Continuous ψ)
    (ρ : FramedGaloisRep ℚ R (Fin 2)) (σ : FramedGaloisRep ℚ B (Fin 2))
    (h : letI : Algebra R B := ψ.toAlgebra
      letI : ContinuousSMul R B := continuousSMul_of_algebraMap R B
        (by rw [RingHom.algebraMap_toAlgebra]; exact hψ)
      ∃ e : (B ⊗[R] (Fin 2 → R)) ≃ₗ[B] (Fin 2 → B),
        (ρ.baseChange B).conj e = σ) :
    ∃ E : Matrix (Fin 2) (Fin 2) B, IsUnit E.det ∧
      ∀ g : Field.absoluteGaloisGroup ℚ,
        E * (LinearMap.toMatrix' (ρ g)).map ⇑ψ =
          (LinearMap.toMatrix' (σ g)) * E := by
  letI : Algebra R B := ψ.toAlgebra
  letI : ContinuousSMul R B := continuousSMul_of_algebraMap R B
    (by rw [RingHom.algebraMap_toAlgebra]; exact hψ)
  obtain ⟨e, he⟩ := h
  set p : (B ⊗[R] (Fin 2 → R)) ≃ₗ[B] (Fin 2 → B) :=
    TensorProduct.piScalarRight R B B (Fin 2) with hp
  set u : (Fin 2 → B) ≃ₗ[B] (Fin 2 → B) := p.symm.trans e with hu
  refine ⟨LinearMap.toMatrix' (u : (Fin 2 → B) →ₗ[B] (Fin 2 → B)), ?_, ?_⟩
  · refine Matrix.isUnit_det_of_right_inverse
      (B := LinearMap.toMatrix' (u.symm : (Fin 2 → B) →ₗ[B] (Fin 2 → B))) ?_
    rw [← LinearMap.toMatrix'_comp,
      show (u : (Fin 2 → B) →ₗ[B] (Fin 2 → B)).comp
          (u.symm : (Fin 2 → B) →ₗ[B] (Fin 2 → B)) = LinearMap.id from by
        refine LinearMap.ext fun w => ?_
        simp,
      LinearMap.toMatrix'_id]
  · intro g
    have hlin : (u : (Fin 2 → B) →ₗ[B] (Fin 2 → B)).comp
        (Matrix.toLin' ((LinearMap.toMatrix' (ρ g)).map ⇑ψ)) =
        (σ g).comp (u : (Fin 2 → B) →ₗ[B] (Fin 2 → B)) := by
      refine LinearMap.ext fun w => ?_
      have hx := piScalarRight_baseChange_apply ψ hψ ρ g (p.symm w)
      rw [hp] at hx
      rw [LinearEquiv.apply_symm_apply] at hx
      have hy : p.symm (((LinearMap.toMatrix' (ρ g)).map ⇑ψ) *ᵥ w) =
          (ρ.baseChange B) g (p.symm w) := by
        rw [← hx, LinearEquiv.symm_apply_apply]
      have hz := congrArg
        (fun τ : GaloisRep ℚ B (Fin 2 → B) => τ g (e (p.symm w))) he
      simp only [GaloisRep.conj_apply, LinearEquiv.conj_apply_apply,
        LinearEquiv.symm_apply_apply] at hz
      show u (((LinearMap.toMatrix' (ρ g)).map ⇑ψ) *ᵥ w) = σ g (u w)
      rw [hu]
      show e (p.symm (((LinearMap.toMatrix' (ρ g)).map ⇑ψ) *ᵥ w)) =
        σ g (e (p.symm w))
      rw [hy]
      exact hz
    have hm := congrArg LinearMap.toMatrix' hlin
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp,
      LinearMap.toMatrix'_toLin'] at hm

open scoped Matrix in
open scoped TensorProduct in
set_option linter.unusedSectionVars false in
/-- **The level-`I` classifying pair of a residually identified
deformation** (PROVEN 2026-07-25 — step 1 of the pro-finite limit
`isWeaklyUniversalOnIdentifiedFrames_of_finite`, its
deformation-theoretic stratum, and the only part of that limit which is
not pure commutative algebra): a deformation `D` classifying every
FINITE residually identified deformation classifies `D'` modulo every
proper ideal `I` with finite quotient inside `ker D'.π` — by a ring map
`ψ : D.R →+* D'.R ⧸ I` compatible with the `ℤ_ℓ`-structures and the
reductions, together with an invertible matrix `E` conjugating the
`ψ`-pushforward of `D.ρ` onto the reduction of `D'.ρ`.

Classical proof: base change `D'` along the surjection `D'.R ↠ D'.R ⧸ I`.
The quotient is a FINITE local ring (local because `I ≠ ⊤`), Noetherian
and — its maximal ideal being nilpotent — discrete, `𝔪`-adic and
`𝔪`-adically complete, so
`Dq := (D'.R ⧸ I, (D'.ρ ⊗ (D'.R ⧸ I))ᵉ, D'.π/I)` is an object of this
file's `HardlyRamifiedDeformation` category with FINITE coefficient
ring: hardly-ramifiedness pushes forward by
`isHardlyRamified_baseChange_quotient` (with its ingredients
`isFlatAt_baseChange_quotient` and `isTameAtTwo_baseChange`, all three
hoisted above this point) followed by `isHardlyRamified_conj` along the
canonical `(D'.R ⧸ I) ⊗ (Fin 2 → D'.R) ≅ Fin 2 → (D'.R ⧸ I)`
(`TensorProduct.piScalarRight` — the same re-framing step as in
`exists_hardlyRamified_lift_of_five_le`), the reduction map factors
because `I ≤ ker D'.π`, and the residual identification of `Dq` is that
of `D'` transported through the tensor cancellation
`k ⊗_{D'.R ⧸ I} ((D'.R ⧸ I) ⊗_{D'.R} M) ≅ k ⊗_{D'.R} M`. Feeding `Dq`
to the finite hypothesis `hD` yields the ring map and the conjugating
linear equivalence; the equivalence becomes the matrix `E` by reading it
in the standard frames, its determinant being a unit because it is an
isomorphism.

WHAT THE PROOF ACTUALLY DOES, and where it differs from the sketch
above. The test object `Dq` is built with `pushforwardFrame`, the
canonical "apply the quotient map to the matrix entries" pushforward
introduced with the deformation-condition cut, rather than by hand as a
base change followed by a re-framing; its hardly-ramifiedness is then
`isHardlyRamified_pushforwardFrame` in one step. The Mazur-category
clauses of `D'.R ⧸ I` all come from ONE fact — its maximal ideal is
nilpotent, `exists_maximalIdeal_pow_eq_bot`, the ring being finite hence
Artinian: that makes `I` open (`isOpen_of_ne_top_of_finite_quotient`),
hence the quotient topology DISCRETE, hence `IsAdic`
(`isAdic_of_pow_eq_bot`) and `IsAdicComplete`
(`isAdicComplete_of_pow_eq_bot`).

The residual identification transports WITHOUT any tensor-cancellation
argument, which is the simplification the `pushforwardFrame` vocabulary
buys: reading both identifications in the standard frame through
`GaloisRep.conj_trans` turns the claim into the functoriality
`pushforwardFrame (D'.π/I) ∘ pushforwardFrame (mk I) = pushforwardFrame
D'.π` (`pushforwardFrame_comp` plus `pushforwardFrame_congr`), i.e. into
`Matrix.map_map`. Likewise `charFrob_compat` is
`charpoly_pushforwardFrame` plus `Polynomial.map_map`. Finally the
linear equivalence delivered by `hD` becomes the matrix `E` by
`exists_matrix_of_conj_baseChange`, the converse of
`exists_conj_baseChange_of_matrix`.

(The base-change transfer lemmas `isFlatAt_baseChange_quotient` and
`isHardlyRamified_baseChange_quotient` were stated for PRIME quotients;
the ideals of interest here — the powers `𝔪ⁿ` — are not prime and
primality was nowhere consumed, so the `[P.IsPrime]` hypothesis was
dropped from both. That generalization is no longer on this proof's
path, `isHardlyRamified_pushforwardFrame` having replaced the hand-built
chain, but it is a strict weakening and every call site still
typechecks.)

CIRCULARITY GUARD (inherited from the leaf): the hypothesis package is
the one the odd-prime dichotomy
`not_isIrreducible_of_isHardlyRamified_of_five_le` refutes, and that
dichotomy is proven over pillar α, which this cluster proves; a vacuous
discharge through it is circular. No import from `Family.lean`,
`Lift.lean` or `Modularity/*` may be added. -/
theorem exists_ringHom_matrix_quotient_of_finite
    {ρbar : GaloisRep ℚ k V} (D : HardlyRamifiedDeformation hℓOdd ρbar)
    (hD : D.IsWeaklyUniversalOnIdentifiedFramesFinite)
    (D' : HardlyRamifiedDeformation hℓOdd ρbar)
    (hid : D'.IsResidualIdentified) :
    letI := D.commRing; letI := D.topologicalSpace; letI := D.isTopologicalRing
    letI := D.isLocalRing; letI := D.algebra
    letI := D'.commRing; letI := D'.topologicalSpace
    letI := D'.isTopologicalRing; letI := D'.isLocalRing; letI := D'.algebra
    ∀ (I : Ideal D'.R), I ≠ ⊤ → Finite (D'.R ⧸ I) →
      ∀ hIπ : ∀ a ∈ I, D'.π a = 0,
      ∃ (ψ : D.R →+* D'.R ⧸ I) (E : Matrix (Fin 2) (Fin 2) (D'.R ⧸ I)),
        ψ.comp (algebraMap ℤ_[ℓ] D.R) =
            (Ideal.Quotient.mk I).comp (algebraMap ℤ_[ℓ] D'.R) ∧
          (Ideal.Quotient.lift I D'.π hIπ).comp ψ = D.π ∧
          IsUnit E.det ∧
          ∀ g : Field.absoluteGaloisGroup ℚ,
            E * (LinearMap.toMatrix' (D.ρ g)).map ⇑ψ =
              ((LinearMap.toMatrix' (D'.ρ g)).map
                ⇑(Ideal.Quotient.mk I)) * E := by
  letI := D.commRing; letI := D.topologicalSpace; letI := D.isTopologicalRing
  letI := D.isLocalRing; letI := D.algebra
  letI := D'.commRing; letI := D'.topologicalSpace
  letI := D'.isTopologicalRing; letI := D'.isLocalRing; letI := D'.algebra
  letI := D'.isNoetherianRing
  intro I hItop hIfin hIπ
  haveI := hIfin
  -- `D'.R ⧸ I` is a nontrivial finite local ring: discrete, adic, complete
  haveI hnt : Nontrivial (D'.R ⧸ I) := by
    rw [← not_subsingleton_iff_nontrivial, Ideal.Quotient.subsingleton_iff]
    exact hItop
  haveI hlocQ : IsLocalRing (D'.R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hmkcont : Continuous (Ideal.Quotient.mk I) :=
    (QuotientRing.isOpenQuotientMap_mk I).continuous
  have hIopen : IsOpen (I : Set D'.R) :=
    isOpen_of_ne_top_of_finite_quotient D'.isAdic I hItop hIfin
  haveI hdiscQ : DiscreteTopology (D'.R ⧸ I) := by
    rw [discreteTopology_iff_isOpen_singleton_zero]
    have himg : ((Ideal.Quotient.mk I) '' (I : Set D'.R)) = {0} := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hy
      · rintro rfl
        exact ⟨0, I.zero_mem, map_zero _⟩
    rw [← himg]
    exact (QuotientRing.isOpenMap_coe I) _ hIopen
  obtain ⟨N, hN⟩ := exists_maximalIdeal_pow_eq_bot (D'.R ⧸ I)
  have hadicQ : IsAdic (IsLocalRing.maximalIdeal (D'.R ⧸ I)) :=
    isAdic_of_pow_eq_bot hN
  haveI hcompQ :
      IsAdicComplete (IsLocalRing.maximalIdeal (D'.R ⧸ I)) (D'.R ⧸ I) :=
    isAdicComplete_of_pow_eq_bot hN
  -- the reduction map of the quotient deformation
  set πQ : (D'.R ⧸ I) →+* k := Ideal.Quotient.lift I D'.π hIπ
  have hπQmk : πQ.comp (Ideal.Quotient.mk I) = D'.π := by
    refine RingHom.ext fun x => ?_
    rfl
  have hπQcont : Continuous πQ := continuous_of_discreteTopology
  have halg : (Ideal.Quotient.mk I).comp (algebraMap ℤ_[ℓ] D'.R) =
      algebraMap ℤ_[ℓ] (D'.R ⧸ I) := rfl
  -- the quotient deformation: an object of Mazur's category with FINITE ring
  set Dq : HardlyRamifiedDeformation hℓOdd ρbar :=
    { R := D'.R ⧸ I
      isAdic := hadicQ
      isAdicComplete := hcompQ
      ρ := pushforwardFrame (Ideal.Quotient.mk I) hmkcont D'.ρ
      isHardlyRamified := isHardlyRamified_pushforwardFrame hℓOdd
        (Ideal.Quotient.mk I) hmkcont halg D'.isHardlyRamified
      π := πQ
      π_surjective := by
        intro y
        obtain ⟨x, hx⟩ := D'.π_surjective y
        refine ⟨Ideal.Quotient.mk I x, ?_⟩
        have h := RingHom.congr_fun hπQmk x
        rw [RingHom.comp_apply] at h
        rw [h, hx]
      charFrob_compat := by
        intro q hq hq2 hqℓ
        have h := D'.charFrob_compat q hq hq2 hqℓ
        simp only [GaloisRep.charFrob_eq_charpoly_globalFrob] at h ⊢
        rw [charpoly_pushforwardFrame (Ideal.Quotient.mk I) hmkcont D'.ρ,
          Polynomial.map_map, hπQmk]
        exact h }
  -- the residual identification of `D'`, read in the standard frame
  letI : Algebra D'.R k := D'.π.toAlgebra
  letI : ContinuousSMul D'.R k := continuousSMul_of_algebraMap D'.R k
    (by rw [RingHom.algebraMap_toAlgebra]; exact D'.continuous_pi)
  obtain ⟨e₀, he₀⟩ := hid
  have hframe : (pushforwardFrame D'.π D'.continuous_pi D'.ρ).conj
      ((TensorProduct.piScalarRight D'.R k k (Fin 2)).symm.trans e₀) = ρbar := by
    rw [show pushforwardFrame D'.π D'.continuous_pi D'.ρ =
      (D'.ρ.baseChange k).conj (TensorProduct.piScalarRight D'.R k k (Fin 2))
      from rfl, GaloisRep.conj_trans,
      show (TensorProduct.piScalarRight D'.R k k (Fin 2)).trans
        ((TensorProduct.piScalarRight D'.R k k (Fin 2)).symm.trans e₀) = e₀ from by
        refine LinearEquiv.ext fun x => ?_
        simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]]
    exact he₀
  -- it transports to the quotient deformation by functoriality alone
  have hidQ : Dq.IsResidualIdentified := by
    letI : Algebra Dq.R k := Dq.π.toAlgebra
    letI : ContinuousSMul Dq.R k := continuousSMul_of_algebraMap Dq.R k
      (by rw [RingHom.algebraMap_toAlgebra]; exact continuous_of_discreteTopology)
    have hcomp : Continuous ⇑(πQ.comp (Ideal.Quotient.mk I)) := by
      rw [hπQmk]; exact D'.continuous_pi
    have hstep : (Dq.ρ.baseChange k).conj
        (TensorProduct.piScalarRight Dq.R k k (Fin 2)) =
        pushforwardFrame D'.π D'.continuous_pi D'.ρ := by
      show pushforwardFrame πQ hπQcont
        (pushforwardFrame (Ideal.Quotient.mk I) hmkcont D'.ρ) = _
      rw [pushforwardFrame_comp (Ideal.Quotient.mk I) hmkcont πQ hπQcont
        hcomp D'.ρ]
      exact pushforwardFrame_congr hcomp D'.continuous_pi hπQmk D'.ρ
    refine ⟨(TensorProduct.piScalarRight Dq.R k k (Fin 2)).trans
      ((TensorProduct.piScalarRight D'.R k k (Fin 2)).symm.trans e₀), ?_⟩
    rw [← GaloisRep.conj_trans, hstep]
    exact hframe
  -- feed the FINITE hypothesis, and read its conjugation as a matrix
  obtain ⟨f, hfc, hfZ, hfπ, hex⟩ := hD Dq hIfin hidQ
  obtain ⟨E, hEdet, hEconj⟩ :=
    exists_matrix_of_conj_baseChange f hfc D.ρ Dq.ρ hex
  refine ⟨f, E, ?_, ?_, hEdet, ?_⟩
  · rw [hfZ]; exact halg.symm
  · exact hfπ
  · intro g
    rw [hEconj g]
    show LinearMap.toMatrix'
        (pushforwardFrame (Ideal.Quotient.mk I) hmkcont D'.ρ g) * E =
      ((LinearMap.toMatrix' (D'.ρ g)).map ⇑(Ideal.Quotient.mk I)) * E
    rw [toMatrix'_pushforwardFrame]

/-- **The pro-finite limit upgrade** (PROVEN 2026-07-25 over the single
deformation-theoretic leaf `exists_ringHom_matrix_quotient_of_finite` —
the commutative-algebra half of the Schlessinger cut): a deformation
that classifies every FINITE residually identified deformation
classifies every residually identified deformation. No arithmetic is
involved: the hardly ramified conditions enter only through the fact
that they are stable under quotient base change (which is what the
level leaf consumes), and the input and output clauses are identical
apart from the finiteness restriction.

Classical route, in four steps; steps 2–4 are proven here.

1. *Level-`n` test objects and their classifying data.* Base change
   `D'` along `D'.R ↠ D'.R ⧸ 𝔪ⁿ`, a FINITE local ring, and feed the
   result to the finite hypothesis. This is
   `exists_ringHom_matrix_quotient_of_finite`, the one remaining leaf;
   its three base-change ingredients
   (`isHardlyRamified_baseChange_quotient`,
   `isFlatAt_baseChange_quotient`, `isTameAtTwo_baseChange`) have been
   hoisted above this point.
2. *Pairs, not linear equivalences.* The classifying datum is a ring
   map `ψₙ` TOGETHER WITH a conjugation `eₙ` of the pushforward of
   `D.ρ` onto the reduced representation — and the type of `eₙ` DEPENDS
   on `ψₙ` (it is a `(D'.R ⧸ 𝔪ⁿ)`-linear equivalence out of a tensor
   product formed along `ψₙ`), so the tower is one of dependent pairs
   and is not an inverse system of sets. It is turned into one by
   replacing `eₙ` with its MATRIX in the standard frames:
   `exists_conj_baseChange_of_matrix` above is the dictionary, and the
   inverse system is one of pairs `(ψ, E)` in the product type
   `(D.R →+* D'.R ⧸ 𝔪ⁿ) × Matrix (Fin 2) (Fin 2) (D'.R ⧸ 𝔪ⁿ)`. This is
   exactly where the naive transfer of `Patching.lean`'s pro-finite
   upgrade fails: that argument carries only the TRACE-level clause
   through the limit, so its system is one of ring maps alone.
3. *Kőnig.* For fixed `n` there are only FINITELY many such pairs: a
   `ψ` with `π ∘ ψ = D.π` is local, hence kills `𝔪_{D.R}ⁿ` (the maximal
   ideal of `D'.R ⧸ 𝔪ⁿ` has vanishing `n`-th power), so it factors
   through the finite ring `D.R ⧸ 𝔪_{D.R}ⁿ`
   (`finite_quotient_of_maximalIdeal_pow_le`, hoisted above), and `E`
   is a matrix over a finite ring. The sets are nonempty by step 1 and
   stable under the transition maps `D'.R ⧸ 𝔪ᵐ ↠ D'.R ⧸ 𝔪ⁿ`.
4. *Assembly.* `D'.R` is `𝔪`-adically complete and separated
   (`isAdicComplete`), so the compatible system assembles —
   `exists_ringHom_matrix_of_forall_quotient_mem` above does steps 3
   and 4 at once. `ψ` is continuous because it is local
   (`continuous_of_map_maximalIdeal_le`); `E` is invertible because its
   determinant is a unit modulo `𝔪`, and `D'.R` is local; and the
   `ℤ_ℓ`-clause and the conjugation equation, holding modulo every
   `𝔪ⁿ`, hold outright by separatedness (Krull).

Interface-side twin: `Modularity/Patching.lean`'s
`isWeaklyUniversalOnIdentifiedDeformation_of_finiteTests`, which
performs the trace-level analogue of steps 1–4 over the leaves
`exists_ringHom_quotient_of_finiteTests`,
`finite_quotient_maximalIdeal_pow` and
`exists_ringHom_of_forall_quotient_mem` (the last two still sorries
there; both are proven outright in this file's version — the finiteness
by `finite_quotient_of_maximalIdeal_pow_le`, the limit by
`exists_ringHom_matrix_of_forall_quotient_mem`).

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
    D.IsWeaklyUniversalOnIdentifiedFrames := by
  classical
  letI := D.commRing; letI := D.topologicalSpace; letI := D.isTopologicalRing
  letI := D.isLocalRing; letI := D.algebra
  intro D' hid
  letI := D'.commRing; letI := D'.topologicalSpace
  letI := D'.isTopologicalRing; letI := D'.isLocalRing; letI := D'.algebra
  haveI := D.isNoetherianRing
  haveI := D'.isNoetherianRing
  -- the maximal-adic tower of the coefficient ring of `D'`
  set J : Ideal D'.R := IsLocalRing.maximalIdeal D'.R with hJ
  haveI : IsAdicComplete J D'.R := D'.isAdicComplete
  have hkerπ : RingHom.ker D'.π = J :=
    IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective D'.π D'.π_surjective)
  have hkerD : RingHom.ker D.π = IsLocalRing.maximalIdeal D.R :=
    IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective D.π D.π_surjective)
  have hJne : J ≠ ⊤ := (IsLocalRing.maximalIdeal.isMaximal D'.R).ne_top
  have hJpowne : ∀ n : ℕ, n ≠ 0 → J ^ n ≠ ⊤ := by
    intro n hn htop
    exact hJne (top_le_iff.mp (htop ▸ Ideal.pow_le_self hn))
  have hfinlev : ∀ n : ℕ, Finite (D'.R ⧸ J ^ n) := fun n =>
    finite_quotient_of_maximalIdeal_pow_le D'.π D'.π_surjective ⟨n, le_rfl⟩
  have hπpow : ∀ (n : ℕ), n ≠ 0 → ∀ a ∈ J ^ n, D'.π a = 0 := by
    intro n hn a ha
    have hmem : a ∈ RingHom.ker D'.π := by
      rw [hkerπ]
      exact Ideal.pow_le_self hn ha
    exact hmem
  -- adic separatedness of `D'.R`: an element is pinned by its reductions
  have hsep : ∀ x : D'.R, (∀ n : ℕ, x ∈ J ^ n) → x = 0 := by
    intro x hx
    refine IsHausdorff.haus (I := J) (M := D'.R) inferInstance x fun n => ?_
    rw [SModEq.sub_mem, sub_zero]
    have hsm : (J ^ n : Ideal D'.R) ≤ (J ^ n) • (⊤ : Submodule D'.R D'.R) := by
      intro r hr
      have hmem : r • (1 : D'.R) ∈ (J ^ n) • (⊤ : Submodule D'.R D'.R) :=
        Submodule.smul_mem_smul hr Submodule.mem_top
      simpa using hmem
    exact hsm (hx n)
  have heq : ∀ a b : D'.R,
      (∀ n : ℕ, Ideal.Quotient.mk (J ^ n) a = Ideal.Quotient.mk (J ^ n) b) →
      a = b := by
    intro a b hab
    have h0 : a - b = 0 := hsep _ fun n => Ideal.Quotient.eq.mp (hab n)
    exact sub_eq_zero.mp h0
  -- step 3, finiteness half: an admissible `ψ` factors through `D.R ⧸ 𝔪ⁿ`
  have hfinhom : ∀ (n : ℕ) (hn : n ≠ 0),
      {ψ : D.R →+* D'.R ⧸ J ^ n |
        (Ideal.Quotient.lift (J ^ n) D'.π (hπpow n hn)).comp ψ =
          D.π}.Finite := by
    intro n hn
    set Jq : Ideal (D'.R ⧸ J ^ n) := J.map (Ideal.Quotient.mk (J ^ n))
      with hJq
    have hkerlift : ∀ y : D'.R ⧸ J ^ n,
        (Ideal.Quotient.lift (J ^ n) D'.π (hπpow n hn)) y = 0 → y ∈ Jq := by
      intro y hy
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [Ideal.Quotient.lift_mk] at hy
      exact Ideal.mem_map_of_mem _ (by rw [← hkerπ]; exact hy)
    have hJqpow : Jq ^ n = ⊥ := by
      rw [hJq, ← Ideal.map_pow, Ideal.map_quotient_self]
    have hkill : ∀ ψ : D.R →+* D'.R ⧸ J ^ n,
        (Ideal.Quotient.lift (J ^ n) D'.π (hπpow n hn)).comp ψ = D.π →
        ∀ x ∈ (IsLocalRing.maximalIdeal D.R) ^ n, ψ x = 0 := by
      intro ψ hψ x hx
      have hmR : IsLocalRing.maximalIdeal D.R ≤ Ideal.comap ψ Jq := by
        intro y hy
        refine hkerlift _ ?_
        rw [← RingHom.comp_apply, hψ]
        rw [← hkerD] at hy
        exact hy
      have hpow : ∀ j : ℕ,
          (IsLocalRing.maximalIdeal D.R) ^ j ≤ Ideal.comap ψ (Jq ^ j) := by
        intro j
        induction j with
        | zero => simp
        | succ j ih =>
          rw [pow_succ, pow_succ]
          refine le_trans (Ideal.mul_mono ih hmR) ?_
          rw [Ideal.mul_le]
          intro r hr s hs
          have hr' : ψ r ∈ Jq ^ j := hr
          have hs' : ψ s ∈ Jq := hs
          show ψ (r * s) ∈ Jq ^ j * Jq
          rw [map_mul]
          exact Ideal.mul_mem_mul hr' hs'
      have hmem : ψ x ∈ Jq ^ n := hpow n hx
      rw [hJqpow] at hmem
      exact hmem
    haveI : Finite (D.R ⧸ (IsLocalRing.maximalIdeal D.R) ^ n) :=
      finite_quotient_of_maximalIdeal_pow_le D.π D.π_surjective ⟨n, le_rfl⟩
    haveI := hfinlev n
    haveI : Finite ((D.R ⧸ (IsLocalRing.maximalIdeal D.R) ^ n) →+*
        D'.R ⧸ J ^ n) :=
      Finite.of_injective
        (fun g : (D.R ⧸ (IsLocalRing.maximalIdeal D.R) ^ n) →+* D'.R ⧸ J ^ n =>
          (g : (D.R ⧸ (IsLocalRing.maximalIdeal D.R) ^ n) → D'.R ⧸ J ^ n))
        DFunLike.coe_injective
    refine Set.Finite.subset (Set.finite_range
      (fun g : (D.R ⧸ (IsLocalRing.maximalIdeal D.R) ^ n) →+* D'.R ⧸ J ^ n =>
        g.comp (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal D.R) ^ n)))) ?_
    intro ψ hψ
    exact ⟨Ideal.Quotient.lift _ ψ (hkill ψ hψ), RingHom.ext fun _ => rfl⟩
  -- the level-`n` sets of classifying PAIRS
  set X : ∀ n : ℕ, Set ((D.R →+* D'.R ⧸ J ^ n) ×
      Matrix (Fin 2) (Fin 2) (D'.R ⧸ J ^ n)) := fun n =>
    {p | (p.1.comp (algebraMap ℤ_[ℓ] D.R) =
            (Ideal.Quotient.mk (J ^ n)).comp (algebraMap ℤ_[ℓ] D'.R)) ∧
         (∀ hn : n ≠ 0,
            (Ideal.Quotient.lift (J ^ n) D'.π (hπpow n hn)).comp p.1 = D.π) ∧
         IsUnit p.2.det ∧
         (∀ g : Field.absoluteGaloisGroup ℚ,
            p.2 * (LinearMap.toMatrix' (D.ρ g)).map ⇑p.1 =
              ((LinearMap.toMatrix' (D'.ρ g)).map
                ⇑(Ideal.Quotient.mk (J ^ n))) * p.2)}
    with hX
  -- the transition maps of the tower
  have hfacmk : ∀ (m n : ℕ) (hmn : n ≤ m) (a : D'.R),
      Ideal.Quotient.factorPow J hmn (Ideal.Quotient.mk (J ^ m) a) =
        Ideal.Quotient.mk (J ^ n) a := fun _ _ _ a =>
    Ideal.Quotient.factor_mk _ a
  have hliftfac : ∀ (m n : ℕ) (hmn : n ≤ m) (hn : n ≠ 0) (hm : m ≠ 0)
      (y : D'.R ⧸ J ^ m),
      (Ideal.Quotient.lift (J ^ n) D'.π (hπpow n hn))
          (Ideal.Quotient.factorPow J hmn y) =
        (Ideal.Quotient.lift (J ^ m) D'.π (hπpow m hm)) y := by
    intro m n hmn _ _ y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [hfacmk m n hmn a, Ideal.Quotient.lift_mk, Ideal.Quotient.lift_mk]
  -- step 3, stability half
  have hXstab : ∀ (m n : ℕ) (hmn : n ≤ m)
      (p : (D.R →+* D'.R ⧸ J ^ m) × Matrix (Fin 2) (Fin 2) (D'.R ⧸ J ^ m)),
      p ∈ X m →
      ((Ideal.Quotient.factorPow J hmn).comp p.1,
        p.2.map ⇑(Ideal.Quotient.factorPow J hmn)) ∈ X n := by
    intro m n hmn p hp
    simp only [hX, Set.mem_setOf_eq] at hp ⊢
    obtain ⟨h1, h2, h3, h4⟩ := hp
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine RingHom.ext fun x => ?_
      have h1x := RingHom.congr_fun h1 x
      simp only [RingHom.comp_apply] at h1x ⊢
      rw [h1x, hfacmk m n hmn]
    · intro hn
      have hm : m ≠ 0 := by omega
      refine RingHom.ext fun r => ?_
      have h2x := RingHom.congr_fun (h2 hm) r
      simp only [RingHom.comp_apply] at h2x ⊢
      rw [hliftfac m n hmn hn hm, h2x]
    · have hdu : IsUnit ((Ideal.Quotient.factorPow J hmn) p.2.det) := h3.map _
      rwa [RingHom.map_det] at hdu
    · intro g
      have h4g := h4 g
      have hL : (p.2 * (LinearMap.toMatrix' (D.ρ g)).map ⇑p.1).map
          ⇑(Ideal.Quotient.factorPow J hmn) =
        (p.2.map ⇑(Ideal.Quotient.factorPow J hmn)) *
          ((LinearMap.toMatrix' (D.ρ g)).map
            ⇑((Ideal.Quotient.factorPow J hmn).comp p.1)) := by
        rw [Matrix.map_mul, Matrix.map_map]
        rfl
      have hR : (((LinearMap.toMatrix' (D'.ρ g)).map
            ⇑(Ideal.Quotient.mk (J ^ m))) * p.2).map
          ⇑(Ideal.Quotient.factorPow J hmn) =
        ((LinearMap.toMatrix' (D'.ρ g)).map
            ⇑(Ideal.Quotient.mk (J ^ n))) *
          (p.2.map ⇑(Ideal.Quotient.factorPow J hmn)) := by
        rw [Matrix.map_mul, Matrix.map_map]
        congr 1
      rw [← hL, h4g, hR]
  -- step 1: the positive levels are nonempty, by the deformation leaf
  have hXne_pos : ∀ n : ℕ, n ≠ 0 → (X n).Nonempty := by
    intro n hn
    obtain ⟨ψ, E, h1, h2, h3, h4⟩ :=
      exists_ringHom_matrix_quotient_of_finite hℓOdd D hD D' hid (J ^ n)
        (hJpowne n hn) (hfinlev n) (hπpow n hn)
    refine ⟨(ψ, E), ?_⟩
    simp only [hX, Set.mem_setOf_eq]
    exact ⟨h1, fun _ => h2, h3, h4⟩
  have hXne : ∀ n : ℕ, (X n).Nonempty := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · obtain ⟨p, hp⟩ := hXne_pos 1 one_ne_zero
      exact ⟨_, hXstab 1 0 (Nat.zero_le 1) p hp⟩
    · exact hXne_pos n hn
  have hXfin : ∀ n : ℕ, (X n).Finite := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · haveI : Subsingleton (D'.R ⧸ J ^ 0) := by
        rw [Ideal.Quotient.subsingleton_iff, pow_zero, Ideal.one_eq_top]
      refine Set.Subsingleton.finite fun a _ b _ => ?_
      exact Prod.ext (RingHom.ext fun _ => Subsingleton.elim _ _)
        (Matrix.ext fun _ _ => Subsingleton.elim _ _)
    · haveI := hfinlev n
      have hsub : X n ⊆
          {ψ : D.R →+* D'.R ⧸ J ^ n |
            (Ideal.Quotient.lift (J ^ n) D'.π (hπpow n hn)).comp ψ = D.π} ×ˢ
          (Set.univ : Set (Matrix (Fin 2) (Fin 2) (D'.R ⧸ J ^ n))) := by
        rintro ⟨ψ, E⟩ hp
        simp only [hX, Set.mem_setOf_eq] at hp
        exact ⟨hp.2.1 hn, Set.mem_univ _⟩
      exact Set.Finite.subset ((hfinhom n hn).prod Set.finite_univ) hsub
  -- steps 3 and 4: Kőnig, then adic assembly, for the PAIRS
  obtain ⟨ψ, E, hψE⟩ :=
    exists_ringHom_matrix_of_forall_quotient_mem J X hXfin hXne hXstab
  simp only [hX, Set.mem_setOf_eq] at hψE
  -- the reduction clause is already visible at the first level
  have hB : D'.π.comp ψ = D.π := by
    refine RingHom.ext fun r => ?_
    have h1 := RingHom.congr_fun ((hψE 1).2.1 one_ne_zero) r
    simpa using h1
  -- `ψ` is local, hence continuous
  have hloc : Ideal.map ψ (IsLocalRing.maximalIdeal D.R) ≤ J := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    show ψ x ∈ J
    rw [← hkerπ]
    show D'.π (ψ x) = 0
    rw [← RingHom.comp_apply, hB]
    rw [← hkerD] at hx
    exact hx
  have hcont : Continuous ψ :=
    continuous_of_map_maximalIdeal_le D.isAdic D'.isAdic ψ hloc
  -- the `ℤ_ℓ`-clause holds modulo every level, hence holds
  have hA : ψ.comp (algebraMap ℤ_[ℓ] D.R) = algebraMap ℤ_[ℓ] D'.R := by
    refine RingHom.ext fun x => ?_
    refine heq _ _ fun n => ?_
    have hn := RingHom.congr_fun (hψE n).1 x
    simpa using hn
  -- the determinant of `E` is a unit: it is one modulo the maximal ideal
  have hEdet : IsUnit E.det := by
    have h1 := (hψE 1).2.2.1
    rw [show (E.map ⇑(Ideal.Quotient.mk (J ^ 1))).det =
        Ideal.Quotient.mk (J ^ 1) E.det from (RingHom.map_det _ _).symm] at h1
    by_contra hcon
    have hmem : E.det ∈ IsLocalRing.maximalIdeal D'.R := by
      by_contra hnot
      exact hcon (IsLocalRing.notMem_maximalIdeal.mp hnot)
    have hzero : Ideal.Quotient.mk (J ^ 1) E.det = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (by rw [pow_one]; exact hmem)
    rw [hzero] at h1
    haveI : Nontrivial (D'.R ⧸ J ^ 1) := by
      rw [← not_subsingleton_iff_nontrivial, Ideal.Quotient.subsingleton_iff]
      exact hJpowne 1 one_ne_zero
    exact not_isUnit_zero h1
  -- the conjugation equation holds modulo every level, hence holds
  have hD4 : ∀ g : Field.absoluteGaloisGroup ℚ,
      E * (LinearMap.toMatrix' (D.ρ g)).map ⇑ψ =
        (LinearMap.toMatrix' (D'.ρ g)) * E := by
    intro g
    refine Matrix.ext fun i i' => ?_
    refine heq _ _ fun n => ?_
    have hL : (E * (LinearMap.toMatrix' (D.ρ g)).map ⇑ψ).map
        ⇑(Ideal.Quotient.mk (J ^ n)) =
      (E.map ⇑(Ideal.Quotient.mk (J ^ n))) *
        ((LinearMap.toMatrix' (D.ρ g)).map
          ⇑((Ideal.Quotient.mk (J ^ n)).comp ψ)) := by
      rw [Matrix.map_mul, Matrix.map_map]
      rfl
    have hR : ((LinearMap.toMatrix' (D'.ρ g)) * E).map
        ⇑(Ideal.Quotient.mk (J ^ n)) =
      ((LinearMap.toMatrix' (D'.ρ g)).map ⇑(Ideal.Quotient.mk (J ^ n))) *
        (E.map ⇑(Ideal.Quotient.mk (J ^ n))) := Matrix.map_mul
    have hfull := hL.trans (((hψE n).2.2.2 g).trans hR.symm)
    exact congrArg
      (fun M : Matrix (Fin 2) (Fin 2) (D'.R ⧸ J ^ n) => M i i') hfull
  refine ⟨ψ, hcont, hA, hB, ?_⟩
  exact exists_conj_baseChange_of_matrix ψ hcont D.ρ D'.ρ E hEdet hD4

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

/-- **The induced filtration dominates the adic one** (PROVEN
2026-07-25, one line of ideal algebra; the EASY half of the comparison
whose hard half is Carayol's Lemme 1): for a subring `C` of a local ring
`A`, `(𝔪 ∩ C)^n ⊆ 𝔪^n ∩ C`. -/
theorem pow_comap_maximalIdeal_le {A : Type*} [CommRing A] [IsLocalRing A]
    (C : Subring A) (n : ℕ) :
    (Ideal.comap C.subtype (IsLocalRing.maximalIdeal A)) ^ n ≤
      Ideal.comap C.subtype ((IsLocalRing.maximalIdeal A) ^ n) := by
  intro x hx
  have h1 : Ideal.map C.subtype
      ((Ideal.comap C.subtype (IsLocalRing.maximalIdeal A)) ^ n) ≤
      (IsLocalRing.maximalIdeal A) ^ n := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono Ideal.map_comap_le n
  exact h1 (Ideal.mem_map_of_mem _ hx)

open Filter Topology in
/-- **A closed subring of a complete local ring with FINITE residue
field inverts its own units** (PROVEN 2026-07-25 — the engine of the
soft half of Carayol's Théorème 1): if `A` is local, its topology is
the `𝔪`-adic one, and `A/𝔪` is finite, then for a closed subring
`C ⊆ A` every `x ∈ C` with `x ∉ 𝔪` is already a unit OF `C`.

The classical argument writes `x⁻¹` as a limit of a geometric series in
`1 − x/a` for a lift `a ∈ C` of the residue of `x`, and therefore needs
`C ↠ A/𝔪`. FINITENESS of the residue field removes that hypothesis
entirely: the residue of `x` is a nonzero element of the finite field
`A/𝔪`, so `x^(q−1) ∈ 1 + 𝔪` for `q = |A/𝔪|`, and the geometric series
`∑ (1 − x^(q−1))^n` — all of whose partial sums lie in `C`, the argument
`y = 1 − x^(q−1)` lying in `𝔪 ∩ C` — converges in `A` to the inverse of
`x^(q−1)`, because `y^N ∈ 𝔪^N → 0` for the adic topology. `C` is closed,
so that inverse lies in `C`, and `x⁻¹ = x^(q−2) · (x^(q−1))⁻¹`.

Note that no completeness of `A` is used: the limit is exhibited
explicitly as the inverse that already exists in the LOCAL ring `A`;
only closedness of `C` and the adic topology are consumed. -/
theorem isUnit_of_isClosed_of_notMem_maximalIdeal {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsLocalRing A] [Finite (IsLocalRing.ResidueField A)]
    (hadic : IsAdic (IsLocalRing.maximalIdeal A))
    {C : Subring A} (hC : IsClosed (C : Set A)) (x : C)
    (hx : (x : A) ∉ IsLocalRing.maximalIdeal A) : IsUnit x := by
  classical
  haveI : Fintype (IsLocalRing.ResidueField A) := Fintype.ofFinite _
  set q := Fintype.card (IsLocalRing.ResidueField A)
  have hq1 : 0 < q - 1 := Nat.sub_pos_of_lt Fintype.one_lt_card
  -- `x ^ (q - 1) = 1 - y` with `y ∈ 𝔪 ∩ C`
  have hres : IsLocalRing.residue A ((x : A) ^ (q - 1)) = 1 := by
    rw [map_pow]
    exact FiniteField.pow_card_sub_one_eq_one _
      (fun hz => hx ((IsLocalRing.residue_eq_zero_iff _).mp hz))
  set y : C := 1 - x ^ (q - 1) with hy
  have hyc : ((y : C) : A) = 1 - (x : A) ^ (q - 1) := by rw [hy]; push_cast; ring
  have hyR : (y : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, hyc, map_sub, hres, map_one, sub_self]
  have hone : (1 : A) - (y : A) = (x : A) ^ (q - 1) := by rw [hyc]; ring
  -- the inverse of `1 - y` in `A`
  have hu : IsUnit ((1 : A) - (y : A)) := by
    rw [← IsLocalRing.notMem_maximalIdeal, hone]
    intro hmem
    exact hx ((Ideal.IsPrime.pow_mem_iff_mem
      ((IsLocalRing.maximalIdeal.isMaximal A).isPrime) _ hq1).mp hmem)
  set u := hu.unit
  set L : A := ((u⁻¹ : Aˣ) : A) with hL
  have huL : ((1 : A) - (y : A)) * L = 1 := by
    rw [hL, show ((1 : A) - (y : A)) = (u : A) from (hu.unit_spec).symm]
    exact u.mul_inv
  -- the partial sums of the geometric series lie in `C`
  set s : ℕ → C := fun N => ∑ i ∈ Finset.range N, y ^ i with hs
  have hsc : ∀ N, ((s N : C) : A) = ∑ i ∈ Finset.range N, (y : A) ^ i := by
    intro N
    rw [hs]
    push_cast
    rfl
  have hsL : ∀ N, L - ((s N : C) : A) = L * (y : A) ^ N := by
    intro N
    have h1 : ((1 : A) - (y : A)) * ((s N : C) : A) = 1 - (y : A) ^ N := by
      rw [hsc]; exact mul_neg_geom_sum _ _
    have h2 : ((s N : C) : A) = L * (1 - (y : A) ^ N) := by
      calc ((s N : C) : A) = (L * ((1 : A) - (y : A))) * ((s N : C) : A) := by
            rw [mul_comm L, huL, one_mul]
        _ = L * (((1 : A) - (y : A)) * ((s N : C) : A)) := by ring
        _ = L * (1 - (y : A) ^ N) := by rw [h1]
    rw [h2]; ring
  -- so their limit `L` lies in `C`
  have htend : Tendsto (fun N => ((s N : C) : A)) atTop (𝓝 L) := by
    rw [(hadic.hasBasis_nhds L).tendsto_right_iff]
    intro n _
    filter_upwards [eventually_ge_atTop n] with N hN
    refine ⟨-(L * (y : A) ^ N), ?_, ?_⟩
    · refine Ideal.pow_le_pow_right hN ?_
      exact neg_mem (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hyR N))
    · rw [← hsL N]; ring
  have hLC : L ∈ C := hC.mem_of_tendsto htend (.of_forall fun N => (s N).2)
  -- hence `1 - y = x ^ (q - 1)` is a unit of `C`, and therefore so is `x`
  have hunit : IsUnit (1 - y : C) := by
    refine ⟨⟨1 - y, ⟨L, hLC⟩, ?_, ?_⟩, rfl⟩
    · ext
      push_cast
      exact huL
    · ext
      push_cast
      rw [mul_comm]
      exact huL
  have hxq : IsUnit (x ^ (q - 1) : C) := by
    have hxy : (1 - y : C) = x ^ (q - 1) := by rw [hy]; ring
    rwa [hxy] at hunit
  refine isUnit_of_mul_isUnit_left (y := x ^ (q - 1 - 1)) ?_
  have hpow : x * x ^ (q - 1 - 1) = x ^ (q - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hpow]
  exact hxq

/-- **A closed subring of a local ring with finite residue field and
adic topology is LOCAL** (PROVEN 2026-07-25): the nonunits of `C` are
exactly `𝔪 ∩ C` by `isUnit_of_isClosed_of_notMem_maximalIdeal`, and that
is an ideal. -/
theorem isLocalRing_of_isClosed_subring {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsLocalRing A] [Finite (IsLocalRing.ResidueField A)]
    (hadic : IsAdic (IsLocalRing.maximalIdeal A))
    {C : Subring A} (hC : IsClosed (C : Set A)) : IsLocalRing C := by
  haveI : Nontrivial C := ⟨⟨0, 1, fun hz => zero_ne_one (congrArg Subtype.val hz)⟩⟩
  refine IsLocalRing.of_nonunits_add ?_
  intro a b ha hb
  have hmem : ∀ c : C, c ∈ nonunits C → (c : A) ∈ IsLocalRing.maximalIdeal A := by
    intro c hc
    by_contra hcm
    exact hc (isUnit_of_isClosed_of_notMem_maximalIdeal hadic hC c hcm)
  intro hab
  have hsum : ((a : A) + (b : A)) ∈ IsLocalRing.maximalIdeal A :=
    Ideal.add_mem _ (hmem a ha) (hmem b hb)
  have hunit : IsUnit ((a : A) + (b : A)) := by simpa using hab.map C.subtype
  exact IsLocalRing.notMem_maximalIdeal.mpr hunit hsum

/-- **The maximal ideal of such a closed subring is `𝔪 ∩ C`** (PROVEN
2026-07-25), the companion of `isLocalRing_of_isClosed_subring`. -/
theorem maximalIdeal_eq_comap_of_isClosed_subring {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsLocalRing A] [Finite (IsLocalRing.ResidueField A)]
    (hadic : IsAdic (IsLocalRing.maximalIdeal A))
    {C : Subring A} (hC : IsClosed (C : Set A)) [IsLocalRing C] :
    IsLocalRing.maximalIdeal C =
      Ideal.comap C.subtype (IsLocalRing.maximalIdeal A) := by
  ext a
  rw [IsLocalRing.mem_maximalIdeal, Ideal.mem_comap]
  constructor
  · intro ha
    by_contra hcm
    exact ha (isUnit_of_isClosed_of_notMem_maximalIdeal hadic hC a hcm)
  · intro ha hu
    have hunit : IsUnit (a : A) := by simpa using hu.map C.subtype
    exact IsLocalRing.notMem_maximalIdeal.mpr hunit ha

open Filter Topology in
/-- **Carayol's Lemme 1 gives the subring its adic topology** (PROVEN
2026-07-25 as glue over the cofinality hypothesis): if for every `n`
some `𝔪^m ∩ C` is contained in `(𝔪 ∩ C)^n`, then the SUBSPACE topology
on `C` is the `(𝔪 ∩ C)`-adic topology.

Both clauses of `isAdic_iff`. The powers `(𝔪 ∩ C)^n` are open because
they are additive subgroups containing the neighbourhood
`C ∩ 𝔪^m` of `0` — this is exactly the cofinality hypothesis; and every
neighbourhood of `0` in `C` contains some `(𝔪 ∩ C)^n`, by the easy
inclusion `pow_comap_maximalIdeal_le` and adicness upstairs. -/
theorem isAdic_comap_maximalIdeal_of_forall_exists_le {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLocalRing A]
    (hadic : IsAdic (IsLocalRing.maximalIdeal A)) {C : Subring A}
    (hlem : ∀ n : ℕ, ∃ m : ℕ,
      Ideal.comap C.subtype ((IsLocalRing.maximalIdeal A) ^ m) ≤
        (Ideal.comap C.subtype (IsLocalRing.maximalIdeal A)) ^ n) :
    IsAdic (Ideal.comap C.subtype (IsLocalRing.maximalIdeal A)) := by
  rw [isAdic_iff]
  constructor
  · intro n
    obtain ⟨m, hm⟩ := hlem n
    refine AddSubgroup.isOpen_of_mem_nhds
      ((Ideal.comap C.subtype (IsLocalRing.maximalIdeal A) ^ n).toAddSubgroup)
      (g := 0) ?_
    have h0 : (((IsLocalRing.maximalIdeal A) ^ m : Ideal A) : Set A) ∈ 𝓝 (0 : A) :=
      hadic.hasBasis_nhds_zero.mem_of_mem (i := m) trivial
    have h1 : ((C.subtype : C → A) ⁻¹'
        (((IsLocalRing.maximalIdeal A) ^ m : Ideal A) : Set A)) ∈ 𝓝 (0 : C) := by
      rw [nhds_induced]
      exact Filter.mem_comap.mpr ⟨_, by simpa using h0, subset_rfl⟩
    exact Filter.mem_of_superset h1 (fun z hz => hm hz)
  · intro s hs
    rw [nhds_induced, Filter.mem_comap] at hs
    obtain ⟨t, ht, hts⟩ := hs
    obtain ⟨n, hn⟩ := (isAdic_iff.mp hadic).2 t (by simpa using ht)
    exact ⟨n, fun z hz => hts (hn (pow_comap_maximalIdeal_le C n hz))⟩

open Filter Topology in
/-- **Closedness plus Carayol's Lemme 1 give adic completeness of the
subring** (PROVEN 2026-07-25).

Separatedness is free: `(𝔪 ∩ C)^n ⊆ 𝔪^n` and `A` is separated.
Precompleteness is the closedness argument: a sequence Cauchy for the
`(𝔪 ∩ C)`-filtration is Cauchy for the `𝔪`-filtration, hence converges
to some `L ∈ A`; the convergence is topological (the `𝔪^n` are a
neighbourhood basis), so `L ∈ C` because `C` is closed; and Carayol's
Lemme 1 upgrades "`L ≡ f m` mod `𝔪^m`" to "`L ≡ f n` mod `(𝔪 ∩ C)^n`",
by picking `m` with `𝔪^m ∩ C ⊆ (𝔪 ∩ C)^n` and going through `f (max m n)`. -/
theorem isAdicComplete_comap_maximalIdeal_of_forall_exists_le {A : Type*}
    [CommRing A] [TopologicalSpace A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hadic : IsAdic (IsLocalRing.maximalIdeal A)) {C : Subring A}
    (hC : IsClosed (C : Set A))
    (hlem : ∀ n : ℕ, ∃ m : ℕ,
      Ideal.comap C.subtype ((IsLocalRing.maximalIdeal A) ^ m) ≤
        (Ideal.comap C.subtype (IsLocalRing.maximalIdeal A)) ^ n) :
    IsAdicComplete (Ideal.comap C.subtype (IsLocalRing.maximalIdeal A)) C := by
  set I : Ideal C := Ideal.comap C.subtype (IsLocalRing.maximalIdeal A)
  have key : ∀ (n : ℕ) (z : C), z ∈ I ^ n → (z : A) ∈ (IsLocalRing.maximalIdeal A) ^ n :=
    fun n z hz => pow_comap_maximalIdeal_le C n hz
  rw [isAdicComplete_iff]
  refine ⟨⟨?_⟩, ⟨?_⟩⟩
  · -- separatedness
    intro x hx
    simp only [SModEq.zero, smul_eq_mul, Ideal.mul_top] at hx
    have hxR : (x : A) = 0 :=
      IsHausdorff.haus (inferInstance : IsHausdorff (IsLocalRing.maximalIdeal A) A) _
        (fun n => by simpa [SModEq.zero, smul_eq_mul, Ideal.mul_top] using key n x (hx n))
    exact Subtype.ext hxR
  · -- precompleteness
    intro f hf
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hf
    obtain ⟨L, hL⟩ :=
      IsPrecomplete.prec (inferInstance : IsPrecomplete (IsLocalRing.maximalIdeal A) A)
        (f := fun n => ((f n : C) : A))
        (fun {m n} hmn => by
          simpa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using key m _ (hf hmn))
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hL
    have htend : Tendsto (fun n => ((f n : C) : A)) atTop (𝓝 L) := by
      rw [(hadic.hasBasis_nhds L).tendsto_right_iff]
      intro n _
      filter_upwards [eventually_ge_atTop n] with N hN
      refine ⟨((f N : C) : A) - L, Ideal.pow_le_pow_right hN ?_, by ring⟩
      exact hL N
    have hLC : L ∈ C := hC.mem_of_tendsto htend (.of_forall fun n => (f n).2)
    refine ⟨⟨L, hLC⟩, fun n => ?_⟩
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    obtain ⟨m, hm⟩ := hlem n
    have hmem : (⟨L, hLC⟩ : C) - f (max m n) ∈ I ^ n := by
      refine hm ?_
      show ((⟨L, hLC⟩ : C) - f (max m n) : C).val ∈ (IsLocalRing.maximalIdeal A) ^ m
      have hval : (((⟨L, hLC⟩ : C) - f (max m n) : C) : A) =
          -(((f (max m n) : C) : A) - L) := by push_cast; ring
      rw [hval]
      exact neg_mem (Ideal.pow_le_pow_right (le_max_left m n) (hL (max m n)))
    have hstep : f n - f (max m n) ∈ I ^ n := hf (le_max_right m n)
    have hsplit : f n - ⟨L, hLC⟩ =
        (f n - f (max m n)) - ((⟨L, hLC⟩ : C) - f (max m n)) := by ring
    rw [hsplit]
    exact sub_mem hstep hmem

/-- **A complete local ring with finitely generated maximal ideal is
Noetherian** (PROVEN 2026-07-25, in the dedicated module
`HardlyRamified/CompleteLocalNoetherian.lean` — pure commutative algebra,
a mathlib gap; isolated the same day as the "then apply Cohen" half of
Carayol's Noetherianity argument): if `A` is local, `𝔪`-adically complete
and separated, and `𝔪` is finitely generated, then `A` is Noetherian.

This is Stacks 05GH / Matsumura *Commutative Ring Theory* Thm 8.4 (also
Bourbaki, *Algèbre commutative* III §2 no 9 Cor. 2) in the case
`I = 𝔪`, `A/I` a field: the associated graded ring
`gr_𝔪(A) = ⊕ 𝔪^n/𝔪^{n+1}` is generated over the field `A/𝔪` by the
images of a finite generating set of `𝔪`, hence is a quotient of a
polynomial ring in finitely many variables and so Noetherian by the
Hilbert basis theorem; and a filtered ring that is complete and
separated for its filtration and has Noetherian associated graded ring
is Noetherian (lift a generating set of `in(J)` for an ideal `J`, and
successive approximation converges by completeness).

Mathlib has neither the implication nor an associated graded ring of an
ideal filtration, so the proof does NOT build `gr_𝔪(A)`: it works
directly in the polynomial ring `k[X₁, …, X_r]` over the residue field
that surjects onto it, taking for the "ideal of leading forms" of `J`
the span of `{(map (residue A)) P | P homogeneous of degree n,
aeval f P ∈ J + 𝔪^{n+1}}`. That span is finitely generated by the
Hilbert basis theorem (`MvPolynomial.isNoetherianRing`) and finitely
many of its generators can be taken from the generating set itself
(`Submodule.mem_span_finite_of_mem_span`), which is what supplies the
homogeneous lifts; `homogeneousComponent_mul_isHomogeneous` does the
degree bookkeeping, and `IsPrecomplete`/`IsHausdorff` run and terminate
the successive approximation. See that module's docstring for details.

The Cohen-structure route — presenting such an `A` as a quotient of
`Λ[[x₁, …, x_g]]` for a coefficient ring `Λ`, which is the form Carayol
quotes — is NOT available inside this module without circularity,
because `exists_coefficientRing_ringHom` and
`surjective_of_mvPowerSeries_ringHom` both already ASSUME
`IsNoetherianRing`. The proof used here involves no coefficient ring and
no Witt vectors. -/
theorem isNoetherianRing_of_fg_maximalIdeal {A : Type*} [CommRing A]
    [IsLocalRing A] (hcomp : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hfg : (IsLocalRing.maximalIdeal A).FG) : IsNoetherianRing A :=
  CompleteLocalNoetherian.isNoetherianRing_of_isAdicComplete_of_fg hcomp hfg

/-- **Carayol's Lemme 1 for the trace subring** (sorry leaf — the first
of the two ARITHMETIC halves into which
`exists_isLocalRing_traceSubring` was decomposed on 2026-07-25): the
filtration induced on `R' = traceSubring ℓ D.ρ` by the `𝔪`-adic
filtration of `D.R` is cofinal with the `𝔪'`-adic filtration of `R'`
itself, where `𝔪' = 𝔪 ∩ R'`. One inclusion, `𝔪'^n ⊆ 𝔪^n ∩ R'`, is
formal (`pow_comap_maximalIdeal_le`); THIS is the other one.

WHY IT IS NOT FORMAL. For a general closed subring `C` of a complete
Noetherian local ring the statement FAILS, and it fails for the same
reason Noetherianity does: take `A = k[[x, y]]` with `k` finite and `C`
the closed subring topologically generated by `x, xy, xy², xy³, …`.
Every `A/𝔪^N` is finite, so `C` is a closed (indeed profinite) local
subring with residue field `k`; but `𝔪'/𝔪'²` is infinite-dimensional
(the `xyⁿ` are independent modulo `𝔪'² ⊆ (x²)`), so no power of `𝔪'`
can absorb `𝔪^2 ∩ C ∋ xyⁿ` uniformly. The arithmetic hypotheses of the
Carayol package are therefore load-bearing here, exactly as for
`fg_comap_maximalIdeal_traceSubring` below.

Carayol's own route (Contemp. Math. 165, Lemme 1) derives this from the
finite generation of `𝔪'` together with the profiniteness of `D.R` —
`D.R/𝔪^N` is finite because `k` is finite and `D.R` is Noetherian — so
that `R'` is compact for the induced topology; the `𝔪'`-adic topology is
finer, `R'` is Hausdorff for the induced one, and once `𝔪'` is finitely
generated and `R'` is `𝔪'`-adically complete the identity map from the
`𝔪'`-adic to the induced topology is a continuous bijection from a
compact space to a Hausdorff space, hence a homeomorphism. A future
owner may prefer to prove the two arithmetic leaves TOGETHER by that
compactness route rather than separately.

NOTE (2026-07-25): the primary source could not be obtained in this
session — the Anna's Archive copy of Contemp. Math. 165 is a DjVu served
over a plain-HTTP mirror, which the download tool refuses (and rightly:
its https mirror presents a self-signed chain). The route above is
reconstructed, not transcribed; treat the reference as a pointer.

ROUTE AUDIT (2026-07-25): this leaf is ENTANGLED with
`fg_comap_maximalIdeal_traceSubring` and the two should be taken by one
owner together — see the extended route audit on that leaf's docstring,
which records (i) the compactness/quotient route through a weakly
universal *and trace-generated* datum, and exactly why it is circular in
this module, and (ii) why the complete-Nakayama reduction of finite
generation to cotangent finiteness cannot be applied before this leaf.
The third member of the cluster, `isNoetherianRing_of_fg_maximalIdeal`,
was PROVEN on 2026-07-25 and is no longer a blocker. -/
theorem exists_pow_comap_le_pow_maximalIdeal_traceSubring (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible)
    (D : HardlyRamifiedDeformation hℓOdd ρbar)
    (htr : letI := D.commRing; letI := D.topologicalSpace
      letI := D.isTopologicalRing; letI := D.algebra
      ∀ g : Field.absoluteGaloisGroup ℚ,
        ((D.ρ g).charpoly).coeff 1 ∈ traceSubring ℓ D.ρ) :
    letI := D.commRing; letI := D.topologicalSpace
    letI := D.isTopologicalRing; letI := D.isLocalRing; letI := D.algebra
    ∀ n : ℕ, ∃ m : ℕ,
      Ideal.comap (traceSubring ℓ D.ρ).subtype
          ((IsLocalRing.maximalIdeal D.R) ^ m) ≤
        (Ideal.comap (traceSubring ℓ D.ρ).subtype
          (IsLocalRing.maximalIdeal D.R)) ^ n :=
  sorry

/-- **Finite generation of `𝔪' = 𝔪 ∩ R'`** (sorry leaf — the second
ARITHMETIC half of `exists_isLocalRing_traceSubring`, and the REAL
content of Carayol's Théorème 1 on the ring-theoretic side; isolated
2026-07-25): the maximal ideal of the closed trace subring
`R' = traceSubring ℓ D.ρ` is finitely generated.

Together with adic completeness (`isAdicComplete_comap_maximalIdeal_of_forall_exists_le`,
proven, over the Lemme 1 leaf above) this yields Noetherianity through
`isNoetherianRing_of_fg_maximalIdeal`, which is the "then apply Cohen"
step of the docstring route on `exists_isLocalRing_traceSubring`.

WHY IT IS NOT FORMAL: `k[[x, xy, xy², …]] ⊆ k[[x,y]]` (see
`exists_pow_comap_le_pow_maximalIdeal_traceSubring`) is a closed local
subring of a complete Noetherian local ring with the same finite residue
field whose maximal ideal is NOT finitely generated. So no argument that
uses only closedness can work: the hypotheses `hℓ5`, `h`, `hirr` and
`htr` must be consumed. Carayol consumes them through the ABSOLUTE
irreducibility of `ρbar` (odd + irreducible + `ℓ` odd), which is what
makes `R'` the image of a deformation ring with finite-dimensional
tangent space rather than an arbitrary closed subring: the mod-`ℓ`
cotangent space `𝔪'/(𝔪'² + ℓ)` is dual to a Selmer group cut out by the
hardly ramified conditions, and that Selmer group is finite. Concretely
one may take the finite generating set to be lifts of a `k`-basis of
that cotangent space; finiteness of the tangent space is the same input
that the universality stratum
`exists_isStrictlyUniversalOnFiniteFrames` consumes.

Note that this module already proves the analogous finiteness for the
FULL coefficient ring in
`finite_quotient_span_of_isWeaklyUniversal_isTraceGenerated` /
`moduleFinite_of_finite_quotient_span`; those are stated for a WEAKLY
UNIVERSAL trace-generated datum, and are not applicable to the arbitrary
`D` of this leaf, but they are the closest existing template.

TWO ROUTES AUDITED AND BLOCKED (2026-07-25, by the owner who proved
`isNoetherianRing_of_fg_maximalIdeal`). Recording them so the next owner
does not re-derive them:

* *The compactness / quotient route.* `D.R` is Noetherian, complete,
  local with FINITE residue field, so every `D.R/𝔪^N` is finite and
  `D.R` is profinite. If `Dᵘ` were a weakly universal deformation that
  is ALSO trace-generated, the map `φ : Dᵘ.R → D.R` supplied by weak
  universality would be local (it commutes with the two reductions), so
  `φ(𝔪ᵘ) ⊆ 𝔪` and `φ` is continuous; its image would be compact hence
  closed, would contain every `charFrob` coefficient and the `ℤ_ℓ`-image
  (so `R' ⊆ im φ`), and trace generation of `Dᵘ` gives the reverse
  inclusion `im φ = φ(closure Tᵘ) ⊆ closure (φ Tᵘ) = R'`. Then
  `R' ≅ Dᵘ.R / ker φ` is Noetherian and `𝔪' = φ(𝔪ᵘ)` is finitely
  generated outright — and Lemme 1 falls out of the same compactness.
  **This is CIRCULAR here**: the only source of a trace-generated datum
  in this module is `exists_isTraceGenerated_ringHom`, which builds its
  datum ON `traceSubring` and therefore consumes
  `exists_isLocalRing_traceSubring`, i.e. this very leaf.
  `exists_isWeaklyUniversal` alone (which is available, and declared
  earlier) yields only `R' ⊆ im φ`, the useless direction.
* *The complete-Nakayama route.* For a ring that is `I`-adically
  complete and separated, `I` is finitely generated as soon as
  `I/I²` is (successive approximation on `I^n = I^{n-1}(x) + I^{n+1}`
  converges). That would reduce this leaf to finiteness of the
  cotangent space `𝔪'/𝔪'²` — exactly Mazur's tangent-space finiteness,
  and the right shape of arithmetic input. **It cannot be applied
  first**: the `𝔪'`-adic completeness of `R'`
  (`isAdicComplete_comap_maximalIdeal_of_forall_exists_le`) is itself
  proven only OVER the sibling leaf
  `exists_pow_comap_le_pow_maximalIdeal_traceSubring`, so using it here
  would make the intended route circular (Carayol derives Lemme 1 FROM
  finite generation, not the other way round). Running the
  approximation in the subspace topology instead — where `R'` is
  complete for free, being closed in the complete `D.R` — needs
  `𝔪^n ∩ R' ⊆ (x)·𝔪^{n-1} + 𝔪^{n+1} ∩ R'`, which is again Lemme 1.

CONSEQUENCE: this leaf and `exists_pow_comap_le_pow_maximalIdeal_traceSubring`
are entangled and should be taken by ONE owner, together, with the
genuine arithmetic input — finiteness of the hardly ramified Selmer
group cutting out the tangent space — supplied first. The third leaf of
the cluster, `isNoetherianRing_of_fg_maximalIdeal`, is no longer a
blocker: it was PROVEN on 2026-07-25. Note also that the interface
change contemplated for `traceSubring` (taking it over `Λ ≅ W(k)`
rather than `ℤ_ℓ`) does NOT touch either of these two leaves: it removes
`subring_closure_charFrob_coeff_eq_top`, not the finiteness input.

References: Carayol, Contemp. Math. 165, Théorème 1 and Lemme 1;
Mazur, *Deforming Galois representations*, §1.6 (finiteness of the
tangent space of the deformation functor); Matsumura, §29 (Cohen). -/
theorem fg_comap_maximalIdeal_traceSubring (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible)
    (D : HardlyRamifiedDeformation hℓOdd ρbar)
    (htr : letI := D.commRing; letI := D.topologicalSpace
      letI := D.isTopologicalRing; letI := D.algebra
      ∀ g : Field.absoluteGaloisGroup ℚ,
        ((D.ρ g).charpoly).coeff 1 ∈ traceSubring ℓ D.ρ) :
    letI := D.commRing; letI := D.topologicalSpace
    letI := D.isTopologicalRing; letI := D.isLocalRing; letI := D.algebra
    (Ideal.comap (traceSubring ℓ D.ρ).subtype
      (IsLocalRing.maximalIdeal D.R)).FG :=
  sorry

/-- **Coefficient-ring structure of Carayol's trace subring `R'`**
(PROVEN 2026-07-25 as an assembly over three sharper leaves — the
ring-theoretic half of Carayol's Théorème 1, split off 2026-07-25 and
DECOMPOSED the same day): the closed `ℤ_ℓ`-subalgebra
`R' = traceSubring ℓ D.ρ` of the coefficient ring of a hardly ramified
deformation is itself a coefficient ring: local, Noetherian, with the
subspace topology equal to its own maximal-adic topology, and
maximal-adically complete and separated.

WHAT IS PROVEN HERE, and it is the whole soft half of the docstring
route this node used to record:

* **Locality**, outright and without any hypothesis on the trace data:
  `isLocalRing_of_isClosed_subring`, over
  `isUnit_of_isClosed_of_notMem_maximalIdeal`. The route recorded here
  before ("`R'` surjects onto `k`, so `x ∈ R' \ 𝔪'` has a residue that
  lifts to `R'`, and the geometric series in `1 − x/a` converges")
  needed `subring_closure_charFrob_coeff_eq_top`, a SIBLING sorry leaf.
  It is not needed: the residue field `k` is FINITE, so `x ∉ 𝔪` already
  gives `x^(q−1) ∈ 1 + 𝔪` with `q = |k|`, and the geometric series in
  `1 − x^(q−1)` — whose partial sums are polynomials in an element of
  `𝔪 ∩ R'`, hence lie in `R'` — converges to `(x^(q−1))⁻¹`. So this
  node no longer depends on the residual-trace-field leaf at all.
* **The maximal ideal is `𝔪' = 𝔪 ∩ R'`**:
  `maximalIdeal_eq_comap_of_isClosed_subring`.
* **The subspace topology is `𝔪'`-adic**, and **`R'` is `𝔪'`-adically
  complete and separated**: `isAdic_comap_maximalIdeal_of_forall_exists_le`
  and `isAdicComplete_comap_maximalIdeal_of_forall_exists_le`, both
  proven, over the single comparison input below. Separatedness is free
  from `𝔪'^n ⊆ 𝔪^n`; precompleteness is closedness of `R'` in the
  complete `D.R`.

WHAT REMAINS, in two sharply stated ARITHMETIC leaves — the third,
general-commutative-algebra one was PROVEN on 2026-07-25:

* `exists_pow_comap_le_pow_maximalIdeal_traceSubring` — Carayol's
  **Lemme 1**: `∀ n, ∃ m, 𝔪^m ∩ R' ⊆ 𝔪'^n`.
* `fg_comap_maximalIdeal_traceSubring` — **`𝔪'` is finitely generated**.
* `isNoetherianRing_of_fg_maximalIdeal` — the general commutative
  algebra "complete + `𝔪` f.g. ⟹ Noetherian", i.e. the "then apply
  Cohen" step — **PROVEN 2026-07-25** in
  `HardlyRamified/CompleteLocalNoetherian.lean` (Stacks 05GH), so this
  node is now blocked only by the two arithmetic leaves above.

NOETHERIANITY remains the genuine content and is FALSE for a general
closed subring of a complete Noetherian local ring — `k[[x, xy, xy², …]]`
inside `k[[x,y]]` is a closed local subring with the same finite residue
field and a non-finitely-generated maximal ideal, and it also refutes
Lemme 1. That counterexample is recorded on the two arithmetic leaves,
and it is why the hypotheses of the Carayol package (`hℓ5`, hard
ramification, irreducibility of `ρbar`, the trace hypothesis `htr`) are
carried on them even though the soft half proven here consumes none of
them.

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
        (traceSubring ℓ D.ρ) := by
  letI := D.commRing; letI := D.topologicalSpace
  letI := D.isTopologicalRing; letI := D.isLocalRing; letI := D.algebra
  letI := D.isNoetherianRing
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal D.R) D.R := D.isAdicComplete
  -- the residue field of `D.R` is `k`, hence finite
  haveI : Finite (IsLocalRing.ResidueField D.R) := by
    have hker : RingHom.ker D.π = IsLocalRing.maximalIdeal D.R :=
      IsLocalRing.ker_eq_maximalIdeal D.π D.π_surjective
    have hlift : IsLocalRing.ResidueField D.R →+* k :=
      Ideal.Quotient.lift (IsLocalRing.maximalIdeal D.R) D.π
        (fun a ha => by rwa [← RingHom.mem_ker, hker])
    exact Finite.of_injective hlift hlift.injective
  -- `R'` is closed, being a topological closure
  have hclosed : IsClosed ((traceSubring ℓ D.ρ : Subring D.R) : Set D.R) :=
    Subring.isClosed_topologicalClosure _
  have hlem := exists_pow_comap_le_pow_maximalIdeal_traceSubring hℓOdd hdim hℓ5 h hirr D htr
  haveI hloc : IsLocalRing (traceSubring ℓ D.ρ) :=
    isLocalRing_of_isClosed_subring D.isAdic hclosed
  have hmax : IsLocalRing.maximalIdeal (traceSubring ℓ D.ρ) =
      Ideal.comap (traceSubring ℓ D.ρ).subtype (IsLocalRing.maximalIdeal D.R) :=
    maximalIdeal_eq_comap_of_isClosed_subring D.isAdic hclosed
  have hadicC : IsAdic (IsLocalRing.maximalIdeal (traceSubring ℓ D.ρ)) := by
    rw [hmax]
    exact isAdic_comap_maximalIdeal_of_forall_exists_le D.isAdic hlem
  have hcomplC : IsAdicComplete (IsLocalRing.maximalIdeal (traceSubring ℓ D.ρ))
      (traceSubring ℓ D.ρ) := by
    rw [hmax]
    exact isAdicComplete_comap_maximalIdeal_of_forall_exists_le D.isAdic hclosed hlem
  refine ⟨hloc, ?_, hadicC, hcomplC⟩
  refine isNoetherianRing_of_fg_maximalIdeal hcomplC ?_
  rw [hmax]
  exact fg_comap_maximalIdeal_traceSubring hℓOdd hdim hℓ5 h hirr D htr

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
2026-07-25; AUDITED 2026-07-25 — **VERDICT: NOT DISCHARGEABLE. Remove
it by the interface change described below; do NOT dispatch a proof
effort at it.**): the coefficient field `k` is generated as a ring by
the coefficients of the Frobenius characteristic polynomials of `ρbar`
at the good primes — equivalently, `k` is the trace field of `ρbar`.

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
consumed at `k = ZMod ℓ` (`Lift.lean`'s `exists_hardlyRamifiedLift`) —
because any subring of `𝔽_ℓ` containing `1` is everything, and the
generating set is nonempty (the `charFrob` are monic of degree 2, so
`coeff 2 = 1` is in it).

## AUDIT (2026-07-25): the leaf is the ch. 4 headline in disguise

Quantified over the coefficient field `k` — which is how it is stated,
`k` being a section variable — this leaf is EQUIVALENT to this
project's own ch. 4 headline
`not_isIrreducible_of_isHardlyRamified_of_five_le`
(`Modularity/KhareWintenberger.lean`). It is therefore not a
deformation-theoretic fact provable here: every proof of it is
circular. Argument, in three steps.

1. *Every hypothesis of this leaf is stable under extension of the
   coefficient field.* `IsHardlyRamified` (`HardlyRamified/Defs.lean`)
   is the conjunction of: `det ρ` equal to the cyclotomic character
   pushed through `algebraMap ℤ_[ℓ] R`; unramifiedness outside
   `{2, ℓ}`; `IsFlatAt` at `ℓ`; and the tame-at-`2` clause (a
   surjective linear functional whose quotient character is unramified
   with trivial square). Each is transported along
   `GaloisRep.baseChange` for a field extension `E → k`, and the
   development already relies on exactly that transport elsewhere
   (`(ρO.baseChange kk').IsFlatAt`, `Modularity/Interface.lean`).
   Irreducibility transports too: a hardly ramified irreducible `ρbar`
   over a finite field of odd characteristic is ABSOLUTELY irreducible
   (oddness of the determinant — the very step recorded on
   `exists_framedGaloisRep_traceSubring` above), and absolute
   irreducibility is preserved by base change.

2. *The conclusion is not stable.* The `charFrob` coefficients of a
   base change `ρbar₀ ⊗_E k` are the images of those of `ρbar₀`, hence
   lie in the subfield `E`; `Subring.closure` of a subset of `E` is
   contained in `E`. For `E ⊊ k` the conclusion `… = ⊤` fails.

3. *Hence the leaf implies nonexistence.* Given ANY irreducible hardly
   ramified `ρbar₀` over a finite field `E` of characteristic `ℓ`,
   choose a proper finite extension `k ⊋ E` and apply this leaf to
   `ρbar₀ ⊗_E k`: steps 1 and 2 contradict each other. So the leaf
   implies "there is no irreducible hardly ramified mod-`ℓ`
   representation over any finite field of characteristic `ℓ`" for
   every odd `ℓ` — the ch. 4 headline that pillars α, β, γ exist to
   prove. The leaf carries no `5 ≤ ℓ` hypothesis, so it is if anything
   STRONGER than that headline.

**The consuming cone does NOT force `k = 𝔽_ℓ`,** so the leaf cannot be
salvaged by proving it only at the prime field. `Lift.lean`'s B6a is
indeed at `k = ZMod ℓ`, but pillar α
(`exists_hardlyRamified_lift_residual_of_five_le`) is consumed at a
GENERAL finite `k` through the headline: `Modularity/Interface.lean`'s
residual-modularity leaves
(`exists_weightTwoEigenform_residual_of_isIrreducible_of_five_le` and
the `ℓ ≥ 5` branches near its lines 3648, 3748, 7066) are stated over a
general `k`, and at its line ~21090 the field is literally produced by
`exists_residual_isHardlyRamified_odd` as the residue field of an
arbitrary local coefficient ring — not the prime field.

## The interface change that removes this leaf

The defect is that `traceSubring` / `HardlyRamifiedDeformation.IsTraceGenerated`
are taken over `ℤ_ℓ`, whereas Mazur's and Carayol's deformation
categories are categories of complete Noetherian local **`W(k)`**-algebras
with residue field `k`. Over `ℤ_ℓ` the residue field of the trace
subring `R'` is only the trace field, which is what forces this leaf;
over a coefficient ring `Λ` with `Λ ↠ k` it is `k` by construction and
the `π_surjective` field of the descended datum is free.

PREFERRED FIX (cheapest, and internal to this module): let `Λ` be the
Cohen coefficient ring of `D.R` supplied by the leaf
`exists_coefficientRing_ringHom` already in this file — it delivers
`ι : Λ →+* D.R` with `D.π ∘ ι` SURJECTIVE — and replace
`Set.range (algebraMap ℤ_[ℓ] ·)` by `Set.range ι` in both `traceSubring`
and `IsTraceGenerated`. Then `subring_closure_charFrob_coeff_eq_top`
disappears from `exists_isTraceGenerated_ringHom_of_forall_trace_mem`
(its `π_surjective` obligation becomes `ι`'s surjectivity onto `k`),
and the universality/finiteness/presentation strata that consume
`IsTraceGenerated` are, if anything, better served: their minimal
presentations are already stated over `Λ ≅ W(k)`.

ALTERNATIVE FIX (the "normalization" route, more work): keep the
`ℤ_ℓ`-spelling and make pillar α at a general `k` a COROLLARY of pillar
α at the trace field `E ⊆ k` — descend `ρbar` to `E` (legitimate: `k`
is finite, so `Br(E) = 0`, and an absolutely irreducible representation
with traces in `E` is conjugate to one over `E`), lift there, then push
the lift back up along the unramified base change `O ↦ O ⊗_{W(E)} W(k)`.
This is the literature's "take `k` to be the trace field"; in Lean it is
two substantial new leaves.

BOTH fixes cross into declarations with other owners (`traceSubring` and
`IsTraceGenerated` feed the two sibling leaves and the universality
strata; the alternative touches `Modularity/KhareWintenberger.lean`), so
neither was made by this leaf's owner. Until one is made, this `sorry`
stands as the honest record of the gap.

References: Khare–Wintenberger, *Serre's modularity conjecture (I)*, §2
(the coefficient field is the field generated by the traces); Carayol,
*Formes modulaires et représentations galoisiennes à valeurs dans un
anneau local complet*, Théorème 1 (the residue field of the trace
subring is the trace field); Mazur, *Deforming Galois representations*,
§1.2 (the deformation category is over `W(k)`). -/
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

/-- **Integrality transfer along a change of base ring** (PROVEN
2026-07-25, elementary): if `φ : R →+* S` intertwines the two algebra
structures on `A` (`algebraMap S A ∘ φ = algebraMap R A`), then an
element integral over `R` is integral over `S` — map the monic witness
polynomial coefficientwise along `φ`, which preserves monicity and, by
the intertwining, its value at `x`.

Consumed below with `φ = PadicInt.toZMod : ℤ_[ℓ] →+* ZMod ℓ`, to pass
from integrality over `ℤ_ℓ` (the form in which the mod-`ℓ` fibre leaf
states its conclusion) to integrality over the FIELD `ZMod ℓ`, which is
what makes the generated subring a field. -/
theorem isIntegral_of_algebraMap_comp {R S A : Type*} [CommRing R] [CommRing S]
    [CommRing A] [Algebra R A] [Algebra S A] (φ : R →+* S)
    (hφ : ∀ r, algebraMap S A (φ r) = algebraMap R A r) {x : A}
    (h : IsIntegral R x) : IsIntegral S x := by
  obtain ⟨f, hmonic, heval⟩ := h
  refine ⟨f.map φ, hmonic.map φ, ?_⟩
  rw [Polynomial.eval₂_map]
  rw [show (algebraMap S A).comp φ = algebraMap R A from RingHom.ext hφ]
  exact heval

/-- **Algebraic elements generate a finite subring** (PROVEN 2026-07-25,
pure commutative algebra — no arithmetic content): a subring `B` of a
domain `A`, every element of which is integral over a field `F`, is
FINITE as soon as `A` carries a ring map `ψ` to a finite field.

Proof: a nonzero element of `B` is a nonzero element of the domain `A`
integral over the field `F`, hence a UNIT of `A` (`IsIntegral.isUnit`),
so its image under `ψ` is a unit of the target field and in particular
nonzero. Therefore `ψ` is injective on `B` (apply this to a difference),
and `B` embeds in the finite target.

This is the step that bounds the residue ring of a point of the mod-`ℓ`
fibre: the closed subring topologically generated by the Frobenius
traces cannot be an infinite algebraic extension of `𝔽_ℓ`, because it is
a FIELD and therefore meets the maximal ideal only in `0`, so the
residue map — surjective onto the finite `k` — already embeds it. -/
theorem finite_subring_of_forall_isIntegral {A : Type*} [CommRing A] [IsDomain A]
    {F : Type*} [Field F] [Algebra F A] {κ : Type*} [Field κ] [Finite κ]
    (ψ : A →+* κ) {B : Subring A} (hB : ∀ x ∈ B, IsIntegral F x) :
    ((B : Set A)).Finite := by
  have hinj : Set.InjOn ψ (B : Set A) := by
    intro a ha b hb hab
    by_contra hne
    have hsub : a - b ∈ B := B.sub_mem ha hb
    have h0 : a - b ≠ 0 := sub_ne_zero.mpr hne
    obtain ⟨u, hu⟩ := (hB _ hsub).isUnit h0
    have hψ0 : ψ (a - b) = 0 := by rw [map_sub, hab, sub_self]
    rw [← hu] at hψ0
    exact (IsUnit.map ψ ⟨u, rfl⟩).ne_zero hψ0
  exact Set.Finite.of_finite_image (Set.toFinite _) hinj

/-- **Density and Krull's intersection theorem** (PROVEN 2026-07-25,
pure commutative algebra and topology — no arithmetic content): in a
Noetherian local ring whose topology is the maximal-adic one, a
topologically DENSE subring `C` whose image in `R ⧸ p` is FINITE forces
the prime `p` to be the maximal ideal.

Proof: write `A = R ⧸ p`, a Noetherian domain, and `J = 𝔪 · A` for the
image of the maximal ideal, a proper ideal of `A` (its contraction is
`𝔪 ⊔ p = 𝔪 ≠ ⊤`). Krull's intersection theorem for Noetherian domains
(`Ideal.iInf_pow_eq_bot_of_isDomain`) gives `⋂ₙ Jⁿ = 0`. Density in the
adic topology says every `x : R` is approximated by `C` to every adic
order: `x - c ∈ 𝔪ⁿ`, hence `x̄ - c̄ ∈ Jⁿ`. Since the image of `C` is
finite, choosing `n` beyond the finitely many orders at which `x̄`
differs from each element of that image forces `x̄` to BE one of them —
so `A` equals the finite image, and a finite domain is a field
(`Finite.isField_of_domain`), i.e. `p` is maximal, i.e. `p = 𝔪`.

Note the pigeonhole is finite, not a limiting argument: no completeness
of `R` is used, only Noetherian-ness through Krull. -/
theorem eq_maximalIdeal_of_isPrime_of_finite_image {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (hadic : IsAdic (IsLocalRing.maximalIdeal R))
    {C : Subring R} (hgen : C.topologicalClosure = ⊤) {p : Ideal R}
    (hp : p.IsPrime)
    (hfin : ((Ideal.Quotient.mk p) '' (C : Set R)).Finite) :
    p = IsLocalRing.maximalIdeal R := by
  classical
  haveI := hp
  haveI : IsDomain (R ⧸ p) := Ideal.Quotient.isDomain p
  haveI : IsNoetherianRing (R ⧸ p) :=
    isNoetherianRing_of_surjective R (R ⧸ p) (Ideal.Quotient.mk p)
      Ideal.Quotient.mk_surjective
  -- the image of the maximal ideal is a proper ideal of the quotient
  set J : Ideal (R ⧸ p) :=
    (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk p) with hJdef
  have hpm : p ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal hp.ne_top
  have hJ : J ≠ ⊤ := by
    intro htop
    have hcomap : Ideal.comap (Ideal.Quotient.mk p) J = IsLocalRing.maximalIdeal R := by
      rw [hJdef, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hpm]
    rw [htop] at hcomap
    simp only [Ideal.comap_top] at hcomap
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top hcomap.symm
  have hKrull : ⨅ n : ℕ, J ^ n = ⊥ := Ideal.iInf_pow_eq_bot_of_isDomain J hJ
  -- density: every element is approximated by the subring to any adic order
  have hopen : ∀ n : ℕ, IsOpen (((IsLocalRing.maximalIdeal R ^ n : Ideal R)) : Set R) :=
    (isAdic_iff.mp hadic).1
  have hdense : Dense ((C : Set R)) := by
    have hcoe := congrArg (fun S : Subring R => (S : Set R)) hgen
    simp only [Subring.coe_top] at hcoe
    exact dense_iff_closure_eq.mpr hcoe
  have happrox : ∀ (x : R) (n : ℕ), ∃ c ∈ C,
      x - c ∈ (IsLocalRing.maximalIdeal R ^ n : Ideal R) := by
    intro x n
    have hU : IsOpen ((fun y => x + y) ''
        (((IsLocalRing.maximalIdeal R ^ n : Ideal R)) : Set R)) :=
      (isOpenMap_add_left x) _ (hopen n)
    have hxU : x ∈ (fun y => x + y) ''
        (((IsLocalRing.maximalIdeal R ^ n : Ideal R)) : Set R) :=
      ⟨0, Submodule.zero_mem _, by simp⟩
    obtain ⟨y, hy1, hy2⟩ := hdense.inter_open_nonempty _ hU ⟨x, hxU⟩
    obtain ⟨m, hm, rfl⟩ := hy1
    exact ⟨x + m, hy2, by simpa using neg_mem hm⟩
  -- pigeonhole: the finite image already contains everything
  have hsurj : ∀ a : R ⧸ p, a ∈ (Ideal.Quotient.mk p) '' (C : Set R) := by
    intro a
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hne : ∀ e : R ⧸ p, e ≠ Ideal.Quotient.mk p x →
        ∃ n : ℕ, Ideal.Quotient.mk p x - e ∉ J ^ n := by
      intro e he
      by_contra hall
      have hall' : ∀ n : ℕ, Ideal.Quotient.mk p x - e ∈ J ^ n := fun n => by
        by_contra hn
        exact hall ⟨n, hn⟩
      have hmem : Ideal.Quotient.mk p x - e ∈ ⨅ n : ℕ, J ^ n :=
        Submodule.mem_iInf _ |>.mpr hall'
      rw [hKrull] at hmem
      exact he (sub_eq_zero.mp (Submodule.mem_bot _ |>.mp hmem)).symm
    choose! N hN using hne
    obtain ⟨c, hcC, hc⟩ := happrox x (hfin.toFinset.sup N)
    have hmem : Ideal.Quotient.mk p x - Ideal.Quotient.mk p c ∈ J ^ hfin.toFinset.sup N := by
      rw [← map_sub, hJdef, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hc
    by_cases hcx : Ideal.Quotient.mk p c = Ideal.Quotient.mk p x
    · exact ⟨c, hcC, hcx⟩
    · exact absurd (Ideal.pow_le_pow_right
        (Finset.le_sup (hfin.mem_toFinset.mpr ⟨c, hcC, rfl⟩)) hmem) (hN _ hcx)
  haveI : Finite (R ⧸ p) :=
    Set.finite_univ_iff.mp (hfin.subset (fun a _ => hsurj a))
  exact IsLocalRing.eq_maximalIdeal
    (Ideal.Quotient.maximal_of_isField p (Finite.isField_of_domain (R ⧸ p)))

omit [Algebra ℤ_[ℓ] k] [TopologicalSpace k] [DiscreteTopology k] in
/-- **From algebraic traces to a one-point mod-`ℓ` fibre** (PROVEN
2026-07-25, pure commutative algebra and topology — no arithmetic
content; this is the JOINT at which the mod-`ℓ` fibre leaf below was cut
on 2026-07-25): let `R` be a Noetherian local `ℤ_ℓ`-algebra carrying the
maximal-adic topology, with a surjection `π` onto the finite field `k`,
topologically generated as a `ℤ_ℓ`-algebra by a set `T`. If `p` is a
prime containing `ℓ` and every element of `T` becomes INTEGRAL over
`ℤ_ℓ` in `R ⧸ p`, then `p = 𝔪`.

Proof, in three moves, each a lemma above:
* `ℓ ∈ p` makes `R ⧸ p` a domain of characteristic `ℓ`, so it is a
  `ZMod ℓ`-algebra and its `ℤ_ℓ`-structure map factors through
  `PadicInt.toZMod` — whence, by `isIntegral_of_algebraMap_comp`, the
  generators are integral over the FIELD `ZMod ℓ`, and so is the whole
  subring they generate (`RingHom.map_closure` plus `Subring.closure_le`
  into the integral closure).
* `finite_subring_of_forall_isIntegral`, applied to the map `R ⧸ p → k`
  induced by `π` (legitimate since `p ≤ 𝔪 = ker π`), makes that subring
  — the image of the topologically dense generated subring — FINITE.
* `eq_maximalIdeal_of_isPrime_of_finite_image` then closes: density plus
  Krull's intersection theorem upgrade "finite image" to "the quotient
  IS that finite image", and a finite domain is a field.

The arithmetic hypothesis is thus reduced to the integrality of the
Frobenius traces modulo `p` — see the leaf below. -/
theorem eq_maximalIdeal_of_isPrime_of_isIntegral_quotient {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [Algebra ℤ_[ℓ] R]
    (hadic : IsAdic (IsLocalRing.maximalIdeal R))
    (π : R →+* k) (hπ : Function.Surjective π)
    {T : Set R}
    (hgen : (Subring.closure (Set.range (algebraMap ℤ_[ℓ] R) ∪ T)).topologicalClosure = ⊤)
    {p : Ideal R} (hp : p.IsPrime) (hℓ : ((ℓ : ℕ) : R) ∈ p)
    (hint : ∀ x ∈ T, IsIntegral ℤ_[ℓ] (Ideal.Quotient.mk p x)) :
    p = IsLocalRing.maximalIdeal R := by
  classical
  haveI := hp
  haveI : IsDomain (R ⧸ p) := Ideal.Quotient.isDomain p
  have hpm : p ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal hp.ne_top
  -- the quotient has characteristic `ℓ`
  have hℓ0 : ((ℓ : ℕ) : R ⧸ p) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk p) ℓ, Ideal.Quotient.eq_zero_iff_mem]
    exact hℓ
  haveI : CharP (R ⧸ p) ℓ := by
    have hd : ringChar (R ⧸ p) ∣ ℓ := ringChar.dvd hℓ0
    have hne : ringChar (R ⧸ p) ≠ 1 := CharP.ringChar_ne_one
    have heq : ringChar (R ⧸ p) = ℓ :=
      ((Nat.Prime.eq_one_or_self_of_dvd Fact.out _ hd).resolve_left hne)
    exact heq ▸ ringChar.charP (R ⧸ p)
  letI : Algebra (ZMod ℓ) (R ⧸ p) := ZMod.algebra _ ℓ
  -- compatibility of the `ℤ_ℓ`- and `ZMod ℓ`-algebra structures
  have hcompat : ∀ z : ℤ_[ℓ],
      algebraMap (ZMod ℓ) (R ⧸ p) (PadicInt.toZMod z) = algebraMap ℤ_[ℓ] (R ⧸ p) z := by
    intro z
    have h1 : z - ((PadicInt.zmodRepr z : ℕ) : ℤ_[ℓ]) ∈
        Ideal.span {((ℓ : ℕ) : ℤ_[ℓ])} := by
      rw [← PadicInt.maximalIdeal_eq_span_p]
      exact PadicInt.sub_zmodRepr_mem z
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h1
    have h2 : algebraMap ℤ_[ℓ] (R ⧸ p) z = ((PadicInt.zmodRepr z : ℕ) : R ⧸ p) := by
      have hcm := congrArg (algebraMap ℤ_[ℓ] (R ⧸ p)) hc
      rw [map_mul, map_sub, map_natCast, map_natCast, hℓ0, mul_zero] at hcm
      linear_combination -hcm
    rw [h2, show PadicInt.toZMod z = ((PadicInt.zmodRepr z : ℕ) : ZMod ℓ) from rfl,
      map_natCast]
  -- everything in the image subring is integral over `ZMod ℓ`
  have hall : ∀ x ∈ (Subring.closure (Set.range (algebraMap ℤ_[ℓ] R) ∪ T)).map
      (Ideal.Quotient.mk p), IsIntegral (ZMod ℓ) x := by
    rw [RingHom.map_closure]
    intro x hx
    have hle : Subring.closure
        ((Ideal.Quotient.mk p) '' (Set.range (algebraMap ℤ_[ℓ] R) ∪ T)) ≤
        (integralClosure (ZMod ℓ) (R ⧸ p)).toSubring := by
      rw [Subring.closure_le]
      rintro y ⟨z, hz, rfl⟩
      rcases hz with ⟨w, rfl⟩ | hz
      · show IsIntegral (ZMod ℓ) _
        have hq : Ideal.Quotient.mk p (algebraMap ℤ_[ℓ] R w) =
            algebraMap ℤ_[ℓ] (R ⧸ p) w := rfl
        rw [hq, ← hcompat w]
        exact isIntegral_algebraMap
      · exact isIntegral_of_algebraMap_comp PadicInt.toZMod hcompat (hint z hz)
    exact hle hx
  -- hence the image is finite, and density finishes the job
  have hker : RingHom.ker π = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective π hπ)
  have hpk : ∀ a ∈ p, π a = 0 := by
    intro a ha
    rw [← RingHom.mem_ker, hker]
    exact hpm ha
  have hfin := finite_subring_of_forall_isIntegral (F := ZMod ℓ)
    (Ideal.Quotient.lift p π hpk) hall
  rw [Subring.coe_map] at hfin
  exact eq_maximalIdeal_of_isPrime_of_finite_image hadic hgen hp hfin

/-- **The Dickson polynomials are monic of the expected degree** (PROVEN
2026-07-26, elementary; auxiliary two-step-induction form). `dickson 1 a n`
is the polynomial family with `D₀ = 2`, `D₁ = X`,
`D_{n+2} = X · D_{n+1} − a · D_n`, i.e. the one satisfying
`Dₙ(x + y) = xⁿ + yⁿ` when `x y = a` — the trace of the `n`-th power of a
2×2 matrix as a polynomial in its trace and determinant. Monicity of
degree exactly `n` (for `n ≥ 1`) is what makes it a WITNESS OF
INTEGRALITY: `tr M` is a root of the monic `Dₙ(X) − tr(Mⁿ)` over any
subring containing `det M` and `tr(Mⁿ)`. -/
lemma monic_natDegree_dickson_one_aux {R : Type*} [CommRing R] [Nontrivial R]
    (a : R) : ∀ n : ℕ,
    ((dickson 1 a (n + 1)).Monic ∧ (dickson 1 a (n + 1)).natDegree = n + 1) ∧
    ((dickson 1 a (n + 2)).Monic ∧ (dickson 1 a (n + 2)).natDegree = n + 2) := by
  intro n
  induction n with
  | zero =>
    have hC2 : (C (2 : R) : R[X]) = 2 := map_ofNat C 2
    have h2 : dickson 1 a 2 = X ^ 2 - C (2 * a) := by
      rw [dickson_two, C_mul, hC2]
      push_cast
      ring
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [dickson_one]; exact monic_X
    · rw [dickson_one]; exact natDegree_X
    · rw [h2]; exact monic_X_pow_sub_C _ (by norm_num)
    · rw [h2]; exact natDegree_X_pow_sub_C
  | succ m ih =>
    obtain ⟨⟨hm1, hd1⟩, hm2, hd2⟩ := ih
    have hXmul : (X * dickson 1 a (m + 2)).Monic := monic_X.mul hm2
    have hXdeg : (X * dickson 1 a (m + 2)).natDegree = m + 3 := by
      rw [monic_X.natDegree_mul hm2, natDegree_X, hd2]; omega
    have hCdeg : (C a * dickson 1 a (m + 1)).degree ≤ ((m + 1 : ℕ) : WithBot ℕ) := by
      refine le_trans (degree_mul_le _ _) ?_
      have h1 : (C a).degree ≤ 0 := degree_C_le
      have h2 : (dickson 1 a (m + 1)).degree ≤ ((m + 1 : ℕ) : WithBot ℕ) := by
        have hle := degree_le_natDegree (p := dickson 1 a (m + 1))
        rwa [hd1] at hle
      calc (C a).degree + (dickson 1 a (m + 1)).degree
          ≤ 0 + ((m + 1 : ℕ) : WithBot ℕ) := add_le_add h1 h2
        _ = ((m + 1 : ℕ) : WithBot ℕ) := by rw [zero_add]
    have hCnat : (C a * dickson 1 a (m + 1)).natDegree ≤ m + 1 :=
      natDegree_le_iff_degree_le.mpr hCdeg
    have hrec : dickson 1 a (m + 3) =
        X * dickson 1 a (m + 2) - C a * dickson 1 a (m + 1) := dickson_add_two 1 a (m + 1)
    have hltN : (C a * dickson 1 a (m + 1)).natDegree <
        (X * dickson 1 a (m + 2)).natDegree := by
      rw [hXdeg]; exact lt_of_le_of_lt hCnat (by omega)
    have hlt : (C a * dickson 1 a (m + 1)).degree < (X * dickson 1 a (m + 2)).degree := by
      refine lt_of_le_of_lt hCdeg ?_
      rw [degree_eq_natDegree hXmul.ne_zero, hXdeg]
      exact_mod_cast (by omega : m + 1 < m + 3)
    refine ⟨⟨hm2, hd2⟩, ?_, ?_⟩
    · rw [hrec]; exact hXmul.sub_of_left hlt
    · rw [hrec, natDegree_sub_eq_left_of_natDegree_lt hltN, hXdeg]

/-- **The Dickson polynomials are monic of the expected degree** (PROVEN
2026-07-26, elementary): for `n ≥ 1`, `dickson 1 a n` is monic of degree
`n`. See `monic_natDegree_dickson_one_aux`. -/
lemma monic_natDegree_dickson_one {R : Type*} [CommRing R] [Nontrivial R]
    (a : R) (n : ℕ) (hn : n ≠ 0) :
    (dickson 1 a n).Monic ∧ (dickson 1 a n).natDegree = n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (monic_natDegree_dickson_one_aux a m).1

/-- **Cayley–Hamilton in rank 2** (PROVEN 2026-07-26, elementary):
`M² = (tr M)·M − (det M)·1` for a 2×2 matrix over any nontrivial
commutative ring. This is `Matrix.aeval_self_charpoly` read through
`Matrix.charpoly_fin_two`, and it is what makes the trace of the powers of
`M` satisfy the Dickson recursion. -/
lemma sq_eq_trace_smul_sub_det_smul {A : Type*} [CommRing A] [Nontrivial A]
    (M : Matrix (Fin 2) (Fin 2) A) : M ^ 2 = M.trace • M - M.det • 1 := by
  have h := Matrix.aeval_self_charpoly M
  rw [Matrix.charpoly_fin_two, map_add, map_sub, map_mul, aeval_X_pow, aeval_C, aeval_X,
    aeval_C, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
    one_mul] at h
  have hab : M ^ 2 - (M.trace • M - M.det • 1) = M ^ 2 - M.trace • M + M.det • 1 := by abel
  rw [← sub_eq_zero, hab, h]

/-- **Traces of powers follow the Dickson recursion** (PROVEN 2026-07-26,
elementary; auxiliary two-step-induction form):
`tr (Mⁿ) = Dₙ(tr M)` where `Dₙ = dickson 1 (det M) n`. The recursion is
Cayley–Hamilton `Mⁿ⁺² = (tr M)·Mⁿ⁺¹ − (det M)·Mⁿ` traced. -/
lemma trace_pow_eq_eval_dickson_aux {A : Type*} [CommRing A] [Nontrivial A]
    (M : Matrix (Fin 2) (Fin 2) A) : ∀ n : ℕ,
    (M ^ n).trace = (dickson 1 M.det n).eval M.trace ∧
    (M ^ (n + 1)).trace = (dickson 1 M.det (n + 1)).eval M.trace := by
  have hrec : ∀ n : ℕ, M ^ (n + 2) = M.trace • M ^ (n + 1) - M.det • M ^ n := by
    intro n
    have hsplit : M ^ (n + 2) = M ^ n * M ^ 2 := pow_add M n 2
    rw [hsplit, sq_eq_trace_smul_sub_det_smul, mul_sub, mul_smul_comm, mul_smul_comm,
      mul_one, ← pow_succ]
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [pow_zero, Matrix.trace_one, dickson_zero]
      norm_num
    · rw [pow_one, dickson_one, eval_X]
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    rw [hrec m, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, ih.1, ih.2,
      dickson_add_two]
    simp only [eval_sub, eval_mul, eval_X, eval_C]
    ring

/-- **Traces of powers follow the Dickson recursion** (PROVEN 2026-07-26,
elementary): `tr (Mⁿ) = (dickson 1 (det M) n).eval (tr M)`. -/
lemma trace_pow_eq_eval_dickson {A : Type*} [CommRing A] [Nontrivial A]
    (M : Matrix (Fin 2) (Fin 2) A) (n : ℕ) :
    (M ^ n).trace = (dickson 1 M.det n).eval M.trace :=
  (trace_pow_eq_eval_dickson_aux M n).1

/-- **Descent of integrality from a power** (PROVEN 2026-07-26, elementary
— this is the algebraic half of the Khare–Wintenberger base-change
descent): if the determinant of a 2×2 matrix `M` and the trace of ONE
positive power `Mⁿ` are integral over a base ring, then so is `tr M`.

Proof: `tr M` is a root of `dickson 1 (det M) n − C (tr (Mⁿ))`, which is
MONIC of degree `n ≥ 1` with coefficients in `integralClosure R A`
(`monic_natDegree_dickson_one`, `trace_pow_eq_eval_dickson`); so `tr M` is
integral over the integral closure, hence over `R` by transitivity
(`isIntegral_trans`).

Arithmetic use: if `F/ℚ` is finite and `Frob_q^f` lies in `G_F`, the trace
of `ρ(Frob_q)` is integral over anything the traces of `ρ|_{G_F}` are
integral over — the determinant being a cyclotomic value, hence already
defined over the base. -/
theorem isIntegral_trace_of_isIntegral_trace_pow {Rb A : Type*} [CommRing Rb] [CommRing A]
    [Nontrivial A] [Algebra Rb A] {n : ℕ} (hn : n ≠ 0) (M : Matrix (Fin 2) (Fin 2) A)
    (hdet : IsIntegral Rb M.det) (htr : IsIntegral Rb (M ^ n).trace) :
    IsIntegral Rb M.trace := by
  set S := integralClosure Rb A with hS
  have hd : M.det ∈ S := hdet
  have hs : (M ^ n).trace ∈ S := htr
  have hmon := monic_natDegree_dickson_one (⟨M.det, hd⟩ : S) n hn
  refine isIntegral_trans (A := S) M.trace ?_
  refine ⟨dickson 1 (⟨M.det, hd⟩ : S) n - C (⟨(M ^ n).trace, hs⟩ : S), ?_, ?_⟩
  · refine hmon.1.sub_of_left ?_
    refine lt_of_le_of_lt degree_C_le ?_
    rw [degree_eq_natDegree hmon.1.ne_zero, hmon.2]
    exact_mod_cast Nat.pos_of_ne_zero hn
  · rw [eval₂_sub, eval₂_eq_eval_map, Polynomial.map_dickson, eval₂_C]
    have hmapd : (algebraMap S A) (⟨M.det, hd⟩ : S) = M.det := rfl
    rw [hmapd, ← trace_pow_eq_eval_dickson M n]
    simp

/-- **Some positive power of any element lands in a finite-index subgroup**
(PROVEN 2026-07-26, elementary): the powers `gⁱ` cannot lie in pairwise
distinct cosets of a finite-index `H`, so `g^{j−i} ∈ H` for some `i < j`.
This is the group-theoretic half of the base-change descent: with `H = G_F`
for a number field `F` of degree `d`, it produces the residue degree
`f ≤ d` with `Frob_q^f ∈ G_F`, without needing `F/ℚ` normal or `H` open. -/
theorem exists_pow_mem_of_finiteIndex {G : Type*} [Group G] (H : Subgroup G)
    [H.FiniteIndex] (g : G) : ∃ m : ℕ, 0 < m ∧ g ^ m ∈ H := by
  have key : ∀ i j : ℕ, i < j →
      (QuotientGroup.mk (g ^ i) : G ⧸ H) = QuotientGroup.mk (g ^ j) →
      ∃ m : ℕ, 0 < m ∧ g ^ m ∈ H := by
    intro i j hij heq
    refine ⟨j - i, by omega, ?_⟩
    have hmem : (g ^ i)⁻¹ * g ^ j ∈ H := QuotientGroup.eq.mp heq
    have hpow : g ^ i * g ^ (j - i) = g ^ j := by
      rw [← pow_add]; congr 1; omega
    have hrw : (g ^ i)⁻¹ * g ^ j = g ^ (j - i) := by rw [← hpow, inv_mul_cancel_left]
    rwa [hrw] at hmem
  obtain ⟨i, j, hne, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun i : ℕ => (QuotientGroup.mk (g ^ i) : G ⧸ H))
  rcases lt_or_gt_of_ne hne with hij | hij
  · exact key i j hij heq
  · exact key j i hij heq.symm

/-- **Potential-modularity leaf** (sorry node — the single genuinely deep
arithmetic node of the lifting core, isolated on 2026-07-26 as the residue
of the trace form after the Khare–Wintenberger DESCENT was proven): in the
weakly universal, trace-generated hardly ramified deformation ring there is
a FINITE-INDEX subgroup `H ≤ G_ℚ` on which the Frobenius-free traces of the
universal deformation are already integral over `ℤ_ℓ` modulo any prime
`p ∋ ℓ` — i.e. `−(coeff 1)` of the characteristic polynomial of `D.ρ g` is
integral for every `g ∈ H`.

WHAT `H` IS. Verbatim the potential-modularity input: `H = G_F` for the
totally real solvable-at-the-relevant-places field `F/ℚ` produced by
Taylor's Moret-Bailly argument, over which `ρbar|_{G_F}` becomes modular.
Over `F` the Taylor–Wiles–Kisin patching method proves `R_F = T_F` with
`T_F` a Hecke algebra of Hilbert modular forms of fixed weight and level,
hence a FINITE `ℤ_ℓ`-algebra; the deformation `D.ρ|_{G_F}` is classified by
a map `R_F → D.R`, so every trace `tr D.ρ(g)`, `g ∈ G_F`, is the image of
an element integral over `ℤ_ℓ`. `[F : ℚ] < ∞` is exactly `H.FiniteIndex`.
The mod-`p` quotient is kept in the statement deliberately: it is the
weakest form that still supports the consumer, and it is strictly weaker
than `Module.Finite ℤ_[ℓ] D.R`, which is what the un-quotiented form would
give back through the completeness bootstrap
`moduleFinite_of_finite_quotient_span`.

WHY THIS JOINT (2026-07-26). The predecessor leaf — every `charFrob`
coefficient at every good prime is integral mod `p` — contains three pieces
of pure algebra that are now discharged and must never be re-proved:
* only the coefficient `1` (the trace) has content. The constant
  coefficient is the DETERMINANT, i.e. `algebraMap ℤ_[ℓ]` of a cyclotomic
  value by `IsHardlyRamified.det`, so it is integral for free; the leading
  coefficient is `1` and every coefficient above the second vanishes,
  the charpoly being monic of degree `2`.
* the trace at a Frobenius element descends from the trace on a
  finite-index subgroup, by the Dickson identity `tr(Mⁿ) = Dₙ(tr M, det M)`
  with `Dₙ` MONIC of degree `n`: this is
  `isIntegral_trace_of_isIntegral_trace_pow`, and it is precisely
  Khare–Wintenberger's descent of the `F`-level statement to `ℚ` (the
  residue degree `f` of `q` in `F` being the `n`). Nothing about `q`
  survives it — which is why the leaf is now a statement about the
  representation, not about Frobenius elements.
* the passage from `Frob_q` to a power in `H` is
  `exists_pow_mem_of_finiteIndex`, elementary coset counting.
So the surviving obligation is exactly the modularity input, with every
piece of algebra that used to be entangled with it removed.

WHERE THE PROOF WILL HAVE TO COME FROM (audit, 2026-07-25, unchanged and
NOT to be redone). `Fermat/FLT/Modularity/Patching.lean` proves both halves
of `R = T` for its own deformation vocabulary —
`surjective_ringHom_of_charFrob_eq` and
`injective_ringHom_of_isWeaklyUniversal`, the latter through the patched-
module engine — but it carries `Module.Finite ℤ_[ℓ] T` as a HYPOTHESIS on
the Hecke side and produces no finiteness of any deformation ring, so even
the Hecke-algebra input is not yet available in the repository. Nor are its
declarations reachable from here: `Patching.lean` imports
`Modularity/KhareWintenberger.lean`, which imports THIS module, so
consuming it would close the dependency cycle this module's circularity
guard exists to prevent. Discharging this leaf therefore needs either
(i) the KW-free module split recorded in
`~/.flt-design-deformation-patching-dedup.md` plus genuine finiteness of
`T`, or (ii) the Hilbert-modular potential-modularity route, which is the
one the statement is now shaped for. CIRCULARITY GUARD: the odd-prime
dichotomy `not_isIrreducible_of_isHardlyRamified_of_five_le` must NOT be
used to discharge this vacuously — it is itself proven over pillar α, which
this cluster proves.

References: Khare–Wintenberger, *Serre's modularity conjecture (I)*,
Thm. 4.1 and §4, and *(II)*; Taylor, *Remarks on a conjecture of Fontaine
and Mazur* and *On the meromorphic continuation of degree two L-functions*;
Kisin, *Moduli of finite flat group schemes, and modularity*;
Darmon–Diamond–Taylor, *Fermat's Last Theorem*, §3; Buzzard's 2026 EPSRC
course, Lecture 4. -/
theorem exists_finiteIndex_isIntegral_charpolyCoeff_quotient_of_isWeaklyUniversal_isTraceGenerated
    (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible)
    (D : HardlyRamifiedDeformation hℓOdd ρbar)
    (hw : D.IsWeaklyUniversal) (ht : D.IsTraceGenerated) :
    letI := D.commRing; letI := D.topologicalSpace
    letI := D.isTopologicalRing; letI := D.algebra
    ∃ H : Subgroup (Field.absoluteGaloisGroup ℚ), H.FiniteIndex ∧
      ∀ p : Ideal D.R, p.IsPrime → ((ℓ : ℕ) : D.R) ∈ p →
        ∀ g ∈ H, IsIntegral ℤ_[ℓ]
          (Ideal.Quotient.mk p ((D.ρ g).charpoly.coeff 1)) :=
  sorry

/-- **Mod-`ℓ` fibre leaf, TRACE form** (PROVEN 2026-07-26 over the
potential-modularity leaf
`exists_finiteIndex_isIntegral_charpolyCoeff_quotient_of_isWeaklyUniversal_isTraceGenerated`
above, the Dickson descent `isIntegral_trace_of_isIntegral_trace_pow` and
the coset counting `exists_pow_mem_of_finiteIndex`; NARROWED TWICE before
that, on 2026-07-25: first from the
`𝔪`-primarity form `∃ n, 𝔪 ^ n ≤ (ℓ)` to the pointwise statement "every
prime containing `ℓ` is `𝔪`" — the dévissage being the pure commutative
algebra `exists_maximalIdeal_pow_le_span_of_forall_isPrime` above — and
then from that statement to the present trace form, the dévissage being
`eq_maximalIdeal_of_isPrime_of_isIntegral_quotient` above): in the
weakly universal, trace-generated hardly ramified deformation ring —
i.e. the genuine universal ring, as constructed by
`exists_isWeaklyUniversal_isTraceGenerated` — every coefficient of every
Frobenius characteristic polynomial at a good prime is INTEGRAL over
`ℤ_ℓ` modulo any prime `p ∋ ℓ`. Equivalently, since `ℓ ∈ p` makes
`D.R ⧸ p` an algebra over the prime field `𝔽_ℓ`: the Frobenius traces of
the mod-`ℓ` specialization of the universal deformation are ALGEBRAIC
over `𝔽_ℓ`.

WHY THIS JOINT. The geometric statement it replaces — the maximal ideal
is the only prime of `D.R` containing `ℓ`, i.e. the mod-`ℓ` fibre of
`Spec D.R` is a single point — follows from it by
`eq_maximalIdeal_of_isPrime_of_isIntegral_quotient`: algebraic traces
generate a subring of the domain `D.R ⧸ p` that is a FIELD, that field
embeds in the finite residue field `k` (a field meets the maximal ideal
only in `0`), hence is finite; being also topologically DENSE — this is
exactly trace generation — Krull's intersection theorem makes it the
whole of `D.R ⧸ p`, a finite domain, hence a field, so `p = 𝔪`. The
converse implication is immediate (if `p = 𝔪` then `D.R ⧸ p = k` is
finite), so the cut gives nothing away; what it buys is that the
surviving obligation is a statement about Hecke-eigenvalue-like NUMBERS
— the form in which Taylor–Wiles–Kisin patching and potential
modularity actually produce it, namely that the eigenvalues live in a
finite `ℤ_ℓ`-algebra — instead of a statement about Krull dimension.

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

HOW IT IS NOW PROVEN (2026-07-26). Three of the four coefficient cases
carry no arithmetic at all and are discharged here: the constant
coefficient is the determinant of `D.ρ (globalFrob q)`, which
`IsHardlyRamified.det` pins to `algebraMap ℤ_[ℓ]` of a cyclotomic value,
hence integral for free; `coeff 2 = 1` and `coeff n = 0` for `n ≥ 3`, the
characteristic polynomial of a rank-2 endomorphism being monic of degree
`2`. The remaining coefficient — the TRACE — is obtained from the
potential-modularity leaf
`exists_finiteIndex_isIntegral_charpolyCoeff_quotient_of_isWeaklyUniversal_isTraceGenerated`
above by the Khare–Wintenberger base-change descent, which is proven here
in two elementary pieces: `exists_pow_mem_of_finiteIndex` produces `m > 0`
with `Frob_q^m ∈ H` (the residue degree of `q` in `F`), and
`isIntegral_trace_of_isIntegral_trace_pow` — the Dickson identity
`tr(Mᵐ) = Dₘ(tr M, det M)` with `Dₘ` MONIC of degree `m` — brings the
integrality back down from `tr(ρ(Frob_q)^m)` to `tr ρ(Frob_q)`, the
determinant being available as a cyclotomic value. So everything that
remains open here is the modularity input, and it is stated in the leaf
above; see its docstring for the audit of what discharging it requires.

The hypotheses characterize `D` up to canonical isomorphism (weak
universality + trace generation = universality, by
`isUniversal_of_isWeaklyUniversal_isTraceGenerated` and the rigidity
theorem `exists_ringEquiv_of_isUniversal`), so a future proof may
construct its own universal datum, prove ITS mod-`ℓ` fibre a point, and
transport the result along the canonical isomorphism.

References: Khare–Wintenberger, *Serre's modularity conjecture (I)*,
Thm. 4.1 and §4, and *(II)*; Taylor, *Remarks on a conjecture of
Fontaine and Mazur*; Kisin, *Moduli of finite flat group schemes, and
modularity*; Buzzard's 2026 EPSRC course, Lecture 4. -/
theorem isIntegral_charFrobCoeff_quotient_of_isWeaklyUniversal_isTraceGenerated
    (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible)
    (D : HardlyRamifiedDeformation hℓOdd ρbar)
    (hw : D.IsWeaklyUniversal) (ht : D.IsTraceGenerated) :
    letI := D.commRing; letI := D.topologicalSpace
    letI := D.isTopologicalRing; letI := D.algebra
    ∀ p : Ideal D.R, p.IsPrime → ((ℓ : ℕ) : D.R) ∈ p →
      ∀ q (hq : q.Prime), q ≠ 2 → q ≠ ℓ → ∀ n : ℕ,
        IsIntegral ℤ_[ℓ] (Ideal.Quotient.mk p
          ((D.ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff n)) := by
  letI := D.commRing; letI := D.topologicalSpace
  letI := D.isTopologicalRing; letI := D.isLocalRing; letI := D.algebra
  obtain ⟨H, hHfi, hH⟩ :=
    exists_finiteIndex_isIntegral_charpolyCoeff_quotient_of_isWeaklyUniversal_isTraceGenerated
      hℓOdd hdim hℓ5 h hirr D hw ht
  intro p hp hℓp q hq hq2 hqℓ n
  haveI := hp
  haveI : IsDomain (D.R ⧸ p) := Ideal.Quotient.isDomain p
  have hcard : Fintype.card (Fin 2) - 1 = 1 := by simp
  have hcoeffR : ∀ P : Matrix (Fin 2) (Fin 2) D.R, P.charpoly.coeff 1 = -P.trace := by
    intro P
    have hh := Matrix.trace_eq_neg_charpoly_coeff P
    rw [hcard] at hh
    rw [hh, neg_neg]
  have hcoeffQ : ∀ P : Matrix (Fin 2) (Fin 2) (D.R ⧸ p), P.charpoly.coeff 1 = -P.trace := by
    intro P
    have hh := Matrix.trace_eq_neg_charpoly_coeff P
    rw [hcard] at hh
    rw [hh, neg_neg]
  -- the Frobenius element, and the endomorphism the deformation attaches to it
  set g : Field.absoluteGaloisGroup ℚ :=
    globalFrob hq.toHeightOneSpectrumRingOfIntegersRat
  have hchar : D.ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat = (D.ρ g).charpoly :=
    GaloisRep.charFrob_eq_charpoly_globalFrob D.ρ _
  have hfinrank : Module.finrank D.R (Fin 2 → D.R) = 2 := by simp
  -- the constant coefficient is the determinant: a cyclotomic value from `ℤ_ℓ`
  have hdetR : ∀ x : Field.absoluteGaloisGroup ℚ,
      (D.ρ x).charpoly.coeff 0 = algebraMap ℤ_[ℓ] D.R
        (cyclotomicCharacter (AlgebraicClosure ℚ) ℓ x.toRingEquiv) := by
    intro x
    have hdet := LinearMap.det_eq_sign_charpoly_coeff (D.ρ x)
    rw [hfinrank] at hdet
    have h1 : LinearMap.det (D.ρ x) = (D.ρ x).charpoly.coeff 0 := by rw [hdet]; ring
    rw [← h1, ← GaloisRep.det_apply, D.isHardlyRamified.det x]
  have hintdet : ∀ x : Field.absoluteGaloisGroup ℚ,
      IsIntegral ℤ_[ℓ] (Ideal.Quotient.mk p ((D.ρ x).charpoly.coeff 0)) := by
    intro x
    rw [hdetR x]
    have hqa : Ideal.Quotient.mk p (algebraMap ℤ_[ℓ] D.R
        (cyclotomicCharacter (AlgebraicClosure ℚ) ℓ x.toRingEquiv)) =
        algebraMap ℤ_[ℓ] (D.R ⧸ p)
          (cyclotomicCharacter (AlgebraicClosure ℚ) ℓ x.toRingEquiv) := rfl
    rw [hqa]
    exact isIntegral_algebraMap
  rw [hchar]
  match n with
  | 0 => exact hintdet g
  | 1 =>
    -- the TRACE: descend from the finite-index subgroup by the Dickson recursion
    obtain ⟨m, hm0, hmH⟩ := exists_pow_mem_of_finiteIndex H g
    set Mx : Matrix (Fin 2) (Fin 2) D.R := LinearMap.toMatrixAlgEquiv' (D.ρ g) with hMx
    set N : Matrix (Fin 2) (Fin 2) (D.R ⧸ p) := Mx.map (Ideal.Quotient.mk p) with hN
    have hpow : ∀ j : ℕ, (LinearMap.toMatrixAlgEquiv' (D.ρ (g ^ j)) :
        Matrix (Fin 2) (Fin 2) D.R) = Mx ^ j := by
      intro j
      rw [hMx, map_pow, map_pow]
    have hcharMx : ∀ x : Field.absoluteGaloisGroup ℚ,
        (D.ρ x).charpoly =
          (LinearMap.toMatrixAlgEquiv' (D.ρ x) : Matrix (Fin 2) (Fin 2) D.R).charpoly := by
      intro x
      have hb := LinearMap.charpoly_toMatrix (D.ρ x) (Pi.basisFun D.R (Fin 2))
      rw [LinearMap.toMatrix_eq_toMatrix'] at hb
      rw [← hb]
      rfl
    have hmapcoeff : ∀ P : Matrix (Fin 2) (Fin 2) D.R,
        Ideal.Quotient.mk p (P.charpoly.coeff 1) =
          (P.map (Ideal.Quotient.mk p)).charpoly.coeff 1 := by
      intro P
      rw [Matrix.charpoly_map, Polynomial.coeff_map]
    have hNdet : IsIntegral ℤ_[ℓ] N.det := by
      have hd : N.det = Ideal.Quotient.mk p Mx.det := by
        rw [hN, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      have hMxdet : Mx.det = (D.ρ g).charpoly.coeff 0 := by
        have h0 := hcharMx g
        have hsign := Matrix.det_eq_sign_charpoly_coeff Mx
        simp only [Fintype.card_fin] at hsign
        rw [h0, ← hMx, hsign]
        ring
      rw [hd, hMxdet]
      exact hintdet g
    have hNtr : IsIntegral ℤ_[ℓ] ((N ^ m).trace) := by
      have hNm : N ^ m = (Mx ^ m).map (Ideal.Quotient.mk p) := by
        rw [hN, ← RingHom.mapMatrix_apply, ← map_pow, RingHom.mapMatrix_apply]
      have htr : (N ^ m).trace = Ideal.Quotient.mk p ((Mx ^ m).trace) := by
        rw [hNm, ← AddMonoidHom.map_trace]
      have hMxm : (Mx ^ m).trace = -((D.ρ (g ^ m)).charpoly.coeff 1) := by
        rw [hcharMx (g ^ m), hpow m, hcoeffR, neg_neg]
      rw [htr, hMxm, map_neg]
      exact (hH p hp hℓp (g ^ m) hmH).neg
    have hNtrace := isIntegral_trace_of_isIntegral_trace_pow
      (Rb := ℤ_[ℓ]) hm0.ne' N hNdet hNtr
    have hfin : Ideal.Quotient.mk p ((D.ρ g).charpoly.coeff 1) = -N.trace := by
      rw [hcharMx g, ← hMx, hmapcoeff Mx, ← hN, hcoeffQ]
    rw [hfin]
    exact hNtrace.neg
  | 2 =>
    have hmonic : (D.ρ g).charpoly.Monic := LinearMap.charpoly_monic _
    have hdeg : (D.ρ g).charpoly.natDegree = 2 := by
      rw [LinearMap.charpoly_natDegree, hfinrank]
    have h1 : (D.ρ g).charpoly.coeff 2 = 1 := by
      have hlead := hmonic.coeff_natDegree
      rwa [hdeg] at hlead
    rw [h1, map_one]
    exact isIntegral_one
  | (j + 3) =>
    have hdeg : (D.ρ g).charpoly.natDegree = 2 := by
      rw [LinearMap.charpoly_natDegree, hfinrank]
    have h0 : (D.ρ g).charpoly.coeff (j + 3) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; omega)
    rw [h0, map_zero]
    exact isIntegral_zero

/-- **Mod-`ℓ` fibre stratum** (PROVEN 2026-07-25 over the trace-form leaf
`isIntegral_charFrobCoeff_quotient_of_isWeaklyUniversal_isTraceGenerated`
just above and the pure commutative algebra
`eq_maximalIdeal_of_isPrime_of_isIntegral_quotient`): in the weakly
universal, trace-generated hardly ramified deformation ring the maximal
ideal is the ONLY prime containing `ℓ` — the mod-`ℓ` fibre of
`Spec D.R` is a single point.

The assembly below is proven: trace generation supplies the dense
subring topologically generated by `ℤ_ℓ` and the `charFrob`
coefficients, the leaf supplies the integrality of those coefficients
modulo `p`, and the glue turns the two into `p = 𝔪`. See the leaf's
docstring for why the cut was made there and what discharging it
requires. -/
theorem eq_maximalIdeal_of_isPrime_of_isWeaklyUniversal_isTraceGenerated
    (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible)
    (D : HardlyRamifiedDeformation hℓOdd ρbar)
    (hw : D.IsWeaklyUniversal) (ht : D.IsTraceGenerated) :
    letI := D.commRing; letI := D.isLocalRing
    ∀ p : Ideal D.R, p.IsPrime → (ℓ : D.R) ∈ p →
      p = IsLocalRing.maximalIdeal D.R := by
  letI := D.commRing; letI := D.topologicalSpace; letI := D.isTopologicalRing
  letI := D.isLocalRing; letI := D.algebra
  haveI := D.isNoetherianRing
  have ht' : (Subring.closure (Set.range (algebraMap ℤ_[ℓ] D.R) ∪
      {x : D.R | ∃ q, ∃ hq : q.Prime, q ≠ 2 ∧ q ≠ ℓ ∧ ∃ n : ℕ,
        x = (D.ρ.charFrob
          hq.toHeightOneSpectrumRingOfIntegersRat).coeff n})).topologicalClosure
      = ⊤ := ht
  intro p hp hℓp
  refine eq_maximalIdeal_of_isPrime_of_isIntegral_quotient D.isAdic D.π D.π_surjective
    ht' hp hℓp ?_
  rintro x ⟨q, hq, hq2, hqℓ, n, rfl⟩
  exact isIntegral_charFrobCoeff_quotient_of_isWeaklyUniversal_isTraceGenerated hℓOdd
    hdim hℓ5 h hirr D hw ht p hp hℓp q hq hq2 hqℓ n

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

/-- **The variable ideal is the kernel of the constant term** (PROVEN
2026-07-25): a multivariate power series in FINITELY many variables
whose constant term vanishes lies in the ideal generated by the
variables, i.e. it can be written `∑ᵢ xᵢ gᵢ`.

Mathlib has no such lemma (`MvPowerSeries.X_dvd_iff` covers divisibility
by ONE variable), and both presentation strata below need it: the
maximal ideal of `Λ[[x₁,…,x_g]]` is `𝔪_Λ + (x₁,…,x_g)`, which is what
turns a kernel element into a linear form modulo `𝔪²`.

Proof: split `f` into the chunks `c i` collecting the monomials whose
LEAST variable of positive exponent is `xᵢ` — a finite decomposition
because `Fin g` is finite and every nonzero monomial has a least such
variable (`Finsupp.support.min'`). Each chunk has all coefficients
supported in `{m | m i ≠ 0}`, hence is divisible by `xᵢ`
(`MvPowerSeries.X_dvd_iff`), and the chunks sum to `f` because the
constant term is zero. -/
theorem mem_span_range_X_of_constantCoeff_eq_zero {Λ : Type*} [CommRing Λ] {g : ℕ}
    {f : MvPowerSeries (Fin g) Λ} (hf : MvPowerSeries.constantCoeff f = 0) :
    f ∈ Ideal.span (Set.range (MvPowerSeries.X : Fin g → MvPowerSeries (Fin g) Λ)) := by
  classical
  -- `c i` collects the monomials of `f` whose least variable of positive
  -- exponent is `x i`; every monomial of `f` occurs in exactly one `c i`.
  set c : Fin g → MvPowerSeries (Fin g) Λ := fun i m =>
    if (∀ j, j < i → m j = 0) ∧ m i ≠ 0 then MvPowerSeries.coeff m f else 0 with hc
  have hcoeff : ∀ (i : Fin g) (m : Fin g →₀ ℕ), MvPowerSeries.coeff m (c i) =
      if (∀ j, j < i → m j = 0) ∧ m i ≠ 0 then MvPowerSeries.coeff m f else 0 :=
    fun _ _ => rfl
  have hdvd : ∀ i, (MvPowerSeries.X i : MvPowerSeries (Fin g) Λ) ∣ c i := by
    intro i
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm
    rw [hcoeff, if_neg]
    rintro ⟨-, h2⟩
    exact h2 hm
  have hsum : f = ∑ i, c i := by
    ext m
    rw [map_sum]
    by_cases hm0 : m = 0
    · subst hm0
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, Finset.sum_eq_zero]
      intro i _
      rw [hcoeff, if_neg]
      rintro ⟨-, h2⟩
      exact h2 rfl
    · have hne : m.support.Nonempty := Finsupp.support_nonempty_iff.mpr hm0
      set i₀ := m.support.min' hne with hi₀
      have hi₀mem : m i₀ ≠ 0 := Finsupp.mem_support_iff.mp (Finset.min'_mem _ hne)
      have hlt : ∀ j, j < i₀ → m j = 0 := by
        intro j hj
        by_contra hj0
        exact absurd (Finset.min'_le _ _ (Finsupp.mem_support_iff.mpr hj0)) (not_le.mpr hj)
      rw [Finset.sum_eq_single i₀]
      · rw [hcoeff, if_pos ⟨hlt, hi₀mem⟩]
      · intro i _ hi
        rw [hcoeff, if_neg]
        rintro ⟨h1, h2⟩
        rcases lt_or_gt_of_ne hi with h | h
        · exact h2 (hlt i h)
        · exact hi₀mem (h1 i₀ h)
      · intro h
        exact absurd (Finset.mem_univ i₀) h
  rw [hsum]
  refine Ideal.sum_mem _ fun i _ => ?_
  obtain ⟨d, hd⟩ := hdvd i
  rw [hd]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- Membership in the maximal ideal of a power series ring over a local
ring is membership of the CONSTANT TERM in the maximal ideal downstairs
(PROVEN 2026-07-25, from `MvPowerSeries.isUnit_iff_constantCoeff`). -/
theorem mem_maximalIdeal_mvPowerSeries_iff {Λ : Type*} [CommRing Λ] [IsLocalRing Λ]
    {σ : Type*} (f : MvPowerSeries σ Λ) :
    f ∈ IsLocalRing.maximalIdeal (MvPowerSeries σ Λ) ↔
      MvPowerSeries.constantCoeff f ∈ IsLocalRing.maximalIdeal Λ := by
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    MvPowerSeries.isUnit_iff_constantCoeff]

/-- **The maximal ideal of a power series ring** (PROVEN 2026-07-25):
`𝔪_{Λ[[x₁,…,x_g]]} = 𝔪_Λ · Λ[[x]] + (x₁, …, x_g)`. At `𝔪_Λ = (ℓ)` this
is the `(ℓ, x₁, …, x_g)` used by the minimality bound below. -/
theorem maximalIdeal_mvPowerSeries_eq {Λ : Type*} [CommRing Λ] [IsLocalRing Λ] {g : ℕ} :
    IsLocalRing.maximalIdeal (MvPowerSeries (Fin g) Λ) =
      (IsLocalRing.maximalIdeal Λ).map
          (MvPowerSeries.C : Λ →+* MvPowerSeries (Fin g) Λ) ⊔
        Ideal.span (Set.range (MvPowerSeries.X : Fin g → MvPowerSeries (Fin g) Λ)) := by
  refine le_antisymm (fun f hf => ?_) (sup_le ?_ ?_)
  · have hcf : MvPowerSeries.constantCoeff f ∈ IsLocalRing.maximalIdeal Λ :=
      (mem_maximalIdeal_mvPowerSeries_iff f).mp hf
    have hsplit : f = MvPowerSeries.C (MvPowerSeries.constantCoeff f) +
        (f - MvPowerSeries.C (MvPowerSeries.constantCoeff f)) := by ring
    rw [hsplit]
    exact Submodule.add_mem_sup (Ideal.mem_map_of_mem _ hcf)
      (mem_span_range_X_of_constantCoeff_eq_zero (by simp))
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    exact (mem_maximalIdeal_mvPowerSeries_iff _).mpr (by simpa using ha)
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact (mem_maximalIdeal_mvPowerSeries_iff _).mpr (by simp)

/-- **Precompleteness transfers along a linear equivalence** (PROVEN
2026-07-25): `IsPrecomplete` is a property of the filtration `I^n • ⊤`,
which a linear equivalence carries across in both directions
(`Submodule.map_smul''` at `⊤`). -/
theorem isPrecomplete_of_linearEquiv {A : Type*} [CommRing A] {M N : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] {I : Ideal A}
    [IsPrecomplete I M] (e : M ≃ₗ[A] N) : IsPrecomplete I N := by
  have hmap : ∀ (n : ℕ) (x y : M), x ≡ y [SMOD (I ^ n • ⊤ : Submodule A M)] →
      e x ≡ e y [SMOD (I ^ n • ⊤ : Submodule A N)] := by
    intro n x y h
    rw [SModEq.sub_mem] at h ⊢
    have hx : e x - e y ∈ (I ^ n • (⊤ : Submodule A M)).map (e : M →ₗ[A] N) := by
      rw [← map_sub]
      exact Submodule.mem_map_of_mem h
    rwa [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr
      e.surjective] at hx
  have hmapsymm : ∀ (n : ℕ) (x y : N), x ≡ y [SMOD (I ^ n • ⊤ : Submodule A N)] →
      e.symm x ≡ e.symm y [SMOD (I ^ n • ⊤ : Submodule A M)] := by
    intro n x y h
    rw [SModEq.sub_mem] at h ⊢
    have hx : e.symm x - e.symm y ∈ (I ^ n • (⊤ : Submodule A N)).map (e.symm : N →ₗ[A] M) := by
      rw [← map_sub]
      exact Submodule.mem_map_of_mem h
    rwa [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr
      e.symm.surjective] at hx
  constructor
  intro f hf
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) (fun n => e.symm (f n))
    fun {m n} hmn => hmapsymm m _ _ (hf hmn)
  refine ⟨e L, fun n => ?_⟩
  have := hmap n _ _ (hL n)
  rwa [e.apply_symm_apply] at this

/-- **Precompleteness passes to finite products** (PROVEN 2026-07-25):
`J • ⊤` in `ι → A` is the coordinatewise `J` (one direction by
`Submodule.smul_induction_on`, the other by writing `x` as the finite
sum of its `Pi.single` components), so a Cauchy sequence is Cauchy in
each of the finitely many coordinates and the limits assemble. -/
theorem isPrecomplete_pi {A : Type*} [CommRing A] {ι : Type*} [Fintype ι] {I : Ideal A}
    [IsPrecomplete I A] : IsPrecomplete I (ι → A) := by
  classical
  have hmem : ∀ (J : Ideal A) (x : ι → A),
      x ∈ J • (⊤ : Submodule A (ι → A)) ↔ ∀ i, x i ∈ J := by
    intro J x
    constructor
    · intro hx
      refine Submodule.smul_induction_on hx (fun a ha y _ i => ?_) (fun p q hp hq i => ?_)
      · simp only [Pi.smul_apply, smul_eq_mul]
        exact Ideal.mul_mem_right _ _ ha
      · exact Submodule.add_mem _ (hp i) (hq i)
    · intro h
      have hsum : x = ∑ i, Pi.single i (x i) := by
        ext j
        simp
      rw [hsum]
      refine Submodule.sum_mem _ fun i _ => ?_
      have hsingle : (Pi.single i (x i) : ι → A) = x i • (Pi.single i 1 : ι → A) := by
        ext j
        by_cases hij : j = i <;> simp [hij]
      rw [hsingle]
      exact Submodule.smul_mem_smul (h i) Submodule.mem_top
  have hself : ∀ (J : Ideal A) (a : A), a ∈ J • (⊤ : Submodule A A) ↔ a ∈ J := by
    intro J a
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  constructor
  intro f hf
  have hco : ∀ i, ∃ L : A, ∀ n, f n i ≡ L [SMOD (I ^ n • ⊤ : Submodule A A)] := by
    intro i
    refine IsPrecomplete.prec' (I := I) (fun n => f n i) fun {m n} hmn => ?_
    have h := hf hmn
    rw [SModEq.sub_mem] at h ⊢
    rw [hself]
    have := (hmem _ _).mp h i
    simpa using this
  choose L hL using hco
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem, hmem]
  intro i
  have := hL i n
  rw [SModEq.sub_mem, hself] at this
  simpa using this

/-- **A module-finite FREE module over an `I`-adically precomplete ring
is `I`-adically precomplete** (PROVEN 2026-07-25): choose a basis, which
is finite by module-finiteness, and transport `isPrecomplete_pi` along
`Basis.equivFun`.

Mathlib has no such statement — its `IsPrecomplete` producers are the
trivial ideals, Artinian local rings, `PadicInt`, `WittVector`, the
`X`-adic (Mv)PowerSeries rings, and adic completions themselves — so
this is the missing bridge from "`ℤ_ℓ` is complete" to "a coefficient
ring finite over `ℤ_ℓ` is complete". -/
theorem isPrecomplete_of_free_finite {A : Type*} [CommRing A] {M : Type*}
    [AddCommGroup M] [Module A M] [Module.Free A M] [Module.Finite A M] {I : Ideal A}
    [IsPrecomplete I A] : IsPrecomplete I M := by
  classical
  haveI : IsPrecomplete I (Module.Free.ChooseBasisIndex A M → A) := isPrecomplete_pi
  exact isPrecomplete_of_linearEquiv (Module.Free.chooseBasis A M).equivFun.symm

omit [Field k] [Finite k] [Algebra ℤ_[ℓ] k] [TopologicalSpace k]
  [DiscreteTopology k] in
/-- **`(ℓ)`-adic precompleteness of a finite free `ℤ_ℓ`-algebra** (PROVEN
2026-07-25): `ℤ_ℓ` is `𝔪`-adically complete (mathlib), `𝔪 = (ℓ)`
(`PadicInt.maximalIdeal_eq_span_p`), so `isPrecomplete_of_free_finite`
makes `A` precomplete as a `ℤ_ℓ`-MODULE, and
`IsPrecomplete.map_algebraMap_iff` converts that into precompleteness for
the ideal `(ℓ)` of `A` itself.

This is what discharges the `IsPrecomplete` clause of
`exists_coefficientRing_ringHom` for the `AdjoinRoot` coefficient ring:
`AdjoinRoot G` is free over `ℤ_ℓ` on the power basis of the monic `G`. -/
theorem isPrecomplete_span_natCast_of_free_finite (A : Type*) [CommRing A] [Algebra ℤ_[ℓ] A]
    [Module.Free ℤ_[ℓ] A] [Module.Finite ℤ_[ℓ] A] :
    IsPrecomplete (Ideal.span {(ℓ : A)}) A := by
  haveI : IsPrecomplete (IsLocalRing.maximalIdeal ℤ_[ℓ]) A := isPrecomplete_of_free_finite
  have hmap : (IsLocalRing.maximalIdeal ℤ_[ℓ]).map (algebraMap ℤ_[ℓ] A)
      = Ideal.span {(ℓ : A)} := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span]
    congr 1
    simp
  rw [← hmap]
  exact IsPrecomplete.map_algebraMap_iff.mpr inferInstance

omit [TopologicalSpace k] [DiscreteTopology k] in
/-- **The residue field has characteristic `ℓ`** (PROVEN 2026-07-25):
`natCast_self_eq_zero` says `(ℓ : k) = 0`, so `ringChar k` divides the
prime `ℓ` and is not `1`. Packaged as the `CharP` instance, which is
what the `ZMod ℓ`-algebra structure on `k` needs. -/
lemma charP_residue_field : CharP k ℓ := by
  haveI := ringChar.charP k
  have hd : ringChar k ∣ ℓ := ringChar.dvd (natCast_self_eq_zero (ℓ := ℓ) (k := k))
  have h1 : ringChar k ≠ 1 := CharP.char_ne_one k (ringChar k)
  have h : ringChar k = ℓ := ((Fact.out : ℓ.Prime).eq_one_or_self_of_dvd _ hd).resolve_left h1
  exact h ▸ ringChar.charP k

omit [Finite k] [Algebra ℤ_[ℓ] k] [TopologicalSpace k] [DiscreteTopology k] in
/-- **Surjectivity from a multiplicative generator in the range**
(PROVEN 2026-07-25): a ring map into `k` whose image contains an element
all of whose powers exhaust `k \ {0}` is onto. This is the substitute for
"the image is a subring containing the prime field and `α`, hence is
`𝔽_ℓ[α] = k`": going through the CYCLIC group `kˣ` avoids having to build
the prime-field subalgebra structure on the range. -/
lemma surjective_of_generator_mem_range {A : Type*} [CommRing A] (ρ : A →+* k)
    {α : k} (hα : ∃ a : A, ρ a = α)
    (hgen : ∀ x : k, x ≠ 0 → ∃ n : ℕ, α ^ n = x) :
    Function.Surjective ρ := by
  obtain ⟨a, ha⟩ := hα
  intro x
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  · obtain ⟨n, hn⟩ := hgen x hx
    exact ⟨a ^ n, by rw [map_pow, ha, hn]⟩

omit [Algebra ℤ_[ℓ] k] [TopologicalSpace k] [DiscreteTopology k] in
/-- **A finite field has a multiplicative generator** (PROVEN
2026-07-25): a generator of the cyclic group `kˣ`, read as an element of
`k` whose natural-number powers exhaust `k \ {0}`. -/
lemma exists_pow_generator (k : Type u) [Field k] [Finite k] :
    ∃ α : k, ∀ x : k, x ≠ 0 → ∃ n : ℕ, α ^ n = x := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := kˣ)
  refine ⟨(g : k), fun x hx => ?_⟩
  have hmem : Units.mk0 x hx ∈ Submonoid.powers g :=
    mem_powers_iff_mem_zpowers.mpr (hg (Units.mk0 x hx))
  obtain ⟨n, hn⟩ := hmem
  exact ⟨n, by simpa using congrArg (Units.val) hn⟩

omit [TopologicalSpace k] [DiscreteTopology k] in
/-- **`ℤ_[ℓ] →+* k` is unique** (PROVEN 2026-07-25): `ℓ` dies in `k`, so
every ring map out of `ℤ_[ℓ]` kills `ker (PadicInt.toZMod) = (ℓ)` and is
therefore determined by the composite through the prime field. Written
without quotients: each `x : ℤ_[ℓ]` differs from the natural number
`(toZMod x).val` by a multiple of `ℓ`. This is what identifies
`algebraMap ℤ_[ℓ] k` with `π ∘ algebraMap ℤ_[ℓ] R`, so that the
polynomial `G` below can be evaluated over `R` and over `k`
compatibly. -/
lemma ringHom_padicInt_ext (f₁ f₂ : ℤ_[ℓ] →+* k) : f₁ = f₂ := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have key : ∀ (f : ℤ_[ℓ] →+* k) (x : ℤ_[ℓ]),
      f x = (((PadicInt.toZMod (p := ℓ) x).val : ℕ) : k) := by
    intro f x
    set n : ℕ := (PadicInt.toZMod (p := ℓ) x).val with hn
    have hxn : PadicInt.toZMod (p := ℓ) ((n : ℕ) : ℤ_[ℓ]) = PadicInt.toZMod (p := ℓ) x := by
      rw [map_natCast, hn, ZMod.natCast_val, ZMod.cast_id]
    have hmem : x - (n : ℤ_[ℓ]) ∈ RingHom.ker (PadicInt.toZMod (p := ℓ)) := by
      rw [RingHom.mem_ker, map_sub, hxn, sub_self]
    rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
      Ideal.mem_span_singleton] at hmem
    obtain ⟨y, hy⟩ := hmem
    have hx : x = (n : ℤ_[ℓ]) + (ℓ : ℤ_[ℓ]) * y := by linear_combination hy
    rw [hx, map_add, map_mul, map_natCast, map_natCast,
      natCast_self_eq_zero (ℓ := ℓ) (k := k), zero_mul, add_zero]
  exact RingHom.ext fun x => (key f₁ x).trans (key f₂ x).symm

omit [Field k] [Finite k] [Algebra ℤ_[ℓ] k] in
/-- **`ℓ` lies in the Jacobson radical of any module-finite
`ℤ_ℓ`-algebra** (PROVEN 2026-07-25 — the going-up half of "the
coefficient ring is local"): if `A` is module-finite over `ℤ_[ℓ]` then it
is integral over it, so the contraction of a maximal ideal of `A` is
maximal in `ℤ_[ℓ]`, hence equals `(ℓ)` because `ℤ_[ℓ]` is local. So `ℓ`
lies in EVERY maximal ideal of `A`. This replaces the completeness /
determinant arguments usually used to see that `1 + ℓ y` is a unit. -/
lemma natCast_mem_jacobson {A : Type*} [CommRing A] [Algebra ℤ_[ℓ] A]
    [Module.Finite ℤ_[ℓ] A] : ((ℓ : ℕ) : A) ∈ Ideal.jacobson (⊥ : Ideal A) := by
  haveI : Algebra.IsIntegral ℤ_[ℓ] A := Algebra.IsIntegral.of_finite ℤ_[ℓ] A
  rw [Ideal.jacobson]
  refine Ideal.mem_sInf.mpr ?_
  rintro J ⟨-, hJ⟩
  haveI := hJ
  have hcomap : (J.comap (algebraMap ℤ_[ℓ] A)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := ℤ_[ℓ]) J
  have heq : J.comap (algebraMap ℤ_[ℓ] A) = IsLocalRing.maximalIdeal ℤ_[ℓ] :=
    IsLocalRing.eq_maximalIdeal hcomap
  have hℓ : ((ℓ : ℕ) : ℤ_[ℓ]) ∈ J.comap (algebraMap ℤ_[ℓ] A) := by
    rw [heq, PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  rw [Ideal.mem_comap, map_natCast] at hℓ
  exact hℓ

omit [Fact ℓ.Prime] [Field k] [Finite k] [Algebra ℤ_[ℓ] k] in
/-- **A maximal principal ideal inside the Jacobson radical makes the ring
local** (PROVEN 2026-07-25): every maximal ideal contains the Jacobson
radical, hence contains `x`, hence contains the MAXIMAL ideal `(x)` and
therefore equals it. -/
lemma isLocalRing_of_span_isMaximal {A : Type*} [CommRing A] {x : A}
    (hmax : (Ideal.span {x}).IsMaximal) (hjac : x ∈ Ideal.jacobson (⊥ : Ideal A)) :
    IsLocalRing A := by
  refine IsLocalRing.of_unique_max_ideal ⟨Ideal.span {x}, hmax, fun J hJ => ?_⟩
  rw [Ideal.jacobson] at hjac
  have hxJ : x ∈ J := Ideal.mem_sInf.mp hjac ⟨bot_le, hJ⟩
  exact (hmax.eq_of_le hJ.ne_top (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hxJ))).symm

omit [TopologicalSpace k] [DiscreteTopology k] in
/-- **The unramified extension of `ℤ_ℓ` with residue field `k`, as a
polynomial datum** (PROVEN 2026-07-25 — the arithmetic heart of the
coefficient-ring leaf): there is a MONIC `G : ℤ_[ℓ][X]`, irreducible,
together with a multiplicative generator `α` of `k` and the (unique) map
`φ : ℤ_[ℓ] →+* k`, such that `α` is a SIMPLE root of `G` over `k` and
every `q : ℤ_[ℓ][X]` vanishing at `α` lies in `(G, ℓ)`.

Construction: `α` generates the cyclic group `kˣ`, so `k = 𝔽_ℓ[α]`; let
`g = minpoly (ZMod ℓ) α`, monic and irreducible, and SEPARABLE because
`ZMod ℓ` is a perfect field — which is exactly `g'(α) ≠ 0`. Lift `g`
coefficientwise along the surjection `PadicInt.toZMod` to a monic `G` of
the same degree (`Polynomial.lifts_and_natDegree_eq_and_monic`);
`Polynomial.Monic.irreducible_of_irreducible_map` then makes `G`
irreducible. The last clause is `minpoly.dvd` upstairs: `q` vanishing at
`α` means `g ∣ q mod ℓ`, so `q - G·H` reduces to `0`, i.e. all of its
coefficients lie in `ker toZMod = (ℓ)` (`Ideal.mem_map_C_iff`).

This is the mathematical content that replaces the Cohen structure
theorem here: the residue field is FINITE, hence monogenic, so its
unramified lift is `ℤ_[ℓ][X]/(G)` and no Witt-vector theory is needed.
Reference: Serre, *Local Fields* II §5 (unramified extensions are
monogenic, obtained by lifting the residue extension). -/
theorem exists_monic_generator_poly :
    ∃ (G : ℤ_[ℓ][X]) (α : k) (φ : ℤ_[ℓ] →+* k), G.Monic ∧ Irreducible G ∧
      (∀ x : k, x ≠ 0 → ∃ n : ℕ, α ^ n = x) ∧
      G.eval₂ φ α = 0 ∧
      (derivative G).eval₂ φ α ≠ 0 ∧
      (∀ q : ℤ_[ℓ][X], q.eval₂ φ α = 0 →
        ∃ H S : ℤ_[ℓ][X], q = G * H + Polynomial.C ((ℓ : ℕ) : ℤ_[ℓ]) * S) := by
  classical
  haveI : CharP k ℓ := charP_residue_field
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  letI : Algebra (ZMod ℓ) k := ZMod.algebra k ℓ
  obtain ⟨α, hgen⟩ := exists_pow_generator k
  haveI : Module.Finite (ZMod ℓ) k := Module.Finite.of_finite
  haveI : Algebra.IsIntegral (ZMod ℓ) k := Algebra.IsIntegral.of_finite _ _
  have hint : IsIntegral (ZMod ℓ) α := Algebra.IsIntegral.isIntegral α
  set g : (ZMod ℓ)[X] := minpoly (ZMod ℓ) α with hgdef
  have hgm : g.Monic := minpoly.monic hint
  have hgirr : Irreducible g := minpoly.irreducible hint
  have hsurj : Function.Surjective (PadicInt.toZMod (p := ℓ)) := fun a =>
    ⟨((a.val : ℕ) : ℤ_[ℓ]), by rw [map_natCast, ZMod.natCast_val, ZMod.cast_id]⟩
  obtain ⟨G, hGmap, -, hGm⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic
      (Polynomial.mem_lifts_of_surjective hsurj g) hgm
  set φ : ℤ_[ℓ] →+* k := (algebraMap (ZMod ℓ) k).comp (PadicInt.toZMod (p := ℓ)) with hφdef
  have hmap : ∀ q : ℤ_[ℓ][X],
      q.eval₂ φ α = Polynomial.aeval α (q.map (PadicInt.toZMod (p := ℓ))) := by
    intro q
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hφdef]
  refine ⟨G, α, φ, hGm, ?_, hgen, ?_, ?_, ?_⟩
  · exact Polynomial.Monic.irreducible_of_irreducible_map (PadicInt.toZMod (p := ℓ)) G hGm
      (by rw [hGmap]; exact hgirr)
  · rw [hmap, hGmap]
    exact minpoly.aeval _ _
  · rw [hmap, ← Polynomial.derivative_map, hGmap]
    haveI : PerfectField (ZMod ℓ) := inferInstance
    have hgaeval : Polynomial.aeval α g = 0 := minpoly.aeval _ _
    have hsep : g.Separable := PerfectField.separable_of_irreducible hgirr
    obtain ⟨v, w, hvw⟩ := hsep
    intro hzero
    have hone := congrArg (Polynomial.aeval α) hvw
    rw [map_add, map_mul, map_mul, map_one, hgaeval, hzero, mul_zero, mul_zero,
      add_zero] at hone
    exact zero_ne_one hone
  · intro q hq
    have hq' : Polynomial.aeval α (q.map (PadicInt.toZMod (p := ℓ))) = 0 := by
      rw [← hmap]; exact hq
    obtain ⟨h, hh⟩ := minpoly.dvd (ZMod ℓ) α hq'
    obtain ⟨H, hH⟩ :=
      (Polynomial.mem_lifts h).mp (Polynomial.mem_lifts_of_surjective hsurj h)
    have hz : (q - G * H).map (PadicInt.toZMod (p := ℓ)) = 0 := by
      rw [Polynomial.map_sub, Polynomial.map_mul, hGmap, hH, ← hh, sub_self]
    have hc : ∀ n, (q - G * H).coeff n ∈ Ideal.span {((ℓ : ℕ) : ℤ_[ℓ])} := by
      intro n
      have hcn := congrArg (fun p : (ZMod ℓ)[X] => p.coeff n) hz
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hcn
      rw [← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod, RingHom.mem_ker]
      exact hcn
    have hmem : (q - G * H) ∈
        Ideal.map (Polynomial.C : ℤ_[ℓ] →+* ℤ_[ℓ][X]) (Ideal.span {((ℓ : ℕ) : ℤ_[ℓ])}) :=
      Ideal.mem_map_C_iff.mpr hc
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at hmem
    obtain ⟨S, hS⟩ := hmem
    exact ⟨H, S, by linear_combination hS⟩

omit [TopologicalSpace k] [DiscreteTopology k] in
/-- **The residue map of the coefficient ring has kernel `(ℓ)`** (PROVEN
2026-07-25): `AdjoinRoot.lift φ α` sends `root G` to `α`, and its kernel
is exactly `(ℓ)` — the inclusion `⊇` is `(ℓ : k) = 0`, and `⊆` is the
membership `q ∈ (G, ℓ)` supplied by `exists_monic_generator_poly`,
since `G` itself dies in `AdjoinRoot G`. Being the kernel of a surjection
onto a FIELD, `(ℓ)` is therefore maximal. -/
theorem exists_adjoinRoot_residue {G : ℤ_[ℓ][X]} {α : k} {φ : ℤ_[ℓ] →+* k}
    (hGeval : G.eval₂ φ α = 0)
    (hdiv : ∀ q : ℤ_[ℓ][X], q.eval₂ φ α = 0 →
      ∃ H S : ℤ_[ℓ][X], q = G * H + Polynomial.C ((ℓ : ℕ) : ℤ_[ℓ]) * S) :
    ∃ ψ : AdjoinRoot G →+* k, ψ (AdjoinRoot.root G) = α ∧
      RingHom.ker ψ = Ideal.span {((ℓ : ℕ) : AdjoinRoot G)} := by
  have hCℓ : AdjoinRoot.mk G (Polynomial.C ((ℓ : ℕ) : ℤ_[ℓ])) = ((ℓ : ℕ) : AdjoinRoot G) := by
    rw [Polynomial.C_eq_natCast]
    exact map_natCast (AdjoinRoot.mk G) ℓ
  refine ⟨AdjoinRoot.lift φ α hGeval, AdjoinRoot.lift_root _, le_antisymm ?_ ?_⟩
  · intro x hx
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective x
    rw [RingHom.mem_ker, AdjoinRoot.lift_mk] at hx
    obtain ⟨H, S, hHS⟩ := hdiv q hx
    rw [Ideal.mem_span_singleton]
    refine ⟨AdjoinRoot.mk G S, ?_⟩
    rw [hHS, map_add, map_mul, map_mul, AdjoinRoot.mk_self, zero_mul, zero_add, hCℓ]
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_natCast]
    exact natCast_self_eq_zero

omit [TopologicalSpace k] [DiscreteTopology k] in
/-- **Cohen coefficient-ring leaf** (PROVEN 2026-07-25 — pure commutative
algebra, the first of the four strata into which the minimal
presentation of `exists_minimal_mvPowerSeries_presentation` was
DECOMPOSED the same day): a complete Noetherian local `ℤ_ℓ`-algebra `R`
with residue field `k` (it maps ONTO `k`) receives a compatible
COEFFICIENT RING `Λ` — an unramified complete local domain,
module-finite over `ℤ_ℓ`, with maximal ideal `(ℓ)`, mapping to `R` by a
`ℤ_ℓ`-algebra map `ι` that is onto the residue field.

CLAUSE ADDED 2026-07-25, after the proof below was written:
`IsPrecomplete (𝔪_Λ) Λ`. The surjectivity stratum
`surjective_of_mvPowerSeries_ringHom` is FALSE without it (see its
docstring for the counterexample `Λ = ℤ_(ℓ)`, `R = ℤ_ℓ`), and the
`AdjoinRoot` construction below delivers it with no extra arithmetic:
`Λ` is FREE over `ℤ_ℓ` on the power basis of the monic `G`, so
`isPrecomplete_span_natCast_of_free_finite` applies. (The clause was
originally justified through `WittVector.isAdicCompleteIdealSpanP`; the
proof does not go through Witt vectors, and does not need to — freeness
over `ℤ_ℓ` is what completeness actually rests on in either route.)

CAVEAT retained from the pre-proof docstring, still live: the CLAUSES do
not by themselves pin `Λ ≅ W(k)` — a finite field satisfies every one of
them (local Noetherian domain, module-finite over `ℤ_ℓ`, and
`𝔪_Λ = (ℓ) = ⊥` when `ℓ = 0` in `Λ`), so `dim Λ` is not pinned to `1` by
the clause set alone. Downstream that unit of dimension is load-bearing
and is carried explicitly by the relation-count leaf
`exists_relations_lt_le_smul_of_minimal_mvPowerSeries_presentation`,
which concludes `(ℓ : Λ) ≠ 0`. The construction below DOES give it (the
`AdjoinRoot` lift is `ℓ`-torsion-free), so a future simplification may
move `(ℓ : Λ) ≠ 0` into this conclusion and let the arithmetic leaf drop
it.

Classically `Λ = W(k)`, the Witt vectors of the finite field `k`, and the
clauses pin `Λ` up to isomorphism. **The proof does NOT go through Witt
vectors**, and in particular does not need the two mathlib gaps an
earlier version of this docstring named as blockers
(`Module.Finite ℤ_[ℓ] (𝕎 k)` and `maximalIdeal (𝕎 k) = (ℓ)`, both still
absent at this pin): since `k` is FINITE it is monogenic over its prime
field, so its unramified lift can be written down as
`Λ₀ := AdjoinRoot G` for the monic `ℤ_ℓ`-lift `G` of the minimal
polynomial of a generator of `kˣ` produced by
`exists_monic_generator_poly`. Then

* `Λ₀` is a DOMAIN because `G` is irreducible (reduction criterion) hence
  prime in the UFD `ℤ_[ℓ][X]` (`AdjoinRoot.isDomain_of_prime`);
* `Λ₀` is MODULE-FINITE and NOETHERIAN over `ℤ_[ℓ]` by the power basis
  `1, root G, …` of a monic quotient (`Monic.finite_adjoinRoot`);
* `(ℓ)` is MAXIMAL in `Λ₀` as the kernel of the surjection onto the field
  `k` computed in `exists_adjoinRoot_residue`, and `Λ₀` is LOCAL with
  `𝔪 = (ℓ)` by GOING UP (`natCast_mem_jacobson`) — no completeness,
  Nakayama or determinant argument is used;
* the lift `ι` is HENSEL's lemma in `R`: `R` is `𝔪`-adically complete,
  hence Henselian at `𝔪` (`IsAdicComplete.henselianRing`), and `α` is a
  SIMPLE root of `G` over `k = R/𝔪` (separability of the residue minimal
  polynomial), so it lifts to a root `a ∈ R` of `G`; then
  `ι := AdjoinRoot.lift (algebraMap ℤ_[ℓ] R) a`. This is the concrete
  form of "`W(k)/ℤ_ℓ` is formally étale, so the residue map lifts".
* `π ∘ ι` is ONTO because its image contains `α`, a generator of the
  cyclic group `kˣ` (`surjective_of_generator_mem_range`).

The only friction is UNIVERSES: `AdjoinRoot G` lives in `Type 0` while
the statement quantifies `Λ` over `k`'s universe, so the conclusion is
carried across by `Shrink` — `Shrink.algEquiv` transports the domain,
Noetherian and module-finiteness instances, while locality and the
maximal ideal are re-derived downstairs from the transported residue map
rather than transported.

References: Serre, *Local Fields*, II §5 (unramified extensions of a
complete discretely valued field with perfect residue field are
monogenic); de Smit–Lenstra, *Explicit construction of universal
deformation rings*, §2 (App. to Cornell–Silverman–Stevens); Matsumura,
*Commutative Ring Theory*, §29 (the Cohen structure theorem this
replaces). -/
theorem exists_coefficientRing_ringHom {R : Type*} [CommRing R]
    [IsLocalRing R] [Algebra ℤ_[ℓ] R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (π : R →+* k) (hπsurj : Function.Surjective π) :
    ∃ (Λ : Type u) (_ : CommRing Λ) (_ : IsDomain Λ) (_ : IsLocalRing Λ)
      (_ : IsNoetherianRing Λ) (_ : Algebra ℤ_[ℓ] Λ)
      (_ : Module.Finite ℤ_[ℓ] Λ)
      (_ : IsPrecomplete (IsLocalRing.maximalIdeal Λ) Λ),
      IsLocalRing.maximalIdeal Λ = Ideal.span {(ℓ : Λ)} ∧
      ∃ ι : Λ →+* R,
        ι.comp (algebraMap ℤ_[ℓ] Λ) = algebraMap ℤ_[ℓ] R ∧
        Function.Surjective (π.comp ι) := by
  classical
  obtain ⟨G, α, φ, hGm, hGirr, hgen, hGeval, hGderiv, hdiv⟩ :=
    exists_monic_generator_poly (ℓ := ℓ) (k := k)
  have hφ : φ = π.comp (algebraMap ℤ_[ℓ] R) := ringHom_padicInt_ext _ _
  haveI : Module.Finite ℤ_[ℓ] (AdjoinRoot G) := hGm.finite_adjoinRoot
  haveI : IsDomain (AdjoinRoot G) :=
    AdjoinRoot.isDomain_of_prime (UniqueFactorizationMonoid.irreducible_iff_prime.mp hGirr)
  obtain ⟨ψ, hψroot, hψker⟩ := exists_adjoinRoot_residue hGeval hdiv
  -- Hensel's lemma in `R`: lift `α` to a root of `G`
  obtain ⟨a₀, ha₀⟩ := hπsurj α
  have hkerπ : RingHom.ker π = IsLocalRing.maximalIdeal R :=
    IsLocalRing.ker_eq_maximalIdeal π hπsurj
  set F : R[X] := G.map (algebraMap ℤ_[ℓ] R) with hFdef
  have hFm : F.Monic := hGm.map _
  have hFeval : F.eval a₀ ∈ IsLocalRing.maximalIdeal R := by
    have h1 : π (F.eval a₀) = G.eval₂ φ α := by
      rw [hFdef, Polynomial.eval_map, Polynomial.hom_eval₂, ha₀, ← hφ]
    rw [← hkerπ, RingHom.mem_ker, h1]
    exact hGeval
  have hFderiv : IsUnit (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)
      ((derivative F).eval a₀)) := by
    refine IsUnit.map _ (IsLocalRing.notMem_maximalIdeal.mp ?_)
    rw [← hkerπ, RingHom.mem_ker]
    intro hzero
    have h2 : π ((derivative F).eval a₀) = (derivative G).eval₂ φ α := by
      rw [hFdef, Polynomial.derivative_map, Polynomial.eval_map, Polynomial.hom_eval₂, ha₀, ← hφ]
    exact hGderiv (h2 ▸ hzero)
  obtain ⟨a, haroot, hamod⟩ :=
    HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal R) F hFm a₀ hFeval hFderiv
  have hπa : π a = α := by
    have hz : π (a - a₀) = 0 := by rw [← RingHom.mem_ker, hkerπ]; exact hamod
    rw [map_sub, sub_eq_zero] at hz
    rw [hz, ha₀]
  have hroot₂ : G.eval₂ (algebraMap ℤ_[ℓ] R) a = 0 := by
    rw [← Polynomial.eval_map, ← hFdef]; exact haroot
  set ι₀ : AdjoinRoot G →+* R := AdjoinRoot.lift (algebraMap ℤ_[ℓ] R) a hroot₂ with hι₀
  -- move the coefficient ring into `k`'s universe
  haveI : Small.{u} (AdjoinRoot G) := inferInstance
  let e : Shrink.{u} (AdjoinRoot G) ≃ₐ[ℤ_[ℓ]] AdjoinRoot G := Shrink.algEquiv ℤ_[ℓ] (AdjoinRoot G)
  let E : Shrink.{u} (AdjoinRoot G) →+* AdjoinRoot G := e.toRingEquiv.toRingHom
  haveI : IsDomain (Shrink.{u} (AdjoinRoot G)) :=
    Function.Injective.isDomain E e.injective
  haveI : IsNoetherianRing (Shrink.{u} (AdjoinRoot G)) :=
    isNoetherianRing_of_ringEquiv (AdjoinRoot G) e.symm.toRingEquiv
  haveI : Module.Finite ℤ_[ℓ] (Shrink.{u} (AdjoinRoot G)) :=
    Module.Finite.equiv e.symm.toLinearEquiv
  have hkerψ' : RingHom.ker (ψ.comp E)
      = Ideal.span {((ℓ : ℕ) : Shrink.{u} (AdjoinRoot G))} := by
    ext x
    rw [RingHom.mem_ker, RingHom.comp_apply, ← RingHom.mem_ker, hψker,
      Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨e.symm c, e.injective ?_⟩
      rw [map_mul, map_natCast, AlgEquiv.apply_symm_apply]
      exact hc
    · rintro ⟨c, hc⟩
      exact ⟨e c, by rw [show E x = e x from rfl, hc, map_mul, map_natCast]⟩
  have hψ'surj : Function.Surjective (ψ.comp E) := by
    refine surjective_of_generator_mem_range _ ⟨e.symm (AdjoinRoot.root G), ?_⟩ hgen
    show ψ (e (e.symm (AdjoinRoot.root G))) = α
    rw [AlgEquiv.apply_symm_apply]
    exact hψroot
  have hmaxΛ : (Ideal.span {((ℓ : ℕ) : Shrink.{u} (AdjoinRoot G))}).IsMaximal :=
    hkerψ' ▸ RingHom.ker_isMaximal_of_surjective (ψ.comp E) hψ'surj
  haveI : IsLocalRing (Shrink.{u} (AdjoinRoot G)) :=
    isLocalRing_of_span_isMaximal hmaxΛ natCast_mem_jacobson
  -- `(ℓ)`-adic precompleteness: `AdjoinRoot G` is FREE over `ℤ_ℓ` on the
  -- power basis of the monic `G`, and `ℤ_ℓ` is `(ℓ)`-adically complete
  haveI : Module.Free ℤ_[ℓ] (AdjoinRoot G) :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' hGm).basis
  haveI : Module.Free ℤ_[ℓ] (Shrink.{u} (AdjoinRoot G)) :=
    Module.Free.of_equiv e.symm.toLinearEquiv
  haveI : IsPrecomplete (IsLocalRing.maximalIdeal (Shrink.{u} (AdjoinRoot G)))
      (Shrink.{u} (AdjoinRoot G)) := by
    rw [← IsLocalRing.eq_maximalIdeal hmaxΛ]
    exact isPrecomplete_span_natCast_of_free_finite _
  refine ⟨Shrink.{u} (AdjoinRoot G), inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance,
    (IsLocalRing.eq_maximalIdeal hmaxΛ).symm, ι₀.comp E, ?_, ?_⟩
  · refine RingHom.ext fun x => ?_
    show ι₀ (e (algebraMap ℤ_[ℓ] (Shrink.{u} (AdjoinRoot G)) x)) = algebraMap ℤ_[ℓ] R x
    rw [AlgEquiv.commutes, AdjoinRoot.algebraMap_eq, hι₀, AdjoinRoot.lift_of]
  · refine surjective_of_generator_mem_range _ ⟨e.symm (AdjoinRoot.root G), ?_⟩ hgen
    show π (ι₀ (e (e.symm (AdjoinRoot.root G)))) = α
    rw [AlgEquiv.apply_symm_apply, hι₀, AdjoinRoot.lift_root, hπa]

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

omit [Fact (Nat.Prime ℓ)] [Finite k] [Algebra ℤ_[ℓ] k] [TopologicalSpace k]
  [DiscreteTopology k] in
/-- **Surjectivity stratum of the de Smit–Lenstra presentation** (PROVEN
2026-07-25 — pure commutative algebra, the third stratum of the
same-day decomposition of `exists_minimal_mvPowerSeries_presentation`):
the substitution map `φ : Λ[[x₁, …, x_g]] → R` of
`exists_mvPowerSeries_ringHom_of_mem_maximalIdeal` is SURJECTIVE as
soon as `Λ` covers the residue field (`π ∘ ι` onto) and the `tᵢ`
generate `𝔪_R` modulo `𝔪_R² + ℓR`.

**HYPOTHESIS ADDED 2026-07-25: `Λ` must be `𝔪_Λ`-adically precomplete,
because without it the statement is FALSE.** Counterexample at `g = 0`:
`Λ = ℤ_(ℓ)` (the localisation of `ℤ` at `ℓ`, local with `𝔪 = (ℓ)`),
`R = ℤ_ℓ`, `k = 𝔽_ℓ`, `t` the empty family — every hypothesis holds and
`φ` is the inclusion `ℤ_(ℓ) ↪ ℤ_ℓ`, which is not onto. Completeness of
the coefficient ring is what makes the successive approximation
converge, and it is free at the point of use: the coefficient-ring leaf
`exists_coefficientRing_ringHom` now hands out `Λ = W(k)` together with
its `IsAdicComplete`, which mathlib proves
(`WittVector.isAdicCompleteIdealSpanP`).

Proof, in two applications of mathlib's complete-Nakayama surjectivity
criterion `surjective_of_mk_map_comp_surjective` — a map out of an
`I`-adically precomplete ring onto an `I·S`-adically Hausdorff ring is
onto as soon as it is onto modulo `I·S`:

* in the VARIABLE direction, with `I = (x₁, …, x_g)`, precompleteness is
  mathlib's `IsAdicComplete (span (range X)) (MvPowerSeries σ Λ)` for
  finite `σ`, and `I·R = (t₁, …, t_g) =: T` is Hausdorff because `R` is
  Noetherian local (`IsHausdorff.of_isLocalRing`); so it suffices that
  `φ` be onto `R ⧸ T`;
* in the `ℓ` direction, with `I = 𝔪_Λ = (ℓ)`, applied to
  `Λ → R ⧸ T`: this is where the added precompleteness of `Λ` is used,
  and it suffices that `Λ` be onto `(R ⧸ T) ⧸ (ℓ)`.

The last surjectivity is residue-field surjectivity plus NAKAYAMA:
`hspan` says `𝔪_R = T + 𝔪_R² + ℓR`, so
`Submodule.le_of_le_smul_of_le_jacobson_bot` (over the Noetherian `𝔪_R`,
contained in the Jacobson radical) upgrades it to `𝔪_R = T + ℓR` on the
nose; given `r ∈ R`, residue surjectivity of `π ∘ ι` supplies `a ∈ Λ`
with `r − ι a ∈ ker π = 𝔪_R = T + ℓR`, which is exactly the required
congruence. -/
theorem surjective_of_mvPowerSeries_ringHom {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    {Λ : Type*} [CommRing Λ] [IsLocalRing Λ]
    [IsPrecomplete (IsLocalRing.maximalIdeal Λ) Λ]
    (hΛℓ : IsLocalRing.maximalIdeal Λ = Ideal.span {(ℓ : Λ)})
    (π : R →+* k) (ι : Λ →+* R) (hι : Function.Surjective (π.comp ι))
    {g : ℕ} (t : Fin g → R)
    (hspan : IsLocalRing.maximalIdeal R = Ideal.span (Set.range t) ⊔
      (IsLocalRing.maximalIdeal R ^ 2 ⊔ Ideal.span {(ℓ : R)}))
    (φ : MvPowerSeries (Fin g) Λ →+* R)
    (hφC : φ.comp (MvPowerSeries.C : Λ →+* MvPowerSeries (Fin g) Λ) = ι)
    (hφX : ∀ i, φ (MvPowerSeries.X i) = t i) :
    Function.Surjective φ := by
  classical
  have hπsurj : Function.Surjective π := Function.Surjective.of_comp hι
  have hkerπ : RingHom.ker π = IsLocalRing.maximalIdeal R :=
    IsLocalRing.ker_eq_maximalIdeal π hπsurj
  -- Nakayama: the `tᵢ` and `ℓ` generate `𝔪_R` on the nose
  have hle : IsLocalRing.maximalIdeal R ≤
      Ideal.span (Set.range t) ⊔ Ideal.span {(ℓ : R)} := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot
      (Ideal.fg_of_isNoetherianRing _) (IsLocalRing.maximalIdeal_le_jacobson _) ?_
    have hsq : IsLocalRing.maximalIdeal R • IsLocalRing.maximalIdeal R
        = IsLocalRing.maximalIdeal R ^ 2 := by
      rw [Ideal.smul_eq_mul, ← pow_two]
    rw [hsq]
    conv_lhs => rw [hspan]
    exact sup_le (le_sup_of_le_left le_sup_left)
      (sup_le le_sup_right (le_sup_of_le_left le_sup_right))
  set T : Ideal R := Ideal.span (Set.range t) with hTdef
  have hmapT : Ideal.map φ
      (Ideal.span (Set.range (MvPowerSeries.X : Fin g → MvPowerSeries (Fin g) Λ))) = T := by
    rw [hTdef, Ideal.map_span]
    congr 1
    ext r
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hφX i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨MvPowerSeries.X i, ⟨i, rfl⟩, hφX i⟩
  have hTle : T ≤ IsLocalRing.maximalIdeal R := by
    rw [hTdef]; conv_rhs => rw [hspan]
    exact le_sup_left
  have hTne : T ≠ ⊤ := by
    intro h
    rw [h, top_le_iff] at hTle
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top hTle
  haveI : Nontrivial (R ⧸ T) := Ideal.Quotient.nontrivial_iff.mpr hTne
  haveI : IsLocalRing (R ⧸ T) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk T) Ideal.Quotient.mk_surjective
  haveI : IsNoetherianRing (R ⧸ T) :=
    isNoetherianRing_of_surjective R (R ⧸ T) (Ideal.Quotient.mk T)
      Ideal.Quotient.mk_surjective
  haveI : IsHausdorff (Ideal.map φ
      (Ideal.span (Set.range (MvPowerSeries.X : Fin g → MvPowerSeries (Fin g) Λ)))) R := by
    rw [hmapT]
    exact IsHausdorff.of_isLocalRing T R hTne
  refine surjective_of_mk_map_comp_surjective
    (I := Ideal.span (Set.range (MvPowerSeries.X : Fin g → MvPowerSeries (Fin g) Λ))) φ ?_
  rw [hmapT]
  -- it suffices that `Λ` already surjects onto `R ⧸ T`
  have hℓΛ : (ℓ : Λ) ∈ IsLocalRing.maximalIdeal Λ := by
    rw [hΛℓ]; exact Ideal.subset_span rfl
  have hbar : Function.Surjective ((Ideal.Quotient.mk T).comp ι) := by
    haveI : IsHausdorff (Ideal.map ((Ideal.Quotient.mk T).comp ι)
        (IsLocalRing.maximalIdeal Λ)) (R ⧸ T) := by
      refine IsHausdorff.of_isLocalRing _ _ ?_
      refine ne_of_lt (lt_of_le_of_lt ?_
        (lt_top_iff_ne_top.mpr (IsLocalRing.maximalIdeal.isMaximal (R ⧸ T)).ne_top))
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      simp only [Ideal.mem_comap, RingHom.comp_apply]
      haveI : IsLocalHom (Ideal.Quotient.mk T) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      refine map_nonunit (Ideal.Quotient.mk T) _ ?_
      rw [← hkerπ, RingHom.mem_ker]
      have := IsLocalRing.ker_eq_maximalIdeal (π.comp ι) hι
      rw [← this, RingHom.mem_ker] at ha
      exact ha
    refine surjective_of_mk_map_comp_surjective (I := IsLocalRing.maximalIdeal Λ) _ ?_
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨a, ha⟩ := hι (π r)
    refine ⟨a, ?_⟩
    rw [RingHom.comp_apply, Ideal.Quotient.eq]
    have hdiff : ι a - r ∈ T ⊔ Ideal.span {(ℓ : R)} := by
      refine hle ?_
      rw [← hkerπ, RingHom.mem_ker, map_sub, sub_eq_zero]
      exact ha
    obtain ⟨x₁, hx₁, x₂, hx₂, hx⟩ := Submodule.mem_sup.mp hdiff
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp hx₂
    have hkey : (Ideal.Quotient.mk T) (ι a) - (Ideal.Quotient.mk T) r
        = (Ideal.Quotient.mk T) ((ℓ : R) * s) := by
      rw [← map_sub, ← hx, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hx₁, zero_add,
        mul_comm]
    rw [RingHom.comp_apply, hkey]
    have hmem : ((Ideal.Quotient.mk T).comp ι) (ℓ : Λ) ∈
        Ideal.map ((Ideal.Quotient.mk T).comp ι) (IsLocalRing.maximalIdeal Λ) :=
      Ideal.mem_map_of_mem _ hℓΛ
    have hcast : ((Ideal.Quotient.mk T).comp ι) (ℓ : Λ)
        = (Ideal.Quotient.mk T) ((ℓ : R)) := by
      rw [RingHom.comp_apply, map_natCast, map_natCast]
    rw [hcast] at hmem
    rw [map_mul]
    exact Ideal.mul_mem_right _ _ hmem
  intro y
  obtain ⟨a, ha⟩ := hbar y
  exact ⟨MvPowerSeries.C a, by
    rw [RingHom.comp_apply,
      show φ (MvPowerSeries.C a) = ι a from RingHom.congr_fun hφC a]
    exact ha⟩

omit [Fact (Nat.Prime ℓ)] in
/-- **Minimality (kernel-bound) stratum of the de Smit–Lenstra
presentation** (PROVEN 2026-07-25 — pure commutative algebra, the fourth
stratum of the same-day decomposition of
`exists_minimal_mvPowerSeries_presentation`): when the `tᵢ` are a
MINIMAL family generating `𝔪_R` modulo `𝔪_R² + ℓR` — the length `g` is
least among all such families, as produced by
`exists_minimal_span_sup_of_isNoetherianRing` — the substitution map
`φ` has `ker φ ≤ 𝔪_S² + (ℓ)`, i.e. `φ` is an isomorphism on mod-`ℓ`
cotangent spaces and the presentation is minimal.

Proof: `𝔪_Λ = (ℓ)` makes `𝔪_S = (ℓ) + (x₁, …, x_g)`
(`maximalIdeal_mvPowerSeries_eq`, over the power-series ingredient
`mem_span_range_X_of_constantCoeff_eq_zero`: a series with vanishing
constant term is `∑ᵢ xᵢ gᵢ`). So a kernel element `f`, which lies in
`𝔪_S` because `φ f = 0` is not a unit, is `f = y + ∑ᵢ cᵢ xᵢ` with
`y ∈ (ℓ)`, and replacing each `cᵢ` by its constant term `aᵢ` costs only
`𝔪_S²` — whence `f ≡ ∑ᵢ C(aᵢ) xᵢ` modulo `𝔪_S² + (ℓ)`.

Now suppose `f ∉ 𝔪_S² + (ℓ)`; then some `aⱼ` is a unit of `Λ` (all
`aᵢ ∈ 𝔪_Λ = (ℓ)` would put `f` back inside). Applying `φ` — a local hom,
being surjective — sends `𝔪_S² + (ℓ)` into `𝔪_R² + ℓR =: J`, so
`∑ᵢ ι(aᵢ) tᵢ ∈ J`; multiplying by the unit `ι(aⱼ)⁻¹` exhibits
`tⱼ ∈ span {tᵢ : i ≠ j} ⊔ J`. Hence the family with `tⱼ` deleted (indexed
by `Fin.succAbove j`) still generates `𝔪_R` modulo `𝔪_R² + ℓR`,
contradicting minimality of `g` (`hmin` applied at `g − 1`). -/
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
        Ideal.span {(ℓ : MvPowerSeries (Fin g) Λ)} := by
  classical
  intro f hf
  by_contra hfK
  -- `f` lies in the maximal ideal, since `φ f = 0` is not a unit
  have hfm : f ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin g) Λ) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h0 : IsUnit (0 : R) := by
      have := hu.map φ
      rwa [RingHom.mem_ker.mp hf] at this
    exact not_isUnit_zero h0
  -- `𝔪_S = (ℓ) + (x₁, …, x_g)`
  have hCℓ : (MvPowerSeries.C : Λ →+* MvPowerSeries (Fin g) Λ) '' {(ℓ : Λ)}
      = {((ℓ : ℕ) : MvPowerSeries (Fin g) Λ)} := by
    simp
  rw [maximalIdeal_mvPowerSeries_eq, hΛℓ, Ideal.map_span, hCℓ] at hfm
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hfm
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hz
  -- the linear part of `f`, read off from the constant terms of the `cᵢ`
  set a : Fin g → Λ := fun i => MvPowerSeries.constantCoeff (c i) with hadef
  have hrem : f - ∑ i, MvPowerSeries.C (a i) * MvPowerSeries.X i ∈
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin g) Λ) ^ 2 ⊔
        Ideal.span {((ℓ : ℕ) : MvPowerSeries (Fin g) Λ)} := by
    have hrw : f - ∑ i, MvPowerSeries.C (a i) * MvPowerSeries.X i
        = y + ∑ i, (c i - MvPowerSeries.C (a i)) * MvPowerSeries.X i := by
      rw [← hyz, ← hc]
      simp only [smul_eq_mul, sub_mul, Finset.sum_sub_distrib]
      ring
    rw [hrw]
    refine Submodule.add_mem _ (Ideal.mem_sup_right hy) (Ideal.sum_mem _ fun i _ => ?_)
    refine Ideal.mem_sup_left ?_
    rw [pow_two]
    refine Ideal.mul_mem_mul ?_ ?_
    · exact (mem_maximalIdeal_mvPowerSeries_iff _).mpr (by simp [hadef])
    · exact (mem_maximalIdeal_mvPowerSeries_iff _).mpr (by simp)
  -- minimality forces one of the `aᵢ` to be a unit
  have hex : ∃ j, a j ∉ IsLocalRing.maximalIdeal Λ := by
    by_contra hall
    have hall' : ∀ i, a i ∈ IsLocalRing.maximalIdeal Λ :=
      fun i => not_not.mp fun h => hall ⟨i, h⟩
    refine hfK ?_
    have hlin : ∑ i, MvPowerSeries.C (a i) * MvPowerSeries.X i ∈
        IsLocalRing.maximalIdeal (MvPowerSeries (Fin g) Λ) ^ 2 ⊔
          Ideal.span {((ℓ : ℕ) : MvPowerSeries (Fin g) Λ)} := by
      refine Ideal.sum_mem _ fun i _ => Ideal.mem_sup_right ?_
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (hΛℓ ▸ hall' i)
      refine Ideal.mul_mem_right _ _ ?_
      rw [← hb]
      simpa using Ideal.mul_mem_left _ (MvPowerSeries.C b)
        (Ideal.subset_span (Set.mem_singleton ((ℓ : ℕ) : MvPowerSeries (Fin g) Λ)))
    simpa using Ideal.add_mem _ hrem hlin
  obtain ⟨j, hj⟩ := hex
  obtain ⟨n, rfl⟩ : ∃ n, g = n + 1 := ⟨g - 1, (Nat.succ_pred_eq_of_pos j.pos).symm⟩
  -- the family with `t j` deleted
  set s : Fin n → R := fun i => t (j.succAbove i) with hsdef
  -- `φ` is a local hom, so it carries the relation down to `R`
  haveI : IsLocalHom φ := IsLocalHom.of_surjective φ hφsurj
  have hmapK : Ideal.map φ (IsLocalRing.maximalIdeal (MvPowerSeries (Fin (n + 1)) Λ) ^ 2 ⊔
      Ideal.span {((ℓ : ℕ) : MvPowerSeries (Fin (n + 1)) Λ)}) ≤
      IsLocalRing.maximalIdeal R ^ 2 ⊔ Ideal.span {(ℓ : R)} := by
    rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_span]
    refine sup_le (le_sup_of_le_left ?_) (le_sup_of_le_right ?_)
    · rw [pow_two, pow_two]
      exact Ideal.mul_mono (IsLocalRing.map_maximalIdeal_le φ)
        (IsLocalRing.map_maximalIdeal_le φ)
    · simp
  have hφsum : ∑ i, ι (a i) * t i ∈
      IsLocalRing.maximalIdeal R ^ 2 ⊔ Ideal.span {(ℓ : R)} := by
    have himg := hmapK (Ideal.mem_map_of_mem φ hrem)
    rw [map_sub, RingHom.mem_ker.mp hf, map_sum] at himg
    simp only [map_mul, show ∀ i, φ (MvPowerSeries.C (a i)) = ι (a i) from
      fun i => RingHom.congr_fun hφC (a i), hφX] at himg
    simpa using neg_mem himg
  -- hence `t j` is redundant
  have hkey : t j ∈ Ideal.span (Set.range s) ⊔
      (IsLocalRing.maximalIdeal R ^ 2 ⊔ Ideal.span {(ℓ : R)}) := by
    have hother : ∀ i ∈ Finset.univ.erase j, ι (a i) * t i ∈
        Ideal.span (Set.range s) ⊔
          (IsLocalRing.maximalIdeal R ^ 2 ⊔ Ideal.span {(ℓ : R)}) := by
      intro i hi
      obtain ⟨kk, hkk⟩ := Fin.exists_succAbove_eq (Finset.mem_erase.mp hi).1
      exact Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨kk, by
        rw [hsdef]; exact congrArg t hkk⟩))
    have h1 : ι (a j) * t j ∈ Ideal.span (Set.range s) ⊔
        (IsLocalRing.maximalIdeal R ^ 2 ⊔ Ideal.span {(ℓ : R)}) := by
      have hsplit : ι (a j) * t j
          = (∑ i, ι (a i) * t i) - ∑ i ∈ Finset.univ.erase j, ι (a i) * t i := by
        rw [Finset.sum_erase_eq_sub (Finset.mem_univ j)]
        ring
      rw [hsplit]
      exact Ideal.sub_mem _ (Ideal.mem_sup_right hφsum) (Ideal.sum_mem _ hother)
    have hunit : IsUnit (ι (a j)) := by
      refine IsUnit.map ι ?_
      by_contra hcon
      exact hj ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hcon))
    obtain ⟨u, hu⟩ := hunit
    have hfin : t j = (↑u⁻¹ : R) * (ι (a j) * t j) := by
      rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
    rw [hfin]
    exact Ideal.mul_mem_left _ _ h1
  -- contradiction with minimality of `g = n + 1`
  have hgen : IsLocalRing.maximalIdeal R = Ideal.span (Set.range s) ⊔
      (IsLocalRing.maximalIdeal R ^ 2 ⊔ Ideal.span {(ℓ : R)}) := by
    refine le_antisymm ?_ ?_
    · conv_lhs => rw [hspan]
      refine sup_le ?_ le_sup_right
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      by_cases hij : i = j
      · rw [hij]; exact hkey
      · obtain ⟨kk, hkk⟩ := Fin.exists_succAbove_eq hij
        exact Ideal.mem_sup_left (Ideal.subset_span ⟨kk, by
          rw [hsdef]; exact congrArg t hkk⟩)
    · refine sup_le ?_ ?_
      · rw [Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        exact ht _
      · conv_rhs => rw [hspan]
        exact le_sup_right
  have := hmin n s (fun i => ht _) hgen
  omega

omit [TopologicalSpace k] [DiscreteTopology k] in
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
  obtain ⟨Λ, iCR, iDom, iLoc, iNoeth, iAlg, iFin, iPre, hΛℓ, ι, hιcomp, hιsurj⟩ :=
    exists_coefficientRing_ringHom (ℓ := ℓ) (k := k) π hπsurj
  letI := iCR; letI := iDom; letI := iLoc; letI := iNoeth; letI := iAlg
  letI := iFin; letI := iPre
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

/-- **Nakayama descent for a minimal generating family** (PROVEN
2026-07-25, pure commutative algebra): in a Noetherian local ring, an
ideal contained in the span of finitely many of its own elements
TOGETHER WITH `𝔪 · I` is already their span. This is the formal half of
the Böckle relation bound: the arithmetic input only has to produce
`r ≤ g` relations spanning `ker φ` *modulo* `𝔪 · ker φ` — which is what
obstruction theory gives, a family dual to a subspace of `H²` inside the
`k`-vector space `ker φ/𝔪 · ker φ` — and Nakayama
(`Submodule.le_of_le_smul_of_le_jacobson_bot`, with `𝔪` inside the
Jacobson radical of a local ring) upgrades that to an honest generating
family. Consumed by the relation-bound assembly
`exists_relations_lt_of_minimal_mvPowerSeries_presentation` below. -/
theorem eq_span_of_le_span_sup_smul {S : Type*} [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S] {I : Ideal S} {r : ℕ}
    (f : Fin r → S) (hf : ∀ i, f i ∈ I)
    (hle : I ≤ Ideal.span (Set.range f) ⊔ IsLocalRing.maximalIdeal S • I) :
    I = Ideal.span (Set.range f) := by
  refine le_antisymm ?_ (Ideal.span_le.mpr ?_)
  · exact Submodule.le_of_le_smul_of_le_jacobson_bot
      (IsNoetherian.noetherian I)
      (IsLocalRing.maximalIdeal_le_jacobson ⊥)
      hle
  · rintro x ⟨i, rfl⟩
    exact hf i

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

The assembly proven here is Nakayama's lemma, factored out above as
`eq_span_of_le_span_sup_smul` (in the form
`Submodule.le_of_le_smul_of_le_jacobson_bot`): `Λ[[x₁,…,x_g]]` is
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
  exact ⟨r, f, hℓΛ, hrg, eq_span_of_le_span_sup_smul f hfmem hle⟩

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
