/-
Modularity/PatchingWitt.lean — own work for the Fermat project (not
vendored from the FLT project).

# Cohen's coefficient ring `𝒪 = 𝕎 k`, hoisted out of `Modularity/Patching.lean`

This module contains, VERBATIM and with no mathematical change, the
Witt-vector/Cohen block that lived in `Modularity/Patching.lean` from
2026-07-27 to 2026-07-31: the coefficientwise topology on `𝕎 k`, the
`TaylorWilesCoefficients` bundle `TaylorWilesCoefficients.wittVector`, the
`IsCohenCoefficients` predicate, the lifting leaf
`existsUnique_ringHom_wittVector_of_isNilpotent`, and
`exists_taylorWilesCoefficients_ringHom`.

## Why it is here rather than in `Patching.lean`

`HardlyRamified/HilbertModularity.lean` needs exactly this material for its own
bottom-level coefficient ring (`exists_hilbertBottomCoeffRingHom`), and it
CANNOT reach `Modularity/Patching.lean`: that module `public import`s
`HilbertModularity.lean` (for the `raisedLevelIsSplitTorusAt_of_fibreProduct`
and `exists_levelIdealSystem_aux_of_clauses` proofs), so the import would be a
cycle.  `HilbertModularity.lean`'s own docstrings asked for this hoist twice —
see the paragraph headed "THE HOIST IS THEREFORE NOW UNBLOCKED, AND IT IS THE
NEXT STEP" on `exists_hilbertTaylorWilesBottomPresentation`.  The alternative,
duplicating Cohen's structure theorem at the `F` level, is ~1100 lines of
commutative algebra written twice and two leaves
(`existsUnique_ringHom_wittVector_of_isNilpotent` twice) where there is one.

The block's only inputs are `Modularity/PatchingCore.lean` (for the
`TaylorWilesCoefficients` bundle) and mathlib's Witt-vector files; a
comment-stripped token scan of the moved region against the 155 declarations
that preceded it in `Patching.lean` found ZERO backward references, which is
what made the move a pure relocation.

CIRCULARITY GUARD (the odd-prime dichotomy guard that `HilbertModularity.lean`'s
header imposes on `Modularity/*` imports): none applies.  Nothing in this module
mentions `ρbar`, a deformation functor, a Hecke algebra, or a modular curve; the
whole file is commutative algebra about `𝕎 k` and complete local rings, and its
import closure is `Modularity/PatchingCore.lean` plus mathlib.  This is the same
test `exists_taylorWilesCoefficients_ringHom` already applies to itself in its
own docstring below.
-/
module

public import Fermat.FLT.Modularity.PatchingCore

public import Mathlib.RingTheory.WittVector.DiscreteValuationRing
public import Mathlib.RingTheory.WittVector.Complete
public import Mathlib.RingTheory.WittVector.Truncated
public import Mathlib.RingTheory.WittVector.Teichmuller
public import Mathlib.RingTheory.WittVector.TeichmullerSeries
-- the Witt-vector coefficient ring `𝒪 = 𝕎 k` of the Cohen decomposition
-- below: `WittVector.isDiscreteValuationRing`, `quotientPEquiv`,
-- `ker_constantCoeff`, `mem_span_p_pow_iff_le_coeff_eq_zero`, `truncate`,
-- `teichmuller` and `eq_of_apply_teichmuller_eq`
public import Mathlib.RingTheory.Perfectoid.FontaineTheta
-- `WittVector.ghostComponentModPPow : 𝕎 (R ⧸ p) →+* R ⧸ p^(n+1)` (which needs
-- NO hypothesis on `R` at all — the perfectoid hypotheses in that file are
-- imposed only afterwards, for `fontaineTheta` itself)
public import Mathlib.Algebra.CharP.Lemmas
-- `Commute.exists_add_pow_prime_eq`, the binomial input to the `p`-power
-- contraction `sub_pow_mem_pow_succ` below
public import Mathlib.RingTheory.AdicCompletion.RingHom
-- `IsAdicComplete.StrictMono.liftRingHom`
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
-- `Ideal.Quotient.factorPow`
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.Data.Countable.Small
-- the `Type 0` transport of the finite residue field `k` demanded by
-- `TaylorWilesCoefficients.carrier : Type`
public import Mathlib.FieldTheory.Perfect
-- `PerfectRing.ofFiniteOfIsReduced`
public import Mathlib.Topology.Homeomorph.Lemmas
-- `Homeomorph.compactSpace`/`Homeomorph.t2Space`
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Connected.TotallyDisconnected
-- proof-only, and easy to miss: without these two the route
-- `IsUltrametricDist ℤ_[p] → TotallySeparatedSpace → TotallyDisconnectedSpace`
-- is unavailable and `TotallyDisconnectedSpace ℤ_[p]` fails to synthesize
-- with no hint of the cause
public import Mathlib.Topology.Algebra.Algebra
-- `Algebra.TopologicallyFG`
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Completeness

@[expose] public section

namespace GaloisRepresentation.Modularity

/-! ### Cohen's coefficient ring: `𝕎 k` as a `TaylorWilesCoefficients`

The block below (2026-07-27) discharges obligation (a) of
`exists_taylorWilesCoefficients_ringHom`: it exhibits the Witt vectors
`𝕎 k` of a finite field `k` of characteristic `p` as a
`TaylorWilesCoefficients` bundle, and it does so with NO sorry.  The
topological half — which the leaf's docstring flagged as the part needing
`𝕎 k = lim 𝕎_n(k)` — turned out not to need the inverse-limit
description at all: `𝕎 k` is by DEFINITION a structure whose single field
is `coeff : ℕ → k`, so the coefficientwise topology makes it
HOMEOMORPHIC to `ℕ → k`, and compactness, Hausdorffness and total
disconnectedness are Tychonoff plus transport.  Only the continuity of
the ring operations needs an argument, and that argument is
`WittVector.truncate` (the `n`-th coefficient of `x + y`, `x * y`, `-x`
depends on the first `n + 1` coefficients of `x` and `y` alone) landing
in a FINITE, hence discrete, space.

For a perfect `k` of characteristic `p` this topology IS the `p`-adic
one, by `WittVector.mem_span_p_pow_iff_le_coeff_eq_zero`
(`(p)^n = {x | ∀ i < n, x.coeff i = 0}`), so nothing unnatural is being
installed. -/

/-- **The coefficientwise topology on `𝕎 k`** (PROVEN 2026-07-27), for a
DISCRETE coefficient ring `k`: the topology induced from `ℕ → k` along
`WittVector.coeff`.  For `k` perfect of characteristic `p` this is the
`p`-adic topology, because `(p)^n` is exactly the set of Witt vectors
whose first `n` coefficients vanish
(`WittVector.mem_span_p_pow_iff_le_coeff_eq_zero`). -/
@[reducible] def wittVectorTopology (p : ℕ) (k : Type*) [TopologicalSpace k] :
    TopologicalSpace (WittVector p k) :=
  TopologicalSpace.induced (fun x : WittVector p k => x.coeff) inferInstance

/-- `𝕎 k` with the coefficientwise topology is HOMEOMORPHIC to `ℕ → k`
(PROVEN 2026-07-27) — `WittVector p k` is a one-field structure, so
`coeff` is a bijection, and the topology was defined to make it inducing.
This is what makes the profiniteness of `𝕎 k` for finite `k` a transport
of Tychonoff rather than an inverse-limit construction. -/
def wittVectorHomeomorph (p : ℕ) (k : Type*) [TopologicalSpace k] :
    @Homeomorph (WittVector p k) (ℕ → k) (wittVectorTopology p k) inferInstance :=
  letI := wittVectorTopology p k
  { toFun := fun x => x.coeff
    invFun := WittVector.mk p
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := continuous_induced_dom
    continuous_invFun := continuous_induced_rng.mpr continuous_id }

/-- Each coefficient function `x ↦ x.coeff i` is continuous (PROVEN
2026-07-27). -/
theorem continuous_wittVector_coeff (p : ℕ) (k : Type*) [TopologicalSpace k] (i : ℕ) :
    @Continuous (WittVector p k) k (wittVectorTopology p k) _ (fun x => x.coeff i) := by
  letI := wittVectorTopology p k
  exact (continuous_apply i).comp
    (@continuous_induced_dom _ _ (fun x : WittVector p k => x.coeff) _)

/-- `𝕎 k` is COMPACT for the coefficientwise topology when `k` is
(PROVEN 2026-07-27) — Tychonoff on `ℕ → k`, transported. -/
theorem wittVector_compactSpace (p : ℕ) (k : Type*) [TopologicalSpace k] [CompactSpace k] :
    @CompactSpace (WittVector p k) (wittVectorTopology p k) := by
  letI := wittVectorTopology p k
  exact (wittVectorHomeomorph p k).symm.compactSpace

/-- `𝕎 k` is HAUSDORFF for the coefficientwise topology when `k` is
(PROVEN 2026-07-27). -/
theorem wittVector_t2Space (p : ℕ) (k : Type*) [TopologicalSpace k] [T2Space k] :
    @T2Space (WittVector p k) (wittVectorTopology p k) := by
  letI := wittVectorTopology p k
  exact (wittVectorHomeomorph p k).symm.t2Space

/-- `𝕎 k` is TOTALLY DISCONNECTED for the coefficientwise topology when
`k` is (PROVEN 2026-07-27). -/
theorem wittVector_totallyDisconnectedSpace (p : ℕ) (k : Type*) [TopologicalSpace k]
    [TotallyDisconnectedSpace k] :
    @TotallyDisconnectedSpace (WittVector p k) (wittVectorTopology p k) := by
  letI := wittVectorTopology p k
  exact ⟨(wittVectorHomeomorph p k).isEmbedding.isTotallyDisconnected
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

/-- `truncate n x` is the tuple of the first `n` coefficients of `x`
(PROVEN 2026-07-27).  This is the bridge that turns the ring operations
of `𝕎 k` into functions of finitely many coefficients. -/
theorem wittVector_truncate_eq_mk (p n : ℕ) [Fact p.Prime] {k : Type*} [CommRing k]
    (x : WittVector p k) :
    WittVector.truncate n x = TruncatedWittVector.mk p (fun i : Fin n => x.coeff i) :=
  TruncatedWittVector.ext fun i => by
    rw [WittVector.coeff_truncate, TruncatedWittVector.coeff_mk]

/-- **The ring operations of `𝕎 k` are continuous** for the
coefficientwise topology (PROVEN 2026-07-27).

The whole content is that `WittVector.truncate (n+1)` is a RING
HOMOMORPHISM onto `TruncatedWittVector p (n+1) k = (Fin (n+1) → k)`, so
the `n`-th coefficient of `x + y` (resp. `x * y`, `-x`) is an explicit
function of the first `n + 1` coefficients of `x` and `y`; that function
is continuous for free because its domain `(Fin (n+1) → k)²` is DISCRETE
(`Pi.discreteTopology` on a finite index set).  No finiteness of `k` is
needed here — only discreteness. -/
theorem wittVector_isTopologicalRing (p : ℕ) [Fact p.Prime] (k : Type*) [CommRing k]
    [TopologicalSpace k] [DiscreteTopology k] :
    @IsTopologicalRing (WittVector p k) (wittVectorTopology p k) _ := by
  letI := wittVectorTopology p k
  have hcoeff : ∀ i : ℕ, Continuous fun x : WittVector p k => x.coeff i :=
    continuous_wittVector_coeff p k
  have hΦ : ∀ n : ℕ, Continuous fun q : WittVector p k × WittVector p k =>
      ((fun i : Fin (n + 1) => q.1.coeff i), (fun i : Fin (n + 1) => q.2.coeff i)) := by
    intro n
    exact (continuous_pi fun i : Fin (n + 1) => (hcoeff (i : ℕ)).comp continuous_fst).prodMk
      (continuous_pi fun i : Fin (n + 1) => (hcoeff (i : ℕ)).comp continuous_snd)
  have hΦ' : ∀ n : ℕ, Continuous fun x : WittVector p k =>
      (fun i : Fin (n + 1) => x.coeff i) :=
    fun n => continuous_pi fun i : Fin (n + 1) => hcoeff (i : ℕ)
  have hadd : Continuous fun q : WittVector p k × WittVector p k => q.1 + q.2 := by
    refine continuous_induced_rng.mpr (continuous_pi fun n => ?_)
    show Continuous fun q : WittVector p k × WittVector p k => (q.1 + q.2).coeff n
    have : (fun q : WittVector p k × WittVector p k => (q.1 + q.2).coeff n) =
        (fun a : (Fin (n + 1) → k) × (Fin (n + 1) → k) =>
          TruncatedWittVector.coeff (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))
            (TruncatedWittVector.mk p a.1 + TruncatedWittVector.mk p a.2)) ∘
        (fun q : WittVector p k × WittVector p k =>
          ((fun i : Fin (n + 1) => q.1.coeff i), (fun i : Fin (n + 1) => q.2.coeff i))) := by
      funext q
      simp only [Function.comp_apply, ← wittVector_truncate_eq_mk, ← map_add,
        WittVector.coeff_truncate]
    rw [this]
    exact continuous_of_discreteTopology.comp (hΦ n)
  have hmul : Continuous fun q : WittVector p k × WittVector p k => q.1 * q.2 := by
    refine continuous_induced_rng.mpr (continuous_pi fun n => ?_)
    show Continuous fun q : WittVector p k × WittVector p k => (q.1 * q.2).coeff n
    have : (fun q : WittVector p k × WittVector p k => (q.1 * q.2).coeff n) =
        (fun a : (Fin (n + 1) → k) × (Fin (n + 1) → k) =>
          TruncatedWittVector.coeff (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))
            (TruncatedWittVector.mk p a.1 * TruncatedWittVector.mk p a.2)) ∘
        (fun q : WittVector p k × WittVector p k =>
          ((fun i : Fin (n + 1) => q.1.coeff i), (fun i : Fin (n + 1) => q.2.coeff i))) := by
      funext q
      simp only [Function.comp_apply, ← wittVector_truncate_eq_mk, ← map_mul,
        WittVector.coeff_truncate]
    rw [this]
    exact continuous_of_discreteTopology.comp (hΦ n)
  have hneg : Continuous fun x : WittVector p k => -x := by
    refine continuous_induced_rng.mpr (continuous_pi fun n => ?_)
    show Continuous fun x : WittVector p k => (-x).coeff n
    have : (fun x : WittVector p k => (-x).coeff n) =
        (fun a : Fin (n + 1) → k =>
          TruncatedWittVector.coeff (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))
            (-TruncatedWittVector.mk p a)) ∘
        (fun x : WittVector p k => (fun i : Fin (n + 1) => x.coeff i)) := by
      funext x
      simp only [Function.comp_apply, ← wittVector_truncate_eq_mk, ← map_neg,
        WittVector.coeff_truncate]
    rw [this]
    exact continuous_of_discreteTopology.comp (hΦ' n)
  exact { toIsTopologicalSemiring := { toContinuousAdd := ⟨hadd⟩, toContinuousMul := ⟨hmul⟩ }
          toContinuousNeg := ⟨hneg⟩ }

section WittVectorLocal

variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [CharP k p] [PerfectRing k p]

/-- **`𝔪_{𝕎 k} = (p)`** (PROVEN 2026-07-27): the kernel of
`WittVector.constantCoeff` is `(p)` (mathlib's
`WittVector.ker_constantCoeff`), and it is maximal because
`constantCoeff` is a surjection onto the field `k`; a maximal ideal of a
local ring is THE maximal ideal. -/
theorem wittVector_maximalIdeal_eq_span_p :
    _root_.IsLocalRing.maximalIdeal (WittVector p k) = Ideal.span {(p : WittVector p k)} := by
  refine (_root_.IsLocalRing.eq_maximalIdeal ?_).symm
  rw [← WittVector.ker_constantCoeff (p := p) (k := k)]
  exact RingHom.ker_isMaximal_of_surjective _ (WittVector.constantCoeff_surjective p)

/-- **The residue field of `𝕎 k` is `k`** (PROVEN 2026-07-27), via
mathlib's `WittVector.quotientPEquiv : 𝕎 k ⧸ (p) ≃+* k`. -/
noncomputable def wittVectorResidueEquiv :
    (WittVector p k ⧸ _root_.IsLocalRing.maximalIdeal (WittVector p k)) ≃+* k :=
  (Ideal.quotEquivOfEq (wittVector_maximalIdeal_eq_span_p p k)).trans WittVector.quotientPEquiv

/-- The `finite_residueField` field of `TaylorWilesCoefficients` for
`𝒪 = 𝕎 k` (PROVEN 2026-07-27). -/
theorem wittVector_finite_residueField [Finite k] :
    Finite (WittVector p k ⧸ _root_.IsLocalRing.maximalIdeal (WittVector p k)) :=
  Finite.of_equiv k (wittVectorResidueEquiv p k).symm.toEquiv

/-- The `exists_isRegular_maximalIdeal` field of `TaylorWilesCoefficients`
for `𝒪 = 𝕎 k` (PROVEN 2026-07-27): `𝔪 = (p)` is spanned by the
length-one regular sequence `[p]`, `p` being a nonzerodivisor of `𝕎 k`
by `WittVector.eq_zero_of_p_mul_eq_zero`.  This is the `𝕎 k` analogue of
`exists_isRegular_ofList_eq_maximalIdeal_padicInt` in `PatchingCore`, and
it is what says `𝒪` is a DVR. -/
theorem wittVector_exists_isRegular_maximalIdeal :
    ∃ ts : List (WittVector p k), ts.length = 0 + 1 ∧
      RingTheory.Sequence.IsRegular (WittVector p k) ts ∧
      Ideal.ofList ts = _root_.IsLocalRing.maximalIdeal (WittVector p k) := by
  have hmem : ∀ r ∈ [(p : WittVector p k)],
      r ∈ _root_.IsLocalRing.maximalIdeal (WittVector p k) := by
    intro r hr
    rw [List.mem_singleton] at hr
    subst hr
    rw [wittVector_maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  have hp : IsSMulRegular (WittVector p k) (p : WittVector p k) := by
    intro x y h
    simp only [smul_eq_mul] at h
    have hz : (x - y) * (p : WittVector p k) = 0 := by
      rw [sub_mul, mul_comm x, mul_comm y, h, sub_self]
    exact sub_eq_zero.mp (WittVector.eq_zero_of_p_mul_eq_zero _ hz)
  refine ⟨[(p : WittVector p k)], rfl,
    RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal (WittVector p k) hmem
      (RingTheory.Sequence.IsWeaklyRegular.cons hp (RingTheory.Sequence.IsWeaklyRegular.nil _ _)),
    ?_⟩
  rw [Ideal.ofList_singleton, wittVector_maximalIdeal_eq_span_p]

/-- **Teichmüller approximation** (PROVEN 2026-07-27): every Witt vector
is matched to any prescribed coefficient depth by an element of the
subRING generated over `ℤ` by the Teichmüller lifts.

Induction on the depth `n`: if `a` agrees with `x` below `n` then
`x - a ∈ (p^n)`, say `x - a = z · p^n`; the Teichmüller lift
`c = τ(z.coeff 0)` has the same constant coefficient as `z`, so
`z - c ∈ (p)` and `x - (a + c·p^n) ∈ (p^{n+1})`.  This is the ℤ-integral
form of the Teichmüller expansion `x = Σ_i τ(x_i^{p^{-i}}) p^i`, and it
is all that topological finite generation needs. -/
theorem exists_mem_adjoin_teichmuller_coeff_eq (x : WittVector p k) (n : ℕ) :
    ∃ a ∈ Algebra.adjoin ℤ (Set.range (WittVector.teichmuller p (R := k))),
      ∀ i < n, WittVector.coeff a i = x.coeff i := by
  induction n with
  | zero => exact ⟨0, Subalgebra.zero_mem _, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ n ih =>
    obtain ⟨a, ha, hac⟩ := ih
    have hy : x - a ∈ Ideal.span {(p : WittVector p k) ^ n} := by
      rw [WittVector.mem_span_p_pow_iff_le_coeff_eq_zero]
      exact WittVector.le_coeff_eq_iff_le_sub_coeff_eq_zero.mp fun i hi => (hac i hi).symm
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hy
    set c : WittVector p k := WittVector.teichmuller p (z.coeff 0) with hc
    have hzc : z - c ∈ Ideal.span {(p : WittVector p k) ^ 1} := by
      rw [WittVector.mem_span_p_pow_iff_le_coeff_eq_zero]
      refine WittVector.le_coeff_eq_iff_le_sub_coeff_eq_zero.mp fun i hi => ?_
      obtain rfl : i = 0 := by omega
      rw [hc, WittVector.teichmuller_coeff_zero]
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hzc
    refine ⟨a + c * (p : WittVector p k) ^ n, ?_, ?_⟩
    · exact Subalgebra.add_mem _ ha (Subalgebra.mul_mem _
        (Algebra.subset_adjoin ⟨_, rfl⟩) (Subalgebra.pow_mem _ (Subalgebra.natCast_mem _ p) n))
    · intro i hi
      have hmem : x - (a + c * (p : WittVector p k) ^ n) ∈
          Ideal.span {(p : WittVector p k) ^ (n + 1)} := by
        refine Ideal.mem_span_singleton'.mpr ⟨w, ?_⟩
        linear_combination hz + (p : WittVector p k) ^ n * hw
      exact ((WittVector.le_coeff_eq_iff_le_sub_coeff_eq_zero (n := n + 1)).mpr
        ((WittVector.mem_span_p_pow_iff_le_coeff_eq_zero _ (n + 1)).mp hmem) i hi).symm

/-- The `topologicallyFG` field of `TaylorWilesCoefficients` for
`𝒪 = 𝕎 k` (PROVEN 2026-07-27): `𝕎 k` is topologically generated over
`ℤ` by the FINITELY many Teichmüller lifts `τ(a)`, `a ∈ k`.

The generating set is `Set.range (WittVector.teichmuller p)`, finite
because `k` is; density is `exists_mem_adjoin_teichmuller_coeff_eq`
turned into a limit: the approximants converge coefficientwise, and the
topology is exactly the coefficientwise one.  This replaces the
`W(k) = ℤ_p[ζ]`-with-`ζ`-a-Teichmüller-lift-of-a-generator route recorded
in the leaf docstring, which would have needed the polynomial
presentation of `𝕎 k` over `ℤ_[p]`. -/
theorem wittVector_topologicallyFG [Finite k] [TopologicalSpace k] [DiscreteTopology k] :
    @Algebra.TopologicallyFG ℤ (WittVector p k) _ _ _ (wittVectorTopology p k)
      (wittVector_isTopologicalRing p k) := by
  letI := wittVectorTopology p k
  haveI := wittVector_isTopologicalRing p k
  have hfin : (Set.range (WittVector.teichmuller p (R := k))).Finite := Set.finite_range _
  refine ⟨⟨hfin.toFinset, ?_⟩⟩
  rw [hfin.coe_toFinset]
  intro x
  choose a ha hac using fun n => exists_mem_adjoin_teichmuller_coeff_eq p k x n
  refine mem_closure_of_tendsto (b := Filter.atTop) ?_ (Filter.Eventually.of_forall ha)
  rw [(⟨rfl⟩ : Topology.IsInducing (fun y : WittVector p k => y.coeff)).tendsto_nhds_iff]
  refine tendsto_pi_nhds.mpr fun i => ?_
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (i + 1)] with n hn
  exact (hac n i (by omega)).symm

end WittVectorLocal

/-- **`𝕎 k` IS a Taylor–Wiles coefficient ring** (PROVEN 2026-07-27) —
obligation (a) of `exists_taylorWilesCoefficients_ringHom`, discharged
with no sorry.  `k` is taken in `Type 0` because
`TaylorWilesCoefficients.carrier` is; the caller supplies the transport
(`Shrink.{0} k`, legitimate because `k` is finite hence countable).

Where each field comes from:

* `commRing`/`isLocalRing`/`isNoetherianRing` and
  `exists_isRegular_maximalIdeal` — mathlib's
  `WittVector.isDiscreteValuationRing` (a DVR is local, Noetherian, and
  has principal maximal ideal), through
  `wittVector_exists_isRegular_maximalIdeal`.
* `finite_residueField` — `WittVector.quotientPEquiv`, through
  `wittVector_finite_residueField`.
* the TOPOLOGICAL half — the coefficientwise (= `p`-adic) topology
  `wittVectorTopology`, whose profiniteness is Tychonoff on `ℕ → k`
  transported along `wittVectorHomeomorph`.
* `topologicallyFG` — `wittVector_topologicallyFG`, from the Teichmüller
  expansion. -/
noncomputable def TaylorWilesCoefficients.wittVector (p : ℕ) [Fact p.Prime] (k : Type)
    [Field k] [Finite k] [CharP k p] : TaylorWilesCoefficients :=
  letI : TopologicalSpace k := ⊥
  haveI : DiscreteTopology k := ⟨rfl⟩
  haveI : PerfectRing k p := PerfectRing.ofFiniteOfIsReduced p k
  { carrier := WittVector p k
    topologicalSpace := wittVectorTopology p k
    isTopologicalRing := wittVector_isTopologicalRing p k
    compactSpace := wittVector_compactSpace p k
    t2Space := wittVector_t2Space p k
    totallyDisconnectedSpace := wittVector_totallyDisconnectedSpace p k
    finite_residueField := wittVector_finite_residueField p k
    topologicallyFG := wittVector_topologicallyFG p k
    exists_isRegular_maximalIdeal := wittVector_exists_isRegular_maximalIdeal p k }

/-- Iterating `frobeniusEquiv⁻¹` `n` times and then raising to the `p ^ n`
is the identity (PROVEN 2026-07-30).  This is the ONLY place perfectness of
`k` is used in the Witt-vector lifting leaf below, and it is used twice: once
to exhibit a Teichmüller representative as a `p ^ n`-th power (uniqueness),
and once to cancel the Frobenius twist that `ghostComponentModPPow` introduces
(existence). -/
theorem symm_frobeniusEquiv_pow_pow {p : ℕ} [Fact p.Prime]
    {k : Type*} [CommRing k] [CharP k p] [PerfectRing k p] (n : ℕ) (a : k) :
    (((_root_.frobeniusEquiv k p).symm ^ n) a) ^ p ^ n = a := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    have hmul : ((_root_.frobeniusEquiv k p).symm ^ (n + 1)) a
        = ((_root_.frobeniusEquiv k p).symm ^ n) ((_root_.frobeniusEquiv k p).symm a) := by
      rw [pow_succ]; rfl
    rw [hmul, pow_succ p n, pow_mul, ih]
    exact frobeniusEquiv_symm_pow_p k p a

/-- **The characteristic-`p` section along a NILPOTENT ideal** (PROVEN
2026-07-30): a surjection `π : T ↠ k` of characteristic-`p` rings with
NILPOTENT kernel splits, provided `k` is perfect.

This is the char-`p` shadow of Cohen's theorem, and it is completely
elementary: if `(ker π) ^ M = ⊥` then `ker π ≤ ker (Frob ^ M)`, because
`x ∈ ker π` gives `x ^ (p ^ M) ∈ (ker π) ^ (p ^ M) ≤ (ker π) ^ M = ⊥`.  So
`Frob ^ M : T →+* T` factors through `π`, giving `s' : k →+* T` with
`π ∘ s' = Frob_k ^ M`; precomposing with `Frob_k⁻¹ ^ M` — which exists
EXACTLY because `k` is perfect — turns it into a genuine section.

NOTE the hypothesis is nilpotence of the IDEAL, not elementwise nilpotence:
a uniform exponent is what makes `Frob ^ M` kill the kernel, and no single
`M` works for a merely nil ideal. -/
theorem exists_ringHom_section_of_isNilpotent_ker
    {p : ℕ} [Fact p.Prime]
    {T : Type*} [CommRing T] [CharP T p]
    {k : Type*} [CommRing k] [CharP k p] [PerfectRing k p]
    (π : T →+* k) (hπ : Function.Surjective π)
    (hnil : IsNilpotent (RingHom.ker π)) :
    ∃ s : k →+* T, ∀ a, π (s a) = a := by
  obtain ⟨M, hM⟩ := hnil
  have hMle : M ≤ p ^ M := (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
  have hle : RingHom.ker π ≤ RingHom.ker (_root_.iterateFrobenius T p M) := by
    intro x hx
    have h1 : x ^ p ^ M ∈ RingHom.ker π ^ p ^ M := Ideal.pow_mem_pow hx _
    have h2 : (RingHom.ker π : Ideal T) ^ p ^ M ≤ RingHom.ker π ^ M :=
      Ideal.pow_le_pow_right hMle
    have h3 := h2 h1
    rw [hM] at h3
    simpa [RingHom.mem_ker, _root_.iterateFrobenius] using h3
  set s' : k →+* T := π.liftOfSurjective hπ ⟨_root_.iterateFrobenius T p M, hle⟩ with hs'
  have hs'comp : ∀ x : T, s' (π x) = x ^ p ^ M := fun x =>
    RingHom.liftOfSurjective_comp_apply π hπ ⟨_root_.iterateFrobenius T p M, hle⟩ x
  have hπs' : ∀ a : k, π (s' a) = a ^ p ^ M := by
    intro a
    obtain ⟨x, rfl⟩ := hπ a
    rw [hs'comp, map_pow]
  refine ⟨s'.comp (((_root_.frobeniusEquiv k p).symm ^ M : k ≃+* k) : k →+* k), fun a => ?_⟩
  rw [RingHom.comp_apply, hπs']
  exact symm_frobeniusEquiv_pow_pow M a

/-- **The `p`-power map contracts the `I`-adic filtration by one step**, for
`I` an ideal CONTAINING `p` (PROVEN 2026-07-30): if `x − y ∈ I ^ m` with
`m ≥ 1` then `x ^ p − y ^ p ∈ I ^ (m + 1)`.

Write `d = x − y`.  The prime binomial identity
`(y + d) ^ p = y ^ p + d ^ p + p·y·d·r` (`Commute.exists_add_pow_prime_eq`)
puts the error into two pieces: `d ^ p ∈ I ^ (m·p) ≤ I ^ (m+1)` since
`m·p ≥ 2m ≥ m+1`, and `p·y·d·r ∈ I ^ m · I` since `p ∈ I`. -/
theorem sub_pow_mem_pow_succ {S : Type*} [CommRing S] {p : ℕ} (hp : p.Prime)
    {I : Ideal S} (hpI : (p : S) ∈ I) {m : ℕ} (hm : 1 ≤ m) {x y : S}
    (h : x - y ∈ I ^ m) : x ^ p - y ^ p ∈ I ^ (m + 1) := by
  obtain ⟨r, hr⟩ := (Commute.all y (x - y)).exists_add_pow_prime_eq hp
  rw [show y + (x - y) = x by ring] at hr
  have h1 : (x - y) ^ p ∈ I ^ (m + 1) := by
    have hmp : I ^ (m * p) ≤ I ^ (m + 1) :=
      Ideal.pow_le_pow_right (by nlinarith [hp.two_le])
    refine hmp ?_
    rw [pow_mul]
    exact Ideal.pow_mem_pow h p
  have h2 : (p : S) * y * (x - y) * r ∈ I ^ (m + 1) := by
    have hmem : (x - y) * ((p : S) * y * r) ∈ I ^ m * I := Ideal.mul_mem_mul h
      (I.mul_mem_right _ (I.mul_mem_right _ hpI))
    rw [pow_succ]
    convert hmem using 1
    ring
  rw [show x ^ p - y ^ p = (x - y) ^ p + (p : S) * y * (x - y) * r by rw [hr]; ring]
  exact Ideal.add_mem _ h1 h2

/-- Iterating the previous lemma: `x − y ∈ I` gives
`x ^ (p ^ n) − y ^ (p ^ n) ∈ I ^ (n + 1)` (PROVEN 2026-07-30).  Note the growth
is only LINEAR in `n`, which is all that is needed and all that is true. -/
theorem sub_pow_pow_mem_pow {S : Type*} [CommRing S] {p : ℕ} (hp : p.Prime)
    {I : Ideal S} (hpI : (p : S) ∈ I) {x y : S} (h : x - y ∈ I) (n : ℕ) :
    x ^ p ^ n - y ^ p ^ n ∈ I ^ (n + 1) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    have hstep := sub_pow_mem_pow_succ hp hpI (Nat.succ_le_succ (Nat.zero_le n)) ih
    simpa [pow_succ p n, pow_mul] using hstep

/-- **Two elements that are `p ^ n`-th powers of congruent elements for EVERY
`n` are equal**, modulo a nilpotent ideal containing `p` (PROVEN 2026-07-30).

This is the uniqueness of the Teichmüller (multiplicative) section, in the
form the Witt-vector leaf below consumes it: `f ([a])` is a `p ^ n`-th power
for every `n` (of `f ([a ^ (1/p ^ n)])`), and its image in `S ⧸ I` is pinned,
so any two ring maps agreeing after `σ` agree on Teichmüller representatives —
whereupon `WittVector.eq_of_apply_teichmuller_eq` finishes. -/
theorem eq_of_forall_exists_pow_sub_mem {S : Type*} [CommRing S] {p : ℕ} (hp : p.Prime)
    {I : Ideal S} (hpI : (p : S) ∈ I) (hI : IsNilpotent I) {u v : S}
    (h : ∀ n : ℕ, ∃ x y : S, u = x ^ p ^ n ∧ v = y ^ p ^ n ∧ x - y ∈ I) : u = v := by
  obtain ⟨M, hM⟩ := hI
  obtain ⟨x, y, hu, hv, hxy⟩ := h M
  have hmem := sub_pow_pow_mem_pow hp hpI hxy M
  rw [← hu, ← hv] at hmem
  have hle : I ^ (M + 1) ≤ I ^ M := Ideal.pow_le_pow_right (Nat.le_succ M)
  have hbot : u - v ∈ I ^ M := hle hmem
  rw [hM] at hbot
  exact sub_eq_zero.mp (by simpa using hbot)

/-! #### Lifting `𝕎 k` along a nilpotent thickening — the four ingredients

Added 2026-07-31 by the PROOF of `existsUnique_ringHom_wittVector_of_isNilpotent`
below, which was the sole remaining leaf of the Cohen coefficient-ring cluster.
Nothing here mentions `ρbar`, a deformation functor or a Hecke algebra: it is
Witt-vector commutative algebra, and it is stated in the generality mathlib
states its Witt API in.

THE ROUTE, and it is NOT the Teichmüller-expansion computation the leaf's old
docstring priced it as.  Writing `f x = Σ_i ω(x_i^{p^{-i}}) p^i` and proving by
hand that the sum is a ring map is the classical argument, and it is a large
Witt-polynomial computation.  It can be avoided entirely, because BOTH maps in
the factorisation

    `𝕎 k --𝕎(s')--> 𝕎 (S/p) --θ--> S`

are obtained from ring maps that already exist:

* `s' : k →+* S/p` is a ring SECTION of `S/p ↠ k`.  In characteristic `p` the
  Teichmüller section is a ring map for free, because Frobenius IS a ring map:
  set `s a := (any lift of a^{p^{-m}}) ^ p^m`, which is well defined as soon as
  `p^m` kills `ker σ`, since two lifts differ by `j ∈ ker σ` and
  `(b + j)^{p^m} = b^{p^m} + j^{p^m}` — no binomial coefficients survive.  This
  is `exists_ringHom_section_of_charP`.
* `θ : 𝕎 (S/p) →+* S` is mathlib's ghost component `w_M` DESCENDED along the
  surjection `𝕎 S ↠ 𝕎 (S/p)`.  It descends because `w_M x = Σ_{i≤M} p^i x_i^{p^{M-i}}`
  and `i + p^{M-i} ≥ M + 1` whenever `p ∣ x_i` — which is exactly mathlib's
  `WittVector.pow_dvd_ghostComponent_of_dvd_coeff`.  This is
  `exists_ringHom_ghostComponent_quotient_p`.

The composite reads off `σ (f x) = (x.coeff 0)^{p^M}`, one Frobenius twist away
from `constantCoeff`; `k` is PERFECT, so the twist is undone by precomposing the
section with `(iterateFrobeniusEquiv k p M).symm`.  That is the ONE place
perfectness of `k` is used for existence (it is used again, through
`WittVector.eq_of_apply_teichmuller_eq`, for uniqueness).

The remaining two lemmas are the arithmetic behind UNIQUENESS: two lifts of the
same Teichmüller representative differ by an element of `ker σ`, and raising to
a large `p`-th power kills the difference. -/

/-- **Kummer's bound in the only case needed** (PROVEN 2026-07-31):
`p^(n+1-m) ∣ (p^n).choose j` for `0 < j < p^m ≤ p^n`.

Mathlib's `Nat.Prime.dvd_choose_pow` gives only ONE factor of `p`; the whole
point here is the `p`-ADIC VALUATION `v_p((p^n).choose j) = n - v_p(j)`, and the
elementary route to it is the absorption identity
`p^n * (p^n - 1).choose (j-1) = (p^n).choose j * j`
(`Nat.add_one_mul_choose_eq`): writing `j = p^a * u` with `p ∤ u` and `a < m`,
cancelling `p^a` and using `Nat.Coprime` leaves `p^(n-a) ∣ (p^n).choose j`. -/
theorem prime_pow_dvd_choose_prime_pow
    {p : ℕ} (hp : p.Prime) {m n j : ℕ} (hj0 : j ≠ 0) (hjm : j < p ^ m) (hmn : m ≤ n) :
    p ^ (n + 1 - m) ∣ (p ^ n).choose j := by
  have hp1 : 1 < p := hp.one_lt
  set a := j.factorization p with ha
  have hpa : p ^ a ∣ j := Nat.ordProj_dvd j p
  have hale : p ^ a ≤ j := Nat.le_of_dvd (Nat.pos_of_ne_zero hj0) hpa
  have ham : a < m := by
    by_contra h
    push Not at h
    exact absurd (le_trans (Nat.pow_le_pow_right (le_of_lt hp1) h) hale) (by omega)
  have hpn1 : p ^ n - 1 + 1 = p ^ n := Nat.succ_pred_eq_of_pos (Nat.pow_pos (by omega))
  have hj1 : j - 1 + 1 = j := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hj0)
  have hid : p ^ n * (p ^ n - 1).choose (j - 1) = (p ^ n).choose j * j := by
    have h := Nat.add_one_mul_choose_eq (p ^ n - 1) (j - 1)
    rw [hpn1, hj1] at h
    exact h
  have hdvd : p ^ n ∣ (p ^ n).choose j * j := ⟨_, hid.symm⟩
  obtain ⟨u, hu⟩ := hpa
  have hnpu : ¬ p ∣ u := by
    intro hdu
    obtain ⟨w, hw⟩ := hdu
    have : p ^ (a + 1) ∣ j := ⟨w, by rw [hu, hw, pow_succ]; ring⟩
    exact Nat.pow_succ_factorization_not_dvd hj0 hp this
  have han : a ≤ n := le_of_lt (lt_of_lt_of_le ham hmn)
  have hdvd2 : p ^ (n - a) ∣ (p ^ n).choose j * u := by
    have hdvd' : p ^ n ∣ (p ^ n).choose j * (p ^ a * u) := by rw [← hu]; exact hdvd
    have key : p ^ a * p ^ (n - a) ∣ p ^ a * ((p ^ n).choose j * u) := by
      have e1 : p ^ a * p ^ (n - a) = p ^ n := by rw [← pow_add]; congr 1; omega
      have e2 : p ^ a * ((p ^ n).choose j * u) = (p ^ n).choose j * (p ^ a * u) := by ring
      rw [e1, e2]; exact hdvd'
    exact (mul_dvd_mul_iff_left (a := p ^ a) (by positivity)).mp key
  have hcop : Nat.Coprime (p ^ (n - a)) u :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnpu)
  have hfin : p ^ (n - a) ∣ (p ^ n).choose j := hcop.dvd_of_dvd_mul_right hdvd2
  exact dvd_trans (pow_dvd_pow p (by omega)) hfin

/-- **Frobenius rigidity where `p` is nilpotent** (PROVEN 2026-07-31): in any
commutative ring, if `(p : S)^M = 0` and `(u - v)^(p^m) = 0` then
`u^(p^n) = v^(p^n)` as soon as `M + m ≤ n + 1` (and `m ≤ n`).

This is the whole content of the UNIQUENESS half below.  Note that `S` has no
characteristic hypothesis: the binomial expansion of `(v + d)^(p^n)` is killed
term by term from two sides — the terms with `d`-exponent `≥ p^m` vanish because
`d` is nilpotent, and the rest have a binomial coefficient divisible by `p^M` by
`prime_pow_dvd_choose_prime_pow`. -/
theorem pow_prime_pow_eq_of_sub_pow_eq_zero {S : Type*} [CommRing S] {p : ℕ} (hp : p.Prime)
    {M m n : ℕ} (hpM : (p : S) ^ M = 0) {u v : S} (hd : (u - v) ^ p ^ m = 0)
    (hmn : m ≤ n) (hn : M + m ≤ n + 1) :
    u ^ p ^ n = v ^ p ^ n := by
  set d : S := u - v with hddef
  have huvd : u = v + d := by rw [hddef]; ring
  rw [huvd, add_pow]
  rw [Finset.sum_eq_single (p ^ n)]
  · simp
  · intro b hb hbne
    rcases Nat.lt_or_ge b (p ^ n) with hlt | hge
    · set j := p ^ n - b with hjdef
      have hj0 : j ≠ 0 := by omega
      rcases Nat.lt_or_ge j (p ^ m) with hjm | hjm
      · have hch : p ^ (n + 1 - m) ∣ (p ^ n).choose b := by
          have hsym : (p ^ n).choose b = (p ^ n).choose j := by
            rw [hjdef, Nat.choose_symm (le_of_lt hlt)]
          rw [hsym]
          exact prime_pow_dvd_choose_prime_pow hp hj0 hjm hmn
        obtain ⟨c, hc⟩ := hch
        have hMle : M ≤ n + 1 - m := by omega
        have hzero : ((p ^ n).choose b : S) = 0 := by
          rw [hc]
          push_cast
          rw [show n + 1 - m = M + (n + 1 - m - M) by omega, pow_add, hpM]
          ring
        rw [hzero, mul_zero]
      · have hdj : d ^ j = 0 := by
          rw [show j = p ^ m + (j - p ^ m) by omega, pow_add, hd, zero_mul]
        rw [hdj, mul_zero, zero_mul]
    · exfalso
      simp only [Finset.mem_range] at hb
      omega
  · intro h
    exact absurd (Finset.self_mem_range_succ (p ^ n)) h

/-- **A surjection onto a PERFECT ring in characteristic `p` with uniformly
nilpotent kernel SPLITS** (PROVEN 2026-07-31): if `σ : A ↠ k` is a surjection of
characteristic-`p` rings, `k` is perfect, and `x ^ p^m = 0` for every
`x ∈ ker σ`, then `σ` has a ring-theoretic section.

The section is the Teichmüller one, `s a := (any lift of a^{p^{-m}}) ^ p^m`.
Everything is free because Frobenius is a RING map in characteristic `p`:
well-definedness is `(b + j)^{p^m} = b^{p^m} + j^{p^m}` with `j^{p^m} = 0`, and
additivity/multiplicativity hold because `lift x + lift y` is a lift of `x + y`.

The UNIFORM exponent `p^m` is what makes this elementary, and it is why the leaf
below is stated with a uniform nilpotency bound; see its docstring. -/
theorem exists_ringHom_section_of_charP {p : ℕ} [Fact p.Prime]
    {A : Type*} [CommRing A] [CharP A p]
    {k : Type*} [CommRing k] [CharP k p] [PerfectRing k p]
    {σ : A →+* k} (hσ : Function.Surjective σ) {m : ℕ}
    (hker : ∀ x ∈ RingHom.ker σ, x ^ p ^ m = 0) :
    ∃ s : k →+* A, ∀ a, σ (s a) = a := by
  classical
  have hrig : ∀ x y : A, σ x = σ y → x ^ p ^ m = y ^ p ^ m := by
    intro x y h
    have hmem : x - y ∈ RingHom.ker σ := by
      rw [RingHom.mem_ker, map_sub, h, sub_self]
    have h0 : (x - y) ^ p ^ m = 0 := hker _ hmem
    rw [sub_pow_char_pow] at h0
    exact sub_eq_zero.mp h0
  set ψ : k ≃+* k := (iterateFrobeniusEquiv k p m).symm with hψ
  have hψpow : ∀ a : k, (ψ a) ^ p ^ m = a := by
    intro a
    have h := (iterateFrobeniusEquiv k p m).apply_symm_apply a
    rwa [iterateFrobeniusEquiv_def] at h
  set g : k → A := fun a => Function.surjInv hσ (ψ a) with hg
  have hgs : ∀ a, σ (g a) = ψ a := fun a => Function.surjInv_eq hσ _
  refine ⟨{ toFun := fun a => (g a) ^ p ^ m
            map_one' := ?_
            map_mul' := ?_
            map_zero' := ?_
            map_add' := ?_ }, ?_⟩
  · have h : σ (g 1) = σ 1 := by rw [hgs, map_one, map_one]
    rw [hrig _ _ h, one_pow]
  · intro a b
    have h : σ (g (a * b)) = σ (g a * g b) := by
      simp only [hgs, map_mul]
    rw [hrig _ _ h, mul_pow]
  · have h : σ (g 0) = σ 0 := by rw [hgs, map_zero, map_zero]
    rw [hrig _ _ h, zero_pow (Nat.pow_pos (Nat.Prime.pos Fact.out)).ne']
  · intro a b
    have h : σ (g (a + b)) = σ (g a + g b) := by
      simp only [hgs, map_add]
    rw [hrig _ _ h, add_pow_char_pow]
  · intro a
    show σ ((g a) ^ p ^ m) = a
    rw [map_pow, hgs, hψpow]

/-- **The ghost component `w_M` descends to `𝕎 (S/p) →+* S`** (PROVEN
2026-07-31) whenever `(p : S)^(M+1) = 0`.

`𝕎 S ↠ 𝕎 (S/p)` is surjective coefficientwise, and its kernel is killed by
`w_M`: mathlib's `WittVector.pow_dvd_ghostComponent_of_dvd_coeff` says
`p ∣ x.coeff i` for all `i ≤ M` implies `p^(M+1) ∣ w_M x`, which is `0` here.
`RingHom.liftOfSurjective` then produces the descended map.

This is the map usually written `θ` (Fontaine); the point of getting it this way
is that its ring-map property is mathlib's, not ours — `ghostComponent` is
already a `RingHom`, and descending a `RingHom` along a surjection needs only a
kernel inclusion. -/
theorem exists_ringHom_ghostComponent_quotient_p {p : ℕ} [Fact p.Prime]
    {S : Type*} [CommRing S] {M : ℕ} (hpM : (p : S) ^ (M + 1) = 0) :
    ∃ θ : WittVector p (S ⧸ Ideal.span {(p : S)}) →+* S,
      θ.comp (WittVector.map (Ideal.Quotient.mk (Ideal.span {(p : S)})))
        = WittVector.ghostComponent M := by
  classical
  set J : Ideal S := Ideal.span {(p : S)} with hJ
  set F : WittVector p S →+* WittVector p (S ⧸ J) :=
    WittVector.map (Ideal.Quotient.mk J) with hF
  have hFsurj : Function.Surjective F :=
    WittVector.map_surjective _ Ideal.Quotient.mk_surjective
  have hkerle : RingHom.ker F ≤
      RingHom.ker (WittVector.ghostComponent M : WittVector p S →+* S) := by
    intro x hx
    rw [RingHom.mem_ker] at hx ⊢
    have hc : ∀ i ≤ M, (p : S) ∣ x.coeff i := by
      intro i _
      have h1 : (Ideal.Quotient.mk J) (x.coeff i) = 0 := by
        have h2 := congrArg (fun y : WittVector p (S ⧸ J) => y.coeff i) hx
        simpa [hF, WittVector.map_coeff] using h2
      rw [← Ideal.mem_span_singleton, ← hJ]
      exact (Ideal.Quotient.eq_zero_iff_mem).mp h1
    obtain ⟨c, hcc⟩ := WittVector.pow_dvd_ghostComponent_of_dvd_coeff hc
    rw [hcc, hpM, zero_mul]
  exact ⟨RingHom.liftOfSurjective F hFsurj ⟨WittVector.ghostComponent M, hkerle⟩,
    RingHom.liftOfRightInverse_comp _ _ _ _⟩

/-- **Lifting `𝕎 k` along a NILPOTENT thickening — PROVEN 2026-07-31**, closing
LEAF B1a-i-α of the 2026-07-27 decomposition of
`exists_taylorWilesCoefficients_ringHom` and with it the whole Cohen
coefficient-ring cluster: if `p` is nilpotent in `S` and `σ : S ↠ k` has
uniformly nilpotent kernel, then `σ` lifts UNIQUELY to a ring homomorphism
`𝕎 k → S`.

This is the finite-level half of Cohen's structure theorem (Serre,
*Corps Locaux*, II §5 Thm. 3 / *Local Fields* II §5; Matsumura,
*Commutative Ring Theory*, Thm. 29.1–29.4; Eisenbud, *Commutative
Algebra*, Thm. 7.7), and it is what makes `𝕎 k` "the" `p`-adic lift of a
perfect ring: `𝕎 k` is formally étale over `ℤ_p` in the `p`-adic sense,
so a lift along a nilpotent thickening exists and is unique.

# ROUTE AS ACTUALLY TAKEN (2026-07-30) — and the classical route was NOT it

Both halves go through the Teichmüller expansion, but neither half needed the
"expand `f x = Σ_i ω(x_i^{p^{-i}}) · p^i` and check it is a ring map"
computation this docstring used to prescribe, and NEITHER needed an induction
along the filtration by powers of `ker σ`.  That computation is the expensive
way to write down a map out of `𝕎`, and mathlib already contains it.

* **UNIQUENESS.**  `WittVector.eq_of_apply_teichmuller_eq`
  (`Mathlib/RingTheory/WittVector/TeichmullerSeries.lean`) says two ring maps
  `𝕎 k →+* S` agreeing on Teichmüller representatives are equal when `p` is
  nilpotent in `S`.  So it remains to show that `σ.comp f = constantCoeff`
  PINS `f ([a])`.  It does, and with NO limit argument: `[a] = [a^{p^{-n}}]^{p^n}`
  because `k` is perfect, so `f ([a])` is a `p^n`-th power of an element lying
  over `a^{p^{-n}}` for EVERY `n`, and two such elements agree because the
  `p`-power map contracts the `ker σ`-adic filtration by one step each time
  (`sub_pow_mem_pow_succ`, `sub_pow_pow_mem_pow`, `eq_of_forall_exists_pow_sub_mem`
  above).  Note `p ∈ ker σ` automatically, since `k` has characteristic `p`;
  that is what makes the contraction available.

* **EXISTENCE — the whole map is `𝕎(section) ; ghostComponentModPPow`.**  The
  key observation is that `WittVector.ghostComponentModPPow`
  (`Mathlib/RingTheory/Perfectoid/FontaineTheta.lean`) is stated with **no
  hypothesis on `R` whatsoever** — the perfectoid/`IsAdicComplete` assumptions
  in that file are imposed only later, for `fontaineTheta` itself.  It is the
  lift of the `n`-th ghost component along `𝕎 R ↠ 𝕎 (R ⧸ p)`:

      ghostComponentModPPow n : 𝕎 (R ⧸ p) →+* R ⧸ p^(n+1).

  Take `R = S` and `n = N` where `p^N = 0` in `S`.  Then `(p)^{N+1} = ⊥`, so
  `S ⧸ (p)^{N+1} ≅ S` and the target IS `S`.  It therefore suffices to produce
  a ring map `k →+* S ⧸ p`, i.e. a SECTION of `S ⧸ p ↠ k` — and `S ⧸ p` has
  characteristic `p`, so that is the elementary char-`p` splitting
  `exists_ringHom_section_of_isNilpotent_ker` above (Frobenius kills a nilpotent
  ideal after finitely many steps; perfectness of `k` untwists the result).

  The composite `𝕎 k --𝕎(s ∘ Frob⁻ᴺ)--> 𝕎 (S ⧸ p) --gh_N--> S` is the lift.  The
  `Frob⁻ᴺ` twist is not cosmetic: `gh_N` of a Teichmüller class is the `p^N`-th
  power of a lift, so without it the map would induce `a ↦ a^{p^N}` on residue
  fields rather than the identity — the same twist, and for the same reason,
  that `fontaineThetaModPPow` carries.

# WHAT IS **NOT** OWED, and this is what shrank the leaf (2026-07-27)

The COMPLETION half is free.  `IsAdicComplete.StrictMono.liftRingHom`
(`Mathlib/RingTheory/AdicCompletion/RingHom.lean`) is the universal
property of `IsAdicComplete` for RING maps: a compatible family
`𝕎 k →+* R ⧸ 𝔪^{n+1}` assembles into `𝕎 k →+* R`.  That is exactly what
`exists_ringHom_wittVector_of_isAdicComplete` below does with this leaf,
and the compatibility of the family comes from the UNIQUENESS clause
here — which is why the statement is `∃!` and not `∃`.  The earlier
docstring's "the coefficient-ring map `W(k) → R` is absent from all
three trees" is correct only about the finite-level statement below.

FAITHFULNESS.  The hypotheses are the exact ones under which the
statement is classical: `p` nilpotent in `S`, `σ` surjective, `ker σ`
nilpotent (so `S → k` is a nilpotent thickening), `k` a PERFECT field of
characteristic `p`.  Dropping perfectness makes it false (there is no
canonical multiplicative section for imperfect `k`); dropping
nilpotence of `ker σ` makes it false (`S` must be an infinitesimal
thickening for the successive lifting to terminate).

**HYPOTHESIS CORRECTED 2026-07-30 — `ker σ` NILPOTENT, not elementwise nil.**
The statement previously read `hker : ∀ x ∈ RingHom.ker σ, IsNilpotent x`,
which is the strictly weaker "nil ideal" condition and does NOT match the
docstring's own prose ("nilpotent kernel", "`S` must be an infinitesimal
thickening").  The difference is not pedantic and it is exactly where the
proof lives: the char-`p` section is built from `Frobenius^M` killing the
kernel, and a nil ideal admits no uniform `M` — the sets
`{x^{p^n} : σ x = a^{p^{-n}}}` form a decreasing chain of nonempty sets whose
intersection is nonempty for a NILPOTENT ideal (the sets are eventually
singletons) and need not be for a merely nil one.  The uniqueness half
survives the weakening; the existence half is not known to.

Nothing was lost downstream: the sole consumer
`exists_ringHom_wittVector_of_isAdicComplete` applies this at
`R ⧸ 𝔪^{n+1}`, whose kernel `𝔪/𝔪^{n+1}` is nilpotent with the UNIFORM
exponent `n+1` — indeed its old proof of the elementwise form already
produced that uniform exponent and then threw it away.

CIRCULARITY GUARD: none applies — no `ρbar`, no deformation functor, no
Hecke algebra occurs in the statement. -/
theorem existsUnique_ringHom_wittVector_of_isNilpotent
    {p : ℕ} [Fact p.Prime] {k : Type*} [Field k] [CharP k p] [PerfectRing k p]
    {S : Type*} [CommRing S] (hpS : IsNilpotent (p : S))
    {σ : S →+* k} (hσ : Function.Surjective σ)
    (hker : IsNilpotent (RingHom.ker σ)) :
    ∃! f : WittVector p k →+* S, σ.comp f = WittVector.constantCoeff := by
  have hp : p.Prime := Fact.out
  have hpmem : (p : S) ∈ RingHom.ker σ := by
    simp [RingHom.mem_ker, map_natCast]
  -- UNIQUENESS: two lifts agree on Teichmüller representatives.
  have key : ∀ f g : WittVector p k →+* S, σ.comp f = WittVector.constantCoeff →
      σ.comp g = WittVector.constantCoeff → f = g := by
    intro f g hf hg
    refine WittVector.eq_of_apply_teichmuller_eq f g hpS fun a => ?_
    refine eq_of_forall_exists_pow_sub_mem hp hpmem hker fun n => ?_
    refine ⟨f (WittVector.teichmuller p (((_root_.frobeniusEquiv k p).symm ^ n) a)),
      g (WittVector.teichmuller p (((_root_.frobeniusEquiv k p).symm ^ n) a)), ?_, ?_, ?_⟩
    · rw [← map_pow, ← map_pow, symm_frobeniusEquiv_pow_pow n a]
    · rw [← map_pow, ← map_pow, symm_frobeniusEquiv_pow_pow n a]
    · have h1 := congrArg (fun h : WittVector p k →+* k =>
        h (WittVector.teichmuller p (((_root_.frobeniusEquiv k p).symm ^ n) a))) hf
      have h2 := congrArg (fun h : WittVector p k →+* k =>
        h (WittVector.teichmuller p (((_root_.frobeniusEquiv k p).symm ^ n) a))) hg
      simp only [RingHom.coe_comp, Function.comp_apply] at h1 h2
      rw [RingHom.mem_ker, map_sub, h1, h2, sub_self]
  -- EXISTENCE: `𝕎 k --𝕎(s ∘ Frob⁻ᴺ)--> 𝕎 (S ⧸ p) --gh_N--> S ⧸ (p)^{N+1} ≅ S`.
  obtain ⟨N, hN⟩ := hpS
  have hbot : (Ideal.span {(p : S)}) ^ (N + 1) = ⊥ := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_eq_bot, pow_succ, hN, zero_mul]
  have hple : Ideal.span {(p : S)} ≤ RingHom.ker σ := by
    rw [Ideal.span_le]; simp
  set σbar : (S ⧸ Ideal.span {(p : S)}) →+* k :=
    Ideal.Quotient.lift _ σ (fun a ha => RingHom.mem_ker.mp (hple ha)) with hσbar
  have hσbar_mk : ∀ x : S, σbar (Ideal.Quotient.mk (Ideal.span {(p : S)}) x) = σ x :=
    fun _ => rfl
  have hσbar_surj : Function.Surjective σbar := fun a => by
    obtain ⟨x, hx⟩ := hσ a
    exact ⟨Ideal.Quotient.mk _ x, by rw [hσbar_mk, hx]⟩
  haveI : Nontrivial (S ⧸ Ideal.span {(p : S)}) := σbar.domain_nontrivial
  haveI : CharP (S ⧸ Ideal.span {(p : S)}) p := by
    have h0 : ((p : ℕ) : S ⧸ Ideal.span {(p : S)}) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(p : S)})),
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton_self _
    rcases hp.eq_one_or_self_of_dvd _ (ringChar.dvd h0) with h1 | hpe
    · haveI : CharP (S ⧸ Ideal.span {(p : S)}) 1 := ringChar.of_eq h1
      exact (CharP.false_of_nontrivial_of_char_one (R := S ⧸ Ideal.span {(p : S)})).elim
    · exact ringChar.of_eq hpe
  have hkerbar : IsNilpotent (RingHom.ker σbar) := by
    obtain ⟨M, hM⟩ := hker
    refine ⟨M, ?_⟩
    rw [hσbar, Ideal.ker_quotient_lift, ← Ideal.map_pow, hM]
    simp
  obtain ⟨s, hs⟩ := exists_ringHom_section_of_isNilpotent_ker σbar hσbar_surj hkerbar
  set φ : k →+* k := (((_root_.frobeniusEquiv k p).symm ^ N : k ≃+* k) : k →+* k) with hφ
  set ψ : (S ⧸ (Ideal.span {(p : S)}) ^ (N + 1)) →+* S :=
    Ideal.Quotient.lift _ (RingHom.id S) (fun a ha => by
      rw [hbot] at ha; simpa using ha) with hψ
  have hF : σ.comp (ψ.comp ((WittVector.ghostComponentModPPow N).comp
      (WittVector.map (s.comp φ)))) = WittVector.constantCoeff := by
    refine WittVector.eq_of_apply_teichmuller_eq _ _ ⟨1, by simp⟩ fun a => ?_
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (s (φ a))
    have e1 : WittVector.map (s.comp φ) (WittVector.teichmuller p a)
        = WittVector.map (Ideal.Quotient.mk (Ideal.span {(p : S)}))
            (WittVector.teichmuller p t) := by
      rw [WittVector.map_teichmuller, WittVector.map_teichmuller, ht]
      rfl
    have hσt : σ t = φ a := by
      rw [← hσbar_mk, ht, hs]
    simp only [RingHom.coe_comp, Function.comp_apply, e1,
      WittVector.ghostComponentModPPow_map_mk, WittVector.ghostComponent_teichmuller]
    show σ (t ^ p ^ N) = _
    rw [map_pow, hσt, hφ]
    simp
  exact ⟨_, hF, fun g hg => key g _ hg hF⟩

/-- **Cohen's coefficient-ring map `𝕎 k → R`** (PROVEN 2026-07-27 over
`existsUnique_ringHom_wittVector_of_isNilpotent`): for `R` local and
`𝔪_R`-adically complete with residue field `k` (perfect, of
characteristic `p`), there is a ring homomorphism `ι : 𝕎 k →+* R` with
`π ∘ ι = WittVector.constantCoeff` — i.e. `ι` induces the IDENTITY on
residue fields.

The proof is pure assembly and needs no Witt-vector theory of its own:

* `𝔪_R^{n+1} ≤ ker π = 𝔪_R`, so `π` factors through every
  `R ⧸ 𝔪_R^{n+1}`, and that quotient is a nilpotent thickening of `k`
  in which `p` is nilpotent (`p ∈ 𝔪_R` because `k` has characteristic
  `p`).  The leaf therefore applies at every level.
* The resulting family is COMPATIBLE by the leaf's uniqueness clause:
  `factorPow ∘ f_{n+1}` also lifts `π` at level `n`.
* `IsAdicComplete.StrictMono.liftRingHom` assembles it into `𝕎 k →+* R`,
  and reading the identity off at level `0` gives `π ∘ ι = constantCoeff`. -/
theorem exists_ringHom_wittVector_of_isAdicComplete
    {R : Type*} [CommRing R] [IsLocalRing R]
    (hcomplete : IsAdicComplete (_root_.IsLocalRing.maximalIdeal R) R)
    {p : ℕ} [Fact p.Prime] {k : Type*} [Field k] [CharP k p] [PerfectRing k p]
    {π : R →+* k} (hπ : Function.Surjective π) :
    ∃ ι : WittVector p k →+* R, π.comp ι = WittVector.constantCoeff := by
  haveI := hcomplete
  set I : Ideal R := _root_.IsLocalRing.maximalIdeal R with hIdef
  have hkerpi : RingHom.ker π = I :=
    _root_.IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective π hπ)
  have hpow : ∀ n : ℕ, I ^ (n + 1) ≤ RingHom.ker π := fun n => by
    rw [hkerpi]; exact Ideal.pow_le_self (Nat.succ_ne_zero n)
  set res : (n : ℕ) → (R ⧸ I ^ (n + 1)) →+* k := fun n =>
    Ideal.Quotient.lift (I ^ (n + 1)) π (fun a ha => hpow n ha) with hresdef
  have hres_mk : ∀ (n : ℕ) (x : R), res n (Ideal.Quotient.mk (I ^ (n + 1)) x) = π x :=
    fun n x => rfl
  have hres_surj : ∀ n : ℕ, Function.Surjective (res n) := by
    intro n y
    obtain ⟨x, hx⟩ := hπ y
    exact ⟨Ideal.Quotient.mk _ x, by rw [hres_mk, hx]⟩
  -- the kernel of `res n` is `𝔪/𝔪^{n+1}`, killed by the UNIFORM exponent `n + 1`;
  -- this bound was always available and is now what the leaf asks for
  have hres_ker : ∀ (n : ℕ), ∃ N : ℕ, ∀ x ∈ RingHom.ker (res n), x ^ N = 0 := by
    intro n
    refine ⟨n + 1, ?_⟩
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    have hy : y ∈ I := by
      rw [← hkerpi]
      simpa [RingHom.mem_ker, hres_mk] using hx
    exact Ideal.pow_mem_pow hy (n + 1)
  have hpnil : ∀ n : ℕ, IsNilpotent ((p : ℕ) : R ⧸ I ^ (n + 1)) := by
    intro n
    obtain ⟨N, hN⟩ := hres_ker n
    refine ⟨N, hN _ ?_⟩
    simp only [RingHom.mem_ker, map_natCast]
    exact CharP.cast_eq_zero k p
  -- The IDEAL `ker (res n) = 𝔪/𝔪^{n+1}` is nilpotent, with the uniform exponent
  -- `n + 1` that `hres_ker` above already exhibits elementwise and discards.
  -- The leaf needs the ideal form (see its FAITHFULNESS note): a merely nil
  -- kernel admits no uniform Frobenius power, and the section it is built from
  -- does not exist.
  have hres_ker_nilp : ∀ n : ℕ, IsNilpotent (RingHom.ker (res n)) := by
    intro n
    refine ⟨n + 1, ?_⟩
    simp only [hresdef]
    rw [Ideal.ker_quotient_lift, ← Ideal.map_pow, hkerpi]
    simpa using Ideal.map_quotient_self (I ^ (n + 1))
  choose f hf huniq using fun n : ℕ =>
    existsUnique_ringHom_wittVector_of_isNilpotent (p := p) (k := k) (hpnil n)
      (hres_surj n) (hres_ker_nilp n)
  have ha : StrictMono (fun n : ℕ => n + 1) := fun _ _ h => Nat.succ_lt_succ h
  have hcompat : ∀ m : ℕ,
      (Ideal.Quotient.factorPow I (ha.monotone m.le_succ)).comp (f (m + 1)) = f m := by
    intro m
    have hstep : (res m).comp (Ideal.Quotient.factorPow I (ha.monotone m.le_succ))
        = res (m + 1) := by
      refine RingHom.ext fun z => ?_
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
      rfl
    refine huniq m _ ?_
    show (res m).comp ((Ideal.Quotient.factorPow I (ha.monotone m.le_succ)).comp (f (m + 1)))
      = WittVector.constantCoeff
    rw [← RingHom.comp_assoc, hstep, hf (m + 1)]
  refine ⟨IsAdicComplete.StrictMono.liftRingHom I ha f (fun {m} => hcompat m), ?_⟩
  ext x
  have hlvl := IsAdicComplete.StrictMono.mk_liftRingHom I ha f (fun {m} => hcompat m) (n := 0) x
  calc π (IsAdicComplete.StrictMono.liftRingHom I ha f (fun {m} => hcompat m) x)
      = res 0 (Ideal.Quotient.mk (I ^ (0 + 1))
          (IsAdicComplete.StrictMono.liftRingHom I ha f (fun {m} => hcompat m) x)) :=
        (hres_mk 0 _).symm
    _ = res 0 (f 0 x) := by rw [hlvl]
    _ = WittVector.constantCoeff x := congrArg (fun g : WittVector p k →+* k => g x) (hf 0)

set_option linter.checkUnivs false in
/-- **`𝒪` is a COHEN COEFFICIENT RING for `k`** (added 2026-07-29 as the
faithfulness repair of `exists_auxDeformationPresSurjection` far below):
`𝒪` maps into EVERY `𝔪`-adically complete local ring `A` of universe `u`
whose residue field is `k`, inducing the identity on residue fields.

This is exactly the property `W(k)` has and a RAMIFIED coefficient ring
does not, and it is the property the presentation leaves need but had no
way to state, because `TaylorWilesCoefficients` is a bundle rather than a
characterisation: it fixes `𝒪` up to nothing at all beyond "complete DVR
with a finite residue field".

# WHY THE DEVELOPMENT NEEDS IT — THE `𝒪`-ALGEBRA GAP

`AuxDeformationDatum` is a category of complete local **`ℤ_[p]`**-algebras,
while every statement of the form `∃ pres : 𝒪[[x_1, …, x_q]] →+* R_Q` (or
`𝒪[[x_1, …, x_q]] ⧸ I ≃+* R_Q`) asserts, before any Greenberg–Wiles content
whatsoever, that `R_Q` is an **`𝒪`-algebra** — compose with
`MvPowerSeries.C`.  Nothing else in those statements mentions `𝒪`, so they
were universally quantified over coefficient rings that no deformation ring
can receive; see the FALSITY AUDIT of
`exists_auxDeformationPresSurjection` for the two witnesses
(`PowerSeries k₀` in equal characteristic, and `ℤ_[p][π]/(π² − p)` in
unequal characteristic — the second survives every repair that only fixes
the residue field).

This predicate closes both at once: over an `𝒪` satisfying it, `R_Q` IS an
`𝒪`-algebra, by the same Cohen map that `exists_ringHom_wittVector_of_isAdicComplete`
above already builds.  Both witnesses fail it — `PowerSeries k₀` cannot map
to a ring of characteristic `0`, and `ℤ_[p][π]/(π² − p)` cannot map to a
complete local ring with no square root of `p`.

It is discharged, not assumed, at the ONE place the development actually
chooses `𝒪` (`exists_taylorWilesCoefficients_ringHom` below, which returns
`TaylorWilesCoefficients.wittVector`), and threaded from there down to the
leaf; so no new obligation is created anywhere. -/
def IsCohenCoefficients.{u, v} (coeff : TaylorWilesCoefficients)
    (k : Type v) [Field k] : Prop :=
  ∀ (A : Type u) [CommRing A] [IsLocalRing A],
    IsAdicComplete (IsLocalRing.maximalIdeal A) A →
    ∀ πA : A →+* k, Function.Surjective πA →
      ∃ ι : coeff.carrier →+* A, Function.Surjective (πA.comp ι)

/-- **Cohen's COEFFICIENT RING, with its map into `R`** (PROVEN
2026-07-27 over the single leaf
`existsUnique_ringHom_wittVector_of_isNilpotent`; was LEAF B1a-i of the
2026-07-27 decomposition of `exists_taylorWilesCoefficientsPresentation`,
"the substantial half"): for `R` local and `𝔪_R`-adically complete with
finite residue field `k`, there is a `TaylorWilesCoefficients` `𝒪` and a
ring map `ι : 𝒪 →+* R` lifting the residue field, i.e. with `π ∘ ι`
surjective.

Classically `𝒪 = W(k)`, the Witt vectors of `k` (Cohen 1946; Matsumura,
*Commutative Ring Theory*, Thm. 29.1–29.4; Eisenbud, *Commutative
Algebra*, Thm. 7.7).  `k` is finite hence perfect of characteristic `p`,
so `W(k)` is the unique absolutely unramified complete DVR with residue
field `k`, and it is formally smooth over `ℤ_p`; since `R` is
`𝔪_R`-adically complete and `p ∈ 𝔪_R`, the map `W(k) → R` is built by
lifting `k = R/𝔪_R` successively through `R/𝔪_R^{n+1} ↠ R/𝔪_R^n` and
passing to the limit.  Equivalently, and this is usually the cheaper
formalisation: the Teichmüller section `k → R` obtained from
`x ↦ lim_n (x̃_n)^{p^n}` (well defined by completeness and perfectness)
is multiplicative, and `W(k)`'s universal property in the OTHER
direction from `WittVector.lift` — a multiplicative section of
`R ↠ k` induces `W(k) → R` — is what has to be written.

WHAT WAS OWED, AND WHAT REMAINS (2026-07-27; UPDATED 2026-07-30).  The two
obligations this docstring recorded have been discharged as follows; NOTHING in
this declaration is open any more, and its whole residual content was the one
leaf `existsUnique_ringHom_wittVector_of_isNilpotent` above — **which was
itself PROVEN on 2026-07-30, so this declaration is now sorry-free outright.**

1. **The bundle — DONE, sorry-free**, as
   `TaylorWilesCoefficients.wittVector` above.  Two of this docstring's
   own suggestions turned out to be more expensive than necessary and
   were NOT followed, which is worth recording because both were the
   obvious route:
   * The TOPOLOGY is *not* installed through `WithIdeal (W k) := ⟨𝔪⟩`,
     and compactness does *not* go through `W(k) = lim W_n(k)`.
     `WittVector p k` is by definition a one-field structure over
     `coeff : ℕ → k`, so the coefficientwise topology
     (`wittVectorTopology`) makes it HOMEOMORPHIC to `ℕ → k`
     (`wittVectorHomeomorph`), and compactness / Hausdorffness / total
     disconnectedness are Tychonoff plus transport.  Only continuity of
     the ring operations needs an argument, and `WittVector.truncate`
     supplies it.  For perfect `k` this topology IS the `p`-adic one, by
     `WittVector.mem_span_p_pow_iff_le_coeff_eq_zero`.
   * `Algebra.TopologicallyFG ℤ (W k)` does *not* need
     `W(k) = ℤ_p[ζ]`.  The finite set `{τ(a) : a ∈ k}` of ALL
     Teichmüller lifts generates topologically
     (`wittVector_topologicallyFG`), by the integral Teichmüller
     approximation `exists_mem_adjoin_teichmuller_coeff_eq`.
   The `Type 0` transport is `Shrink.{0} k` (a finite field is countable,
   hence `Small.{0}`), not `Fin (Nat.card k)`.
2. **The lift `ι : W(k) →+* R` — the COMPLETION half is FREE**, and the
   previous note missed this.  `IsAdicComplete.StrictMono.liftRingHom`
   (`Mathlib/RingTheory/AdicCompletion/RingHom.lean`) is mathlib's
   universal property of `IsAdicComplete` for RING maps.  So
   `exists_ringHom_wittVector_of_isAdicComplete` above is pure assembly
   over the FINITE-LEVEL statement, which is the single remaining leaf:
   lifting `𝕎 k → S` along a nilpotent thickening `S ↠ k` with `p`
   nilpotent in `S`.  Its uniqueness clause is what makes the family of
   level-`n` lifts compatible, and half of that uniqueness is already in
   mathlib as `WittVector.eq_of_apply_teichmuller_eq`.

MISSING MACHINERY (re-checked 2026-07-27 against our pin, `~/cs/FLT` and
`Fermat/FLT/Mathlib/`; the refuting check for each is a grep for the
name):

* **Cohen's structure theorem is absent from mathlib.** The only file
  matching `Cohen` is `Mathlib/RingTheory/Noetherian/OfPrime.lean`,
  which is Cohen's *other* theorem ("Noetherian iff every prime is
  finitely generated") and is unrelated.
  `grep -rln 'Cohen' .lake/packages/mathlib/Mathlib ~/cs/FLT Fermat`
* The coefficient-ring map `W(k) → R` is absent from all three trees —
  but only its FINITE-LEVEL half is genuinely missing, see item 2 above.

WHAT IS **NOT** OWED ANY MORE, and this is the correction that shrank
this leaf.  The convergence and surjectivity halves of Cohen have been
split off and are NOT part of this leaf:
`exists_ringHom_mvPowerSeries_of_isAdicComplete` (PROVEN above) builds
the substitution homomorphism, and
`surjective_of_span_range_eq_maximalIdeal` (below) is its surjectivity.
Neither needs Witt vectors.

FAITHFULNESS.  The statement asks only for SOME coefficient ring lifting
the residue field; it does not pin `𝒪 = W(k)`, and it must not, because
`TaylorWilesCoefficients` is a bundle rather than a characterisation.  A
prover is free to return any DVR bundle that maps to `R` and hits `k`.
Note the leaf would be FALSE if `[Finite k]` were dropped: the
`finite_residueField` field of `TaylorWilesCoefficients` forces `𝒪` to
have a finite residue field, and `π ∘ ι` surjective then forces `k`
itself to be finite.

CIRCULARITY GUARD: none applies — this leaf mentions no `ρbar`, no
deformation functor and no Hecke algebra, so no route to the odd-prime
dichotomy can even be stated against it.

**STRENGTHENED 2026-07-29.**  The conclusion now also asserts
`IsCohenCoefficients.{u, v} coeff k` — the returned `𝒪` maps into EVERY
complete local ring of universe `u` with residue field `k`, not merely
into the `R` it was asked about.  That costs the proof nothing (the
argument never uses anything about `R` beyond the two hypotheses, so it is
simply run under a `∀ A`), and it is what carries the `𝒪`-algebra
structure down to the deformation rings; see `IsCohenCoefficients` above
for the two coefficient rings this excludes and why the presentation
leaves are false without it. -/
theorem exists_taylorWilesCoefficients_ringHom.{u, v}
    {R : Type u} [CommRing R] [IsLocalRing R]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal R) R)
    {k : Type v} [Field k] [Finite k] {π : R →+* k}
    (hπ : Function.Surjective π) :
    ∃ coeff : TaylorWilesCoefficients,
      IsCohenCoefficients.{u, v} coeff k ∧
      ∃ ι : coeff.carrier →+* R, Function.Surjective (π.comp ι) := by
  -- the residue characteristic, and its primality
  haveI : CharP k (ringChar k) := ringChar.charP k
  haveI hfp : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k (ringChar k)⟩
  set p := ringChar k with hpdef
  -- a `Type 0` model of `k`: `TaylorWilesCoefficients.carrier` is a `Type`,
  -- and a finite field is countable hence `Small.{0}`
  letI e : Shrink.{0} k ≃+* k := Shrink.ringEquiv.{0, _} k
  haveI : Finite (Shrink.{0} k) := Finite.of_equiv k e.symm.toEquiv
  haveI : CharP (Shrink.{0} k) p :=
    charP_of_injective_ringHom (f := (e.symm : k →+* Shrink.{0} k)) e.symm.injective p
  haveI : PerfectRing (Shrink.{0} k) p := PerfectRing.ofFiniteOfIsReduced p _
  -- Cohen's map, for an ARBITRARY complete local `A` with residue field `k`;
  -- `R` is then just one instance of it.
  have hcohen : IsCohenCoefficients.{u, v}
      (TaylorWilesCoefficients.wittVector p (Shrink.{0} k)) k := by
    intro A _ _ hA πA hπA
    obtain ⟨ι, hι⟩ := exists_ringHom_wittVector_of_isAdicComplete hA
      (p := p) (k := Shrink.{0} k) (π := (e.symm : k →+* Shrink.{0} k).comp πA)
      (e.symm.surjective.comp hπA)
    refine ⟨ι, fun y => ?_⟩
    obtain ⟨x, hx⟩ := WittVector.constantCoeff_surjective p (e.symm y)
    refine ⟨x, ?_⟩
    have hx' : (e.symm : k →+* Shrink.{0} k) (πA (ι x)) = e.symm y := by
      rw [show (e.symm : k →+* Shrink.{0} k) (πA (ι x))
          = (((e.symm : k →+* Shrink.{0} k).comp πA).comp ι) x from rfl, hι, hx]
    exact e.symm.injective hx'
  exact ⟨_, hcohen, hcohen R hcomplete π hπ⟩

/-! ### The ABSOLUTELY UNRAMIFIED refinement, for the `F`-level bottom leaf

`exists_taylorWilesCoefficients_ringHom` above returns the bundle and its Cohen
property, and `TaylorWilesCoefficients` records neither `𝔪_𝒪 = (p)` nor
precompleteness — the first because the bundle is deliberately not a
characterisation, the second because the `ℚ`-level Nakayama endgame in
`Modularity/Patching.lean` gets its completeness from the presentation ring
rather than from `𝒪`.  Both are FREE for the witness that theorem actually
returns, `𝕎 k`, and the `F`-level bottom leaf
`exists_hilbertBottomCoeffRingHom` (`HardlyRamified/HilbertModularity.lean`)
needs exactly them.  So they are exported here rather than reproved there. -/

/-- **Cohen's coefficient ring, ABSOLUTELY UNRAMIFIED** (PROVEN 2026-07-31; the
same statement and the same proof as `exists_taylorWilesCoefficients_ringHom`
above, with the two extra conclusions that `𝕎 k` satisfies by construction).

Beyond that theorem's conclusions this asserts

* `𝔪_𝒪 = (p)` — `𝒪` is absolutely unramified.  This is
  `wittVector_maximalIdeal_eq_span_p` above, and it is the clause that (together
  with `TaylorWilesCoefficients.exists_isRegular_maximalIdeal`, which makes `𝒪`
  a DVR, and the residue surjectivity, which forces the residue field to be `k`)
  pins `𝒪 = W(k)` up to isomorphism.  A consumer that omits it is quantified
  over ramified coefficient rings such as `ℤ_[p][π]/(π² − p)`, at which the
  presentation statements below it are FALSE — see the FALSITY AUDIT of
  `exists_auxDeformationPresSurjection` in `Modularity/Patching.lean`;
* `IsPrecomplete 𝔪_𝒪 𝒪` — mathlib's `WittVector.isAdicCompleteIdealSpanP`
  transported along the previous clause.  It is what the complete-Nakayama
  endgame of a presentation `𝒪⟦x₁, …, x_q⟧ ↠ R` needs of the COEFFICIENT ring;
  `ℤ_(ℓ) ↪ ℤ_[ℓ]` is the standard witness that it cannot be dropped.

Note `p` is an EXPLICIT argument here where the theorem above computes it as
`ringChar k`: a consumer with a prime `ℓ` in hand and a residue field known to
have characteristic `ℓ` wants the conclusion stated at `ℓ`, not at `ringChar k`,
and `[CharP k p]` is how it says so.  Deriving `[CharP k p]` costs a consumer
nothing whenever `k` is a finite residue field of a `ℤ_[p]`-algebra — see
`natCast_eq_zero_of_finite_algebra` in `HardlyRamified/HilbertModularity.lean`.

CIRCULARITY GUARD: as for `exists_taylorWilesCoefficients_ringHom` — no `ρbar`,
no deformation functor, no Hecke algebra occurs in the statement. -/
theorem exists_taylorWilesCoefficients_ringHom_unramified.{u, v}
    {R : Type u} [CommRing R] [IsLocalRing R]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal R) R)
    {k : Type v} [Field k] [Finite k] {π : R →+* k}
    (hπ : Function.Surjective π)
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    ∃ coeff : TaylorWilesCoefficients,
      IsLocalRing.maximalIdeal coeff.carrier
          = Ideal.span {(p : coeff.carrier)} ∧
      IsPrecomplete (IsLocalRing.maximalIdeal coeff.carrier) coeff.carrier ∧
      IsCohenCoefficients.{u, v} coeff k ∧
      ∃ ι : coeff.carrier →+* R, Function.Surjective (π.comp ι) := by
  -- a `Type 0` model of `k`: `TaylorWilesCoefficients.carrier` is a `Type`,
  -- and a finite field is countable hence `Small.{0}`
  letI e : Shrink.{0} k ≃+* k := Shrink.ringEquiv.{0, _} k
  haveI : Finite (Shrink.{0} k) := Finite.of_equiv k e.symm.toEquiv
  haveI : CharP (Shrink.{0} k) p :=
    charP_of_injective_ringHom (f := (e.symm : k →+* Shrink.{0} k)) e.symm.injective p
  haveI : PerfectRing (Shrink.{0} k) p := PerfectRing.ofFiniteOfIsReduced p _
  -- Cohen's map, for an ARBITRARY complete local `A` with residue field `k`
  have hcohen : IsCohenCoefficients.{u, v}
      (TaylorWilesCoefficients.wittVector p (Shrink.{0} k)) k := by
    intro A _ _ hA πA hπA
    obtain ⟨ι, hι⟩ := exists_ringHom_wittVector_of_isAdicComplete hA
      (p := p) (k := Shrink.{0} k) (π := (e.symm : k →+* Shrink.{0} k).comp πA)
      (e.symm.surjective.comp hπA)
    refine ⟨ι, fun y => ?_⟩
    obtain ⟨x, hx⟩ := WittVector.constantCoeff_surjective p (e.symm y)
    refine ⟨x, ?_⟩
    have hx' : (e.symm : k →+* Shrink.{0} k) (πA (ι x)) = e.symm y := by
      rw [show (e.symm : k →+* Shrink.{0} k) (πA (ι x))
          = (((e.symm : k →+* Shrink.{0} k).comp πA).comp ι) x from rfl, hι, hx]
    exact e.symm.injective hx'
  -- `𝔪 = (p)` and precompleteness, both for `𝕎 (Shrink.{0} k)`
  have hmax : _root_.IsLocalRing.maximalIdeal (WittVector p (Shrink.{0} k))
      = Ideal.span {(p : WittVector p (Shrink.{0} k))} :=
    wittVector_maximalIdeal_eq_span_p p (Shrink.{0} k)
  -- NOTE the `.toIsPrecomplete` PROJECTION rather than instance search: the goal
  -- is stated at `coeff.carrier`, which is only DEFEQ to `WittVector p (Shrink.{0} k)`,
  -- and typeclass resolution does not unfold a structure projection.
  have hac : IsAdicComplete
      (_root_.IsLocalRing.maximalIdeal (WittVector p (Shrink.{0} k)))
      (WittVector p (Shrink.{0} k)) := by
    rw [hmax]; infer_instance
  exact ⟨TaylorWilesCoefficients.wittVector p (Shrink.{0} k), hmax,
    hac.toIsPrecomplete, hcohen, hcohen R hcomplete π hπ⟩

end GaloisRepresentation.Modularity
