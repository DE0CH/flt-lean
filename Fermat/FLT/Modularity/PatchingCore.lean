/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib.Algebra.CharP.Basic
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.Data.Finsupp.Option
public import Mathlib.Data.Nat.Choose.Dvd
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Depth.Rees
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.MvPowerSeries.PiTopology
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.PowerSeries.Ideal
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.Regular.Flat
public import Mathlib.RingTheory.Regular.Free
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.Algebra.Module.Compact
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Fermat.FLT.Mathlib.RingTheory.AdicCompletion.Finite
public import Fermat.FLT.Mathlib.RingTheory.PowerSeries.AdicComplete
-- `Algebra.TopologicallyFG`, a field of `TaylorWilesCoefficients`. This
-- vendored module imports only mathlib, so it is safe upstream of
-- `HardlyRamified/HilbertModularity.lean`.
public import Fermat.FLT.Modularity.PatchingVendored.TopologicallyFG
-- The vendored patching engine (ultraproduct / inverse limit), consumed by
-- `nonempty_patchedModule_of_patchingData` in the hoisted section below.
-- Its `Fermat`-import closure is exactly the ten `PatchingVendored/` modules
-- and contains neither this module nor `HilbertModularity.lean`, which is
-- what makes the hoist acyclic.
public import Fermat.FLT.Modularity.PatchingVendored.System
-- `Infinite ℤ_[p]` (through `CharZero`), used by `charP_of_ringHom_padicInt`.
public import Mathlib.Algebra.CharZero.Infinite

/-!
# Taylor–Wiles patching: the BASE-FIELD-INDEPENDENT core

This module carries the part of the Taylor–Wiles patching endgame that
mentions **no base field at all**: the `PatchedModule` interface, the
Auslander–Buchsbaum development that makes a patched module free over
`R_∞ = ℤ_p[[x₁, …, x_q]]`, and the faithfulness assembly
`PatchedModule.injective` that reads injectivity of the classifying map off
that freeness.

## Why it lives in its own module (2026-07-26)

All of this was written inside `Fermat/FLT/Modularity/Patching.lean`, which is
the `ℚ`-level modularity-lifting development.  The `R_F = T_F` theorem over a
totally real field `F`
(`Fermat/FLT/GaloisRepresentation/HardlyRamified/HilbertModularity.lean`,
`injective_classifyingMap_hilbertHeckeDatum`) needs *exactly this material and
nothing else* from `Patching.lean` — and it cannot import it, because
`Patching.lean` is DOWNSTREAM: it imports
`HardlyRamified/Deformation.lean`, which `public import`s
`HilbertModularity.lean`.

Duplicating 990 lines of commutative algebra into the Hilbert module was the
alternative, and `HilbertModularity.lean` already carries eight local copies of
downstream helpers for exactly this reason.  So the block was HOISTED here
instead: `Patching.lean` and `HilbertModularity.lean` both import it, and there
is one copy.

**Nothing in this module mentions `ℚ`, a number field, a Galois
representation, or a deformation condition.**  `PatchedModule p ψ` is a
statement about a ring map `ψ : Runiv →+* T` and a module over a power series
ring; that is the whole reason the hoist is possible and the reason it is
correct to share it between the two base fields.  The material moved verbatim,
declaration for declaration, with no change to any statement or proof.

## Contents

* `TaylorWilesCoefficients` — the coefficient ring `𝒪` of the presentation
  `R_∞ = 𝒪[[x₁, …, x_q]]` (classically `W(k)`), bundled with the properties the
  proven half of the stack consumes.
* `PatchedModule` — the limit object of the patching process, recorded with
  exactly the fields the injectivity assembly consumes.
* `section AuslanderBuchsbaum` — the dimension induction
  (`free_of_isRegular_of_ofList_eq_maximalIdeal`) over the Rees theorem and
  Davis coset prime avoidance, the `PowerSeriesCurry` section identifying
  `A[[(xᵢ)_{i : Option σ}]]` with `(A[[(xᵢ)_{i : σ}]])⟦X⟧`, and the two
  concrete power-series leaves it is instantiated at, ending in
  `free_of_isRegular_mvPowerSeries` (Diamond, Invent. Math. 128 (1997),
  Thm. 2.4).
* `PatchedModule.injective` — the patched faithfulness assembly.

## References

* Taylor–Wiles, *Ring-theoretic properties of certain Hecke algebras*,
  Ann. of Math. 141 (1995).
* Diamond, *The Taylor–Wiles construction and multiplicity one*,
  Invent. Math. 128 (1997), Thms. 2.1 and 2.4.
* Bruns–Herzog, *Cohen–Macaulay rings*, Thms. 1.3.3 and 2.2.7.
-/

@[expose] public section

namespace GaloisRepresentation.Modularity

/-- **The coefficient ring of the Taylor–Wiles presentation** (added
2026-07-26 as the repair of the residual-field obstruction; see the
`REPAIR` block of `exists_taylorWilesBottomLevel` below for the full
derivation and the decision record).

Classically the auxiliary deformation rings `R_{Q_n}` of the
Taylor–Wiles method are quotients of `𝒪[[x₁, …, x_q]]` for
`𝒪 = W(k)`, the Witt vectors of the residual field — NOT of
`ℤ_p[[x₁, …, x_q]]`.  Hardcoding `ℤ_[p]` in the presentation role is
correct exactly when `k = 𝔽_p`, and in general it makes the interface
UNSATISFIABLE: a surjection `ℤ_p[[x]] ↠ R ↠ R_univ ↠ k` forces
`k ≃+* ZMod p` (the maximal ideal of a power series ring over a local
ring is the preimage of the base's maximal ideal, so the composite
already factors through `ℤ_[p] ↠ k`).

This bundles the coefficient ring together with exactly the properties
the PROVEN half of the patching stack consumes, so that the sorried
arithmetic leaves may CHOOSE it (classically `WittVector p k`) instead
of being handed `ℤ_[p]`.  Bundling rather than ten separate binders is
deliberate: `TaylorWilesLevel`/`TaylorWilesLevelRaw` take it as a
single parameter, and the two arithmetic leaves produce a single
existential witness.

The carrier is a `Type` (universe `0`) for the same reason the tower's
other data is: every intended object is a countable pro-finitely
presented `ℤ_p`-algebra — `W(k)` for finite `k` is countable — so a
universe-`0` copy always exists, and this keeps the whole patching
stack universe-monomorphic in the coefficient argument.

Where each field is consumed: `isLocalRing`/`isNoetherianRing` and
`exists_isRegular_maximalIdeal` feed the Auslander–Buchsbaum endgame
(`free_of_isRegular_mvPowerSeries`, through
`exists_isRegular_ofList_eq_maximalIdeal_mvPowerSeries` — the last
field says exactly that `𝒪` is a DVR, i.e. that `𝒪[[x₁, …, x_q]]` is
regular of dimension `q + 1`); `finite_residueField`,
`compactSpace` and `topologicallyFG` feed the vendored patching
construction (`PatchingAlgebra.lift` and the uniform-rank bounds) at
the presentation ring.  All hold for `W(k)` with `k` a finite
field. -/
structure TaylorWilesCoefficients where
  /-- The underlying ring `𝒪`. -/
  carrier : Type
  [commRing : CommRing carrier]
  [topologicalSpace : TopologicalSpace carrier]
  [isTopologicalRing : IsTopologicalRing carrier]
  [compactSpace : CompactSpace carrier]
  [t2Space : T2Space carrier]
  [totallyDisconnectedSpace : TotallyDisconnectedSpace carrier]
  [isLocalRing : IsLocalRing carrier]
  [isNoetherianRing : IsNoetherianRing carrier]
  /-- The residue field of `𝒪` is finite (classically it is `k`). -/
  finite_residueField : Finite (carrier ⧸ IsLocalRing.maximalIdeal carrier)
  /-- `𝒪` is topologically finitely generated over `ℤ` (classically
  `W(k) = ℤ_p[ζ]` is the closure of `ℤ[ζ]`). -/
  topologicallyFG : Algebra.TopologicallyFG ℤ carrier
  /-- `𝔪_𝒪` is generated by a single `𝒪`-regular element — `𝒪` is a
  discrete valuation ring.  This is what makes `𝒪[[x₁, …, x_q]]`
  regular local of dimension `q + 1`, the input to the
  Auslander–Buchsbaum step. -/
  exists_isRegular_maximalIdeal : ∃ ts : List carrier, ts.length = 0 + 1 ∧
    RingTheory.Sequence.IsRegular carrier ts ∧
    Ideal.ofList ts = IsLocalRing.maximalIdeal carrier

attribute [instance] TaylorWilesCoefficients.commRing
  TaylorWilesCoefficients.topologicalSpace
  TaylorWilesCoefficients.isTopologicalRing
  TaylorWilesCoefficients.compactSpace
  TaylorWilesCoefficients.t2Space
  TaylorWilesCoefficients.totallyDisconnectedSpace
  TaylorWilesCoefficients.isLocalRing
  TaylorWilesCoefficients.isNoetherianRing
  TaylorWilesCoefficients.finite_residueField
  TaylorWilesCoefficients.topologicallyFG

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
  /-- The coefficient ring `𝒪` of the presentation `R_∞ = 𝒪[[x₁, …, x_q]]`
  (classically `W(k)`; see `TaylorWilesCoefficients`).  Hardcoding
  `ℤ_[p]` here was the residual-field obstruction repaired
  2026-07-26. -/
  coeff : TaylorWilesCoefficients
  /-- The patched module `M_∞`. -/
  Minf : Type v
  [addCommGroupMinf : AddCommGroup Minf]
  [moduleMinf : Module (MvPowerSeries (Fin q) coeff.carrier) Minf]
  /-- `M_∞` is finite over `R_∞` (patched from module-finiteness at
  every level). -/
  finiteMinf : Module.Finite (MvPowerSeries (Fin q) coeff.carrier) Minf
  /-- The Taylor–Wiles depth input: an `M_∞`-regular sequence of
  length `q + 1` inside the maximal ideal of `R_∞` (the image of the
  maximal regular sequence of `Λ_∞ = ℤ_p[[S₁, …, S_q]]`, over which
  `M_∞` is finite free by the Taylor–Wiles freeness lemma). -/
  exists_isRegular : ∃ rs : List (MvPowerSeries (Fin q) coeff.carrier),
    rs.length = q + 1 ∧
    (∀ x ∈ rs, x ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin q) coeff.carrier)) ∧
    RingTheory.Sequence.IsRegular Minf rs
  /-- The patching surjection `R_∞ ↠ R_univ`. -/
  toRuniv : MvPowerSeries (Fin q) coeff.carrier →+* Runiv
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
  proj_smul : ∀ (x : MvPowerSeries (Fin q) coeff.carrier) (m : Minf),
    proj (x • m) = ψ (toRuniv x) • proj m
  /-- The kernel of the bottom identification is exactly the
  augmentation submodule `𝔞·M_∞`, `𝔞 = ker(R_∞ ↠ R_univ)` (this
  inclusion; the reverse follows from `proj_smul`). -/
  mem_smul_top_of_proj_eq_zero : ∀ m : Minf, proj m = 0 →
    m ∈ RingHom.ker toRuniv •
      (⊤ : Submodule (MvPowerSeries (Fin q) coeff.carrier) Minf)

/-! #### The Auslander–Buchsbaum machinery behind patching leaf 3

`free_of_isRegular_mvPowerSeries` (Diamond 1997, Thm. 2.4) is PROVEN
below (2026-07-24) by a dimension induction over Noetherian local
rings — the Auslander–Buchsbaum instance the patching endgame needs,
founded on two mathlib pillars that the earlier audit note missed
(the pin DOES carry a depth layer): the **Rees theorem**
(`ModuleCat.exists_isRegular_tfae`, existence of length-`n`
`M`-regular sequences in `I` ↔ vanishing of `Ext^{<n}(R/I, M)`) and
the **Nakayama dévissage** `Module.free_quotSMulTop_iff_free`
(freeness lifts through the quotient by an `M`-regular element of the
Jacobson radical).  The induction (theorem
`free_of_isRegular_of_ofList_eq_maximalIdeal`): if the maximal ideal
of `R` is SPANNED by a regular sequence `ts` of length `n` — the
statement-level form of "`R` is regular local of dimension `n`" — and
the finite module `M` carries an `M`-regular sequence of length `n`
in the maximal ideal ("depth `M ≥ n`"), then `M` is free.  Step: pick
by Davis coset prime avoidance (`exists_add_notMem_of_forall_not_le`)
a replacement generator `x = t₀ + y`, `y ∈ (ts.tail)`, avoiding every
associated prime of `M` (legitimate because `𝔪 ∉ Ass M`: the head of
`rs` is `M`-regular); then `x` is `M`-regular
(`isSMulRegular_of_forall_notMem_associatedPrimes`), `x :: ts.tail`
is again a spanning regular sequence (permutation invariance
`IsLocalRing.isRegular_of_perm` plus invariance of the last element
modulo the ideal of the earlier ones), `R/(x)` is again a
"power-series-like" Noetherian local ring with spanning regular
sequence of length `n - 1`, the depth hypothesis descends to `M/xM`
by the Rees theorem run through the `Ext` long exact sequence of
`0 → M → M → M/xM → 0` (`exists_isRegular_quotSMulTop_of_isSMulRegular`),
and the induction hypothesis plus the dévissage conclude.  The base
case `n = 0` is a field.  Two concrete power-series leaves feed the
instantiation and stay sorried below: Noetherianity
(`isNoetherianRing_mvPowerSeries`) and the regular system of
parameters `(p, x₁, …, x_q)` spanning the maximal ideal
(`exists_isRegular_ofList_eq_maximalIdeal_mvPowerSeries`). -/

section AuslanderBuchsbaum

open RingTheory.Sequence _root_.IsLocalRing Pointwise CategoryTheory Abelian Limits

/-- **Coset prime avoidance** (E. Davis; Kaplansky, *Commutative
Rings*, Thm. 124; PROVEN): if none of the finitely many primes
`P ∈ ps` contains the ideal `(x) + J`, then some element of the coset
`x + J` avoids every `P ∈ ps`.  Used by the Auslander–Buchsbaum
induction to replace the head generator `t₀` of the maximal ideal by
a congruent-mod-tail generator that is regular for the module.
Standard induction on `ps`: primes containing `J` and primes
contained in another listed prime may be discarded; in the remaining
antichain case, if the avoider `y₁` for `ps \ {P₀}` fails at `P₀`,
correct it by `z·∏ a_Q` with `z ∈ J \ P₀` and `a_Q ∈ Q \ P₀`. -/
theorem exists_add_notMem_of_forall_not_le.{u} {R : Type u} [CommRing R]
    (ps : Finset (Ideal R)) (x : R) (J : Ideal R)
    (hps : ∀ P ∈ ps, P.IsPrime) (h : ∀ P ∈ ps, ¬ (Ideal.span {x} ⊔ J ≤ P)) :
    ∃ y ∈ J, ∀ P ∈ ps, x + y ∉ P := by
  classical
  induction ps using Finset.strongInduction with
  | _ ps IH => ?_
  by_cases hJ : ∃ P ∈ ps, J ≤ P
  · obtain ⟨P, hP, hJP⟩ := hJ
    obtain ⟨y, hyJ, hy⟩ := IH (ps.erase P) (Finset.erase_ssubset hP)
      (fun Q hQ => hps Q (Finset.mem_of_mem_erase hQ))
      (fun Q hQ => h Q (Finset.mem_of_mem_erase hQ))
    refine ⟨y, hyJ, fun Q hQ hmem => ?_⟩
    rcases eq_or_ne Q P with rfl | hne
    · refine h Q hP (sup_le ((Ideal.span_singleton_le_iff_mem _).mpr ?_) hJP)
      simpa using Q.sub_mem hmem (hJP hyJ)
    · exact hy Q (Finset.mem_erase.mpr ⟨hne, hQ⟩) hmem
  push Not at hJ
  by_cases hchain : ∃ P ∈ ps, ∃ Q ∈ ps, P ≠ Q ∧ P ≤ Q
  · obtain ⟨P, hP, Q, hQ, hne, hle⟩ := hchain
    obtain ⟨y, hyJ, hy⟩ := IH (ps.erase P) (Finset.erase_ssubset hP)
      (fun Q' hQ' => hps Q' (Finset.mem_of_mem_erase hQ'))
      (fun Q' hQ' => h Q' (Finset.mem_of_mem_erase hQ'))
    refine ⟨y, hyJ, fun Q' hQ' hmem => ?_⟩
    rcases eq_or_ne Q' P with rfl | hne'
    · exact hy Q (Finset.mem_erase.mpr ⟨hne.symm, hQ⟩) (hle hmem)
    · exact hy Q' (Finset.mem_erase.mpr ⟨hne', hQ'⟩) hmem
  push Not at hchain
  rcases Finset.eq_empty_or_nonempty ps with rfl | ⟨P₀, hP₀⟩
  · exact ⟨0, J.zero_mem, by simp⟩
  obtain ⟨y₁, hy₁J, hy₁⟩ := IH (ps.erase P₀) (Finset.erase_ssubset hP₀)
    (fun Q hQ => hps Q (Finset.mem_of_mem_erase hQ))
    (fun Q hQ => h Q (Finset.mem_of_mem_erase hQ))
  by_cases hx₀ : x + y₁ ∈ P₀
  · haveI hP₀p : P₀.IsPrime := hps P₀ hP₀
    obtain ⟨z, hzJ, hzP₀⟩ := SetLike.not_le_iff_exists.mp (hJ P₀ hP₀)
    have hpick : ∀ Q ∈ ps.erase P₀, ∃ a, a ∈ Q ∧ a ∉ P₀ := by
      intro Q hQ
      obtain ⟨hne, hQps⟩ := Finset.mem_erase.mp hQ
      exact SetLike.not_le_iff_exists.mp (fun hle => hchain Q hQps P₀ hP₀ hne hle)
    choose a haQ haP using hpick
    set w₀ : R := ∏ Q ∈ (ps.erase P₀).attach, a Q.1 Q.2 with hw₀def
    have hw₀Q : ∀ Q ∈ ps.erase P₀, w₀ ∈ Q := by
      intro Q hQ
      rw [hw₀def, ← Finset.mul_prod_erase _ _ (Finset.mem_attach _ ⟨Q, hQ⟩)]
      exact Ideal.mul_mem_right _ _ (haQ Q hQ)
    have hprodNotMem : w₀ ∉ P₀ := fun hmem => by
      obtain ⟨⟨Q, hQ⟩, -, hmemQ⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
      exact haP Q hQ hmemQ
    refine ⟨y₁ + z * w₀, J.add_mem hy₁J (J.mul_mem_right _ hzJ), fun Q hQ hmem => ?_⟩
    by_cases hne : Q = P₀
    · have hw : z * w₀ ∈ P₀ := by
        have := P₀.sub_mem (hne ▸ hmem) hx₀
        simpa [add_sub_add_left_eq_sub] using this
      exact (hP₀p.mem_or_mem hw).elim hzP₀ hprodNotMem
    · have hwQ : z * w₀ ∈ Q := Q.mul_mem_left z (hw₀Q Q (Finset.mem_erase.mpr ⟨hne, hQ⟩))
      have : x + y₁ ∈ Q := by
        have := Q.sub_mem hmem hwQ
        simpa [← add_assoc] using this
      exact hy₁ Q (Finset.mem_erase.mpr ⟨hne, hQ⟩) this
  · refine ⟨y₁, hy₁J, fun Q hQ => ?_⟩
    rcases eq_or_ne Q P₀ with rfl | hne
    · exact hx₀
    · exact hy₁ Q (Finset.mem_erase.mpr ⟨hne, hQ⟩)

/-- **Avoiding all associated primes gives a regular element**
(PROVEN): over a Noetherian ring the zero-divisors of a module lie in
the union of its associated primes — if `x·z = 0` with `z ≠ 0` then
`ann(z)` sits inside an associated prime
(`exists_le_isAssociatedPrime_of_isNoetherianRing`). -/
theorem isSMulRegular_of_forall_notMem_associatedPrimes.{u, w} {R : Type u} [CommRing R]
    [IsNoetherianRing R] {N : Type w} [AddCommGroup N] [Module R N] {x : R}
    (h : ∀ P ∈ associatedPrimes R N, x ∉ P) : IsSMulRegular N x := by
  intro a b hab
  by_contra hne
  have hz : x • (a - b) = 0 := by
    simp only [smul_sub, sub_eq_zero]
    exact hab
  obtain ⟨P, hP, hle⟩ :=
    exists_le_isAssociatedPrime_of_isNoetherianRing R (a - b) (sub_ne_zero.mpr hne)
  exact h P hP (hle (by rw [Submodule.mem_colon_singleton]; simpa using hz))

/-- **Positive depth pushes the maximal ideal off `Ass N`** (PROVEN):
if some element of the maximal ideal acts regularly on `N`, no
associated prime of `N` can contain the maximal ideal (an associated
prime is the radical of the annihilator of a nonzero element, and a
power of the regular element would kill that element).  This is the
legitimacy check for prime avoidance against `Ass N` inside the
maximal ideal. -/
theorem not_maximalIdeal_le_of_mem_associatedPrimes.{u, w} {R : Type u} [CommRing R]
    [IsLocalRing R] {N : Type w} [AddCommGroup N] [Module R N]
    {P : Ideal R} (hP : P ∈ associatedPrimes R N)
    {r : R} (hr : r ∈ maximalIdeal R) (hreg : IsSMulRegular N r) :
    ¬ maximalIdeal R ≤ P := by
  intro hle
  obtain ⟨hprime, z, hz⟩ := hP
  have hzne : z ≠ 0 := by
    rintro rfl
    rw [Submodule.colon_singleton_zero, Ideal.radical_top] at hz
    exact hprime.ne_top hz
  have hrP : r ∈ P := hle hr
  rw [hz, Ideal.mem_radical_iff] at hrP
  obtain ⟨k, hk⟩ := hrP
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at hk
  exact hzne ((hreg.pow k) (by simpa using hk))

/-- **Depth descent along a regular element** (PROVEN; the classical
`depth (M/xM) = depth M − 1`, in existence form): if the finite
module `M` over the Noetherian local `R` carries an `M`-regular
sequence `rs` inside the maximal ideal and `x ∈ 𝔪` is `M`-regular,
then `M/xM` carries a regular sequence of length `|rs| − 1` inside
the maximal ideal.  Both directions of mathlib's Rees theorem
(`ModuleCat.exists_isRegular_tfae`) are used: `rs` gives
`Ext^{<n}(k, M) = 0`; the `Ext(k, −)` long exact sequence of
`0 → M →ₓ M → M/xM → 0` (via `Ext.covariant_sequence_exact₃'` on
`IsSMulRegular.smulShortComplex_shortExact`) kills
`Ext^{<n−1}(k, M/xM); Rees back-translates into a regular sequence on
`M/xM`. -/
theorem exists_isRegular_quotSMulTop_of_isSMulRegular.{u, w} {R : Type u} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] [Small.{w} R]
    {M : Type w} [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    {rs : List R} (hreg : RingTheory.Sequence.IsRegular M rs)
    (hmem : ∀ r ∈ rs, r ∈ maximalIdeal R)
    {x : R} (hx : x ∈ maximalIdeal R) (hxreg : IsSMulRegular M x) :
    ∃ rs' : List R, rs'.length = rs.length - 1 ∧
      (∀ r ∈ rs', r ∈ maximalIdeal R) ∧
      RingTheory.Sequence.IsRegular (QuotSMulTop x M) rs' := by
  have smul_lt : maximalIdeal R • (⊤ : Submodule R M) < ⊤ :=
    lt_of_le_of_ne le_top
      (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
        (le_trans (maximalIdeal_le_jacobson _) (Ideal.jacobson_mono bot_le))).symm
  haveI : Nontrivial (QuotSMulTop x M) :=
    nontrivial_quotSMulTop_of_mem_maximalIdeal M hx
  have smul_lt' : maximalIdeal R • (⊤ : Submodule R (QuotSMulTop x M)) < ⊤ :=
    lt_of_le_of_ne le_top
      (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
        (le_trans (maximalIdeal_le_jacobson _) (Ideal.jacobson_mono bot_le))).symm
  have tfae₁ := ModuleCat.exists_isRegular_tfae (maximalIdeal R) rs.length
    (ModuleCat.of R M) smul_lt
  have h4 : ∃ rs₀ : List R, rs₀.length = rs.length ∧ (∀ r ∈ rs₀, r ∈ maximalIdeal R) ∧
      RingTheory.Sequence.IsRegular (ModuleCat.of R M) rs₀ := ⟨rs, rfl, hmem, hreg⟩
  have hext := (tfae₁.out 3 1).mp h4
  have hxreg' : IsSMulRegular (ModuleCat.of R M) x := hxreg
  have hext' : ∀ i < rs.length - 1, Subsingleton
      (Ext (ModuleCat.of R (Shrink.{w} (R ⧸ maximalIdeal R)))
        (ModuleCat.of R (QuotSMulTop x M)) i) := by
    intro i hi
    have zero1 := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (hext i (by omega))
    have zero2 := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (hext (i + 1) (by omega))
    exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
      ((Ext.covariant_sequence_exact₃' _ hxreg'.smulShortComplex_shortExact) i (i + 1) rfl)
      (zero1.eq_zero_of_src _) (zero2.eq_zero_of_tgt _)
  have tfae₂ := ModuleCat.exists_isRegular_tfae (maximalIdeal R) (rs.length - 1)
    (ModuleCat.of R (QuotSMulTop x M)) smul_lt'
  exact (tfae₂.out 1 3).mp hext'

/-- **The abstract Auslander–Buchsbaum instance** (PROVEN; Diamond
1997, Thm. 2.4 in spanning-regular-sequence form): over a Noetherian
local ring whose maximal ideal is SPANNED by a regular sequence of
length `n` (the statement-level form of "regular local of dimension
`n`"), any finite module carrying a regular sequence of length `n`
inside the maximal ideal ("depth ≥ dim") is free.  Dimension
induction over `(R, M) ↝ (R/(x), M/xM)`; see the section header for
the full architecture. -/
theorem free_of_isRegular_of_ofList_eq_maximalIdeal.{u, w} (n : ℕ)
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Small.{w} R]
    {M : Type w} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (ts : List R) (hts : RingTheory.Sequence.IsRegular R ts) (htslen : ts.length = n)
    (htsspan : Ideal.ofList ts = maximalIdeal R)
    (rs : List R) (hrs : RingTheory.Sequence.IsRegular M rs) (hrslen : rs.length = n)
    (hrsmem : ∀ r ∈ rs, r ∈ maximalIdeal R) :
    Module.Free R M := by
  induction n generalizing R M with
  | zero =>
    -- the base case: `𝔪 = (∅) = ⊥`, so `R` is a field
    have hbot : maximalIdeal R = ⊥ := by
      rw [← htsspan, List.length_eq_zero_iff.mp htslen, Ideal.ofList_nil]
    have hfield : IsField R := IsLocalRing.isField_iff_maximalIdeal_eq.mpr hbot
    letI := hfield.toField
    exact Module.Free.of_divisionRing R M
  | succ n IH =>
    rcases subsingleton_or_nontrivial M with _hM | _hM
    · infer_instance
    obtain ⟨t₀, ts', rfl⟩ : ∃ a l, ts = a :: l := by
      cases ts with
      | nil => simp at htslen
      | cons a l => exact ⟨a, l, rfl⟩
    obtain ⟨r₀, rs', rfl⟩ : ∃ a l, rs = a :: l := by
      cases rs with
      | nil => simp at hrslen
      | cons a l => exact ⟨a, l, rfl⟩
    have hmem_ts : ∀ t ∈ t₀ :: ts', t ∈ maximalIdeal R := fun t ht =>
      htsspan ▸ Ideal.subset_span ht
    have hr₀ : IsSMulRegular M r₀ := ((isRegular_cons_iff _ _ _).mp hrs).1
    have hr₀m : r₀ ∈ maximalIdeal R := hrsmem r₀ List.mem_cons_self
    -- Davis avoidance: replace `t₀` by `x = t₀ + y`, `y ∈ (ts')`, avoiding
    -- every associated prime of `M` (all of which miss `𝔪 = (t₀) ⊔ (ts')`
    -- because `r₀ ∈ 𝔪` is `M`-regular)
    have hfin : (associatedPrimes R M).Finite := associatedPrimes.finite R M
    obtain ⟨y, hyJ, hy⟩ := exists_add_notMem_of_forall_not_le hfin.toFinset t₀
      (Ideal.ofList ts')
      (fun P hP => (hfin.mem_toFinset.mp hP).1)
      (fun P hP hle => by
        rw [← Ideal.ofList_cons, htsspan] at hle
        exact not_maximalIdeal_le_of_mem_associatedPrimes
          (hfin.mem_toFinset.mp hP) hr₀m hr₀ hle)
    set x := t₀ + y with hxdef
    have hxm : x ∈ maximalIdeal R := by
      apply (maximalIdeal R).add_mem (hmem_ts t₀ List.mem_cons_self)
      rw [← htsspan, Ideal.ofList_cons]
      exact Ideal.mem_sup_right hyJ
    have hxM : IsSMulRegular M x := isSMulRegular_of_forall_notMem_associatedPrimes
      (fun P hP => hy P (hfin.mem_toFinset.mpr hP))
    -- `x :: ts'` is again a spanning regular sequence: permute `t₀` to the
    -- end, exchange it there for the congruent-mod-`(ts')` element `x`,
    -- permute back
    have hperm₁ : RingTheory.Sequence.IsRegular R (ts' ++ [t₀]) :=
      IsLocalRing.isRegular_of_perm hts (List.perm_append_singleton t₀ ts').symm
    have hlastswap : RingTheory.Sequence.IsRegular R (ts' ++ [x]) := by
      refine IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal _ ?_ ?_
      · intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact hmem_ts r (List.mem_cons_of_mem _ hr)
        · rw [List.mem_singleton.mp hr]; exact hxm
      · have hw := hperm₁.toIsWeaklyRegular
        rw [isWeaklyRegular_append_iff] at hw ⊢
        refine ⟨hw.1, ?_⟩
        obtain ⟨-, ht₀q⟩ := hw
        rw [isWeaklyRegular_singleton_iff] at ht₀q ⊢
        have hy0 : ∀ c : R ⧸ (Ideal.ofList ts' • ⊤ : Submodule R R), y • c = 0 := by
          intro c
          obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ c
          rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
          exact Submodule.smul_mem_smul hyJ trivial
        intro a b hab
        refine ht₀q (?_ : t₀ • a = t₀ • b)
        have h1 : x • a = t₀ • a := by rw [hxdef, add_smul, hy0, add_zero]
        have h2 : x • b = t₀ • b := by rw [hxdef, add_smul, hy0, add_zero]
        rw [← h1, ← h2]
        exact hab
    have hxts : RingTheory.Sequence.IsRegular R (x :: ts') :=
      IsLocalRing.isRegular_of_perm hlastswap (List.perm_append_singleton x ts')
    -- the quotient ring `R/(x)` is Noetherian local with maximal ideal
    -- spanned by the images of `ts'`
    haveI hR'nt : Nontrivial (R ⧸ Ideal.span {x}) :=
      Submodule.Quotient.nontrivial_iff.mpr
        (Ideal.span_singleton_ne_top ((IsLocalRing.mem_maximalIdeal x).mp hxm))
    haveI : IsLocalRing (R ⧸ Ideal.span {x}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    haveI : Small.{w} (R ⧸ Ideal.span {x}) :=
      small_of_surjective Ideal.Quotient.mk_surjective
    have hm' : Ideal.map (Ideal.Quotient.mk (Ideal.span {x})) (maximalIdeal R) =
        maximalIdeal (R ⧸ Ideal.span {x}) :=
      IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
    have hQts' : RingTheory.Sequence.IsRegular (QuotSMulTop x R) ts' :=
      ((isRegular_cons_iff _ _ _).mp hxts).2
    have heq : (x • ⊤ : Submodule R R) = (Ideal.span {x} : Ideal R) := by
      rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
    have hRts' : RingTheory.Sequence.IsRegular (R ⧸ Ideal.span {x}) ts' :=
      ((Submodule.quotEquivOfEq _ _ heq).isRegular_congr ts').mp hQts'
    have htss_weak : IsWeaklyRegular (R ⧸ Ideal.span {x})
        (ts'.map (algebraMap R (R ⧸ Ideal.span {x}))) :=
      (isWeaklyRegular_map_algebraMap_iff _ _ ts').mpr hRts'.toIsWeaklyRegular
    have hmem'' : ∀ r ∈ ts'.map (algebraMap R (R ⧸ Ideal.span {x})),
        r ∈ maximalIdeal (R ⧸ Ideal.span {x}) := by
      intro r hr
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hr
      rw [Ideal.Quotient.algebraMap_eq]
      exact hm' ▸ Ideal.mem_map_of_mem _ (hmem_ts t (List.mem_cons_of_mem _ ht))
    have htss : RingTheory.Sequence.IsRegular (R ⧸ Ideal.span {x})
        (ts'.map (algebraMap R (R ⧸ Ideal.span {x}))) :=
      IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal _ hmem'' htss_weak
    have htssspan : Ideal.ofList (ts'.map (algebraMap R (R ⧸ Ideal.span {x}))) =
        maximalIdeal (R ⧸ Ideal.span {x}) := by
      rw [Ideal.Quotient.algebraMap_eq, ← Ideal.map_ofList, ← hm']
      conv_rhs => rw [← htsspan, Ideal.ofList_cons, Ideal.map_sup]
      refine (sup_eq_right.mpr ?_).symm
      rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
      have ht₀y : (Ideal.Quotient.mk (Ideal.span {x})) t₀ = - Ideal.Quotient.mk _ y := by
        rw [eq_neg_iff_add_eq_zero, ← map_add, Ideal.Quotient.eq_zero_iff_mem, ← hxdef]
        exact Ideal.mem_span_singleton_self x
      rw [ht₀y]
      exact neg_mem (Ideal.mem_map_of_mem _ hyJ)
    -- depth descent to `M/xM`, and transfer of the sequence to `R/(x)`
    haveI hMnt' : Nontrivial (QuotSMulTop x M) :=
      nontrivial_quotSMulTop_of_mem_maximalIdeal M hxm
    obtain ⟨rs₂, hrs₂len, hrs₂mem, hrs₂⟩ :=
      exists_isRegular_quotSMulTop_of_isSMulRegular hrs hrsmem hxm hxM
    haveI : Module.Finite (R ⧸ Ideal.span {x}) (QuotSMulTop x M) :=
      Module.Finite.of_restrictScalars_finite R _ _
    have hrs₂w : IsWeaklyRegular (QuotSMulTop x M)
        (rs₂.map (algebraMap R (R ⧸ Ideal.span {x}))) :=
      (isWeaklyRegular_map_algebraMap_iff _ _ rs₂).mpr hrs₂.toIsWeaklyRegular
    have hrs₂mem' : ∀ r ∈ rs₂.map (algebraMap R (R ⧸ Ideal.span {x})),
        r ∈ maximalIdeal (R ⧸ Ideal.span {x}) := by
      intro r hr
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hr
      rw [Ideal.Quotient.algebraMap_eq]
      exact hm' ▸ Ideal.mem_map_of_mem _ (hrs₂mem t ht)
    have hrs₂' : RingTheory.Sequence.IsRegular (QuotSMulTop x M)
        (rs₂.map (algebraMap R (R ⧸ Ideal.span {x}))) :=
      IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal _ hrs₂mem' hrs₂w
    have hts'len : ts'.length = n := by simpa using htslen
    have hrs₂len' : rs₂.length = n := by
      rw [hrs₂len]
      simp only [List.length_cons] at hrslen ⊢
      omega
    -- induction hypothesis downstairs, Nakayama dévissage upstairs
    haveI := Module.finitePresentation_of_finite R M
    refine (Module.free_quotSMulTop_iff_free R M
      (maximalIdeal_le_jacobson ⊥ hxm) hxM).mp ?_
    exact IH (R := R ⧸ Ideal.span {x}) (M := QuotSMulTop x M)
      (ts'.map (algebraMap R _)) htss (by simpa using hts'len) htssspan
      (rs₂.map (algebraMap R _)) hrs₂' (by simpa using hrs₂len') hrs₂mem'

/-! ### The power-series plumbing: currying `A[[x₀, …, xₙ]]`

Both remaining power-series facts — Noetherianity of
`MvPowerSeries (Fin n) A` and the regular system of parameters of
`ℤ_p[[x₁, …, x_q]]` — reduce by induction on the number of variables
to mathlib's ONE-variable theory (`IsNoetherianRing B⟦X⟧`, regularity
of `X`, the maximal ideal of `B⟦X⟧` over a local `B`) along the
currying isomorphism

`MvPowerSeries (Option σ) A ≃+* PowerSeries (MvPowerSeries σ A)`,

which mathlib does not have (only the polynomial analogue
`MvPolynomial.finSuccEquiv` exists).  It is built here by hand from
the exponent equivalence `(Option σ →₀ ℕ) ≃ ℕ × (σ →₀ ℕ)`
(`Finsupp.optionElim`/`Finsupp.some`): multiplicativity is the
antidiagonal-splitting computation
`antidiagonal (optionElim n d) ≃ antidiagonal n ×ˢ antidiagonal d`.
The successor case of the induction goes through
`MvPowerSeries.renameEquiv` along `finSuccEquiv : Fin (n+1) ≃ Option (Fin n)`.
-/

section PowerSeriesCurry

open PowerSeries

variable {σ : Type*} {A : Type*} [CommRing A] {B : Type*} [CommRing B]

/-- Additivity of the exponent currying `Finsupp.optionElim`: splitting
off the `none`-coordinate is an additive bijection
`(Option σ →₀ ℕ) ≃ ℕ × (σ →₀ ℕ)`. -/
lemma optionElim_add {α M : Type*} [AddZeroClass M] (y₁ y₂ : M) (f₁ f₂ : α →₀ M) :
    Finsupp.optionElim (y₁ + y₂) (f₁ + f₂) =
      Finsupp.optionElim y₁ f₁ + Finsupp.optionElim y₂ f₂ := by
  ext a; cases a <;> simp

/-- **Currying a multivariate power series** in the distinguished
variable indexed by `none`: `A[[(xᵢ)_{i : Option σ}]] → (A[[(xᵢ)_{i : σ}]])⟦X⟧`,
`f ↦ Σₙ (Σ_d coeff (optionElim n d) f · x^d) Xⁿ`. -/
noncomputable def optionCurry (f : MvPowerSeries (Option σ) A) :
    PowerSeries (MvPowerSeries σ A) :=
  PowerSeries.mk fun n =>
    (fun d => MvPowerSeries.coeff (Finsupp.optionElim n d) f : MvPowerSeries σ A)

/-- The inverse of `optionCurry`: read the coefficient of the exponent
`u` off the `u none`-th coefficient of the outer series. -/
noncomputable def optionUncurry (F : PowerSeries (MvPowerSeries σ A)) :
    MvPowerSeries (Option σ) A :=
  fun u => MvPowerSeries.coeff u.some (PowerSeries.coeff (u none) F)

lemma coeff_optionCurry (f : MvPowerSeries (Option σ) A) (n : ℕ) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (PowerSeries.coeff n (optionCurry f)) =
      MvPowerSeries.coeff (Finsupp.optionElim n d) f := by
  simp [optionCurry, MvPowerSeries.coeff_apply]

lemma coeff_optionUncurry (F : PowerSeries (MvPowerSeries σ A)) (u : Option σ →₀ ℕ) :
    MvPowerSeries.coeff u (optionUncurry F) =
      MvPowerSeries.coeff u.some (PowerSeries.coeff (u none) F) := by
  simp [optionUncurry, MvPowerSeries.coeff_apply]

lemma optionUncurry_optionCurry (f : MvPowerSeries (Option σ) A) :
    optionUncurry (optionCurry f) = f := by
  ext u
  rw [coeff_optionUncurry, coeff_optionCurry, Finsupp.optionElim_some]

lemma optionCurry_optionUncurry (F : PowerSeries (MvPowerSeries σ A)) :
    optionCurry (optionUncurry F) = F := by
  ext n d
  rw [coeff_optionCurry, coeff_optionUncurry, Finsupp.optionElim_apply_none,
    Finsupp.some_optionElim]

lemma optionCurry_add (f g : MvPowerSeries (Option σ) A) :
    optionCurry (f + g) = optionCurry f + optionCurry g := by
  ext n d
  simp [coeff_optionCurry]

/-- Multiplicativity of the currying map: the antidiagonal of
`optionElim n d` splits as the product of the antidiagonals of `n` and
of `d`, which is exactly the Cauchy product of the curried series. -/
lemma optionCurry_mul (f g : MvPowerSeries (Option σ) A) :
    optionCurry (f * g) = optionCurry f * optionCurry g := by
  classical
  ext n d
  rw [coeff_optionCurry, MvPowerSeries.coeff_mul, PowerSeries.coeff_mul, map_sum]
  simp only [MvPowerSeries.coeff_mul, coeff_optionCurry]
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (i := fun u => ((u.1 none, u.2 none), (u.1.some, u.2.some)))
    (j := fun v => (Finsupp.optionElim v.1.1 v.2.1, Finsupp.optionElim v.1.2 v.2.2))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨u, v⟩ hu
    simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hu
    simp only [Finset.mem_product, Finset.HasAntidiagonal.mem_antidiagonal]
    refine ⟨?_, ?_⟩
    · have := congrArg (fun x => (x : Option σ →₀ ℕ) none) hu
      simpa using this
    · have := congrArg Finsupp.some hu
      simpa using this
  · rintro ⟨⟨i, j⟩, ⟨d1, d2⟩⟩ hv
    simp only [Finset.mem_product, Finset.HasAntidiagonal.mem_antidiagonal] at hv
    simp only [Finset.HasAntidiagonal.mem_antidiagonal]
    rw [← optionElim_add, hv.1, hv.2]
  · rintro ⟨u, v⟩ _
    simp [Finsupp.optionElim_some]
  · rintro ⟨⟨i, j⟩, ⟨d1, d2⟩⟩ _
    simp [Finsupp.some_optionElim]
  · rintro ⟨u, v⟩ _
    simp [Finsupp.optionElim_some]

/-- **The currying isomorphism**
`MvPowerSeries (Option σ) A ≃+* PowerSeries (MvPowerSeries σ A)` — the
power-series analogue of `MvPolynomial.finSuccEquiv`, the shared
gadget behind both power-series leaves below. -/
noncomputable def optionCurryEquiv (σ : Type*) (A : Type*) [CommRing A] :
    MvPowerSeries (Option σ) A ≃+* PowerSeries (MvPowerSeries σ A) where
  toFun := optionCurry
  invFun := optionUncurry
  left_inv := optionUncurry_optionCurry
  right_inv := optionCurry_optionUncurry
  map_mul' := optionCurry_mul
  map_add' := optionCurry_add

/-- Power series in an empty family of variables are just constants
(the base case of both inductions). -/
noncomputable def mvPowerSeriesIsEmptyRingEquiv (σ : Type*) (A : Type*) [IsEmpty σ]
    [CommRing A] : A ≃+* MvPowerSeries σ A :=
  RingEquiv.ofBijective MvPowerSeries.C ⟨MvPowerSeries.C_injective, MvPowerSeries.C_surjective⟩

/-- `X` is a nonzerodivisor of `B⟦X⟧`: multiplication by `X` shifts
coefficients, hence is injective. -/
lemma isSMulRegular_powerSeries_X : IsSMulRegular (PowerSeries B) (X : PowerSeries B) := by
  intro f g h
  simp only [smul_eq_mul] at h
  ext n
  have := congrArg (PowerSeries.coeff (n + 1)) h
  rwa [coeff_succ_X_mul, coeff_succ_X_mul] at this

lemma smul_top_eq_span_powerSeries_X :
    ((X : PowerSeries B) • ⊤ : Submodule (PowerSeries B) (PowerSeries B)) =
      (Ideal.span {(X : PowerSeries B)} : Ideal (PowerSeries B)) := by
  rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]

lemma ker_powerSeries_constantCoeff :
    RingHom.ker (constantCoeff (R := B)) = Ideal.span {(X : PowerSeries B)} := by
  ext f
  rw [RingHom.mem_ker, Ideal.mem_span_singleton, X_dvd_iff]

lemma powerSeries_constantCoeff_surjective :
    Function.Surjective (constantCoeff (R := B)) := fun b => ⟨C b, constantCoeff_C b⟩

/-- `B⟦X⟧ / (X) ≃+* B` through the constant coefficient. -/
noncomputable def quotXRingEquiv (B : Type*) [CommRing B] :
    (PowerSeries B ⧸ Ideal.span {(X : PowerSeries B)}) ≃+* B :=
  (Ideal.quotEquivOfEq ker_powerSeries_constantCoeff.symm).trans
    (RingHom.quotientKerEquivOfSurjective powerSeries_constantCoeff_surjective)

/-- The same identification, read on the module quotient
`QuotSMulTop X B⟦X⟧` in which the regular-sequence recursion lives. -/
noncomputable def quotXAddEquiv (B : Type*) [CommRing B] :
    QuotSMulTop (X : PowerSeries B) (PowerSeries B) ≃+ B :=
  ((Submodule.quotEquivOfEq _ _ smul_top_eq_span_powerSeries_X).toAddEquiv).trans
    (quotXRingEquiv B).toAddEquiv

lemma quotXAddEquiv_mk (f : PowerSeries B) :
    quotXAddEquiv B (Submodule.Quotient.mk f :
      QuotSMulTop (X : PowerSeries B) (PowerSeries B)) = constantCoeff f := rfl

/-- Semilinearity of that identification over `C : B →+* B⟦X⟧`: the
scalar `C t` upstairs acts as `t` downstairs. -/
lemma quotXAddEquiv_smul (t : B) (x : QuotSMulTop (X : PowerSeries B) (PowerSeries B)) :
    quotXAddEquiv B ((C t : PowerSeries B) • x) = t • quotXAddEquiv B x := by
  induction x using Submodule.Quotient.induction_on with
  | H f =>
    rw [← Submodule.Quotient.mk_smul, quotXAddEquiv_mk, quotXAddEquiv_mk]
    simp [smul_eq_mul]

lemma mem_maximalIdeal_powerSeries [IsLocalRing B] (f : PowerSeries B) :
    f ∈ maximalIdeal (PowerSeries B) ↔ constantCoeff f ∈ maximalIdeal B := by
  simp [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]

/-- The maximal ideal of `B⟦X⟧` over a local `B` is `(X) + 𝔪_B·B⟦X⟧`:
split `f = C (constantCoeff f) + X · g`. -/
lemma maximalIdeal_powerSeries (B : Type*) [CommRing B] [IsLocalRing B] :
    maximalIdeal (PowerSeries B) =
      Ideal.span {(X : PowerSeries B)} ⊔ (maximalIdeal B).map (C : B →+* PowerSeries B) := by
  apply le_antisymm
  · intro f hf
    rw [mem_maximalIdeal_powerSeries] at hf
    obtain ⟨g, hg⟩ : (X : PowerSeries B) ∣ (f - C (constantCoeff f)) := by rw [X_dvd_iff]; simp
    have hfeq : f = C (constantCoeff f) + X * g := by rw [← hg]; ring
    rw [hfeq]
    exact Ideal.add_mem _ (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hf))
      (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)))
  · refine sup_le ?_ ?_
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
        mem_maximalIdeal_powerSeries]
      simp
    · rw [Ideal.map_le_iff_le_comap]
      intro m hm
      rw [Ideal.mem_comap, mem_maximalIdeal_powerSeries, constantCoeff_C]
      exact hm

/-- **The one-variable step**: prepending `X` to a regular sequence
spanning `𝔪_B` gives a regular sequence spanning `𝔪_{B⟦X⟧}`.  `X` is
regular on `B⟦X⟧`, the quotient by it is `B` (`quotXAddEquiv`), and
the spanning statement is `maximalIdeal_powerSeries`. -/
theorem exists_isRegular_ofList_eq_maximalIdeal_powerSeries (B : Type*) [CommRing B]
    [IsLocalRing B] (k : ℕ)
    (h : ∃ ts : List B, ts.length = k ∧ RingTheory.Sequence.IsRegular B ts ∧
      Ideal.ofList ts = maximalIdeal B) :
    ∃ ts : List (PowerSeries B), ts.length = k + 1 ∧
      RingTheory.Sequence.IsRegular (PowerSeries B) ts ∧
      Ideal.ofList ts = maximalIdeal (PowerSeries B) := by
  obtain ⟨ts, hlen, hreg, hspan⟩ := h
  refine ⟨X :: ts.map C, by simp [hlen], ?_, ?_⟩
  · rw [isRegular_cons_iff]
    refine ⟨isSMulRegular_powerSeries_X,
      (AddEquiv.isRegular_congr (e := quotXAddEquiv B) ?_).mpr hreg⟩
    exact List.forall₂_map_left_iff.mpr
      (List.forall₂_same.mpr fun t _ x => quotXAddEquiv_smul t x)
  · rw [Ideal.ofList_cons, ← Ideal.map_ofList, hspan]
    exact (maximalIdeal_powerSeries B).symm

/-- Transport of "the maximal ideal is spanned by a regular sequence of
length `k`" along a ring isomorphism of local rings. -/
theorem exists_isRegular_ofList_eq_maximalIdeal_of_ringEquiv {R S : Type*} [CommRing R]
    [CommRing S] [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) {k : ℕ}
    (h : ∃ ts : List R, ts.length = k ∧ RingTheory.Sequence.IsRegular R ts ∧
      Ideal.ofList ts = maximalIdeal R) :
    ∃ ts : List S, ts.length = k ∧ RingTheory.Sequence.IsRegular S ts ∧
      Ideal.ofList ts = maximalIdeal S := by
  obtain ⟨ts, hlen, hreg, hspan⟩ := h
  refine ⟨ts.map e, by simpa using hlen, ?_, ?_⟩
  · refine (AddEquiv.isRegular_congr (e := e.toAddEquiv) ?_).mp hreg
    exact List.forall₂_map_right_iff.mpr
      (List.forall₂_same.mpr fun t _ x => by simp [smul_eq_mul])
  · have h2 : Ideal.ofList (ts.map (e : R →+* S)) = maximalIdeal S := by
      rw [← Ideal.map_ofList, hspan]
      exact map_maximalIdeal_of_surjective (e : R →+* S) e.surjective
    exact h2

/-- The base case: `𝔪_{ℤ_p} = (p)` is spanned by the length-one regular
sequence `[p]` (`p` is a nonzerodivisor of the domain `ℤ_p`). -/
theorem exists_isRegular_ofList_eq_maximalIdeal_padicInt (p : ℕ) [Fact p.Prime] :
    ∃ ts : List ℤ_[p], ts.length = 0 + 1 ∧ RingTheory.Sequence.IsRegular ℤ_[p] ts ∧
      Ideal.ofList ts = maximalIdeal ℤ_[p] := by
  have hmem : ∀ r ∈ [(p : ℤ_[p])], r ∈ maximalIdeal ℤ_[p] := by
    intro r hr
    rw [List.mem_singleton] at hr
    subst hr
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  have hp : IsSMulRegular ℤ_[p] (p : ℤ_[p]) := by
    intro x y h
    simp only [smul_eq_mul] at h
    exact mul_left_cancel₀ (by exact_mod_cast NeZero.ne _) h
  refine ⟨[(p : ℤ_[p])], rfl,
    IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal ℤ_[p] hmem
      (IsWeaklyRegular.cons hp (IsWeaklyRegular.nil _ _)), ?_⟩
  rw [Ideal.ofList_singleton, PadicInt.maximalIdeal_eq_span_p]

end PowerSeriesCurry

/-- **Noetherianity of `A[[x₁, …, xₙ]]`** (power-series leaf; PROVEN
2026-07-24): finite-variable power series over a Noetherian
commutative ring are Noetherian.  Unconditionally true, zero
arithmetic content.  Proven by induction on the number of variables:
the empty case is `mvPowerSeriesIsEmptyRingEquiv` (`A[[]] ≃+* A`), and
the successor case transports mathlib's `IsNoetherianRing B⟦X⟧` (the
power-series Hilbert basis theorem) along the currying isomorphism
`MvPowerSeries (Fin (n+1)) A ≃+* PowerSeries (MvPowerSeries (Fin n) A)`
(`optionCurryEquiv` composed with `MvPowerSeries.renameEquiv` along
`finSuccEquiv`).  Consumed by `free_of_isRegular_mvPowerSeries` to
feed the Auslander–Buchsbaum induction. -/
theorem isNoetherianRing_mvPowerSeries.{uA} (n : ℕ) {A : Type uA} [CommRing A]
    [IsNoetherianRing A] : IsNoetherianRing (MvPowerSeries (Fin n) A) := by
  induction n with
  | zero => exact isNoetherianRing_of_ringEquiv A (mvPowerSeriesIsEmptyRingEquiv (Fin 0) A)
  | succ n ih =>
    haveI := ih
    exact isNoetherianRing_of_ringEquiv _
      (((MvPowerSeries.renameEquiv A (finSuccEquiv n)).toRingEquiv.trans
        (optionCurryEquiv (Fin n) A)).symm)

/-- **The regular system of parameters of `𝒪[[x₁, …, x_q]]`**
(power-series leaf; PROVEN 2026-07-24, GENERALIZED to an arbitrary
coefficient ring 2026-07-26): if the maximal ideal of the local ring
`𝒪` is spanned by a length-one regular sequence — i.e. `𝒪` is a DVR,
the hypothesis `hO`, satisfied by `ℤ_[p]` through
`exists_isRegular_ofList_eq_maximalIdeal_padicInt` and by
`𝒪 = W(k)` — then the maximal ideal of `R_∞ = 𝒪[[x₁, …, x_q]]` is
spanned by a regular sequence of length `q + 1`, concretely the image
of `(x_q, …, x_1, ϖ)` under the currying isomorphisms.

The coefficient ring is a parameter rather than `ℤ_[p]` because of the
INTERFACE OBSTRUCTION recorded at `exists_taylorWilesBottomLevel`
below: presenting the Taylor–Wiles deformation rings over `ℤ_[p]`
silently forces the residual field to be `𝔽_p`.  Unconditionally true,
zero arithmetic content.
Proven by induction on the number of variables from the one-variable
step `exists_isRegular_ofList_eq_maximalIdeal_powerSeries` (prepending
`X` to a regular system of parameters of the local base `B` gives one
of `B⟦X⟧`: `X` is a nonzerodivisor, `B⟦X⟧/(X) ≃ B`, and
`𝔪_{B⟦X⟧} = (X) + 𝔪_B·B⟦X⟧`), based at
`𝔪_{ℤ_p} = (p)` (`exists_isRegular_ofList_eq_maximalIdeal_padicInt`)
and transported at each step along
`MvPowerSeries (Fin (q+1)) ℤ_p ≃+* (MvPowerSeries (Fin q) ℤ_p)⟦X⟧`.
Consumed by `free_of_isRegular_mvPowerSeries`. -/
theorem exists_isRegular_ofList_eq_maximalIdeal_mvPowerSeries {O : Type}
    [CommRing O] [IsLocalRing O]
    (hO : ∃ ts : List O, ts.length = 0 + 1 ∧ RingTheory.Sequence.IsRegular O ts ∧
      Ideal.ofList ts = maximalIdeal O)
    (q : ℕ) :
    ∃ ts : List (MvPowerSeries (Fin q) O), ts.length = q + 1 ∧
      RingTheory.Sequence.IsRegular (MvPowerSeries (Fin q) O) ts ∧
      Ideal.ofList ts = maximalIdeal (MvPowerSeries (Fin q) O) := by
  induction q with
  | zero =>
    exact exists_isRegular_ofList_eq_maximalIdeal_of_ringEquiv
      (mvPowerSeriesIsEmptyRingEquiv (Fin 0) O) hO
  | succ q ih =>
    exact exists_isRegular_ofList_eq_maximalIdeal_of_ringEquiv
      (((MvPowerSeries.renameEquiv O (finSuccEquiv q)).toRingEquiv.trans
        (optionCurryEquiv (Fin q) O)).symm)
      (exists_isRegular_ofList_eq_maximalIdeal_powerSeries _ (q + 1) ih)

/-- **The commutative-algebra endgame** (patching leaf 3; PROVEN
2026-07-24, GENERALIZED to an arbitrary DVR coefficient ring `𝒪`
2026-07-26 — see `exists_isRegular_ofList_eq_maximalIdeal_mvPowerSeries`
above and the INTERFACE OBSTRUCTION at `exists_taylorWilesBottomLevel`
below): a finite module over the regular local ring
`R_∞ = 𝒪[[x₁, …, x_q]]` carrying a regular sequence of length
`q + 1 = dim R_∞` inside the maximal ideal — i.e. of depth at least
`dim R_∞` — is FREE.  This is the Auslander–Buchsbaum step of the
patching argument (Diamond, *The Taylor–Wiles construction and
multiplicity one*, Invent. Math. 128 (1997), Thm. 2.4: over a regular
local ring, `depth M ≥ dim R` forces `pd M = 0`; see also
Diamond–Darmon–Taylor (1995), Thm. 5.28 and Bruns–Herzog,
*Cohen–Macaulay rings*, Thm. 1.3.3 + 2.2.7).  Unconditionally true —
no arithmetic content.  Proven as the instantiation of the abstract
dimension induction `free_of_isRegular_of_ofList_eq_maximalIdeal`
(Rees theorem + Davis avoidance + Nakayama dévissage; see the section
header above) at the two concrete power-series leaves
`isNoetherianRing_mvPowerSeries` and
`exists_isRegular_ofList_eq_maximalIdeal_mvPowerSeries`. -/
theorem free_of_isRegular_mvPowerSeries.{v} {O : Type} [CommRing O]
    [IsLocalRing O] [IsNoetherianRing O] {q : ℕ}
    (hO : ∃ ts : List O, ts.length = 0 + 1 ∧ RingTheory.Sequence.IsRegular O ts ∧
      Ideal.ofList ts = maximalIdeal O)
    {M : Type v} [AddCommGroup M]
    [Module (MvPowerSeries (Fin q) O) M]
    (hfin : Module.Finite (MvPowerSeries (Fin q) O) M)
    {rs : List (MvPowerSeries (Fin q) O)} (hlen : rs.length = q + 1)
    (hmem : ∀ x ∈ rs, x ∈ IsLocalRing.maximalIdeal
      (MvPowerSeries (Fin q) O))
    (hreg : RingTheory.Sequence.IsRegular M rs) :
    Module.Free (MvPowerSeries (Fin q) O) M := by
  haveI := hfin
  haveI : IsNoetherianRing (MvPowerSeries (Fin q) O) :=
    isNoetherianRing_mvPowerSeries q
  obtain ⟨ts, htslen, hts, htsspan⟩ :=
    exists_isRegular_ofList_eq_maximalIdeal_mvPowerSeries hO q
  exact free_of_isRegular_of_ofList_eq_maximalIdeal (q + 1) ts hts htslen htsspan
    rs hreg hlen hmem

end AuslanderBuchsbaum

/-- **`ℤ_[p]` is a Taylor–Wiles coefficient ring** (PROVEN 2026-07-26)
— the classical instance at residual field `𝔽_p`, and the witness every
`ℤ_[p]`-shaped call site of the patching stack now supplies
explicitly.  Local Noetherian complete DVR with residue field `ZMod p`
(`PadicInt.residueField`), compact, and topologically generated over
`ℤ` by the empty set since `ℤ` is dense in `ℤ_[p]`
(`PadicInt.denseRange_intCast`); its maximal ideal is `(p)` with `p` a
nonzerodivisor
(`exists_isRegular_ofList_eq_maximalIdeal_padicInt`). -/
theorem finite_residueField_padicInt (p : ℕ) [Fact p.Prime] :
    Finite (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p]) :=
  Finite.of_equiv (ZMod p) (PadicInt.residueField (p := p)).symm.toEquiv

/-- `ℤ` is dense in `ℤ_[p]`, so `ℤ_[p]` is topologically generated over
`ℤ` by the EMPTY set (`PadicInt.denseRange_intCast`). -/
theorem topologicallyFG_int_padicInt (p : ℕ) [Fact p.Prime] :
    Algebra.TopologicallyFG ℤ ℤ_[p] := by
  refine ⟨⟨∅, ?_⟩⟩
  have he : ((Algebra.adjoin ℤ ((∅ : Finset ℤ_[p]) : Set ℤ_[p]) : Subalgebra ℤ ℤ_[p]) :
      Set ℤ_[p]) = Set.range (algebraMap ℤ ℤ_[p]) := by
    simp [Algebra.adjoin_empty, Algebra.coe_bot]
  rw [he]
  exact PadicInt.denseRange_intCast

noncomputable def TaylorWilesCoefficients.padicInt (p : ℕ) [Fact p.Prime] :
    TaylorWilesCoefficients where
  carrier := ℤ_[p]
  finite_residueField := finite_residueField_padicInt p
  topologicallyFG := topologicallyFG_int_padicInt p
  exists_isRegular_maximalIdeal := exists_isRegular_ofList_eq_maximalIdeal_padicInt p

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
  haveI : Module.Free (MvPowerSeries (Fin P.q) P.coeff.carrier) P.Minf :=
    free_of_isRegular_mvPowerSeries
      P.coeff.exists_isRegular_maximalIdeal P.finiteMinf hlen hmem hreg
  rw [injective_iff_map_eq_zero]
  intro r hr
  obtain ⟨x, rfl⟩ := P.toRuniv_surjective r
  let b := Module.Free.chooseBasis (MvPowerSeries (Fin P.q) P.coeff.carrier) P.Minf
  obtain ⟨i⟩ := b.index_nonempty
  have hproj0 : P.proj (x • b i) = 0 := by
    rw [P.proj_smul, hr, zero_smul]
  have hmem2 := P.mem_smul_top_of_proj_eq_zero _ hproj0
  have hle : Submodule.map (b.coord i)
      (RingHom.ker P.toRuniv •
        (⊤ : Submodule (MvPowerSeries (Fin P.q) P.coeff.carrier) P.Minf)) ≤
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

/-! ### The level-independent Taylor–Wiles patching engine

HOISTED here from `Fermat/FLT/Modularity/Patching.lean` on 2026-07-27,
VERBATIM (no restatement, no reformatting).  Everything below is pure
commutative algebra: it mentions no Galois representation, no Hecke
algebra and no base field, and its only new dependency is the vendored
`PatchingVendored.System`.

The reason for the move is that `Patching.lean` transitively imports
`HilbertModularity.lean` (`Patching → KhareWintenberger → Deformation →
HilbertModularity`), so the `ℚ`-level patching extraction could not be
reused over a totally real base field where it lived.  `PatchingCore` is
below both, so the SAME engine now serves `ℚ` and `F`; the `F`-level
duplicate (`exists_patchedModule_of_hilbertPatchingSystem`, together with
the `HilbertPatchingLevel`/`HilbertPatchingSystem` structures it consumed)
was deleted in the same commit rather than proven a second time.

`Patching.lean` still imports this module, so every `ℚ`-level consumer
sees these names unchanged and at the same fully qualified names.
-/

/-- The **augmentation ideal** `𝔫 = (S₁, …, S_q)` of the Taylor–Wiles
coordinate ring `Λ = ℤ_p[[S₁, …, S_q]]` (realized as
`MvPowerSeries (Fin q) ℤ_[p]`): the ideal generated by the
power-series variables.  Quotienting by `𝔫` "switches off the diamond
operators": `Λ/𝔫 = ℤ_p`, and at a Taylor–Wiles level the
`𝔫`-quotients recover the bottom objects (`R_{Q_n}/𝔫 ≅ R_univ`,
`H_{Q_n}/𝔫 ≅ M₀` — the `ker_toRuniv` and `projM_eq_zero_iff` fields
of `TaylorWilesSystem` below). -/
noncomputable def taylorWilesAug (p : ℕ) [Fact p.Prime] (q : ℕ) :
    Ideal (MvPowerSeries (Fin q) ℤ_[p]) :=
  Ideal.span (Set.range MvPowerSeries.X)

/-- **The Taylor–Wiles level ideal** `𝔟_n = ker(Λ ↠ ℤ_p[Δ_{Q_n}])` in
its classical explicit form (ADDED 2026-07-27 as part of the
decomposition of `exists_taylorWilesLevelRaw`).

For a Taylor–Wiles set `Q_n` the diamond group is
`Δ_{Q_n} = ∏_{q ∈ Q_n} (ℤ/q)^×(p) ≅ ∏_i ℤ/p^{e_i}`, where `e_i` is the
`p`-adic valuation of `q_i − 1` (so `e_i ≥ n`, because `q_i ≡ 1 mod p^n`
is exactly the defining congruence of `IsTaylorWilesPrimeSet`).  The
standard surjection `Λ = ℤ_p[[S_1,…,S_q]] ↠ ℤ_p[Δ_{Q_n}]` sends
`S_i ↦ [γ_i] − 1` for `γ_i` a generator of the `i`-th cyclic factor, and
its kernel is generated by the `q` elements

    (1 + S_i)^{p^{e_i}} − 1 .

Pinning `𝔟_n` to this shape is what keeps the arithmetic leaf
`exists_taylorWilesAuxLevelData` faithful: an ideal handed over
abstractly, constrained only by `𝔟 ≤ 𝔪^n` and `𝔟 ≤ 𝔫`, is satisfied by
`𝔟 = ⊥`, and over `Λ/⊥ = Λ` no finite Hecke module is free — so an
abstract `𝔟` would make the module half of the level FALSE rather than
merely open.  It also makes the two `bIdeal` bounds provable once and
for all, off the arithmetic leaf (see the two lemmas below). -/
noncomputable def taylorWilesLevelIdeal (p : ℕ) [Fact p.Prime] {q : ℕ}
    (e : Fin q → ℕ) : Ideal (MvPowerSeries (Fin q) ℤ_[p]) :=
  Ideal.span (Set.range fun i : Fin q => (1 + MvPowerSeries.X i) ^ p ^ e i - 1)

/-- **The level ideal lies in the augmentation ideal** (PROVEN
2026-07-27): `𝔟_n ⊆ 𝔫`, i.e. `TaylorWilesLevelRaw.bIdeal_le_aug` for the
explicit level ideal.

This is the field added on 2026-07-26 to repair the second defect of the
FORMAL-CONTENT AUDIT of `exists_taylorWilesLevelRaw` (without it `M₀`
could be finite `p`-power torsion and no raw level would exist above
`a₀`).  In the explicit form it is immediate: each generator
`(1 + S_i)^{p^{e_i}} − 1` is divisible by `(1 + S_i) − 1 = S_i`
(`sub_dvd_pow_sub_pow`), hence lies in `𝔫 = (S_1, …, S_q)`.  Note it does
NOT need the congruence `e_i ≥ n` — unlike `bIdeal_le` it has content at
every level, including the bottom one. -/
theorem taylorWilesLevelIdeal_le_aug (p : ℕ) [Fact p.Prime] {q : ℕ}
    (e : Fin q → ℕ) : taylorWilesLevelIdeal p e ≤ taylorWilesAug p q := by
  unfold taylorWilesLevelIdeal taylorWilesAug
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  have hdvd : (MvPowerSeries.X i : MvPowerSeries (Fin q) ℤ_[p]) ∣
      (1 + MvPowerSeries.X i) ^ p ^ e i - 1 := by
    have h := sub_dvd_pow_sub_pow
      (1 + MvPowerSeries.X (σ := Fin q) (R := ℤ_[p]) i) 1 (p ^ e i)
    simpa using h
  obtain ⟨c, hc⟩ := hdvd
  simp only [SetLike.mem_coe, hc]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- **One binomial step of the level-ideal induction** (PROVEN 2026-07-27,
helper for `taylorWilesLevelIdeal_le_maximalIdeal_pow`).

In any commutative ring, if the prime `p` lies in an ideal `I` and
`x ∈ I^m` with `m ≥ 1`, then `(1 + x)^p - 1 ∈ I^{m+1}`.

Proof: expand `(1 + x)^p - 1 = ∑_{j=1}^{p} binom(p, j) x^j`.  For
`1 ≤ j ≤ p - 1` the prime divides `binom(p, j)`
(`Nat.Prime.dvd_choose_self`), and `x^j ∈ I^m`, so the term lies in
`I^m · I = I^{m+1}`.  The top term is `x^p ∈ I^{mp} ⊆ I^{m+1}`, where
`m + 1 ≤ mp` uses BOTH `p ≥ 2` and `m ≥ 1` — at `m = 0` the top term is
genuinely not in `I`, which is why the hypothesis `1 ≤ m` cannot be
dropped (it is supplied by the base case of the induction below). -/
theorem onePlus_pow_prime_sub_one_mem {R : Type*} [CommRing R]
    {I : Ideal R} {p : ℕ} (hp : p.Prime) (hpI : (p : R) ∈ I) {m : ℕ}
    (hm : 1 ≤ m) {x : R} (hx : x ∈ I ^ m) : (1 + x) ^ p - 1 ∈ I ^ (m + 1) := by
  have hexp : (1 + x) ^ p - 1 =
      ∑ k ∈ Finset.range p, x ^ (k + 1) * (p.choose (k + 1) : R) := by
    have h := add_pow x (1 : R) p
    rw [Finset.sum_range_succ'] at h
    simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right,
      Nat.cast_one] at h
    rw [add_comm (1 : R) x, h]
    ring
  rw [hexp]
  refine Submodule.sum_mem _ ?_
  intro k hk
  rw [Finset.mem_range] at hk
  have hxm : x ^ (k + 1) ∈ I ^ m := by
    rw [pow_succ]
    exact Ideal.mul_mem_left _ _ hx
  rcases eq_or_ne (k + 1) p with hkp | hkp
  · rw [hkp, Nat.choose_self, Nat.cast_one, mul_one]
    have h1 : x ^ p ∈ I ^ (m * p) := by
      rw [pow_mul]; exact Ideal.pow_mem_pow hx p
    refine Ideal.pow_le_pow_right ?_ h1
    nlinarith [hp.two_le]
  · have hlt : k + 1 < p := lt_of_le_of_ne hk hkp
    obtain ⟨c, hc⟩ := hp.dvd_choose_self (Nat.succ_ne_zero k) hlt
    rw [hc]
    push_cast
    have hmem : x ^ (k + 1) * (p : R) ∈ I ^ (m + 1) := by
      rw [pow_succ]
      exact Ideal.mul_mem_mul hxm hpI
    rw [← mul_assoc]
    exact Ideal.mul_mem_right _ _ hmem

/-- **The `p`-power binomial estimate** (PROVEN 2026-07-27, helper for
`taylorWilesLevelIdeal_le_maximalIdeal_pow`): if `p ∈ I` and `x ∈ I`
then `(1 + x)^{p^f} - 1 ∈ I^{f+1}`.

Induction on `f`.  At `f = 0` the element is `x ∈ I`.  The step writes
`(1 + x)^{p^{f+1}} = (1 + z)^p` for `z = (1 + x)^{p^f} - 1 ∈ I^{f+1}` and
applies `onePlus_pow_prime_sub_one_mem` at `m = f + 1 ≥ 1`. -/
theorem onePlus_pow_primePow_sub_one_mem {R : Type*} [CommRing R]
    {I : Ideal R} {p : ℕ} (hp : p.Prime) (hpI : (p : R) ∈ I) {x : R}
    (hx : x ∈ I) (f : ℕ) : (1 + x) ^ p ^ f - 1 ∈ I ^ (f + 1) := by
  induction f with
  | zero => simpa using hx
  | succ f ih =>
      have h1 : (1 + x) ^ p ^ (f + 1) = (1 + ((1 + x) ^ p ^ f - 1)) ^ p := by
        have h2 : (1 : R) + ((1 + x) ^ p ^ f - 1) = (1 + x) ^ p ^ f := by ring
        rw [h2, ← pow_mul, ← pow_succ]
      rw [h1]
      exact onePlus_pow_prime_sub_one_mem hp hpI (Nat.le_add_left 1 f) ih

/-- **The level ideals shrink** (PROVEN 2026-07-27; was LEAF A1 of the
2026-07-27 decomposition of `exists_taylorWilesLevelRaw`): `𝔟_n ⊆ 𝔪_Λ^n`
whenever
every exponent satisfies `e_i ≥ n`, i.e.
`TaylorWilesLevelRaw.bIdeal_le` for the explicit level ideal.

This is the convergence input of the whole patching argument — it is what
makes the pigeonhole of `TaylorWilesSystem.exists_patchedModule`
nontrivial — and it is pure commutative algebra over
`Λ = ℤ_p[[S_1,…,S_q]]`, with no Galois or Hecke content whatsoever.

PROOF (as sketched below, and carried out by the two helper lemmas
`onePlus_pow_prime_sub_one_mem` and `onePlus_pow_primePow_sub_one_mem`
above).  Write `a = S_i ∈ 𝔪` and
`z_e = (1 + a)^{p^e} − 1`.  Claim: `z_e ∈ 𝔪^{e+1}`, by induction on `e`.

* `e = 0`: `z_0 = a ∈ 𝔪`.
* step: `z_{e+1} = (1 + z_e)^p − 1 = ∑_{j=1}^{p} binom(p, j) z_e^j`.  For
  `1 ≤ j ≤ p − 1` the prime `p` divides `binom(p, j)`
  (`Nat.Prime.dvd_choose_self`), and `p ∈ 𝔪` (its constant coefficient
  `p` is a nonunit of `ℤ_[p]`), so each such term lies in
  `𝔪 · 𝔪^{e+1} = 𝔪^{e+2}`; and `z_e^p ∈ 𝔪^{p(e+1)} ⊆ 𝔪^{e+2}` because
  `p ≥ 2` gives `p(e+1) ≥ 2e + 2 ≥ e + 2`.

Then `n ≤ e_i` gives `z_{e_i} ∈ 𝔪^{e_i + 1} ⊆ 𝔪^n`, and `Ideal.span_le`
finishes.  (Both edge cases are degenerate and true: at `q = 0` the ideal
is `⊥`, and at `n = 0` the target is `⊤`.)

CIRCULARITY GUARD: none applies — this leaf mentions neither `ρbar` nor
any deformation- or Hecke-theoretic object, so no route to the odd-prime
dichotomy exists. -/
theorem taylorWilesLevelIdeal_le_maximalIdeal_pow (p : ℕ) [Fact p.Prime]
    {q n : ℕ} (e : Fin q → ℕ) (he : ∀ i, n ≤ e i) :
    taylorWilesLevelIdeal p e ≤
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin q) ℤ_[p]) ^ n := by
  have hp : p.Prime := Fact.out
  -- `p` is a nonunit of `Λ`, because its constant coefficient `p` is a
  -- nonunit of `ℤ_[p]`.
  have hpI : ((p : ℕ) : MvPowerSeries (Fin q) ℤ_[p]) ∈
      _root_.IsLocalRing.maximalIdeal (MvPowerSeries (Fin q) ℤ_[p]) := by
    rw [_root_.IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      MvPowerSeries.isUnit_iff_constantCoeff, map_natCast, ← mem_nonunits_iff,
      ← _root_.IsLocalRing.mem_maximalIdeal, PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  -- each variable `S_i = X i` is a nonunit of `Λ`, its constant coefficient
  -- being `0`.
  have hXI : ∀ i : Fin q, (MvPowerSeries.X i : MvPowerSeries (Fin q) ℤ_[p]) ∈
      _root_.IsLocalRing.maximalIdeal (MvPowerSeries (Fin q) ℤ_[p]) := by
    intro i
    rw [_root_.IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_X]
    exact not_isUnit_zero
  rw [taylorWilesLevelIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact Ideal.pow_le_pow_right (le_trans (he i) (Nat.le_succ _))
    (onePlus_pow_primePow_sub_one_mem hp hpI (hXI i) (e i))

set_option linter.checkUnivs false in
/-- **The Taylor–Wiles system** — the tower of finite-level
Taylor–Wiles data, recorded with exactly the fields the
pigeonhole/ultraproduct extraction
(`TaylorWilesSystem.exists_patchedModule`) consumes.  This is the
interface cutting the patching construction `exists_patchedModule`
into its arithmetic half (`exists_taylorWilesSystem` — deformation
theory and Hecke theory at auxiliary Taylor–Wiles levels) and its
pure commutative-algebra half (the extraction of the limit object).

Classically (Taylor–Wiles 1995; Diamond 1997; DDT (1995) §5.5),
writing `Λ = ℤ_p[[S₁, …, S_q]]` for `MvPowerSeries (Fin q) ℤ_[p]` —
used in TWO roles, as the diamond-operator coordinate ring
(`S`-variables: the `diamond`/`bIdeal`/`freeM` fields) and as the
deformation-ring presentation ring `R_∞` (`x`-variables: the `pres`
field); the two roles have the same number `q` of variables precisely
because the FLT-setting local conditions are smooth and the
level-`Q_n` tangent bound equals the Taylor–Wiles number
`q = dim_k H¹_{Q_n}(ℚ, ad⁰ρbar)` — the level-`n` datum is:

* `R n = R_{Q_n}`, the auxiliary deformation ring: `pres n` is the
  `q`-generator power-series presentation (tangent-space bound from
  the `Q_n`-Selmer count), `diamond n` the `Λ`-algebra structure from
  the `Δ_{Q_n} = ∏_{q ∈ Q_n} (ℤ/q)^×(p)`-action on the auxiliary
  deformation problem (the torus split off by the distinct-eigenvalue
  condition, via local class field theory at each `q ∈ Q_n`), and
  `toRuniv n` the control identification `R_{Q_n}/𝔫R_{Q_n} ≅ R_univ`
  (stated kernel-theoretically: a surjection with kernel exactly
  `𝔫·R_{Q_n}`).
* `M n = H_{Q_n}`, the auxiliary Hecke module at level raised by
  `Q_n`, an `R_{Q_n}`-module through the Hecke-side deformation; its
  `Λ`-structure (`moduleCoeffM`) acts through `diamond n`
  (`diamond_smul` — the `IsScalarTower Λ (R n) (M n)` condition in
  explicit form).
* `freeM n` is the **Taylor–Wiles freeness certificate** (the key
  lemma of Taylor–Wiles 1995, in the multiplicity-one-free form of
  Diamond 1997, Thm. 2.1): `H_{Q_n}` is free of the FIXED rank `d`
  over `ℤ_p[Δ_{Q_n}] = Λ/𝔟_n`, stated as a `Λ`-linear coordinate
  equivalence, with the level ideal `𝔟_n = bIdeal n` satisfying
  `𝔟_n ⊆ 𝔪_Λ^n` (`bIdeal_le`; classically
  `𝔟_n = ((1+Sᵢ)^{p^{eᵢ}} − 1 : eᵢ ≥ n) ⊆ 𝔪_Λ^{n+1}` since every
  `q ∈ Q_n` is `≡ 1 mod p^n` — this shrinking is what makes the
  levels converge and the pigeonhole nontrivial).
* `projM n` is the bottom control map `H_{Q_n} ↠ M₀`, with kernel
  exactly `𝔫·H_{Q_n}` (`projM_eq_zero_iff`), intertwining the
  `R_{Q_n}`-action with the `T`-action through `ψ ∘ toRuniv n`
  (`projM_smul` — where the pillar's map `ψ` enters the tower; the
  finite-level shadow of `PatchedModule.proj_smul`).

Both-ways audit: the structure is pure data — inhabitation is
asserted only by `exists_taylorWilesSystem` below, under the full
(classically unsatisfiable) pillar hypothesis roster.  (The
`checkUnivs` linter is disabled as for `PatchedModule`: the three
data universes are deliberately independent.) -/
structure TaylorWilesSystem.{a, b, c, s, uR} (p : ℕ) [Fact p.Prime]
    {Runiv : Type uR} [CommRing Runiv]
    {T : Type s} [CommRing T] (ψ : Runiv →+* T) where
  /-- The number of Taylor–Wiles primes at each level (equivalently,
  power-series variables; classically `dim_k H¹_{Q_n}(ℚ, ad⁰ρbar)`,
  the common size given by Wiles's product formula). -/
  q : ℕ
  /-- The common `Λ/𝔟_n`-rank of the auxiliary Hecke modules
  (classically the `ℤ_p`-rank of the bottom module `M₀`). -/
  d : ℕ
  /-- The coefficient ring `𝒪` of the PRESENTATION role (classically
  `W(k)`); see `TaylorWilesCoefficients` and the `REPAIR` block of
  `exists_taylorWilesBottomLevel`.  The DIAMOND role keeps `ℤ_[p]`:
  `M n` is free over `ℤ_p[Δ_{Q_n}] = Λ/𝔟_n` (of rank `d = [k:𝔽_p]·d_𝒪`)
  because it is free over `𝒪[Δ_{Q_n}]` and `𝒪` is finite free over
  `ℤ_[p]`, and both power-series rings have dimension `q + 1`, which is
  all the patching endgame consumes. -/
  coeff : TaylorWilesCoefficients
  /-- The auxiliary deformation ring `R_{Q_n}` at level `n`. -/
  R : ℕ → Type a
  [commRingR : ∀ n, CommRing (R n)]
  /-- The `q`-generator power-series presentation of `R n` over `𝒪`
  (the tangent-space bound). -/
  pres : ∀ n, MvPowerSeries (Fin q) coeff.carrier →+* R n
  pres_surjective : ∀ n, Function.Surjective (pres n)
  /-- The diamond-operator structure map `Λ → R n`. -/
  diamond : ∀ n, MvPowerSeries (Fin q) ℤ_[p] →+* R n
  /-- The control identification `R n/𝔫R n ≅ Runiv`: surjection
  part. -/
  toRuniv : ∀ n, R n →+* Runiv
  toRuniv_surjective : ∀ n, Function.Surjective (toRuniv n)
  /-- The control identification `R n/𝔫R n ≅ Runiv`: kernel part. -/
  ker_toRuniv : ∀ n,
    RingHom.ker (toRuniv n) = (taylorWilesAug p q).map (diamond n)
  /-- The auxiliary Hecke module `H_{Q_n}` at level `n`. -/
  M : ℕ → Type b
  [addCommGroupM : ∀ n, AddCommGroup (M n)]
  [moduleRM : ∀ n, Module (R n) (M n)]
  [moduleCoeffM : ∀ n, Module (MvPowerSeries (Fin q) ℤ_[p]) (M n)]
  /-- The `Λ`-action on `M n` acts through `diamond n` (the
  `IsScalarTower Λ (R n) (M n)` condition, explicitly). -/
  diamond_smul : ∀ (n : ℕ) (s : MvPowerSeries (Fin q) ℤ_[p]) (m : M n),
    s • m = diamond n s • m
  /-- The level ideal `𝔟_n = ker(Λ ↠ ℤ_p[Δ_{Q_n}])`. -/
  bIdeal : ℕ → Ideal (MvPowerSeries (Fin q) ℤ_[p])
  /-- The levels shrink: `𝔟_n ⊆ 𝔪_Λ^n`. -/
  bIdeal_le : ∀ n,
    bIdeal n ≤ IsLocalRing.maximalIdeal (MvPowerSeries (Fin q) ℤ_[p]) ^ n
  /-- The Taylor–Wiles freeness certificate: `M n` is free of rank `d`
  over `Λ/𝔟_n`, as a `Λ`-linear coordinate equivalence. -/
  freeM : ∀ n, M n ≃ₗ[MvPowerSeries (Fin q) ℤ_[p]]
    (Fin d → MvPowerSeries (Fin q) ℤ_[p] ⧸ bIdeal n)
  /-- The bottom Hecke module (becomes `PatchedModule.M0`
  verbatim). -/
  M0 : Type c
  [addCommGroupM0 : AddCommGroup M0]
  [moduleM0 : Module T M0]
  nontrivialM0 : Nontrivial M0
  /-- The bottom control map `M n ↠ M₀`. -/
  projM : ∀ n, M n →+ M0
  projM_surjective : ∀ n, Function.Surjective (projM n)
  /-- Action compatibility through `ψ`: the finite-level shadow of
  `PatchedModule.proj_smul`. -/
  projM_smul : ∀ (n : ℕ) (x : R n) (m : M n),
    projM n (x • m) = ψ (toRuniv n x) • projM n m
  /-- The kernel of the bottom control map is exactly `𝔫·M n`.  (The
  `←` direction is forced by `diamond_smul`, `projM_smul` and
  `ker_toRuniv`; the `→` direction is the control theorem.) -/
  projM_eq_zero_iff : ∀ (n : ℕ) (m : M n), projM n m = 0 ↔
    m ∈ (taylorWilesAug p q • ⊤ :
      Submodule (MvPowerSeries (Fin q) ℤ_[p]) (M n))

set_option linter.checkUnivs false in
/-- **A single Taylor–Wiles level** — the finite-level datum at one
auxiliary level `Q_n`, i.e. one slice of `TaylorWilesSystem` with the
level index `n` fixed and the level-independent data (`q`, `d`, `M0`)
supplied as parameters.  Every field is the `n`-th component of the
correspondingly named field of `TaylorWilesSystem`, EXCEPT the
freeness certificate, which is recorded here in the form in which it
is proven rather than in the coordinate form in which it is consumed:

* `freeM`/`finiteM`/`finrankM`/`nontrivialQuot` say that `M` is a
  finite free `Λ/𝔟_n`-module of rank `d` — Diamond's Thm. 2.1
  verbatim (`Λ/𝔟_n = ℤ_p[Δ_{Q_n}]`, and `𝔟_n` is a proper ideal, whence
  `nontrivialQuot`) — with `moduleQuotM`/`isScalarTowerM` recording
  that the `Λ`-action on `M` is the one obtained through the quotient
  (the statement "the diamond operators act through `ℤ_p[Δ_{Q_n}]`").
  `nonempty_linearEquiv_fin_of_free_over_quotient` turns this into the
  coordinate equivalence `TaylorWilesSystem.freeM`.

Classically `M = H_{Q_n}` is the auxiliary Hecke module at the level
raised by `Q_n`, `R = R_{Q_n}` the auxiliary deformation ring,
`𝔟_n = ker(Λ ↠ ℤ_p[Δ_{Q_n}])`, and `n` enters only through
`bIdeal_le` — the shrinking `𝔟_n ⊆ 𝔪_Λ^n` coming from `q ≡ 1 mod p^n`
for `q ∈ Q_n`, which is what makes the pigeonhole of the extraction
converge.

Both-ways audit: pure data, as for `TaylorWilesSystem`; inhabitation
is asserted only by `exists_taylorWilesTower` below under the full
pillar roster. -/
structure TaylorWilesLevel.{a, b, c, s, uR} (p : ℕ) [Fact p.Prime]
    {Runiv : Type uR} [CommRing Runiv]
    {T : Type s} [CommRing T] (ψ : Runiv →+* T) (q d n : ℕ)
    (coeff : TaylorWilesCoefficients)
    (M0 : Type c) [AddCommGroup M0] [Module T M0] where
  /-- The auxiliary deformation ring `R_{Q_n}`. -/
  R : Type a
  [commRingR : CommRing R]
  /-- The `q`-generator power-series presentation over `𝒪` (tangent
  bound); see `TaylorWilesSystem.coeff` for why the presentation role
  carries `𝒪` and the diamond role keeps `ℤ_[p]`. -/
  pres : MvPowerSeries (Fin q) coeff.carrier →+* R
  pres_surjective : Function.Surjective pres
  /-- The diamond-operator structure map `Λ → R`. -/
  diamond : MvPowerSeries (Fin q) ℤ_[p] →+* R
  /-- The control identification `R/𝔫R ≅ Runiv`: surjection part. -/
  toRuniv : R →+* Runiv
  toRuniv_surjective : Function.Surjective toRuniv
  /-- The control identification `R/𝔫R ≅ Runiv`: kernel part. -/
  ker_toRuniv : RingHom.ker toRuniv = (taylorWilesAug p q).map diamond
  /-- The auxiliary Hecke module `H_{Q_n}`. -/
  M : Type b
  [addCommGroupM : AddCommGroup M]
  [moduleRM : Module R M]
  [moduleCoeffM : Module (MvPowerSeries (Fin q) ℤ_[p]) M]
  /-- The `Λ`-action on `M` acts through `diamond`. -/
  diamond_smul : ∀ (x : MvPowerSeries (Fin q) ℤ_[p]) (m : M),
    x • m = diamond x • m
  /-- The level ideal `𝔟_n = ker(Λ ↠ ℤ_p[Δ_{Q_n}])`. -/
  bIdeal : Ideal (MvPowerSeries (Fin q) ℤ_[p])
  /-- The levels shrink: `𝔟_n ⊆ 𝔪_Λ^n`. -/
  bIdeal_le : bIdeal ≤
    IsLocalRing.maximalIdeal (MvPowerSeries (Fin q) ℤ_[p]) ^ n
  /-- **The level ideal lies in the augmentation ideal**: `𝔟_n ⊆ 𝔫`
  (added 2026-07-26, see `TaylorWilesLevelRaw.bIdeal_le_aug` for the
  audit that forced it).  Classically immediate — `𝔟_n` is the kernel
  of `Λ ↠ ℤ_p[Δ_{Q_n}]`, `𝔫` the kernel of the composite of that with
  the group-ring augmentation `ℤ_p[Δ_{Q_n}] ↠ ℤ_p` — and it is the
  invariant that makes `M₀ ≅ ℤ_p^d` rather than `(ℤ_p/p^a)^d`.  Unlike
  `bIdeal_le` it is NOT vacuous at `n = 0`. -/
  bIdeal_le_aug : bIdeal ≤ taylorWilesAug p q
  /-- `𝔟_n` is a proper ideal: `ℤ_p[Δ_{Q_n}] ≠ 0`. -/
  nontrivialQuot : Nontrivial (MvPowerSeries (Fin q) ℤ_[p] ⧸ bIdeal)
  [moduleQuotM : Module (MvPowerSeries (Fin q) ℤ_[p] ⧸ bIdeal) M]
  [isScalarTowerM : IsScalarTower (MvPowerSeries (Fin q) ℤ_[p])
    (MvPowerSeries (Fin q) ℤ_[p] ⧸ bIdeal) M]
  /-- The Taylor–Wiles freeness certificate (Diamond 1997, Thm. 2.1):
  `M` is free over `Λ/𝔟_n = ℤ_p[Δ_{Q_n}]` … -/
  freeM : Module.Free (MvPowerSeries (Fin q) ℤ_[p] ⧸ bIdeal) M
  /-- … finitely generated … -/
  finiteM : Module.Finite (MvPowerSeries (Fin q) ℤ_[p] ⧸ bIdeal) M
  /-- … of the level-independent rank `d`. -/
  finrankM :
    Module.finrank (MvPowerSeries (Fin q) ℤ_[p] ⧸ bIdeal) M = d
  /-- The bottom control map `M ↠ M₀`. -/
  projM : M →+ M0
  projM_surjective : Function.Surjective projM
  /-- Action compatibility through `ψ`. -/
  projM_smul : ∀ (x : R) (m : M),
    projM (x • m) = ψ (toRuniv x) • projM m
  /-- **The bottom control theorem**: the kernel of the bottom control
  map is contained in `𝔫·M`.  Only this direction is asserted — the
  reverse inclusion is forced by `diamond_smul`, `projM_smul` and
  `ker_toRuniv`, and is proven in the transposition
  `exists_taylorWilesSystem` below, which assembles the two into the
  system's `projM_eq_zero_iff`. -/
  projM_eq_zero : ∀ m : M, projM m = 0 →
    m ∈ (taylorWilesAug p q • ⊤ :
      Submodule (MvPowerSeries (Fin q) ℤ_[p]) M)

set_option linter.checkUnivs false in
/-- **The Taylor–Wiles tower** — the level-independent data
(`q`, `d`, `M0`) together with a `TaylorWilesLevel` at every level.
This is `TaylorWilesSystem` with the `∀ n` pushed inside, which is how
the arithmetic actually produces it: the auxiliary objects at level
`Q_n` are constructed one level at a time, and only the Taylor–Wiles
number `q` (Wiles's product formula), the freeness rank `d` and the
bottom Hecke module `M₀` are shared.  `exists_taylorWilesSystem`
below transposes a tower into a system.

Both-ways audit: pure data; inhabitation is asserted only by
`exists_taylorWilesTower`. -/
structure TaylorWilesTower.{a, b, c, s, uR} (p : ℕ) [Fact p.Prime]
    {Runiv : Type uR} [CommRing Runiv]
    {T : Type s} [CommRing T] (ψ : Runiv →+* T) where
  /-- The common Taylor–Wiles number `#Q_n = dim_k H¹_{Q_n}`. -/
  q : ℕ
  /-- The common `Λ/𝔟_n`-rank of the auxiliary Hecke modules. -/
  d : ℕ
  /-- The shared coefficient ring `𝒪` of the presentation role
  (classically `W(k)`); see `TaylorWilesSystem.coeff`. -/
  coeff : TaylorWilesCoefficients
  /-- The bottom Hecke module. -/
  M0 : Type c
  [addCommGroupM0 : AddCommGroup M0]
  [moduleM0 : Module T M0]
  nontrivialM0 : Nontrivial M0
  /-- The level-`n` datum, for every `n`. -/
  level : ∀ n, TaylorWilesLevel.{a, b, c, s, uR} p ψ q d n coeff M0

set_option linter.checkUnivs false in
/-- **A Taylor–Wiles level in RAW form** (2026-07-25) — the same
finite-level datum as `TaylorWilesLevel`, with every field that the
arithmetic does not directly produce replaced by the primitive
statement it follows from.  Precisely, the six fields

* `nontrivialQuot`, `moduleQuotM`, `isScalarTowerM`, `freeM`,
  `finiteM`, `finrankM`

of `TaylorWilesLevel` — a `Λ/𝔟_n`-module structure on `M`, its
compatibility with the `Λ`-structure, and freeness of rank `d` over
it — are replaced here by the SINGLE field

* `coordM : Nonempty (M ≃ₗ[Λ] (Fin d → Λ/𝔟_n))`,

the `Λ`-linear coordinate form of Diamond's certificate.  The two
packages are equivalent (`nonempty_taylorWilesLevel_of_raw` below
recovers the native one, PROVEN), but the raw one asserts strictly
less STRUCTURE: a prover of the arithmetic leaves has to exhibit only
`Λ`-linear data, never a quotient-ring module structure or a scalar
tower, and the derived instances are then canonical rather than
chosen.  Everything else is copied verbatim from `TaylorWilesLevel`,
whose docstring documents each field.

This is deliberately NOT a new mathematical carrier: it is the same
carrier at the interface where the Taylor–Wiles arithmetic actually
lands (Diamond 1997, Thm. 2.1 produces a `ℤ_p[Δ_{Q_n}]`-basis, i.e.
coordinates), so that the level-wise cut of `exists_taylorWilesTower`
below can be stated without asking its leaves for bookkeeping.

Both-ways audit: pure data, as for `TaylorWilesLevel`; inhabitation is
asserted only by the two arithmetic leaves below. -/
structure TaylorWilesLevelRaw.{a, b, c, s, uR} (p : ℕ) [Fact p.Prime]
    {Runiv : Type uR} [CommRing Runiv]
    {T : Type s} [CommRing T] (ψ : Runiv →+* T) (q d n : ℕ)
    (coeff : TaylorWilesCoefficients)
    (M0 : Type c) [AddCommGroup M0] [Module T M0] where
  /-- The auxiliary deformation ring `R_{Q_n}`. -/
  R : Type a
  [commRingR : CommRing R]
  /-- The `q`-generator power-series presentation over `𝒪` (tangent
  bound); see `TaylorWilesSystem.coeff`. -/
  pres : MvPowerSeries (Fin q) coeff.carrier →+* R
  pres_surjective : Function.Surjective pres
  /-- The diamond-operator structure map `Λ → R`. -/
  diamond : MvPowerSeries (Fin q) ℤ_[p] →+* R
  /-- The control identification `R/𝔫R ≅ Runiv`: surjection part. -/
  toRuniv : R →+* Runiv
  toRuniv_surjective : Function.Surjective toRuniv
  /-- The control identification `R/𝔫R ≅ Runiv`: kernel part. -/
  ker_toRuniv : RingHom.ker toRuniv = (taylorWilesAug p q).map diamond
  /-- The auxiliary Hecke module `H_{Q_n}`. -/
  M : Type b
  [addCommGroupM : AddCommGroup M]
  [moduleRM : Module R M]
  [moduleCoeffM : Module (MvPowerSeries (Fin q) ℤ_[p]) M]
  /-- The `Λ`-action on `M` acts through `diamond`. -/
  diamond_smul : ∀ (x : MvPowerSeries (Fin q) ℤ_[p]) (m : M),
    x • m = diamond x • m
  /-- The level ideal `𝔟_n = ker(Λ ↠ ℤ_p[Δ_{Q_n}])`. -/
  bIdeal : Ideal (MvPowerSeries (Fin q) ℤ_[p])
  /-- The levels shrink: `𝔟_n ⊆ 𝔪_Λ^n`. -/
  bIdeal_le : bIdeal ≤
    IsLocalRing.maximalIdeal (MvPowerSeries (Fin q) ℤ_[p]) ^ n
  /-- **The level ideal lies in the augmentation ideal**: `𝔟_n ⊆ 𝔫`.

  ADDED 2026-07-26 as the repair of the second defect recorded in the
  FORMAL-CONTENT AUDIT of `exists_taylorWilesLevelRaw` below.  Without
  it the level-wise cut is not merely weak but UNSOUND: `bIdeal_le` is
  vacuous at `n = 0` (`𝔪^0 = ⊤`), so a bottom datum was free to have
  `Λ/(𝔫 + 𝔟_0) = ℤ_p/p^{a}` with `a` finite — i.e. a finite `p`-power
  torsion `M₀` — and for such a bottom datum NO raw level exists at any
  `n > a`, making `exists_taylorWilesLevelRaw` false as stated.

  Classically immediate: `𝔟_n = ker(Λ ↠ ℤ_p[Δ_{Q_n}])` and
  `𝔫 = ker(Λ ↠ ℤ_p[Δ_{Q_n}] ↠ ℤ_p)`, the second map being the
  group-ring augmentation.  Equivalently: `Λ/𝔟_n = ℤ_p[Δ_{Q_n}]` is
  `ℤ_p`-free, so `M₀ ≅ (Λ/(𝔫 + 𝔟_n))^d = ℤ_p^d` — which is what
  `M₀ = H¹(X₀(N), ℤ_p)_𝔪` actually is.  Unlike `bIdeal_le` this field
  has content at EVERY level including the bottom one. -/
  bIdeal_le_aug : bIdeal ≤ taylorWilesAug p q
  /-- **The Taylor–Wiles freeness certificate in coordinate form**
  (Diamond 1997, Thm. 2.1): a `Λ`-linear identification of `M` with
  `(Λ/𝔟_n)^d = ℤ_p[Δ_{Q_n}]^d`. -/
  coordM : Nonempty (M ≃ₗ[MvPowerSeries (Fin q) ℤ_[p]]
    (Fin d → MvPowerSeries (Fin q) ℤ_[p] ⧸ bIdeal))
  /-- The bottom control map `M ↠ M₀`. -/
  projM : M →+ M0
  projM_surjective : Function.Surjective projM
  /-- Action compatibility through `ψ`. -/
  projM_smul : ∀ (x : R) (m : M),
    projM (x • m) = ψ (toRuniv x) • projM m
  /-- **The bottom control theorem** (only the nontrivial inclusion;
  see `TaylorWilesLevel.projM_eq_zero`). -/
  projM_eq_zero : ∀ m : M, projM m = 0 →
    m ∈ (taylorWilesAug p q • ⊤ :
      Submodule (MvPowerSeries (Fin q) ℤ_[p]) M)

set_option linter.checkUnivs false in
/-- **Raw levels are levels** (PROVEN 2026-07-25 — the structural half
of the patching-tower assembly): a `TaylorWilesLevelRaw` over a
NONTRIVIAL bottom module is a `TaylorWilesLevel`.

Proof.  Take the coordinate model `N := (Λ/𝔟_n)^d` itself as the
level's Hecke module, transporting the raw data along the `Λ`-linear
coordinate equivalence `e : M ≃ₗ[Λ] N` supplied by `coordM`.  Then

* `moduleQuotM`, `isScalarTowerM`, `freeM`, `finiteM` are the CANONICAL
  instances of the coordinate model (`Λ/𝔟_n` acting on a finite
  product of copies of itself), and `finrankM` is
  `Module.finrank_fin_fun`, which needs `Λ/𝔟_n` to be nontrivial;
* `nontrivialQuot` is derived rather than assumed: `M₀` is nontrivial
  and `projM` is surjective, so `M` is nontrivial, hence so is `N`
  through `e`, hence `Λ/𝔟_n` is nontrivial (a product of copies of a
  subsingleton is a subsingleton);
* the `R`-action transports along `e`
  (`Function.Injective.module` applied to `e.symm`), and
  `diamond_smul` transports because `e` is `Λ`-linear;
* `projM`, its surjectivity, `projM_smul` and the control theorem
  transport by precomposition with `e.symm`, the last one using
  `Submodule.map_smul''` and `LinearEquiv.range` to push
  `𝔫 · M = 𝔫 · ⊤` forward to `𝔫 · ⊤` in `N`.

Unconditionally true; no hypothesis package beyond nontriviality of
`M₀`, which the tower carries anyway (`TaylorWilesTower.nontrivialM0`). -/
theorem nonempty_taylorWilesLevel_of_raw.{a, b, c, s, uR}
    {p : ℕ} [Fact p.Prime]
    {Runiv : Type uR} [CommRing Runiv]
    {T : Type s} [CommRing T] {ψ : Runiv →+* T} {q d n : ℕ}
    {coeff : TaylorWilesCoefficients}
    {M0 : Type c} [AddCommGroup M0] [Module T M0] (hM0 : Nontrivial M0)
    (L : TaylorWilesLevelRaw.{a, b, c, s, uR} p ψ q d n coeff M0) :
    Nonempty (TaylorWilesLevel.{a, 0, c, s, uR} p ψ q d n coeff M0) := by
  classical
  letI := L.commRingR
  letI := L.addCommGroupM
  letI := L.moduleRM
  letI := L.moduleCoeffM
  haveI := hM0
  obtain ⟨e⟩ := L.coordM
  -- the auxiliary Hecke module is nontrivial: it surjects onto `M₀`
  have hMnt : Nontrivial L.M := by
    obtain ⟨x, y, hxy⟩ := exists_pair_ne M0
    obtain ⟨a', ha'⟩ := L.projM_surjective x
    obtain ⟨b', hb'⟩ := L.projM_surjective y
    refine ⟨a', b', fun h => hxy ?_⟩
    rw [← ha', ← hb', h]
  -- hence the level ring `Λ/𝔟_n` is nontrivial
  haveI hQnt : Nontrivial (MvPowerSeries (Fin q) ℤ_[p] ⧸ L.bIdeal) := by
    obtain ⟨x, y, hxy⟩ := hMnt.exists_pair_ne
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    haveI := hcon
    exact hxy (e.injective (Subsingleton.elim _ _))
  -- transport the `R`-action to the coordinate model
  letI : SMul L.R (Fin d → MvPowerSeries (Fin q) ℤ_[p] ⧸ L.bIdeal) :=
    ⟨fun x v => e (x • e.symm v)⟩
  have hsmulR : ∀ (x : L.R)
      (v : Fin d → MvPowerSeries (Fin q) ℤ_[p] ⧸ L.bIdeal),
      x • v = e (x • e.symm v) := fun _ _ => rfl
  letI : Module L.R (Fin d → MvPowerSeries (Fin q) ℤ_[p] ⧸ L.bIdeal) :=
    Function.Injective.module L.R e.symm.toLinearMap.toAddMonoidHom
      e.symm.injective (fun c v => by
        show e.symm (e (c • e.symm v)) = c • e.symm v
        exact e.symm_apply_apply _)
  refine ⟨{ R := L.R
            commRingR := L.commRingR
            pres := L.pres
            pres_surjective := L.pres_surjective
            diamond := L.diamond
            toRuniv := L.toRuniv
            toRuniv_surjective := L.toRuniv_surjective
            ker_toRuniv := L.ker_toRuniv
            M := Fin d → MvPowerSeries (Fin q) ℤ_[p] ⧸ L.bIdeal
            addCommGroupM := inferInstance
            moduleRM := inferInstance
            moduleCoeffM := inferInstance
            diamond_smul := ?_
            bIdeal := L.bIdeal
            bIdeal_le := L.bIdeal_le
            bIdeal_le_aug := L.bIdeal_le_aug
            nontrivialQuot := hQnt
            moduleQuotM := inferInstance
            isScalarTowerM := inferInstance
            freeM := inferInstance
            finiteM := inferInstance
            finrankM := Module.finrank_fin_fun _
            projM := L.projM.comp e.symm.toLinearMap.toAddMonoidHom
            projM_surjective := ?_
            projM_smul := ?_
            projM_eq_zero := ?_ }⟩
  · intro x v
    rw [hsmulR, ← L.diamond_smul, map_smul, e.apply_symm_apply]
  · exact L.projM_surjective.comp e.symm.surjective
  · intro x v
    show L.projM (e.symm (x • v)) = ψ (L.toRuniv x) • L.projM (e.symm v)
    rw [hsmulR, e.symm_apply_apply, L.projM_smul]
  · intro v hv
    have hv' : L.projM (e.symm v) = 0 := hv
    have hmap : e (e.symm v) ∈
        Submodule.map e.toLinearMap
          (taylorWilesAug p q • (⊤ : Submodule (MvPowerSeries (Fin q) ℤ_[p]) L.M)) :=
      Submodule.mem_map_of_mem (L.projM_eq_zero _ hv')
    rwa [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range,
      e.apply_symm_apply] at hmap

/-- **Universe transport for `PatchedModule`** (PROVEN 2026-07-25):
the patched situation is stated polymorphically in its two module
universes `{v, w}`, but every CONSTRUCTION of one lands in the fixed
universes of the data it is built from — the ultraproduct/inverse-limit
extraction below produces `M_∞` in the universe of the tower's modules
and `M₀` in the universe of the tower's bottom module.  This lemma
closes that gap once and for all, so the extraction leaf may be stated
at its natural universes.

Two shrinkings are chained:

* `M_∞` is `Module.Finite` over `Λ = ℤ_p[[x₁, …, x_q]]`, which is a
  `Type 0`; mathlib's `Module.Finite.repr`/`reprEquiv` present any such
  module as a quotient of `Fin n → Λ`, hence by a `Type 0` module —
  and `ULift` then places it in the requested `Type v`.
* `M₀` is not independently shrinkable, but it does not have to be:
  `proj` is surjective with kernel exactly `𝔞·M_∞`
  (`⊆` is the `mem_smul_top_of_proj_eq_zero` field, `⊇` follows from
  `proj_smul`), so `M₀ ≅ M_∞/𝔞M_∞`, and the shrunk `M_∞` gives a
  `Type 0` model of that quotient.  Its `T`-module structure is
  transported along the resulting additive equivalence; the transport
  is coherent with the `Λ`-action because on `M₀` the `Λ`-action
  factors as `ψ ∘ toRuniv` (this is precisely `proj_smul`), which is
  what makes the transported `proj_smul` hold. -/
theorem PatchedModule.nonempty_transport.{v, w, x, y, s, uR} {p : ℕ}
    [Fact p.Prime] {Runiv : Type uR} [CommRing Runiv] {T : Type s}
    [CommRing T] {ψ : Runiv →+* T} (P : PatchedModule.{x, y, s, uR} p ψ) :
    Nonempty (PatchedModule.{v, w, s, uR} p ψ) := by
  classical
  letI := P.addCommGroupMinf
  letI := P.moduleMinf
  letI := P.addCommGroupM0
  letI := P.moduleM0
  haveI : Nontrivial P.M0 := P.nontrivialM0
  haveI : Module.Finite (MvPowerSeries (Fin P.q) P.coeff.carrier) P.Minf := P.finiteMinf
  -- The `Λ`-module structure on `M₀` through `ψ ∘ toRuniv`; `proj_smul`
  -- says exactly that `proj` is `Λ`-linear for it.
  letI : Module (MvPowerSeries (Fin P.q) P.coeff.carrier) P.M0 :=
    Module.compHom P.M0 (ψ.comp P.toRuniv)
  have hsmulM0 : ∀ (x : MvPowerSeries (Fin P.q) P.coeff.carrier) (z : P.M0),
      x • z = ψ (P.toRuniv x) • z := fun _ _ => rfl
  let projₗ : P.Minf →ₗ[MvPowerSeries (Fin P.q) P.coeff.carrier] P.M0 :=
    { toFun := P.proj
      map_add' := P.proj.map_add
      map_smul' := fun x m => by
        simpa only [RingHom.id_apply, hsmulM0] using P.proj_smul x m }
  have hker : LinearMap.ker projₗ =
      RingHom.ker P.toRuniv •
        (⊤ : Submodule (MvPowerSeries (Fin P.q) P.coeff.carrier) P.Minf) := by
    refine le_antisymm (fun m hm => P.mem_smul_top_of_proj_eq_zero m hm) ?_
    rw [Submodule.smul_le]
    intro a ha m _
    show P.proj (a • m) = 0
    rw [P.proj_smul, RingHom.mem_ker.mp ha, map_zero, zero_smul]
  -- The `Type 0` model of `M_∞` and the induced `Type 0` model of `M₀`.
  set Minf₀ := Module.Finite.repr (MvPowerSeries (Fin P.q) P.coeff.carrier) P.Minf with hMinf₀
  set e : Minf₀ ≃ₗ[MvPowerSeries (Fin P.q) P.coeff.carrier] P.Minf :=
    Module.Finite.reprEquiv (MvPowerSeries (Fin P.q) P.coeff.carrier) P.Minf with he
  set 𝔞 : Ideal (MvPowerSeries (Fin P.q) P.coeff.carrier) := RingHom.ker P.toRuniv with h𝔞
  have hmap : Submodule.map
      (e : Minf₀ →ₗ[MvPowerSeries (Fin P.q) P.coeff.carrier] P.Minf) (𝔞 • ⊤) = 𝔞 • ⊤ := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  set M0₀ := Minf₀ ⧸ (𝔞 • ⊤ : Submodule (MvPowerSeries (Fin P.q) P.coeff.carrier) Minf₀)
    with hM0₀
  set g : M0₀ ≃ₗ[MvPowerSeries (Fin P.q) P.coeff.carrier] P.M0 :=
    (Submodule.Quotient.equiv _ _ e hmap).trans
      ((Submodule.quotEquivOfEq _ _ hker.symm).trans
        (projₗ.quotKerEquivOfSurjective P.proj_surjective)) with hg
  have hg_mk : ∀ m : Minf₀, g (Submodule.Quotient.mk m) = P.proj (e m) := by
    intro m; rfl
  -- Transport the `T`-action along `g`.
  letI : SMul T M0₀ := ⟨fun t z => g.symm (t • g z)⟩
  have hgsmul : ∀ (t : T) (z : M0₀), g (t • z) = t • g z := by
    intro t z; exact g.apply_symm_apply _
  letI : Module T M0₀ :=
    Function.Injective.module T (g.toLinearMap.toAddMonoidHom) g.injective hgsmul
  have hΛT : ∀ (x : MvPowerSeries (Fin P.q) P.coeff.carrier) (z : M0₀),
      x • z = ψ (P.toRuniv x) • z := by
    intro x z
    refine g.injective ?_
    rw [map_smul, hgsmul, hsmulM0]
  haveI : Nontrivial M0₀ := g.toEquiv.nontrivial
  haveI : Module.Finite (MvPowerSeries (Fin P.q) P.coeff.carrier) Minf₀ :=
    Module.Finite.equiv e.symm
  refine ⟨{ q := P.q
            coeff := P.coeff
            Minf := ULift.{v} Minf₀
            finiteMinf := Module.Finite.equiv
              (ULift.moduleEquiv (R := MvPowerSeries (Fin P.q) P.coeff.carrier)
                (M := Minf₀)).symm
            exists_isRegular := ?_
            toRuniv := P.toRuniv
            toRuniv_surjective := P.toRuniv_surjective
            M0 := ULift.{w} M0₀
            nontrivialM0 := inferInstance
            proj := ((AddEquiv.ulift (α := M0₀)).symm.toAddMonoidHom.comp
              ((Submodule.mkQ _).toAddMonoidHom.comp
                (AddEquiv.ulift (α := Minf₀)).toAddMonoidHom))
            proj_surjective := ?_
            proj_smul := ?_
            mem_smul_top_of_proj_eq_zero := ?_ }⟩
  · obtain ⟨rs, hlen, hmem, hreg⟩ := P.exists_isRegular
    refine ⟨rs, hlen, hmem, ?_⟩
    exact ((ULift.moduleEquiv (R := MvPowerSeries (Fin P.q) P.coeff.carrier)
      (M := Minf₀)).trans e |>.isRegular_congr rs).mpr hreg
  · intro z
    obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective
      (𝔞 • ⊤ : Submodule (MvPowerSeries (Fin P.q) P.coeff.carrier) Minf₀) z.down
    exact ⟨ULift.up m, congrArg ULift.up hm⟩
  · intro x m
    show ULift.up (Submodule.Quotient.mk (x • m.down)) =
      ψ (P.toRuniv x) • ULift.up (Submodule.Quotient.mk m.down)
    rw [Submodule.Quotient.mk_smul, hΛT]
    rfl
  · intro m hm
    have hm' : (Submodule.Quotient.mk m.down :
        Minf₀ ⧸ (𝔞 • ⊤ : Submodule (MvPowerSeries (Fin P.q) P.coeff.carrier) Minf₀)) = 0 :=
      congrArg ULift.down hm
    have hmem : m.down ∈ (𝔞 • ⊤ : Submodule (MvPowerSeries (Fin P.q) P.coeff.carrier) Minf₀) := by
      rwa [Submodule.Quotient.mk_eq_zero] at hm'
    have hmapU : Submodule.map (ULift.moduleEquiv
        (R := MvPowerSeries (Fin P.q) P.coeff.carrier) (M := Minf₀)).symm.toLinearMap
        (𝔞 • ⊤) = 𝔞 • ⊤ := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
    rw [← hmapU]
    exact ⟨m.down, hmem, rfl⟩

/-! #### Instantiating the vendored patching development

The three helper lemmas below isolate the bookkeeping that the
instantiation of `Fermat/FLT/Modularity/PatchingVendored/` at a
`TaylorWilesSystem` needs, so that neither of the two `Λ`-actions on the
patched module — the DIAMOND one (through `S.diamond`) and the
PRESENTATION one (through `PatchingAlgebra.lift R F S.pres`) — has to be
mentioned twice.  -/

/-- `IsRegular` counterpart of mathlib's
`RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff` (PROVEN
2026-07-25, same one-line proof through `AddEquiv.isRegular_congr`;
mathlib carries only the weakly-regular version). -/
theorem isRegular_map_algebraMap_iff_of_tower
    {A B N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N] (rs : List A) :
    RingTheory.Sequence.IsRegular N (rs.map (algebraMap A B)) ↔
      RingTheory.Sequence.IsRegular N rs :=
  (AddEquiv.refl N).isRegular_congr <| List.forall₂_map_left_iff.mpr <|
    List.forall₂_same.mpr fun r _ => algebraMap_smul B r

/-- Regularity of a sequence transfers along `Module.compHom` (PROVEN
2026-07-25): if the image sequence `rs.map f` is `N`-regular for the
`B`-action, then `rs` is `N`-regular for the `A`-action through `f`. -/
theorem isRegular_compHom {A B N : Type*} [CommRing A] [CommRing B]
    [AddCommGroup N] [Module B N] (f : A →+* B) (rs : List A)
    (h : RingTheory.Sequence.IsRegular N (rs.map f)) :
    letI := Module.compHom N f
    RingTheory.Sequence.IsRegular N rs := by
  letI : Algebra A B := f.toAlgebra
  letI := Module.compHom N f
  haveI : IsScalarTower A B N := .of_algebraMap_smul fun _ _ => rfl
  exact (isRegular_map_algebraMap_iff_of_tower (B := B) (N := N) rs).mp h

/-- Module-finiteness transfers along a SURJECTIVE ring homomorphism
(PROVEN 2026-07-25): a `B`-module finite over `B` is finite over `A`
when `A ↠ B`, because `B` is then a cyclic `A`-algebra. -/
theorem moduleFinite_compHom {A B N : Type*} [CommRing A] [CommRing B]
    [AddCommGroup N] [Module B N] (f : A →+* B) (hf : Function.Surjective f)
    (h : Module.Finite B N) :
    letI := Module.compHom N f
    Module.Finite A N := by
  letI : Algebra A B := f.toAlgebra
  letI := Module.compHom N f
  haveI : IsScalarTower A B N := .of_algebraMap_smul fun _ _ => rfl
  haveI := h
  haveI : Module.Finite A B := Module.Finite.of_surjective (Algebra.linearMap A B) hf
  exact Module.Finite.trans B N

/-- **The packaging step of the patching extraction** (PROVEN
2026-07-25): every `PatchedModule` field, read off from data living over
an auxiliary local ring `R_∞` presented by `Λ = ℤ_p[[x₁, …, x_q]]`.

This is where the `Λ`-versus-`R_∞` bookkeeping happens, once:

* the `Λ`-action on `M_∞` is the one through the presentation `lift`
  (`Module.compHom`), which is what makes `toRuniv := θ ∘ lift`
  surjective — the DIAMOND `Λ`-action would not give a surjection,
  since the diamond variables die in `Runiv`;
* `finiteMinf` is `moduleFinite_compHom`;
* `exists_isRegular` lifts the given `R_∞`-regular sequence back along
  the surjection `lift`, and the lifts may be chosen in `𝔪_Λ` because a
  surjection of local rings is local (`IsLocalHom.of_surjective`), so a
  lift of a non-unit is a non-unit;
* `mem_smul_top_of_proj_eq_zero` converts `ker θ ·M_∞` (over `R_∞`) into
  `ker (θ ∘ lift) ·M_∞` (over `Λ`) elementwise, again along `lift`. -/
theorem nonempty_patchedModule_of_patchingData.{v, w, s, uR, u}
    {p : ℕ} [Fact p.Prime] {q : ℕ}
    {Runiv : Type uR} [CommRing Runiv] {T : Type s} [CommRing T] (ψ : Runiv →+* T)
    (coeff : TaylorWilesCoefficients)
    {Rinf : Type u} [CommRing Rinf] [IsLocalRing Rinf]
    (lift : MvPowerSeries (Fin q) coeff.carrier →+* Rinf) (hlift : Function.Surjective lift)
    (θ : Rinf →+* Runiv) (hθ : Function.Surjective θ)
    {Minf : Type v} [AddCommGroup Minf] [Module Rinf Minf]
    (hfin : Module.Finite Rinf Minf)
    (rs : List Rinf) (hlen : rs.length = q + 1)
    (hmem : ∀ x ∈ rs, x ∈ IsLocalRing.maximalIdeal Rinf)
    (hreg : RingTheory.Sequence.IsRegular Minf rs)
    {M0 : Type w} [AddCommGroup M0] [Module T M0] (hM0 : Nontrivial M0)
    (proj : Minf →+ M0) (hprojsurj : Function.Surjective proj)
    (hprojsmul : ∀ (a : Rinf) (m : Minf), proj (a • m) = ψ (θ a) • proj m)
    (hprojker : ∀ m : Minf, proj m = 0 →
      m ∈ RingHom.ker θ • (⊤ : Submodule Rinf Minf)) :
    Nonempty (PatchedModule.{v, w, s, uR} p ψ) := by
  classical
  letI : Module (MvPowerSeries (Fin q) coeff.carrier) Minf := Module.compHom Minf lift
  haveI hlh : IsLocalHom lift := .of_surjective lift hlift
  obtain ⟨g, hg⟩ : ∃ g : Rinf → MvPowerSeries (Fin q) coeff.carrier, ∀ b, lift (g b) = b :=
    ⟨fun b => (hlift b).choose, fun b => (hlift b).choose_spec⟩
  have hgmem : ∀ a ∈ rs,
      g a ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin q) coeff.carrier) := by
    intro a ha
    rw [IsLocalRing.mem_maximalIdeal]
    intro hu
    exact (IsLocalRing.mem_maximalIdeal a).mp (hmem a ha) (hg a ▸ hu.map lift)
  have hmaplift : (rs.map g).map lift = rs := by
    simp [List.map_map, Function.comp_def, hg]
  refine ⟨{ q := q
            coeff := coeff
            Minf := Minf
            moduleMinf := inferInstance
            finiteMinf := moduleFinite_compHom lift hlift hfin
            exists_isRegular := ⟨rs.map g, by simpa using hlen, ?_, ?_⟩
            toRuniv := θ.comp lift
            toRuniv_surjective := hθ.comp hlift
            M0 := M0
            nontrivialM0 := hM0
            proj := proj
            proj_surjective := hprojsurj
            proj_smul := ?_
            mem_smul_top_of_proj_eq_zero := ?_ }⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact hgmem a ha
  · exact isRegular_compHom lift (rs.map g) (by rw [hmaplift]; exact hreg)
  · intro x m
    show proj (lift x • m) = ψ (θ (lift x)) • proj m
    exact hprojsmul (lift x) m
  · intro m hm
    refine Submodule.smul_induction_on (hprojker m hm) ?_ ?_
    · intro a ha n _
      have h1 : (g a) • n = a • n := by
        show lift (g a) • n = a • n
        rw [hg a]
      rw [← h1]
      refine Submodule.smul_mem_smul ?_ trivial
      rw [RingHom.mem_ker] at ha ⊢
      show θ (lift (g a)) = 0
      rw [hg a]; exact ha
    · intro x y hx hy
      exact add_mem hx hy

section PatchingInstantiation

open _root_.IsLocalRing
open scoped MvPowerSeries.WithPiTopology

attribute [local instance] Module.quotientAnnihilator

/-! ### The leaves of the patching instantiation

DECOMPOSED 2026-07-25.  `exists_patchedModule_of_fields` below is pure
glue: it hands the raw fields of a `TaylorWilesSystem` to the vendored
patching development in `Modularity/PatchingVendored/`.  It used to
carry ten inline `sorry`ed `have`s, which is the largest single leaf
this file ever had and was not ownable by anybody: the ten steps live in
five unrelated mathematical contexts.  They are restated here as
separate top-level theorems, each in the SMALLEST context in which it is
true, so each has an owner who needs to know only that context:

* three about the coefficient ring `Λ = ℤ_p[[x₁, …, x_q]]` alone —
  `topologicallyFG_int_mvPowerSeries`,
  `finite_quotient_maximalIdeal_pow_mvPowerSeries`,
  `ker_constantCoeff_mvPowerSeries`;
* four of generic commutative algebra —
  `annihilator_eq_of_linearEquiv_piQuotient`,
  `free_quotientAnnihilator_of_linearEquiv_piQuotient`,
  `uniformlyBoundedRank_of_linearEquiv_piQuotient`,
  `mem_maximalIdeal_of_isRegular`;
* three about profinite local rings and their quotients —
  `finite_quotient_maximalIdeal_pow_of_surjective`,
  `continuous_of_finite_quotient_maximalIdeal_pow`,
  `algebra_uniformlyBoundedRank_of_surjective`;
* one about `ℤ_p`-rigidity of the bottom ring,
  `subsingleton_ringHom_padicInt`, packaged for use as
  `ringHom_mvPowerSeries_eq_of_taylorWilesAug_le_ker`;
* two about the bottom identification of the patched module,
  `quotientEquivOver_mkQ_smul` and
  `mem_ker_smul_top_of_quotientEquivOver_mkQ_eq_zero`, stated over the
  vendored variable context so that they are `smul_lemma` resp.
  `Submodule.map_algebraMap_smul` plus quotient bookkeeping.

Two shared bricks were factored out in the process because three leaves
each rested on them: `annihilator_eq_of_linearEquiv_piQuotient` (which
identifies `Ann_Λ (M n)` with `𝔟_n` and feeds the freeness, the rank
bound and the patching-system condition) and
`finite_quotient_maximalIdeal_pow_mvPowerSeries` (which feeds both
continuity of the diamond action and the uniform rank bound on the level
rings).

STATUS after the decomposition (2026-07-25).  Twelve of the sixteen are
PROVEN outright — the cut turned out to be most of the work:
`annihilator_eq_of_linearEquiv_piQuotient`,
`mem_maximalIdeal_of_isRegular`,
`continuousSMul_of_continuous_algebraMap`,
`finite_quotient_maximalIdeal_pow_of_surjective`,
`continuous_of_finite_quotient_maximalIdeal_pow`,
`ringHom_mvPowerSeries_eq_of_taylorWilesAug_le_ker`,
`algebra_uniformlyBoundedRank_of_surjective`,
`isPatchingSystem_of_annihilator_le_maximalIdeal_pow`,
`quotientEquivOver_mkQ_smul`,
`mem_ker_smul_top_of_quotientEquivOver_mkQ_eq_zero`, and — added
2026-07-25 — `free_quotientAnnihilator_of_linearEquiv_piQuotient` and
`uniformlyBoundedRank_of_linearEquiv_piQuotient`, both over the new shared
brick `linearEquivPiQuotientAnnihilator`.  FOUR remain open and are the
real frontier here:

1. `topologicallyFG_int_mvPowerSeries` — density of `ℤ[x₁,…,x_q]` in `Λ`;
   PROVEN 2026-07-25;
2. `finite_quotient_maximalIdeal_pow_mvPowerSeries` — `|Λ/𝔪^k| < ∞`,
   which needs `Λ`'s residue field identified as `𝔽_p`; PROVEN 2026-07-25
   over the new brick `mem_maximalIdeal_mvPowerSeries`;
3. `ker_constantCoeff_mvPowerSeries` — `ker (constantCoeff) = (X₁,…,X_q)`
   in finitely many variables; PROVEN 2026-07-25 over the new brick
   `mem_span_X_image_of_coeff_eq_zero`;
4. `subsingleton_ringHom_padicInt` — `ℤ_p`-rigidity of a complete local
   ring with finite residue field; PROVEN 2026-07-25.

**ALL FOUR ARE NOW PROVEN**, as are the two coordinate-transport leaves
(`free_quotientAnnihilator_of_linearEquiv_piQuotient` and
`uniformlyBoundedRank_of_linearEquiv_piQuotient`) that stood at (4)–(5)
in an earlier numbering, so this block contributes no open leaf. -/

/-- **`Λ = ℤ_p[[x₁, …, x_q]]` is topologically finitely generated over
`ℤ`** (patching-instantiation leaf 1), for the scoped product topology
`MvPowerSeries.WithPiTopology`.

This is the one hypothesis of the vendored `PatchingVendored/Algebra.lean`
that profiniteness does not hand over for free.  The witnessing finite set
is the set of variables `{X i : i : Fin q}`, whose `ℤ`-subalgebra inside
`Λ` is the polynomial ring `ℤ[x₁, …, x_q]`.  It is DENSE because the
topology is the PRODUCT topology on `(Fin q →₀ ℕ) → ℤ_[p]`: a basic
neighbourhood of `f` constrains only finitely many coefficients, so
truncate `f` to those finitely many monomials and approximate each of
their coefficients by an integer, which is possible because `ℤ` is dense
in `ℤ_[p]` (`PadicInt.denseRange_intCast` / `denseRange_natCast`).

Stated for an ARBITRARY `Algebra ℤ Λ` instance because the vendored use
site fixes that instance by unification and there is no guarantee it is
syntactically `algebraInt`; the statement is harmless because
`Algebra ℤ R` is a subsingleton.

PROVEN 2026-07-25.  The proof never touches a neighbourhood basis: it
passes through the topological closure `B := (adjoin ℤ (range X))ᶜˡ`,
which is again a `Subalgebra ℤ Λ` (`Subalgebra.topologicalClosure`,
available because `Λ` is a topological ring for the pi topology).  Three
steps.  (i) `B` contains every constant `C a`, `a : ℤ_[p]`: `C` is
continuous (`MvPowerSeries.WithPiTopology.continuous_C`), so it carries
`closure (range (Int.cast))` — which is all of `ℤ_[p]` by
`PadicInt.denseRange_intCast` — into `closure (C '' range Int.cast)`, and
`C (n : ℤ) = (n : Λ)` lies in the subalgebra `adjoin ℤ (range X)` already.
(ii) `B` therefore contains the image of every `ℤ_[p]`-POLYNOMIAL, by
`MvPolynomial.induction_on` over `C`/`+`/`· X i`, using that `B` is a
subalgebra and contains each `X i`.  (iii) That image is dense
(`MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries`), so
`closure (adjoin ℤ (range X)) = ⊤`. -/
theorem topologicallyFG_int_mvPowerSeries {O : Type*} [CommRing O]
    [TopologicalSpace O] [IsTopologicalRing O]
    (hO : Algebra.TopologicallyFG ℤ O) (q : ℕ)
    [Algebra ℤ (MvPowerSeries (Fin q) O)] :
    Algebra.TopologicallyFG ℤ (MvPowerSeries (Fin q) O) := by
  classical
  obtain ⟨sO, hsO⟩ := hO.out
  refine ⟨⟨sO.image (MvPowerSeries.C (σ := Fin q) (R := O)) ∪
    Finset.univ.image (MvPowerSeries.X (σ := Fin q) (R := O)), ?_⟩⟩
  set Λ := MvPowerSeries (Fin q) O
  set gen : Set Λ := (MvPowerSeries.C (σ := Fin q) (R := O)) '' (sO : Set O) ∪
    Set.range (MvPowerSeries.X (σ := Fin q) (R := O)) with hgen
  have hcoe : ((sO.image (MvPowerSeries.C (σ := Fin q) (R := O)) ∪
      Finset.univ.image (MvPowerSeries.X (σ := Fin q) (R := O)) : Finset Λ) : Set Λ) = gen := by
    simp [hgen]
  rw [hcoe]
  set A : Subalgebra ℤ Λ := Algebra.adjoin ℤ gen with hA
  set B : Subalgebra ℤ Λ := A.topologicalClosure with hB
  have hXB : ∀ i : Fin q, (MvPowerSeries.X i : Λ) ∈ B :=
    fun i => A.le_topologicalClosure (Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩))
  have hCB : ∀ a : O, (MvPowerSeries.C a : Λ) ∈ B := by
    intro a
    have hmem : a ∈ closure ((Algebra.adjoin ℤ (sO : Set O) : Subalgebra ℤ O) : Set O) :=
      hsO a
    have himg : (MvPowerSeries.C : O → Λ) ''
          closure ((Algebra.adjoin ℤ (sO : Set O) : Subalgebra ℤ O) : Set O)
        ⊆ closure ((MvPowerSeries.C : O → Λ) ''
          ((Algebra.adjoin ℤ (sO : Set O) : Subalgebra ℤ O) : Set O)) :=
      image_closure_subset_closure_image MvPowerSeries.WithPiTopology.continuous_C
    have h2 : (MvPowerSeries.C a : Λ) ∈
        closure ((MvPowerSeries.C : O → Λ) ''
          ((Algebra.adjoin ℤ (sO : Set O) : Subalgebra ℤ O) : Set O)) :=
      himg ⟨a, hmem, rfl⟩
    have h3mem : ∀ x ∈ (Algebra.adjoin ℤ (sO : Set O) : Subalgebra ℤ O),
        (MvPowerSeries.C x : Λ) ∈ A := by
      intro x hx
      induction hx using Algebra.adjoin_induction with
      | mem y hy => exact Algebra.subset_adjoin (Or.inl ⟨y, hy, rfl⟩)
      | algebraMap n =>
        have hcast : (MvPowerSeries.C (algebraMap ℤ O n) : Λ) = (n : Λ) := by simp
        rw [hcast]
        exact intCast_mem A n
      | add x y _ _ ihx ihy => rw [map_add]; exact add_mem ihx ihy
      | mul x y _ _ ihx ihy => rw [map_mul]; exact mul_mem ihx ihy
    have h3 : ((MvPowerSeries.C : O → Λ) ''
        ((Algebra.adjoin ℤ (sO : Set O) : Subalgebra ℤ O) : Set O)) ⊆ (A : Set Λ) := by
      rintro _ ⟨x, hx, rfl⟩
      exact h3mem x hx
    have h4 : closure ((MvPowerSeries.C : O → Λ) ''
          ((Algebra.adjoin ℤ (sO : Set O) : Subalgebra ℤ O) : Set O))
        ⊆ (B : Set Λ) := by
      rw [hB, Subalgebra.topologicalClosure_coe]
      exact closure_mono h3
    exact h4 h2
  have hpoly : ∀ φ : MvPolynomial (Fin q) O, ((φ : Λ)) ∈ B := by
    intro φ
    induction φ using MvPolynomial.induction_on with
    | C a =>
      rw [MvPolynomial.coe_C]
      exact hCB a
    | add f g hf hg =>
      rw [MvPolynomial.coe_add]
      exact add_mem hf hg
    | mul_X f i hf =>
      rw [MvPolynomial.coe_mul, MvPolynomial.coe_X]
      exact mul_mem hf (hXB i)
  rw [dense_iff_closure_eq]
  refine Set.eq_univ_of_univ_subset ?_
  rw [← (MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries
    (R := O) (σ := Fin q)).closure_range]
  refine closure_minimal ?_ isClosed_closure
  rintro _ ⟨φ, rfl⟩
  have hmemB := hpoly φ
  rw [hB, ← SetLike.mem_coe, Subalgebra.topologicalClosure_coe] at hmemB
  exact hmemB

/-- **The maximal ideal of a multivariate power series ring over a local
ring is the preimage of `𝔪` under `constantCoeff`** — a unit of
`Λ[[x]]` is exactly a series with unit constant term
(`MvPowerSeries.isUnit_iff_constantCoeff`).  The `PowerSeries` analogue
`mem_maximalIdeal_powerSeries` is proven far above in the
Auslander–Buchsbaum section; this is the multivariate one, needed here
to identify the residue field of `Λ`. -/
theorem mem_maximalIdeal_mvPowerSeries {σ : Type*} {A : Type*} [CommRing A] [IsLocalRing A]
    (f : MvPowerSeries σ A) :
    f ∈ maximalIdeal (MvPowerSeries σ A) ↔ MvPowerSeries.constantCoeff f ∈ maximalIdeal A := by
  simp [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]

/-- **The `𝔪`-adic truncations of `Λ = ℤ_p[[x₁, …, x_q]]` are finite**
(patching-instantiation shared brick, consumed by leaves 5 and 6).

`Λ` is local Noetherian (`isNoetherianRing_mvPowerSeries`) with residue
field `𝔽_p`, since `𝔪_Λ = (p, X₁, …, X_q)` and `Λ/𝔪_Λ ≃ ℤ_[p]/p ≃ 𝔽_p`.
So `Finite (Λ ⧸ 𝔪_Λ)`, and `Ideal.finite_quotient_pow` (which needs only
`𝔪_Λ` finitely generated, i.e. Noetherianity) upgrades that to every
power.  This is exactly the route `IsLocalRing.compactSpace_of_finite_residueField`
takes in `PatchingVendored/AdicTopology.lean`.

PROVEN 2026-07-25 along that route; the residue field is identified
without ever computing `𝔪_Λ` itself, by exhibiting the composite
`ψ = PadicInt.toZMod ∘ constantCoeff : Λ →+* ZMod p` as a surjection with
kernel `𝔪_Λ` (`mem_maximalIdeal_mvPowerSeries` plus
`PadicInt.ker_toZMod`). -/
theorem finite_quotient_maximalIdeal_pow_mvPowerSeries {O : Type*} [CommRing O]
    [IsLocalRing O] [IsNoetherianRing O]
    (hOres : Finite (O ⧸ maximalIdeal O)) (q k : ℕ) :
    Finite (MvPowerSeries (Fin q) O ⧸
      maximalIdeal (MvPowerSeries (Fin q) O) ^ k) := by
  haveI : IsNoetherianRing (MvPowerSeries (Fin q) O) :=
    PowerSeriesAdicComplete.isNoetherianRing_mvPowerSeries q
  haveI := hOres
  set ψ : MvPowerSeries (Fin q) O →+* O ⧸ maximalIdeal O :=
    (Ideal.Quotient.mk (maximalIdeal O)).comp MvPowerSeries.constantCoeff with hψ
  have hsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨MvPowerSeries.C y, by simp [hψ, hy]⟩
  have hker : RingHom.ker ψ = maximalIdeal (MvPowerSeries (Fin q) O) := by
    ext f
    rw [RingHom.mem_ker, mem_maximalIdeal_mvPowerSeries, hψ, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem]
  haveI : Finite (MvPowerSeries (Fin q) O ⧸ maximalIdeal (MvPowerSeries (Fin q) O)) :=
    Finite.of_equiv (O ⧸ maximalIdeal O)
      ((Ideal.quotEquivOfEq hker.symm).trans
        (RingHom.quotientKerEquivOfSurjective hsurj)).symm.toEquiv
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) k

/-- **Peeling variables off one at a time** (the working form of the
augmentation-ideal leaf below, PROVEN 2026-07-25): if every coefficient
of `f` supported away from the finite set `s` vanishes, then `f` lies in
the ideal generated by `{X i : i ∈ s}`.

Induction on the FINSET `s`, which is where the finiteness hypothesis of
`ker_constantCoeff_mvPowerSeries` actually gets consumed — no currying
isomorphism is needed.  At `s = insert a t`, split `f` coefficientwise
into the part `h` supported on `d a = 0` and the rest: the rest is
divisible by `X a` (`MvPowerSeries.X_dvd_iff`) and `h` satisfies the
inductive hypothesis for `t`. -/
theorem mem_span_X_image_of_coeff_eq_zero {σ : Type*} [DecidableEq σ] {A : Type*} [CommRing A]
    (s : Finset σ) (f : MvPowerSeries σ A)
    (hf : ∀ d : σ →₀ ℕ, (∀ i ∈ s, d i = 0) → MvPowerSeries.coeff d f = 0) :
    f ∈ Ideal.span (MvPowerSeries.X '' (s : Set σ)) := by
  classical
  induction s using Finset.induction generalizing f with
  | empty =>
    have hz : f = 0 := by
      ext d
      simpa using hf d (by simp)
    simp [hz]
  | insert a t ha ih =>
    set h : MvPowerSeries σ A := fun d => if d a = 0 then MvPowerSeries.coeff d f else 0 with hh
    have hcoeff : ∀ d : σ →₀ ℕ,
        MvPowerSeries.coeff d h = if d a = 0 then MvPowerSeries.coeff d f else 0 := by
      intro d
      rw [MvPowerSeries.coeff_apply, hh]
    have hdvd : (MvPowerSeries.X a : MvPowerSeries σ A) ∣ (f - h) := by
      rw [MvPowerSeries.X_dvd_iff]
      intro m hm
      rw [map_sub, hcoeff, if_pos hm, sub_self]
    obtain ⟨g, hg⟩ := hdvd
    have hIH : h ∈ Ideal.span (MvPowerSeries.X '' (t : Set σ)) := by
      refine ih h ?_
      intro d hd
      rw [hcoeff]
      split_ifs with hda
      · refine hf d ?_
        intro i hi
        rcases Finset.mem_insert.mp hi with h1 | h1
        · exact h1 ▸ hda
        · exact hd i h1
      · rfl
    have hfeq : f = MvPowerSeries.X a * g + h := by
      have hsub : f - h = MvPowerSeries.X a * g := hg
      linear_combination (norm := ring_nf) hsub
    rw [hfeq]
    refine Ideal.add_mem _ ?_ ?_
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨a, by simp, rfl⟩)
    · refine Ideal.span_mono ?_ hIH
      exact Set.image_mono (by simp [Finset.coe_insert])

/-- **The augmentation ideal is the kernel of the constant coefficient**
(patching-instantiation leaf 7a): for FINITELY many variables,
`ker (constantCoeff) = (X₁, …, X_q) = taylorWilesAug`.

`⊇` is `constantCoeff (X i) = 0`.  `⊆` is
`mem_span_X_image_of_coeff_eq_zero` at `s = univ`: the only exponent `d`
with `d i = 0` for every `i` is `d = 0`, so the hypothesis there is
exactly `constantCoeff f = 0`.  (The `Option`-currying isomorphism
`optionCurryEquiv` is NOT needed — the induction runs over the finset of
variables directly.)

FINITENESS IS ESSENTIAL and is why this is stated over `Fin q`: over
infinitely many variables `∑ᵢ Xᵢ` has zero constant coefficient but is not
in the span of the variables, an ideal all of whose elements involve only
finitely many of them.  In the proof it is consumed as `Finset.univ`.

PROVEN 2026-07-25. -/
theorem ker_constantCoeff_mvPowerSeries (q : ℕ) (A : Type*) [CommRing A] :
    RingHom.ker (MvPowerSeries.constantCoeff (σ := Fin q) (R := A)) =
      Ideal.span (Set.range MvPowerSeries.X) := by
  apply le_antisymm
  · intro f hf
    rw [RingHom.mem_ker] at hf
    have key := mem_span_X_image_of_coeff_eq_zero (Finset.univ : Finset (Fin q)) f ?_
    · rwa [Finset.coe_univ, Set.image_univ] at key
    · intro d hd
      have hd0 : d = 0 := by
        ext i
        exact hd i (Finset.mem_univ i)
      subst hd0
      simpa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using hf
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [SetLike.mem_coe, RingHom.mem_ker]

/-- **The annihilator of a coordinatized level module** (patching-instantiation
shared brick, consumed by leaves 2, 3 and 4; PROVEN 2026-07-25): if `N ≃ₗ[Λ] (Λ/𝔟)^d` and `N`
is nontrivial then `Ann_Λ N = 𝔟`.

Two steps, both routine: the annihilator is an invariant of the `Λ`-linear
isomorphism class (transport `r • n = 0` along `f`), and
`Ann_Λ ((Λ/𝔟)^d) = 𝔟` as soon as `d ≥ 1`, by testing on the constant
family `(1, …, 1)` in one direction and `Ideal.Quotient.eq_zero_iff_mem` in
the other.  `d ≥ 1` is forced by `Nontrivial N`, which the use site gets
from surjectivity of `projM` onto the nontrivial `M₀`. -/
theorem annihilator_eq_of_linearEquiv_piQuotient {Λ : Type*} [CommRing Λ]
    {N : Type*} [AddCommGroup N] [Module Λ N] [Nontrivial N]
    {d : ℕ} {b : Ideal Λ} (f : N ≃ₗ[Λ] (Fin d → Λ ⧸ b)) :
    Module.annihilator Λ N = b := by
  haveI : Nontrivial (Fin d → Λ ⧸ b) := f.symm.surjective.nontrivial
  have hd : 0 < d := by
    by_contra hcon
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (Fin d → Λ ⧸ b)
    exact hxy (funext fun i => absurd i.2 (by omega))
  ext r
  rw [Module.mem_annihilator]
  constructor
  · intro hr
    have h1 := congrArg f (hr (f.symm (fun _ => (1 : Λ ⧸ b))))
    rw [map_smul, f.apply_symm_apply, map_zero] at h1
    have h3 : r • (1 : Λ ⧸ b) = 0 := congrFun h1 ⟨0, hd⟩
    rwa [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem] at h3
  · intro hr n
    apply f.injective
    rw [map_smul, map_zero]
    funext i
    show r • (f n i) = 0
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (f n i)
    rw [← hy, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ hr

/-- **The coordinatization, read over `Λ/Ann` instead of over `Λ`**
(patching-instantiation shared brick, consumed by leaves 2 and 3; PROVEN
2026-07-25).

This is the whole content of both leaves and the reason they were given a
single owner.  Given `f : N ≃ₗ[Λ] (Λ/𝔟)^d` with `N` nontrivial,
`annihilator_eq_of_linearEquiv_piQuotient` says `Ann_Λ N = 𝔟`, so the
codomain may be rewritten as `(Λ/Ann_Λ N)^d` by
`Ideal.quotientEquivAlgOfEq` — which is a `Λ`-algebra equivalence, hence
`Λ`-linear componentwise.  That produces a `Λ`-linear equivalence
`N ≃ₗ[Λ] (Λ/Ann_Λ N)^d`; and since `Λ → Λ/Ann_Λ N` is SURJECTIVE, a
`Λ`-linear map between two `Λ/Ann_Λ N`-modules is automatically
`Λ/Ann_Λ N`-linear (`LinearEquiv.extendScalarsOfSurjective`).  No
semilinear algebra and no `RingHomInvPair` bookkeeping is needed.

The `Λ/Ann_Λ N`-module structure on `N` here is the local instance
`Module.quotientAnnihilator` declared at the top of this section, i.e. the
one the vendored `Module.UniformlyBoundedRank` and `Module.Free`
hypotheses are stated over. -/
noncomputable def linearEquivPiQuotientAnnihilator {Λ : Type*} [CommRing Λ]
    {N : Type*} [AddCommGroup N] [Module Λ N] [Nontrivial N]
    {d : ℕ} {b : Ideal Λ} (f : N ≃ₗ[Λ] (Fin d → Λ ⧸ b)) :
    N ≃ₗ[Λ ⧸ Module.annihilator Λ N] (Fin d → Λ ⧸ Module.annihilator Λ N) :=
  LinearEquiv.extendScalarsOfSurjective
    (R := Λ) (S := Λ ⧸ Module.annihilator Λ N)
    (by
      rw [Ideal.Quotient.algebraMap_eq]
      exact Ideal.Quotient.mk_surjective)
    (f ≪≫ₗ LinearEquiv.piCongrRight fun _ =>
      (Ideal.quotientEquivAlgOfEq Λ
        (annihilator_eq_of_linearEquiv_piQuotient f).symm).toLinearEquiv)

/-- **A coordinatized level module is free over `Λ/Ann`**
(patching-instantiation leaf 2; PROVEN 2026-07-25), the hypothesis
`[∀ i, Module.Free (Λ ⧸ Ann Λ (M i)) (M i)]` of the vendored development.

By `annihilator_eq_of_linearEquiv_piQuotient` the base ring `Λ ⧸ Ann_Λ N`
IS `Λ ⧸ 𝔟`, over which `(Λ/𝔟)^d` is free of rank `d`.  The only wrinkle is
that `f` is stated `Λ`-linearly while freeness is asked over the quotient;
that is exactly what `linearEquivPiQuotientAnnihilator` above removes, after
which this is `Module.Free.of_equiv` against the free module `(Λ/Ann)^d`. -/
theorem free_quotientAnnihilator_of_linearEquiv_piQuotient {Λ : Type*} [CommRing Λ]
    {N : Type*} [AddCommGroup N] [Module Λ N] [Nontrivial N]
    {d : ℕ} {b : Ideal Λ} (f : N ≃ₗ[Λ] (Fin d → Λ ⧸ b)) :
    Module.Free (Λ ⧸ Module.annihilator Λ N) N :=
  Module.Free.of_equiv (linearEquivPiQuotientAnnihilator f).symm

/-- **Uniformly bounded rank of the level modules** (patching-instantiation
leaf 3; PROVEN 2026-07-25): the SAME coordinate rank `d` at every level
bounds the rank uniformly, which is the whole point of the `freeM` field of
`TaylorWilesSystem`.

`rank_{Λ/Ann (M i)} (M i) = rank_{Λ/𝔟ᵢ} ((Λ/𝔟ᵢ)^d) = d` whenever `M i` is
nontrivial, by `linearEquivPiQuotientAnnihilator`; and when `M i` IS trivial
the base ring `Λ/Ann (M i) = Λ/⊤` is the ZERO ring, over which mathlib's
`rank_subsingleton` gives rank `1` — not `0`.  So the bound really is
`d + 2` and not `d + 1`: at `d = 0` a trivial `M i` still has rank `1`.
The case split is made on `Λ ⧸ Ann_Λ (M i)` rather than on `M i`, since
`Ideal.Quotient.nontrivial_iff` plus `Module.annihilator_eq_top_iff` turn
nontriviality of the quotient ring into the nontriviality of `M i` that
`linearEquivPiQuotientAnnihilator` needs. -/
theorem uniformlyBoundedRank_of_linearEquiv_piQuotient {Λ : Type*} [CommRing Λ]
    {ι : Type*} (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module Λ (M i)]
    (d : ℕ) (b : ι → Ideal Λ) (f : ∀ i, M i ≃ₗ[Λ] (Fin d → Λ ⧸ b i)) :
    Module.UniformlyBoundedRank Λ M := by
  refine ⟨d + 2, fun i => ?_⟩
  rcases subsingleton_or_nontrivial (Λ ⧸ Module.annihilator Λ (M i)) with hs | hs
  · rw [rank_subsingleton]
    exact_mod_cast (by omega : (1 : ℕ) < d + 2)
  · have hne : Module.annihilator Λ (M i) ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp hs
    haveI : Nontrivial (M i) := not_subsingleton_iff_nontrivial.mp
      fun h => hne (Module.annihilator_eq_top_iff.mpr h)
    haveI : Module.Finite (Λ ⧸ Module.annihilator Λ (M i)) (M i) :=
      Module.Finite.equiv (linearEquivPiQuotientAnnihilator (f i)).symm
    rw [← Module.finrank_eq_rank, (linearEquivPiQuotientAnnihilator (f i)).finrank_eq,
      Module.finrank_fin_fun]
    exact_mod_cast (by omega : d < d + 2)

/-- **A regular sequence lies in the maximal ideal** (patching-instantiation
leaf 8; PROVEN 2026-07-25), over any local ring.

`RingTheory.Sequence.IsRegular` carries `top_ne_smul :
(⊤ : Submodule A N) ≠ Ideal.ofList rs • ⊤`, so `Ideal.ofList rs ≠ ⊤` —
otherwise `Ideal.top_smul` would make the right side `⊤`.  A proper ideal
of a local ring is contained in `𝔪` (`IsLocalRing.le_maximalIdeal`), and
every member of `rs` is in `Ideal.ofList rs`.

The use site is the sequence pushed from the diamond `Λ` into `R_∞`:
`nonempty_patchedModule_of_patchingData` asks for membership in `𝔪_{R_∞}`
in order to lift the sequence back along the presentation, and this is
where that comes from without knowing anything about `R_∞`. -/
theorem mem_maximalIdeal_of_isRegular {A : Type*} [CommRing A] [IsLocalRing A]
    {N : Type*} [AddCommGroup N] [Module A N] {rs : List A}
    (h : RingTheory.Sequence.IsRegular N rs) :
    ∀ x ∈ rs, x ∈ maximalIdeal A := by
  have hne : Ideal.ofList rs ≠ ⊤ := by
    intro htop
    exact h.top_ne_smul (by rw [htop, Submodule.top_smul])
  intro x hx
  exact IsLocalRing.le_maximalIdeal hne (Ideal.subset_span hx)

/-- **Continuity of the structure map gives a continuous scalar action**
(patching-instantiation leaf 5, the easy half; PROVEN).  Consumed with
`continuous_of_finite_quotient_maximalIdeal_pow` to produce the
`[∀ i, ContinuousSMul Λ (R i)]` hypothesis of the vendored development. -/
theorem continuousSMul_of_continuous_algebraMap {Λ S : Type*} [CommRing Λ] [CommRing S]
    [Algebra Λ S] [TopologicalSpace Λ] [TopologicalSpace S] [IsTopologicalRing S]
    (h : Continuous (algebraMap Λ S)) : ContinuousSMul Λ S := by
  refine ⟨?_⟩
  simp only [Algebra.smul_def]
  exact (h.comp continuous_fst).mul continuous_snd

/-- **Finiteness of the truncations passes along a surjection of local
rings** (patching-instantiation leaf 5, the transport half; PROVEN 2026-07-25).

A surjective ring hom of local rings is local (`IsLocalHom.of_surjective`),
so it carries `𝔪_Λ` into `𝔪_S` and hence `𝔪_Λ^k` into `𝔪_S^k`; the
composite `Λ → S → S/𝔪_S^k` is therefore surjective and kills `𝔪_Λ^k`,
exhibiting `S/𝔪_S^k` as a quotient of the finite `Λ/𝔪_Λ^k`. -/
theorem finite_quotient_maximalIdeal_pow_of_surjective {Λ S : Type*} [CommRing Λ]
    [IsLocalRing Λ] [CommRing S] [IsLocalRing S] (f : Λ →+* S) (hf : Function.Surjective f)
    (k : ℕ) (hfin : Finite (Λ ⧸ maximalIdeal Λ ^ k)) :
    Finite (S ⧸ maximalIdeal S ^ k) := by
  haveI := hfin
  haveI : IsLocalHom f := .of_surjective f hf
  have hle : maximalIdeal Λ ^ k ≤ Ideal.comap f (maximalIdeal S ^ k) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono (((local_hom_TFAE f).out 0 2).mp ‹_›) k
  refine Finite.of_surjective
    (Ideal.Quotient.lift (maximalIdeal Λ ^ k)
      ((Ideal.Quotient.mk (maximalIdeal S ^ k)).comp f) (fun a ha => by
        rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
        exact hle ha)) ?_
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨z, rfl⟩ := hf y
  exact ⟨Ideal.Quotient.mk _ z, rfl⟩

/-- **Automatic continuity into a profinite local ring with finite
truncations** (patching-instantiation leaf 5, the substantive half;
PROVEN 2026-07-25).

`Λ` is compact and its topology is `𝔪`-adic, so `isOpen_iff_finite_quotient'`
(`PatchingVendored/AdicTopology.lean`) says an ideal of `Λ` is open exactly
when its quotient is finite.  For each `k`, `Λ ⧸ (𝔪_S^k).comap f` embeds in
the finite `S/𝔪_S^k`, hence is finite, hence `(𝔪_S^k).comap f` is open;
since `{𝔪_S^k}` is a neighbourhood basis of `0` in `S`
(`hasBasis_maximalIdeal_pow`), `f` is continuous at `0`, hence continuous.

NOTE this is genuinely weaker than `IsLocalRing.Continuous.of_isLocalHom`,
which the assembly uses for the PRESENTATION maps `pres n`: the DIAMOND
maps `dia n` are not local homs (the diamond variables need not land in
`𝔪`), so the local-hom route is unavailable and finiteness of the target's
truncations is what replaces it. -/
theorem continuous_of_finite_quotient_maximalIdeal_pow {Λ S : Type*} [CommRing Λ]
    [IsLocalRing Λ] [IsNoetherianRing Λ] [TopologicalSpace Λ] [IsTopologicalRing Λ]
    [CompactSpace Λ] [IsAdicTopology Λ]
    [CommRing S] [IsLocalRing S] [TopologicalSpace S] [IsTopologicalRing S]
    [IsAdicTopology S] (f : Λ →+* S)
    (hfin : ∀ k, Finite (S ⧸ maximalIdeal S ^ k)) : Continuous f := by
  apply continuous_of_continuousAt_zero
  unfold ContinuousAt
  rw [map_zero]
  apply ((hasBasis_maximalIdeal_pow Λ).tendsto_iff (hasBasis_maximalIdeal_pow S)).mpr
  intro n _
  haveI := hfin n
  haveI : Finite (Λ ⧸ Ideal.comap f (maximalIdeal S ^ n)) :=
    Finite.of_injective _ (Ideal.quotientMap_injective (I := maximalIdeal S ^ n) (f := f))
  obtain ⟨m, hm⟩ := exists_maximalIdeal_pow_le_of_isArtinianRing_quotient
    (Ideal.comap f (maximalIdeal S ^ n))
  exact ⟨m, trivial, fun x hx => hm hx⟩

/-- **`ℤ_p`-rigidity of the bottom ring** (patching-instantiation leaf 7b;
PROVEN 2026-07-25): a complete Noetherian local ring with finite residue
field receives AT MOST ONE ring homomorphism from `ℤ_[p]`.

Two steps.  First, `p` lands in `𝔪`.  This needs no unit/`ℚ_p` argument:
ANY ring homomorphism sends the natural-number cast `(p : ℤ_[p])` to the
natural-number cast `(p : A)` (`map_natCast`), and the existence of even
one `f : ℤ_[p] →+* A` forces the residue field to have characteristic `p`
— compose `f` with `IsLocalRing.residue` and apply
`charP_of_ringHom_padicInt`, which is exactly the statement that a FINITE
field receiving `ℤ_p` has characteristic `p` (the kernel is a nonzero
prime of the DVR `ℤ_p`, hence `(p)`).  So `(p : A) ∈ 𝔪` by
`IsLocalRing.residue_eq_zero_iff`, and `(p : A)^n ∈ 𝔪^n`.

Second, `A` is `𝔪`-adically separated (`IsAdicComplete → IsHausdorff`),
so it suffices to see `f x - g x ∈ 𝔪^n` for every `n`.  Writing
`x = (x.appr n : ℕ) + p^n * c` (`PadicInt.appr_spec`) and using
`map_natCast` again on the first summand, the two natural-number values
cancel and `f x - g x = (p : A)^n * (f c - g c) ∈ 𝔪^n`.

Note what is NOT needed: no continuity hypothesis (the conclusion is
`Subsingleton (ℤ_[p] →+* A)` for ALL ring homs, continuity being a
consequence of the `𝔪`-adic structure rather than an extra assumption),
and `IsNoetherianRing A` is unused by THIS proof — it is carried only to
match the hypothesis shape of the consumer
`ringHom_mvPowerSeries_eq_of_taylorWilesAug_le_ker`.  The completeness
hypothesis is `IsAdicComplete` for the MAXIMAL ideal, which is the ideal
whose powers the `appr` estimate lands in, so the statement is the right
one (contrast `MvPowerSeries`, where mathlib's `IsAdicComplete` is for the
ideal of the variables and is strictly coarser).

HYPOTHESIS AUDIT (recorded 2026-07-26, cross-checked against an
independent proof of the same statement).  `hcomplete` is not logically
necessary: `Ideal.iInf_pow_eq_bot_of_isLocalRing` (Krull intersection)
already gives `⋂ₙ 𝔪ⁿ = ⊥` from `IsLocalRing` + `IsNoetherianRing` alone,
so separatedness can be had without completeness — the alternative proof
trades `hcomplete` for `IsNoetherianRing`, which this one leaves unused.
The hypothesis is KEPT because the consumer supplies it positionally and
because "complete local with finite residue field" is the shape the
patching interface hands down; nobody should read its presence as a claim
that completeness is what makes the statement true.

This is the completed-coefficient analogue of `ringHom_padicInt_eq` above,
which does the same for a finite FIELD target; the finite residue field is
what pins `p`, and `𝔪`-adic separatedness is what replaces "`𝔪 = 0`". -/
theorem subsingleton_ringHom_padicInt (p : ℕ) [Fact p.Prime] {A : Type*} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (hcomplete : IsAdicComplete (maximalIdeal A) A)
    (hres : Finite (A ⧸ maximalIdeal A)) : Subsingleton (ℤ_[p] →+* A) := by
  haveI : Finite (ResidueField A) := hres
  refine ⟨fun f g => ?_⟩
  have hchar : CharP (ResidueField A) p :=
    charP_of_ringHom_padicInt ((residue A).comp f)
  have hpmem : (p : A) ∈ maximalIdeal A := by
    rw [← residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero _ p
  ext x
  rw [← sub_eq_zero]
  refine IsHausdorff.haus hcomplete.toIsHausdorff _ (fun n => ?_)
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, sub_zero]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (PadicInt.appr_spec n x)
  have hx : x = ((x.appr n : ℕ) : ℤ_[p]) + (p : ℤ_[p]) ^ n * c := by
    rw [← hc]; ring
  have key : f x - g x = (p : A) ^ n * (f c - g c) := by
    rw [hx]
    simp only [map_add, map_mul, map_pow, map_natCast]
    ring
  rw [key]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hpmem n)

/-- **The bottom `Λ`-algebra structure is independent of the level**
(patching-instantiation leaf 7; PROVEN 2026-07-25 over
`subsingleton_ringHom_padicInt` and `ker_constantCoeff_mvPowerSeries`): two ring homomorphisms
`Λ = ℤ_p[[x₁, …, x_q]] →+* A` that both kill the augmentation ideal
`taylorWilesAug p q = (X₁, …, X_q)` are EQUAL, when `A` is complete
Noetherian local with finite residue field.

This is the one compatibility the `TaylorWilesSystem` interface does not
record as a field, and it is derivable rather than an omission: both
`(tR n).comp (dia n)` kill `𝔫` — because `ker (tR n) = 𝔫.map (dia n)` —
hence factor through `Λ/𝔫`, which is `ℤ_[p]` by
`ker_constantCoeff_mvPowerSeries` and surjectivity of `constantCoeff`; and
a ring hom out of `ℤ_[p]` into `A` is unique by
`subsingleton_ringHom_padicInt`.

Without it neither `projM` nor `toRuniv` can be read as `Λ`-linear resp.
`Λ`-algebra maps, which is what `PatchingVendored/Over.lean` demands of the
bottom identifications `sR`/`sM`. -/
theorem ringHom_mvPowerSeries_eq_of_taylorWilesAug_le_ker (p : ℕ) [Fact p.Prime] (q : ℕ)
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hcomplete : IsAdicComplete (maximalIdeal A) A) (hres : Finite (A ⧸ maximalIdeal A))
    (f g : MvPowerSeries (Fin q) ℤ_[p] →+* A)
    (hf : taylorWilesAug p q ≤ RingHom.ker f) (hg : taylorWilesAug p q ≤ RingHom.ker g) :
    f = g := by
  haveI := subsingleton_ringHom_padicInt p hcomplete hres
  have hker : RingHom.ker (MvPowerSeries.constantCoeff (σ := Fin q) (R := ℤ_[p])) =
      taylorWilesAug p q := ker_constantCoeff_mvPowerSeries q ℤ_[p]
  have hCeq : f.comp (MvPowerSeries.C (σ := Fin q) (R := ℤ_[p])) =
      g.comp (MvPowerSeries.C (σ := Fin q) (R := ℤ_[p])) := Subsingleton.elim _ _
  ext x
  have hy : x - MvPowerSeries.C (σ := Fin q) (R := ℤ_[p])
      (MvPowerSeries.constantCoeff x) ∈ taylorWilesAug p q := by
    rw [← hker, RingHom.mem_ker, map_sub, MvPowerSeries.constantCoeff_C, sub_self]
  have h1 : f x = f (MvPowerSeries.C (σ := Fin q) (R := ℤ_[p])
      (MvPowerSeries.constantCoeff x)) := by
    have h := hf hy
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h
    exact h
  have h2 : g x = g (MvPowerSeries.C (σ := Fin q) (R := ℤ_[p])
      (MvPowerSeries.constantCoeff x)) := by
    have h := hg hy
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h
    exact h
  rw [h1, h2]
  exact DFunLike.congr_fun hCeq _

section LevelRings

variable {ι : Type*} (R : ι → Type*)
variable [∀ i, CommRing (R i)] [∀ i, IsLocalRing (R i)]
variable [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
variable [∀ i, CompactSpace (R i)] [∀ i, IsAdicTopology (R i)]

/-- **Uniformly bounded rank of the level rings** (patching-instantiation
leaf 6; PROVEN 2026-07-25): if every `R i` is a quotient of one fixed local ring `Λ` whose
`𝔪`-adic truncations are finite, then `|R i / 𝔪^k|` is bounded uniformly
in `i`.

Each `f i` is a surjective hom of local rings, hence local, so
`Λ/𝔪_Λ^k ↠ R i/𝔪_{R i}^k` (this is
`finite_quotient_maximalIdeal_pow_of_surjective` made quantitative), giving
`Nat.card (R i ⧸ 𝔪^k) ≤ Nat.card (Λ ⧸ 𝔪_Λ^k)` for EVERY `i`; take
`Nat.card (Λ ⧸ 𝔪_Λ^k) + 1` as the strict bound.

At the use site `f i` is the presentation `pres i`, not the diamond, which
is why the surjectivity hypothesis is available. -/
theorem algebra_uniformlyBoundedRank_of_surjective {Λ : Type*} [CommRing Λ] [IsLocalRing Λ]
    (f : ∀ i, Λ →+* R i) (hf : ∀ i, Function.Surjective (f i))
    (hfin : ∀ k, Finite (Λ ⧸ maximalIdeal Λ ^ k)) :
    Algebra.UniformlyBoundedRank R := by
  refine ⟨fun k => ⟨Nat.card (Λ ⧸ maximalIdeal Λ ^ k) + 1, fun i => ?_⟩⟩
  haveI := hfin k
  haveI : IsLocalHom (f i) := .of_surjective (f i) (hf i)
  have hle : maximalIdeal Λ ^ k ≤ Ideal.comap (f i) (maximalIdeal (R i) ^ k) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono (((local_hom_TFAE (f i)).out 0 2).mp ‹_›) k
  have hgs : Function.Surjective (Ideal.Quotient.lift (maximalIdeal Λ ^ k)
      ((Ideal.Quotient.mk (maximalIdeal (R i) ^ k)).comp (f i)) (fun a ha => by
        rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
        exact hle ha)) := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨z, rfl⟩ := hf i y
    exact ⟨Ideal.Quotient.mk _ z, rfl⟩
  exact Nat.lt_succ_of_le (Nat.card_le_card_of_surjective _ hgs)

/-- **The level modules form a patching system** (patching-instantiation
leaf 4; PROVEN 2026-07-25): the shrinking annihilators `Ann_Λ (M n) ≤ 𝔪^n` make `M` a patching
system along any ultrafilter refining `atTop`.

Let `α` be an open ideal of the compact `Λ`.  Then `Λ/α` is finite
(`isOpen_iff_finite_quotient'`), hence Artinian, so
`exists_maximalIdeal_pow_le_of_isArtinianRing_quotient` gives a `k` with
`𝔪^k ≤ α`.  For every `n ≥ k` we then have
`Ann_Λ (M n) ≤ 𝔪^n ≤ 𝔪^k ≤ α`, and `{n | k ≤ n} ∈ atTop ≤ F`.

The `Ann_Λ (M n) ≤ 𝔪^n` input is `annihilator_eq_of_linearEquiv_piQuotient`
composed with the `bIdeal_le` field of `TaylorWilesSystem`; the ultrafilter
refining `atTop` is `Ultrafilter.of Filter.atTop`, and nonprincipality —
the classical hypothesis — is exactly what `F ≤ atTop` encodes here. -/
theorem isPatchingSystem_of_annihilator_le_maximalIdeal_pow {Λ : Type*} [CommRing Λ]
    [IsLocalRing Λ] [IsNoetherianRing Λ] [TopologicalSpace Λ] [IsTopologicalRing Λ]
    [CompactSpace Λ] [IsAdicTopology Λ]
    (M : ℕ → Type*) [∀ n, AddCommGroup (M n)] [∀ n, Module Λ (M n)]
    (F : Ultrafilter ℕ) (hF : (F : Filter ℕ) ≤ Filter.atTop)
    (hann : ∀ n, Module.annihilator Λ (M n) ≤ maximalIdeal Λ ^ n) :
    IsPatchingSystem Λ M F := by
  refine ⟨fun α hα => ?_⟩
  haveI : Finite (Λ ⧸ α) := isOpen_iff_finite_quotient'.mp hα
  obtain ⟨k, hk⟩ := exists_maximalIdeal_pow_le_of_isArtinianRing_quotient α
  refine hF ?_
  filter_upwards [Filter.eventually_ge_atTop k] with n hn
  exact (hann n).trans ((Ideal.pow_le_pow_right hn).trans hk)

end LevelRings

section PatchedBottom

variable (Λ : Type*) [CommRing Λ]
variable {ι : Type*} (R : ι → Type*)
variable [∀ i, CommRing (R i)] [∀ i, IsLocalRing (R i)] [∀ i, Algebra Λ (R i)]
variable [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
variable [∀ i, CompactSpace (R i)] [∀ i, IsAdicTopology (R i)]
variable (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module Λ (M i)]
variable [∀ i, Module (R i) (M i)] [∀ i, IsScalarTower Λ (R i) (M i)]
variable (F : Ultrafilter ι)
variable [TopologicalSpace Λ]
variable [IsLocalRing Λ] [IsNoetherianRing Λ] [NonarchimedeanRing Λ] [T2Space Λ]
variable [Algebra.TopologicallyFG ℤ Λ] [CompactSpace Λ] [∀ i, ContinuousSMul Λ (R i)]
variable [∀ i, IsNoetherianRing (R i)]
variable [Algebra.UniformlyBoundedRank R]
variable [∀ i, Module.Free (Λ ⧸ Module.annihilator Λ (M i)) (M i)]
variable [Module.UniformlyBoundedRank Λ M] [IsPatchingSystem Λ M F]
variable {R₀ M₀ : Type*} [CommRing R₀] [AddCommGroup M₀] [Module R₀ M₀] [Module.Finite R₀ M₀]
variable [IsLocalRing R₀] [IsNoetherianRing R₀]
  [TopologicalSpace R₀] [IsTopologicalRing R₀] [CompactSpace R₀] [IsAdicTopology R₀]
variable [Algebra Λ R₀] [Module Λ M₀] [Module.Finite Λ M₀]
variable (𝔫 : Ideal Λ)
variable (sR : ∀ i, (R i ⧸ 𝔫.map (algebraMap Λ (R i))) ≃ₐ[Λ] R₀)
variable (sM : ∀ i, (M i ⧸ (𝔫 • ⊤ : Submodule Λ (M i))) ≃ₗ[Λ] M₀)
variable [IsScalarTower Λ R₀ M₀] [∀ i, Nontrivial (M i)]

/-- **The bottom identification of the patched module is `R_∞`-semilinear**
(patching-instantiation leaf 9; PROVEN 2026-07-25 — it is exactly
`smul_lemma` applied to `Submodule.Quotient.mk m`, the two quotients
being definitionally equal): the composite
`M_∞ ↠ M_∞/𝔫M_∞ ≃ M₀` intertwines the `R_∞`-action on `M_∞` with the
`R₀`-action on `M₀` along `θ = quotientToOver ∘ mk`.

This is `PatchingVendored/System.lean`'s `smul_lemma` composed with the
quotient map `M_∞ ↠ M_∞/𝔫M_∞`.  The one piece of bookkeeping between the
two is that `smul_lemma` quotients by `𝔫 • ⊤` taken in
`Submodule (PatchingAlgebra R F) (PatchingModule Λ M F)` while
`quotientEquivOver` quotients by `𝔫 • ⊤` taken in `Submodule Λ …`; the
vendored bridge is `Submodule.map_algebraMap_smul`, which says
`(𝔫.map (algebraMap Λ R_∞)) • N = 𝔫 • N` for an `R_∞`-submodule `N`.

At the use site `HCompat` is the `projM_smul` field of `TaylorWilesSystem`:
`sM i ∘ mk` IS `projM i` and `sR i ∘ mk` IS `toRuniv i` by construction of
those two identifications, so both sides read
`ψ (toRuniv i r) • projM i m`. -/
theorem quotientEquivOver_mkQ_smul
    (HCompat : ∀ i m (r : R i), sM i (Submodule.Quotient.mk (r • m)) =
      sR i (Ideal.Quotient.mk _ r) • sM i (Submodule.Quotient.mk m))
    (a : PatchingAlgebra R F) (m : PatchingModule Λ M F) :
    PatchingModule.quotientEquivOver Λ M F 𝔫 sM (Submodule.Quotient.mk (a • m)) =
      ((PatchingAlgebra.quotientToOver Λ R F 𝔫 sR).comp (Ideal.Quotient.mk _)) a •
        PatchingModule.quotientEquivOver Λ M F 𝔫 sM (Submodule.Quotient.mk m) :=
  smul_lemma Λ R M F 𝔫 sR sM HCompat a (Submodule.Quotient.mk m)

/-- **The kernel of the bottom identification is inside `ker θ · M_∞`**
(patching-instantiation leaf 10; PROVEN 2026-07-25), the `mem_smul_top_of_proj_eq_zero` field
of `PatchedModule`.

`quotientEquivOver` is injective, so `m` maps to `0` exactly when
`m ∈ 𝔫 • ⊤` computed over `Λ`.  That `Λ`-submodule is contained in the
`R_∞`-submodule `𝔫 • ⊤`, which by `Submodule.map_algebraMap_smul` equals
`(𝔫.map (algebraMap Λ R_∞)) • ⊤`; and
`𝔫.map (algebraMap Λ R_∞) ≤ ker θ` because `θ` is by construction the map
`quotientToOver` out of `R_∞ ⧸ 𝔫.map (algebraMap Λ R_∞)` precomposed with
the quotient map, so it kills that ideal outright.  Conclude by
`Submodule.smul_mono_left`. -/
theorem mem_ker_smul_top_of_quotientEquivOver_mkQ_eq_zero
    (m : PatchingModule Λ M F)
    (hm : PatchingModule.quotientEquivOver Λ M F 𝔫 sM (Submodule.Quotient.mk m) = 0) :
    m ∈ RingHom.ker ((PatchingAlgebra.quotientToOver Λ R F 𝔫 sR).comp (Ideal.Quotient.mk _)) •
      (⊤ : Submodule (PatchingAlgebra R F) (PatchingModule Λ M F)) := by
  have h0 : m ∈ (𝔫 • ⊤ : Submodule Λ (PatchingModule Λ M F)) := by
    rw [← Submodule.Quotient.mk_eq_zero]
    exact (PatchingModule.quotientEquivOver Λ M F 𝔫 sM).injective (by rw [hm, map_zero])
  refine Submodule.smul_induction_on h0 ?_ ?_
  · intro r hr n _
    rw [← algebraMap_smul (PatchingAlgebra R F) r n]
    refine Submodule.smul_mem_smul ?_ trivial
    rw [RingHom.mem_ker, RingHom.comp_apply,
      show (Ideal.Quotient.mk (𝔫.map (algebraMap Λ (PatchingAlgebra R F))))
          (algebraMap Λ (PatchingAlgebra R F) r) = 0 from
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr), map_zero]
  · intro x y hx hy
    exact add_mem hx hy

end PatchedBottom

set_option maxHeartbeats 1000000 in
/-- **The instantiation of the vendored patching development at a
Taylor–Wiles system** (ASSEMBLED 2026-07-25, DECOMPOSED the same day; the
glue is written and compiles, and every step it cannot see through is now
a separately owned top-level leaf immediately above rather than an inline
`sorry`), stated in terms of
the raw fields of `TaylorWilesSystem` so that the field-access noise
stays out of the proof.

The instantiation follows the handoff map in the docstring of
`TaylorWilesSystem.exists_patchedModule_natural`:

* `Λ := MvPowerSeries (Fin q) ℤ_[p]` carries the scoped product topology,
  in which it is compact, Hausdorff, totally disconnected and (by the
  project's own leaf `isNoetherianRing_mvPowerSeries`) Noetherian — so
  `IsLocalRing.IsAdicTopology Λ` and `NonarchimedeanRing Λ` are FREE
  through `PatchingVendored/AdicTopology.lean`'s "profinite + Noetherian
  ⟹ adic" instance, and the product topology never has to be compared
  with the adic one by hand.
* Each level ring `R n` is topologized by fiat with its own
  `𝔪`-adic topology (`IsLocalRing.withIdeal`); it is local and
  Noetherian as a quotient of `Λ`, Hausdorff for free, and COMPACT
  because `pres n` is a continuous surjection from the compact `Λ` —
  continuity being `IsLocalRing.Continuous.of_isLocalHom`, which applies
  precisely because both topologies are adic.
* `Runiv` likewise gets the adic topology by fiat and is compact by
  `IsLocalRing.compactSpace_of_finite_residueField`, fed by `hres` and
  `hcomplete`.
* `F` is an ultrafilter refining `atTop` on `ℕ` (so that the shrinking
  level ideals `bIdeal n ≤ 𝔪^n` make `M` a patching system).
* The patched objects are `R_∞ := PatchingAlgebra R F` with
  `lift := PatchingAlgebra.lift R F pres` (surjective by
  `lift_surjective`) and `M_∞ := PatchingModule Λ M F`, with
  `θ := quotientToOver ∘ mk` surjective by
  `surjective_quotientToOver`; `nonempty_patchedModule_of_patchingData`
  above turns that data into the `PatchedModule`.
* The regular sequence is produced in the DIAMOND copy — `M_∞` is FREE
  over the diamond `Λ` (the decisive output of
  `PatchingVendored/Module.lean`), hence flat, so the maximal regular
  system of parameters of `Λ`
  (`exists_isRegular_ofList_eq_maximalIdeal_mvPowerSeries`) stays
  weakly regular on `M_∞` by `isWeaklyRegular_rTensor`, and upgrades to
  regular by `IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal`
  (this is the Nakayama half) — then transported to `R_∞` by
  `isRegular_map_algebraMap_iff_of_tower`.  No `Module.depth` layer is
  needed, which is why `FLT/Patching/Utils/Depth.lean` was not
  vendored. -/
theorem exists_patchedModule_of_fields.{a, b, c, s, uR} {p : ℕ} [Fact p.Prime]
    {Runiv : Type uR} [CommRing Runiv] [IsLocalRing Runiv] [IsNoetherianRing Runiv]
    {T : Type s} [CommRing T] {ψ : Runiv →+* T}
    (q d : ℕ) (coeff : TaylorWilesCoefficients) (R : ℕ → Type a) [iR : ∀ n, CommRing (R n)]
    (pres : ∀ n, MvPowerSeries (Fin q) coeff.carrier →+* R n)
    (hpres : ∀ n, Function.Surjective (pres n))
    (dia : ∀ n, MvPowerSeries (Fin q) ℤ_[p] →+* R n)
    (tR : ∀ n, R n →+* Runiv) (htR : ∀ n, Function.Surjective (tR n))
    (hkertR : ∀ n, RingHom.ker (tR n) = (taylorWilesAug p q).map (dia n))
    (M : ℕ → Type b) [iMg : ∀ n, AddCommGroup (M n)] [iMR : ∀ n, Module (R n) (M n)]
    [iMΛ : ∀ n, Module (MvPowerSeries (Fin q) ℤ_[p]) (M n)]
    (hdia : ∀ (n : ℕ) (x : MvPowerSeries (Fin q) ℤ_[p]) (m : M n), x • m = dia n x • m)
    (bI : ℕ → Ideal (MvPowerSeries (Fin q) ℤ_[p]))
    (hbI : ∀ n, bI n ≤ maximalIdeal (MvPowerSeries (Fin q) ℤ_[p]) ^ n)
    (fM : ∀ n, M n ≃ₗ[MvPowerSeries (Fin q) ℤ_[p]]
      (Fin d → MvPowerSeries (Fin q) ℤ_[p] ⧸ bI n))
    (M0 : Type c) [iM0g : AddCommGroup M0] [iM0T : Module T M0] (hM0 : Nontrivial M0)
    (prM : ∀ n, M n →+ M0) (hprM : ∀ n, Function.Surjective (prM n))
    (hprMsmul : ∀ (n : ℕ) (x : R n) (m : M n), prM n (x • m) = ψ (tR n x) • prM n m)
    (hprMzero : ∀ (n : ℕ) (m : M n), prM n m = 0 ↔
      m ∈ (taylorWilesAug p q • ⊤ :
        Submodule (MvPowerSeries (Fin q) ℤ_[p]) (M n)))
    (hcomplete : IsAdicComplete (maximalIdeal Runiv) Runiv)
    (hres : Finite (Runiv ⧸ maximalIdeal Runiv)) :
    Nonempty (PatchedModule.{b, c, s, uR} p ψ) := by
  classical
  -- ### the coefficient ring `Λ = ℤ_p[[x₁, …, x_q]]` in its diamond role
  haveI : IsNoetherianRing (MvPowerSeries (Fin q) ℤ_[p]) :=
    isNoetherianRing_mvPowerSeries q
  haveI : CompactSpace (MvPowerSeries (Fin q) ℤ_[p]) :=
    inferInstanceAs (CompactSpace ((Fin q →₀ ℕ) → ℤ_[p]))
  haveI : TotallyDisconnectedSpace (MvPowerSeries (Fin q) ℤ_[p]) :=
    inferInstanceAs (TotallyDisconnectedSpace ((Fin q →₀ ℕ) → ℤ_[p]))
  haveI hadicΛ : IsAdicTopology (MvPowerSeries (Fin q) ℤ_[p]) := inferInstance
  -- LEAF 1 (`topologicallyFG_int_mvPowerSeries`)
  haveI hTFG : ∀ [inst : Algebra ℤ (MvPowerSeries (Fin q) ℤ_[p])],
      Algebra.TopologicallyFG ℤ (MvPowerSeries (Fin q) ℤ_[p]) := by
    intro inst
    exact topologicallyFG_int_mvPowerSeries (topologicallyFG_int_padicInt p) q
  -- ### the coefficient ring `𝒪` in its PRESENTATION role: `R_∞ = 𝒪[[x₁, …, x_q]]`
  -- (the diamond role above keeps `ℤ_[p]`; see `TaylorWilesSystem.coeff`)
  haveI : IsNoetherianRing (MvPowerSeries (Fin q) coeff.carrier) :=
    isNoetherianRing_mvPowerSeries q
  haveI : CompactSpace (MvPowerSeries (Fin q) coeff.carrier) :=
    inferInstanceAs (CompactSpace ((Fin q →₀ ℕ) → coeff.carrier))
  haveI : T2Space (MvPowerSeries (Fin q) coeff.carrier) :=
    inferInstanceAs (T2Space ((Fin q →₀ ℕ) → coeff.carrier))
  haveI : TotallyDisconnectedSpace (MvPowerSeries (Fin q) coeff.carrier) :=
    inferInstanceAs (TotallyDisconnectedSpace ((Fin q →₀ ℕ) → coeff.carrier))
  haveI hadicP : IsAdicTopology (MvPowerSeries (Fin q) coeff.carrier) := inferInstance
  haveI hTFGP : ∀ [inst : Algebra ℤ (MvPowerSeries (Fin q) coeff.carrier)],
      Algebra.TopologicallyFG ℤ (MvPowerSeries (Fin q) coeff.carrier) := by
    intro inst
    exact topologicallyFG_int_mvPowerSeries coeff.topologicallyFG q
  -- ### nontriviality of the levels
  haveI hMnt : ∀ n, Nontrivial (M n) := fun n => (hprM n).nontrivial
  -- the annihilator of each level module, the shared brick behind the
  -- next three steps (`annihilator_eq_of_linearEquiv_piQuotient`)
  have hann : ∀ n, Module.annihilator (MvPowerSeries (Fin q) ℤ_[p]) (M n) = bI n :=
    fun n => annihilator_eq_of_linearEquiv_piQuotient (fM n)
  -- LEAF 2 (`free_quotientAnnihilator_of_linearEquiv_piQuotient`)
  haveI hfree : ∀ n, Module.Free (MvPowerSeries (Fin q) ℤ_[p] ⧸
      Module.annihilator (MvPowerSeries (Fin q) ℤ_[p]) (M n)) (M n) :=
    fun n => free_quotientAnnihilator_of_linearEquiv_piQuotient (fM n)
  -- LEAF 3 (`uniformlyBoundedRank_of_linearEquiv_piQuotient`)
  haveI hubr : Module.UniformlyBoundedRank (MvPowerSeries (Fin q) ℤ_[p]) M :=
    uniformlyBoundedRank_of_linearEquiv_piQuotient M d bI fM
  -- ### the ultrafilter: any nonprincipal one, here a refinement of `atTop`
  letI F : Ultrafilter ℕ := Ultrafilter.of Filter.atTop
  -- LEAF 4 (`isPatchingSystem_of_annihilator_le_maximalIdeal_pow`)
  haveI hps : IsPatchingSystem (MvPowerSeries (Fin q) ℤ_[p]) M F :=
    isPatchingSystem_of_annihilator_le_maximalIdeal_pow M F (Ultrafilter.of_le Filter.atTop)
      (fun n => (hann n).trans_le (hbI n))
  -- ### the level rings, with their `𝔪`-adic topologies
  haveI iRnt : ∀ n, Nontrivial (R n) := fun n => (tR n).domain_nontrivial
  haveI iRloc : ∀ n, IsLocalRing (R n) := fun n => .of_surjective' (pres n) (hpres n)
  haveI iRnoeth : ∀ n, IsNoetherianRing (R n) :=
    fun n => isNoetherianRing_of_surjective _ _ (pres n) (hpres n)
  letI iRwi : ∀ n, WithIdeal (R n) := fun n => IsLocalRing.withIdeal
  haveI iRadic : ∀ n, IsAdicTopology (R n) := fun n => inferInstance
  haveI iRt2 : ∀ n, T2Space (R n) := fun n => inferInstance
  haveI iRlh : ∀ n, IsLocalHom (pres n) := fun n => .of_surjective _ (hpres n)
  have hprescont : ∀ n, Continuous (pres n) := fun n => Continuous.of_isLocalHom _
  haveI iRcpt : ∀ n, CompactSpace (R n) := fun n =>
    ⟨by
      rw [← Set.range_eq_univ.mpr (hpres n)]
      exact isCompact_range (hprescont n)⟩
  letI iRalg : ∀ n, Algebra (MvPowerSeries (Fin q) ℤ_[p]) (R n) := fun n => (dia n).toAlgebra
  -- LEAF 5 (`finite_quotient_maximalIdeal_pow_of_surjective` and
  -- `continuous_of_finite_quotient_maximalIdeal_pow`, glued by
  -- `continuousSMul_of_continuous_algebraMap`)
  haveI iRfin : ∀ (n k : ℕ), Finite (R n ⧸ maximalIdeal (R n) ^ k) := fun n k =>
    finite_quotient_maximalIdeal_pow_of_surjective (pres n) (hpres n) k
      (finite_quotient_maximalIdeal_pow_mvPowerSeries coeff.finite_residueField q k)
  haveI iRcsmul : ∀ n, ContinuousSMul (MvPowerSeries (Fin q) ℤ_[p]) (R n) := fun n =>
    continuousSMul_of_continuous_algebraMap
      (continuous_of_finite_quotient_maximalIdeal_pow (dia n) (iRfin n))
  -- LEAF 6 (`algebra_uniformlyBoundedRank_of_surjective`)
  haveI hRubr : Algebra.UniformlyBoundedRank R :=
    algebra_uniformlyBoundedRank_of_surjective R pres hpres
      (finite_quotient_maximalIdeal_pow_mvPowerSeries coeff.finite_residueField q)
  haveI iRtower : ∀ n, IsScalarTower (MvPowerSeries (Fin q) ℤ_[p]) (R n) (M n) :=
    fun n => .of_algebraMap_smul fun r m => (hdia n r m).symm
  -- ### the bottom ring
  letI iRunivwi : WithIdeal Runiv := IsLocalRing.withIdeal
  haveI : IsAdicTopology Runiv := inferInstance
  haveI : Finite (ResidueField Runiv) := hres
  haveI : IsAdicComplete (maximalIdeal Runiv) Runiv := hcomplete
  haveI : CompactSpace Runiv := IsLocalRing.compactSpace_of_finite_residueField
  -- LEAF 7 (`ringHom_mvPowerSeries_eq_of_taylorWilesAug_le_ker`): both
  -- `tR n ∘ dia n` kill the augmentation ideal, by `hkertR`.
  have hkeraug : ∀ n, taylorWilesAug p q ≤ RingHom.ker ((tR n).comp (dia n)) := by
    intro n x hx
    rw [RingHom.mem_ker, RingHom.comp_apply, ← RingHom.mem_ker, hkertR n]
    exact Ideal.mem_map_of_mem _ hx
  have hcompat : ∀ n, (tR n).comp (dia n) = (tR 0).comp (dia 0) := fun n =>
    ringHom_mvPowerSeries_eq_of_taylorWilesAug_le_ker p q hcomplete hres _ _
      (hkeraug n) (hkeraug 0)
  letI iRunivalg : Algebra (MvPowerSeries (Fin q) ℤ_[p]) Runiv :=
    ((tR 0).comp (dia 0)).toAlgebra
  letI iM0Runiv : Module Runiv M0 := Module.compHom M0 ψ
  letI iM0Λ : Module (MvPowerSeries (Fin q) ℤ_[p]) M0 :=
    Module.compHom M0 (ψ.comp ((tR 0).comp (dia 0)))
  haveI iM0tower : IsScalarTower (MvPowerSeries (Fin q) ℤ_[p]) Runiv M0 :=
    .of_algebraMap_smul fun _ _ => rfl
  -- ### `projM` is `Λ`-linear, and `M₀` is `Λ`-finite
  let prMₗ : ∀ n, M n →ₗ[MvPowerSeries (Fin q) ℤ_[p]] M0 := fun n =>
    { toFun := prM n
      map_add' := (prM n).map_add
      map_smul' := fun r m => by
        show prM n (r • m) = _
        rw [hdia n r m, hprMsmul n (dia n r) m]
        show ψ (tR n (dia n r)) • prM n m = ψ (((tR 0).comp (dia 0)) r) • prM n m
        rw [← hcompat n]; rfl }
  have hkerprM : ∀ n, LinearMap.ker (prMₗ n) =
      (taylorWilesAug p q • ⊤ :
        Submodule (MvPowerSeries (Fin q) ℤ_[p]) (M n)) :=
    fun n => Submodule.ext fun m => (hprMzero n m)
  haveI hM0finΛ : Module.Finite (MvPowerSeries (Fin q) ℤ_[p]) M0 := by
    haveI : Module.Finite (MvPowerSeries (Fin q) ℤ_[p]) (M 0) :=
      Module.Finite.equiv (fM 0).symm
    exact Module.Finite.of_surjective (prMₗ 0) (hprM 0)
  haveI hM0finR : Module.Finite Runiv M0 :=
    Module.Finite.of_restrictScalars_finite (MvPowerSeries (Fin q) ℤ_[p]) Runiv M0
  -- ### the bottom identifications demanded by `PatchingVendored/Over.lean`
  let sR : ∀ n, (R n ⧸ (taylorWilesAug p q).map
        (algebraMap (MvPowerSeries (Fin q) ℤ_[p]) (R n)))
      ≃ₐ[MvPowerSeries (Fin q) ℤ_[p]] Runiv := fun n =>
    AlgEquiv.ofRingEquiv (f := (Ideal.quotEquivOfEq (hkertR n).symm).trans
      (RingHom.quotientKerEquivOfSurjective (htR n))) (fun x => by
        show tR n (dia n x) = ((tR 0).comp (dia 0)) x
        rw [← hcompat n]; rfl)
  let sM : ∀ n, (M n ⧸ (taylorWilesAug p q • ⊤ :
        Submodule (MvPowerSeries (Fin q) ℤ_[p]) (M n)))
      ≃ₗ[MvPowerSeries (Fin q) ℤ_[p]] M0 := fun n =>
    (Submodule.quotEquivOfEq _ _ (hkerprM n).symm).trans
      ((prMₗ n).quotKerEquivOfSurjective (hprM n))
  -- ### the patched objects
  let lift : MvPowerSeries (Fin q) coeff.carrier →+* PatchingAlgebra R F :=
    PatchingAlgebra.lift R F pres
  have hliftsurj : Function.Surjective lift :=
    PatchingAlgebra.lift_surjective R F pres hprescont hpres
  let θ : PatchingAlgebra R F →+* Runiv :=
    (PatchingAlgebra.quotientToOver (MvPowerSeries (Fin q) ℤ_[p]) R F
      (taylorWilesAug p q) sR).comp (Ideal.Quotient.mk _)
  have hθsurj : Function.Surjective θ :=
    (PatchingAlgebra.surjective_quotientToOver (MvPowerSeries (Fin q) ℤ_[p]) R F
      (taylorWilesAug p q) sR).comp Ideal.Quotient.mk_surjective
  let projQ := PatchingModule.quotientEquivOver (MvPowerSeries (Fin q) ℤ_[p]) M F
    (taylorWilesAug p q) sM
  -- ### the regular sequence, produced in the diamond copy and pushed forward
  obtain ⟨ts, htslen, htsreg, htsspan⟩ :=
    exists_isRegular_ofList_eq_maximalIdeal_mvPowerSeries
      (exists_isRegular_ofList_eq_maximalIdeal_padicInt p) q
  have htsmem : ∀ x ∈ ts, x ∈ maximalIdeal (MvPowerSeries (Fin q) ℤ_[p]) := by
    intro x hx
    rw [← htsspan]
    exact Ideal.subset_span hx
  haveI hM0' : Nontrivial M0 := hM0
  haveI hQnt : Nontrivial (PatchingModule (MvPowerSeries (Fin q) ℤ_[p]) M F ⧸
      (taylorWilesAug p q • ⊤ : Submodule (MvPowerSeries (Fin q) ℤ_[p])
        (PatchingModule (MvPowerSeries (Fin q) ℤ_[p]) M F))) := projQ.toEquiv.nontrivial
  haveI hMinfnt : Nontrivial (PatchingModule (MvPowerSeries (Fin q) ℤ_[p]) M F) :=
    Function.Surjective.nontrivial (Submodule.mkQ_surjective
      ((taylorWilesAug p q • ⊤ : Submodule (MvPowerSeries (Fin q) ℤ_[p])
        (PatchingModule (MvPowerSeries (Fin q) ℤ_[p]) M F))))
  have hregdia : RingTheory.Sequence.IsRegular
      (PatchingModule (MvPowerSeries (Fin q) ℤ_[p]) M F) ts := by
    refine (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal htsmem).mpr ?_
    exact ((TensorProduct.lid (MvPowerSeries (Fin q) ℤ_[p])
      (PatchingModule (MvPowerSeries (Fin q) ℤ_[p]) M F)).isWeaklyRegular_congr ts).mp
      (htsreg.1.isWeaklyRegular_rTensor
        (M₂ := PatchingModule (MvPowerSeries (Fin q) ℤ_[p]) M F))
  have hregRinf : RingTheory.Sequence.IsRegular
      (PatchingModule (MvPowerSeries (Fin q) ℤ_[p]) M F)
      (ts.map (algebraMap (MvPowerSeries (Fin q) ℤ_[p]) (PatchingAlgebra R F))) :=
    (isRegular_map_algebraMap_iff_of_tower
      (B := PatchingAlgebra R F) ts).mpr hregdia
  -- LEAF 8 (`mem_maximalIdeal_of_isRegular`)
  have hmemRinf : ∀ x ∈ ts.map (algebraMap (MvPowerSeries (Fin q) ℤ_[p])
        (PatchingAlgebra R F)),
      x ∈ maximalIdeal (PatchingAlgebra R F) :=
    mem_maximalIdeal_of_isRegular hregRinf
  -- ### the bottom identification of the patched module
  let projA : PatchingModule (MvPowerSeries (Fin q) ℤ_[p]) M F →+ M0 :=
    (projQ.toLinearMap.toAddMonoidHom).comp
      (Submodule.mkQ (taylorWilesAug p q • ⊤ :
        Submodule (MvPowerSeries (Fin q) ℤ_[p])
        (PatchingModule (MvPowerSeries (Fin q) ℤ_[p]) M F))).toAddMonoidHom
  have hprojAsurj : Function.Surjective projA :=
    projQ.surjective.comp (Submodule.mkQ_surjective _)
  -- LEAF 9 (`quotientEquivOver_mkQ_smul`); its `HCompat` hypothesis is
  -- the `projM_smul` field read through the construction of `sM`/`sR`.
  have hHCompat : ∀ (n : ℕ) (m : M n) (r : R n),
      sM n (Submodule.Quotient.mk (r • m)) =
        sR n (Ideal.Quotient.mk _ r) • sM n (Submodule.Quotient.mk m) := by
    intro n m r
    show prM n (r • m) = ψ (tR n r) • prM n m
    exact hprMsmul n r m
  have hprojAsmul : ∀ (a : PatchingAlgebra R F)
      (m : PatchingModule (MvPowerSeries (Fin q) ℤ_[p]) M F),
      projA (a • m) = ψ (θ a) • projA m := fun a m =>
    quotientEquivOver_mkQ_smul (MvPowerSeries (Fin q) ℤ_[p]) R M F
      (taylorWilesAug p q) sR sM hHCompat a m
  -- LEAF 10 (`mem_ker_smul_top_of_quotientEquivOver_mkQ_eq_zero`)
  have hprojAker : ∀ m : PatchingModule (MvPowerSeries (Fin q) ℤ_[p]) M F, projA m = 0 →
      m ∈ RingHom.ker θ •
        (⊤ : Submodule (PatchingAlgebra R F)
          (PatchingModule (MvPowerSeries (Fin q) ℤ_[p]) M F)) := fun m hm =>
    mem_ker_smul_top_of_quotientEquivOver_mkQ_eq_zero (MvPowerSeries (Fin q) ℤ_[p]) R M F
      (taylorWilesAug p q) sR sM m hm
  exact nonempty_patchedModule_of_patchingData ψ coeff lift hliftsurj θ hθsurj inferInstance
    (ts.map (algebraMap (MvPowerSeries (Fin q) ℤ_[p]) (PatchingAlgebra R F)))
    (by simpa using htslen) hmemRinf hregRinf hM0 projA hprojAsurj hprojAsmul hprojAker

end PatchingInstantiation

/-- **The patching extraction at its natural universes** (patching
leaf 2b′; ASSEMBLED 2026-07-25 — this declaration is now GLUE over
`exists_patchedModule_of_fields` above, which instantiates the vendored
development and is itself sorry-free glue over the sixteen named leaves
stated immediately above it, six of which are still open; opened
2026-07-25 as the universe-monomorphic
form of `TaylorWilesSystem.exists_patchedModule`): identical content,
but with the patched module in the universe `b` of the tower's modules
`S.M` and the bottom module in the universe `c` of `S.M0`.  The
polymorphic statement follows by `PatchedModule.nonempty_transport`.

This is the shape the vendored FLT patching development
(`Fermat/FLT/Modularity/PatchingVendored/`) can actually hit: its
`PatchingModule Λ M F` is a submodule of a product indexed by the
`Type 0` type `OpenIdeals Λ` of components which are ultraproducts of
quotients of the `M i`, hence lands in `Type b`, and its bottom
identification `PatchingModule.quotientEquivOver` lands on `S.M0`
itself, in `Type c`.

HANDOFF MAP (2026-07-25) — the instantiation of the vendored
development at `S`, worked out but not yet written:

* `Λ := MvPowerSeries (Fin S.q) ℤ_[p]` in its **diamond** role, with
  the scoped product topology `MvPowerSeries.WithPiTopology`.  The
  topological hypotheses of the vendored files are then: `CompactSpace`
  (a product of copies of the compact `ℤ_[p]`), `T2Space`
  (`MvPowerSeries.WithPiTopology.instT2Space`), `IsTopologicalRing`
  (`…instIsTopologicalRing`), `TotallyDisconnectedSpace`, and
  `IsNoetherianRing` (the project's own leaf
  `isNoetherianRing_mvPowerSeries`).  Crucially `IsAdicTopology Λ` is
  then FREE: `PatchingVendored/AdicTopology.lean` carries the instance
  "a profinite Noetherian ring has the `𝔪`-adic topology", so the
  product topology need never be compared with the adic one by hand.
  This was CHECKED against the pin on 2026-07-25: with
  `open scoped MvPowerSeries.WithPiTopology`, the goal
  `IsLocalRing.IsAdicTopology (MvPowerSeries (Fin q) ℤ_[p])` closes by
  `infer_instance` from `[IsNoetherianRing (MvPowerSeries (Fin q) ℤ_[p])]`
  alone, after the two `inferInstanceAs` steps that unfold
  `MvPowerSeries (Fin q) ℤ_[p]` to `(Fin q →₀ ℕ) → ℤ_[p]` for
  `CompactSpace` and `TotallyDisconnectedSpace`.  Gotcha: the latter
  needs `Mathlib.Topology.MetricSpace.Ultra.TotallySeparated` and
  `Mathlib.Topology.Connected.TotallyDisconnected` imported (the route
  is `IsUltrametricDist ℤ_[p] → TotallySeparatedSpace →
  TotallyDisconnectedSpace`, then `Pi.totallyDisconnectedSpace`);
  without them synthesis fails with no hint of the cause.
  `Algebra.TopologicallyFG ℤ Λ` holds because `ℤ`-adjoining the
  variables is dense (`ℤ` is dense in `ℤ_[p]`).
* `ι := ℕ`, `F :=` any nonprincipal ultrafilter on `ℕ`;
  `R i := S.R i` with `Algebra Λ (R i)` given by `S.diamond i`, and
  `M i := S.M i` with `IsScalarTower Λ (R i) (M i)` given by
  `S.diamond_smul`.  Each `R i` is topologized by the topology
  coinduced along the surjection `S.pres i`, which makes it profinite
  (its kernel is f.g. by Noetherianity, hence compact, hence closed),
  so again `IsAdicTopology (R i)` is free, and
  `Algebra.UniformlyBoundedRank R` holds because
  `R i / 𝔪^k` is a quotient of the FIXED finite ring `Λ/𝔪^k`.
* `Module.UniformlyBoundedRank Λ M` and
  `Module.Free (Λ ⧸ Ann Λ (M i)) (M i)` come from `S.freeM` (rank `d`,
  annihilator `S.bIdeal i`), and `IsPatchingSystem Λ M F` from
  `S.bIdeal_le` (`𝔟_n ≤ 𝔪^n → 0`).  Here `1 ≤ S.d` is forced by
  `S.nontrivialM0` through `S.projM_surjective`.
* `Runiv` plays the vendored `R₀`: `hres` and `hcomplete` give
  `CompactSpace` through
  `IsLocalRing.compactSpace_of_finite_residueField`, with the adic
  topology taken by fiat (`IsLocalRing.withIdeal`).
* The bottom identifications `sR`/`sM` demanded by
  `PatchingVendored/Over.lean` are `S.toRuniv i`/`S.projM i` read
  through `S.ker_toRuniv`/`S.projM_eq_zero_iff`, with `𝔫` the
  augmentation ideal `taylorWilesAug p S.q`.  They must be `Λ`-ALGEBRA
  resp. `Λ`-LINEAR, which needs one compatibility NOT recorded as a
  field of `TaylorWilesSystem`: that `(S.toRuniv i).comp (S.diamond i)`
  is independent of `i`.  It is derivable, not an omission: both sides
  kill `𝔫` (by `S.ker_toRuniv`) hence factor through
  `Λ/𝔫 ≅ ℤ_[p]`, and a ring hom `ℤ_[p] →+* Runiv` is unique because
  (i) `p` cannot map to a unit — otherwise `ℚ_p` would embed in
  `Runiv` and its residue field, contradicting `hres` — so `p ↦ 𝔪`,
  and (ii) `Runiv` is `𝔪`-adically separated by `hcomplete`, so the
  value on `ℤ_[p]` is pinned by the value on the dense subring `ℤ`.
* The `PatchedModule` fields are then read off:
  `Minf := PatchingModule Λ M F` with the `Λ`-action taken through
  `PatchingAlgebra.lift R F S.pres` (the **presentation** role of the
  same ring — `lift` needs only ring homs, not `Λ`-algebra maps, so
  the two roles of `Λ` never have to be reconciled);
  `toRuniv := PatchingAlgebra.quotientToOver … ∘ mk ∘ lift`, surjective
  by `PatchingAlgebra.lift_surjective` and
  `PatchingAlgebra.surjective_quotientToOver`; `proj` and `proj_smul`
  from `PatchingModule.quotientEquivOver` and `smul_lemma`;
  `mem_smul_top_of_proj_eq_zero` because `ker proj` is generated by
  the image of `𝔫`, which `toRuniv` kills.
* `exists_isRegular` is where this project departs from FLT (whose
  endgame goes through `Module.depth`, deliberately not vendored):
  take the project's own
  `exists_isRegular_ofList_eq_maximalIdeal_mvPowerSeries` sequence
  `(p, S₁, …, S_q)` in the DIAMOND copy, push it into
  `PatchingAlgebra` and lift it back along the surjection `lift` (the
  lifts stay in `𝔪` because a surjection of local rings is local);
  it is `M_∞`-regular because `M_∞` is FREE over the diamond `Λ`
  (`instance : Module.Free Λ (PatchingModule Λ M F)`, the decisive
  output of `PatchingVendored/Module.lean`) — the transfer lemma is
  `RingTheory.Sequence.isWeaklyRegular_of_free` of
  `FLT/Patching/Utils/Depth.lean`, the one declaration of that file
  worth vendoring. -/
theorem TaylorWilesSystem.exists_patchedModule_natural.{a, b, c, s, uR}
    {p : ℕ} [Fact p.Prime]
    {Runiv : Type uR} [CommRing Runiv] [IsLocalRing Runiv]
    [IsNoetherianRing Runiv]
    {T : Type s} [CommRing T] {ψ : Runiv →+* T}
    (S : TaylorWilesSystem.{a, b, c, s, uR} p ψ)
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal Runiv) Runiv)
    (hres : Finite (Runiv ⧸ IsLocalRing.maximalIdeal Runiv)) :
    Nonempty (PatchedModule.{b, c, s, uR} p ψ) := by
  -- the structure's instance FIELDS are not in scope as instances once the
  -- data fields are passed one by one, so install them first
  letI := S.commRingR
  letI := S.addCommGroupM
  letI := S.moduleRM
  letI := S.moduleCoeffM
  letI := S.addCommGroupM0
  letI := S.moduleM0
  exact exists_patchedModule_of_fields S.q S.d S.coeff S.R S.pres S.pres_surjective S.diamond
    S.toRuniv S.toRuniv_surjective S.ker_toRuniv S.M S.diamond_smul S.bIdeal
    S.bIdeal_le S.freeM S.M0 S.nontrivialM0 S.projM S.projM_surjective S.projM_smul
    (fun n m => ⟨(S.projM_eq_zero_iff n m).mp, (S.projM_eq_zero_iff n m).mpr⟩)
    hcomplete hres

/-- **The patching extraction** (patching leaf 2b; sorry node — the
pure commutative-algebra half, the pigeonhole/inverse-limit heart): a
`TaylorWilesSystem` for `ψ`, together with completeness and residual
finiteness of `Runiv`, yields the `PatchedModule` for `ψ`.
Unconditionally true — no arithmetic content (every hypothesis is
commutative algebra; the Galois/Hecke content is packaged inside the
system's fields).

Classical route (Taylor–Wiles 1995 §3; Diamond 1997, proof of
Thm. 3.1; DDT (1995), proof of Thm. 5.28; Kisin 2009 §(2.2) for the
inverse-limit reorganization): for every open level `α = 𝔪_Λ^j`, the
truncated data `(R n/𝔪^{f(j)}, M n/αM n, toRuniv n, projM n)` ranges
over FINITELY many isomorphism types (all objects are finite of
bounded cardinality, by `pres_surjective` and `freeM` with the fixed
rank `d`), so a pigeonhole (König's lemma, or an ultrafilter as in
`FLT/Patching`) extracts a subtower compatible under the level maps;
the inverse limit `M_∞` is finite over `Λ = ℤ_p[[x₁, …, x_q]]` acting
through the limit of `pres`, indeed finite FREE over the `S`-copy of
`Λ` acting through the limit of `diamond` (the `freeM` coordinates
converge since `𝔟_n → 0` by `bIdeal_le`), whence the images of the
maximal regular sequence `(p, S₁, …, S_q)` — lifted through the limit
presentation into the maximal ideal — form the required `M_∞`-regular
sequence of length `q + 1` (`exists_isRegular`); the limit of
`toRuniv n ∘ pres n` is the patching surjection `R_∞ ↠ Runiv`
(surjectivity from `IsAdicComplete` and residual finiteness, which
exhibit `Runiv` as the limit of its finite `𝔪`-power quotients), and
the limits of `projM` give the bottom identification, with
`proj_smul` from `projM_smul` and `mem_smul_top_of_proj_eq_zero` from
`projM_eq_zero_iff` (converting the `𝔫`-action into the
`ker toRuniv`-action by lifting the variables `Sᵢ` through the limit
presentation into `ker toRuniv`).

VENDORING PLAN (pin-drift audit 2026-07-24): the sorry-free abstract
patching development of the FLT project implements exactly this
extraction in ultraproduct form — `FLT/Patching/Ultraproduct.lean`
(`UltraProduct` and its quotient calculus), `Module.lean`
(`PatchingModule`, `Module.UniformlyBoundedRank`, `IsPatchingSystem`,
and decisively `instance : Module.Free R (PatchingModule R M F)`, the
patched freeness), `Algebra.lean` (`PatchingAlgebra`, `lift`,
`lift_surjective`, `constEquiv`), `Over.lean`/`System.lean`
(`quotientToOver`, `quotientEquivOver`, `smulData`, `smul_lemma` —
the bottom identifications and the action descent), plus
`Utils/{Lemmas,StructureFiniteness,InverseLimit,AdicTopology,
TopologicallyFG,CompactHausdorffRings}.lean`.  All patching names are
FLT-project-local (no mathlib counterparts), so the vendoring cost is
the MATHLIB drift between the FLT pin `81a5d25` (mathlib v4.32.0) and
this project's pin `a3364fa` — plus dropping their
`Utils/Depth.lean`/`REqualsT.lean` layer: their endgame
`ker_RtoT_le_nilradical` goes through `Module.depth` and yields only
`R_red = 𝕋_red`, which our regular-sequence formulation replaces
(leaf 3 `free_of_isRegular_mvPowerSeries` owns the
Auslander–Buchsbaum content instead).  Instantiate at
`Λ := ℤ_p[[S₁, …, S_q]]`, `R i := S.R i`, `M i := S.M i`, `F` any
nonprincipal ultrafilter on `ℕ`, with the topological instances
derived from `pres_surjective` (quotient topologies of the product
topology on `MvPowerSeries`, scoped
`MvPowerSeries.WithPiTopology`): `Algebra.UniformlyBoundedRank` from
the fixed presentation ring, `Module.UniformlyBoundedRank` and
`IsPatchingSystem` from `freeM`/`bIdeal_le` (the `Λ`-annihilator of
`(Λ/𝔟_n)^d` is `𝔟_n ≤ 𝔪^n → 0` for `d ≥ 1`, and `d ≥ 1` is forced by
`nontrivialM0` through `projM_surjective`).

Universe note: the conclusion is polymorphic in `{v, w}`; the
construction lands in fixed universes and is transported by
quotient-presentation shrinking (a finite module over the `Type 0`
ring `MvPowerSeries (Fin q) ℤ_[p]` is isomorphic to a `Type 0`
quotient of `Fin m → MvPowerSeries (Fin q) ℤ_[p]`, and `M0` to the
`proj`-image quotient of `M_∞` with the `T`-action transported along
the identification) followed by `ULift`.

PROOF (glue, 2026-07-25): that universe note is now DISCHARGED —
`PatchedModule.nonempty_transport` above carries out both shrinkings
and the `ULift`, so this node reduces to
`TaylorWilesSystem.exists_patchedModule_natural`, the same statement at
the universes the vendored FLT patching development actually produces.
The abstract patching machinery itself is vendored and verified in
`Fermat/FLT/Modularity/PatchingVendored/` (ten modules, elaborating
clean against this project's mathlib pin); the remaining frontier is
the INSTANTIATION of that machinery at `S`, mapped out in the
docstring of `exists_patchedModule_natural`. -/
theorem TaylorWilesSystem.exists_patchedModule.{v, w, a, b, c, s, uR}
    {p : ℕ} [Fact p.Prime]
    {Runiv : Type uR} [CommRing Runiv] [IsLocalRing Runiv]
    [IsNoetherianRing Runiv]
    {T : Type s} [CommRing T] {ψ : Runiv →+* T}
    (S : TaylorWilesSystem.{a, b, c, s, uR} p ψ)
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal Runiv) Runiv)
    (hres : Finite (Runiv ⧸ IsLocalRing.maximalIdeal Runiv)) :
    Nonempty (PatchedModule.{v, w, s, uR} p ψ) :=
  (S.exists_patchedModule_natural hcomplete hres).elim
    fun P => PatchedModule.nonempty_transport P

/-- **Coordinates for a finite free module over a quotient ring**
(PROVEN): if `M` carries compatible `Λ`- and `Λ/𝔟`-actions and is
finite free of rank `d` over `Λ/𝔟`, then `M ≅ (Λ/𝔟)^d` as a
`Λ`-module.  (Choose a basis, reindex it by `Fin d` using
`finrank = d`, take coordinates, and restrict scalars along
`Λ → Λ/𝔟`.)

This converts the Taylor–Wiles freeness certificate from the form in
which it is proven (Diamond 1997, Thm. 2.1: `H_Q` is free of rank `d`
over `ℤ_p[Δ_Q] = Λ/𝔟_Q`) to the coordinate form
`TaylorWilesSystem.freeM` in which the patching extraction consumes
it. -/
theorem nonempty_linearEquiv_fin_of_free_over_quotient.{uL, uM}
    {Λ : Type uL} [CommRing Λ] (𝔟 : Ideal Λ) [Nontrivial (Λ ⧸ 𝔟)]
    {M : Type uM} [AddCommGroup M] [Module Λ M] [Module (Λ ⧸ 𝔟) M]
    [IsScalarTower Λ (Λ ⧸ 𝔟) M] [Module.Free (Λ ⧸ 𝔟) M]
    [Module.Finite (Λ ⧸ 𝔟) M] (d : ℕ)
    (hd : Module.finrank (Λ ⧸ 𝔟) M = d) :
    Nonempty (M ≃ₗ[Λ] (Fin d → Λ ⧸ 𝔟)) := by
  classical
  let b := Module.Free.chooseBasis (Λ ⧸ 𝔟) M
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex (Λ ⧸ 𝔟) M) = d := by
    rw [← Module.finrank_eq_card_chooseBasisIndex]; exact hd
  let b' : Module.Basis (Fin d) (Λ ⧸ 𝔟) M :=
    b.reindex (Fintype.equivFinOfCardEq hcard)
  exact ⟨(b'.equivFun).restrictScalars Λ⟩

/-- **A Taylor–Wiles TOWER yields a Taylor–Wiles SYSTEM** (PROVEN 2026-07-27):
the transposition `∀ n, level n ↦ ℕ`-indexed families, plus the two derivations
the system's fields need beyond the level's.

This is bookkeeping, and it is deliberately BASE-FIELD-FREE — no Galois
representation, no Hecke algebra, no number field appears — so the SAME lemma
serves the `ℚ`-level assembly and the totally-real-field one. It was extracted
here on 2026-07-27 for exactly that reason: `exists_hilbertPatchingSystem` in
`HardlyRamified/HilbertModularity.lean` needs to produce a `TaylorWilesSystem`,
and the arithmetic over a totally real field produces the auxiliary objects one
DEPTH AT A TIME, i.e. in `TaylorWilesTower` shape. With this lemma that leaf
cuts into "build the tower" plus proven glue, instead of being asked for the
transposed form as well.

The two derivations, neither of which the arithmetic should be asked for:

* **`freeM`** — the level carries freeness as a `Λ/𝔟_n`-module structure plus
  `Module.Free`/`Module.Finite`/`finrank = d`; the system wants the `Λ`-linear
  coordinate equivalence `M ≃ₗ[Λ] (Fin d → Λ/𝔟_n)`.
  `nonempty_linearEquiv_fin_of_free_over_quotient` above converts one to the
  other by choosing a basis.
* **`projM_eq_zero_iff`** — the level states only the hard direction
  (`projM m = 0 → m ∈ 𝔫·M`, the control theorem). The converse is FORCED:
  `𝔫` acts on `M` through `diamond` (`diamond_smul`), `diamond` sends `𝔫` into
  `ker toRuniv` (`ker_toRuniv`), and `projM` is `ψ ∘ toRuniv`-equivariant
  (`projM_smul`), so every element of `𝔫·M` dies under `projM`. That is `hzero`
  below, proven by `Submodule.smul_induction_on`.

NOTE (2026-07-27): `exists_taylorWilesSystem` in `Modularity/Patching.lean`
still carries its own inline copy of this argument. Rewiring it to call this
lemma would remove the duplication and is safe, but that theorem belongs to
another owner's region and was deliberately left untouched here. -/
theorem nonempty_taylorWilesSystem_of_tower.{a, b, c, s, uR}
    {p : ℕ} [Fact p.Prime]
    {Runiv : Type uR} [CommRing Runiv]
    {T : Type s} [CommRing T] {ψ : Runiv →+* T}
    (tw : TaylorWilesTower.{a, b, c, s, uR} p ψ) :
    Nonempty (TaylorWilesSystem.{a, b, c, s, uR} p ψ) := by
  classical
  letI := tw.addCommGroupM0
  letI := tw.moduleM0
  letI iR : ∀ n, CommRing (tw.level n).R := fun n => (tw.level n).commRingR
  letI iAG : ∀ n, AddCommGroup (tw.level n).M :=
    fun n => (tw.level n).addCommGroupM
  letI iRM : ∀ n, Module (tw.level n).R (tw.level n).M :=
    fun n => (tw.level n).moduleRM
  letI iCoeff : ∀ n,
      Module (MvPowerSeries (Fin tw.q) ℤ_[p]) (tw.level n).M :=
    fun n => (tw.level n).moduleCoeffM
  letI iQuot : ∀ n,
      Module (MvPowerSeries (Fin tw.q) ℤ_[p] ⧸ (tw.level n).bIdeal)
        (tw.level n).M :=
    fun n => (tw.level n).moduleQuotM
  letI iTower : ∀ n, IsScalarTower (MvPowerSeries (Fin tw.q) ℤ_[p])
      (MvPowerSeries (Fin tw.q) ℤ_[p] ⧸ (tw.level n).bIdeal)
      (tw.level n).M :=
    fun n => (tw.level n).isScalarTowerM
  letI iNontriv : ∀ n,
      Nontrivial (MvPowerSeries (Fin tw.q) ℤ_[p] ⧸ (tw.level n).bIdeal) :=
    fun n => (tw.level n).nontrivialQuot
  letI iFree : ∀ n,
      Module.Free (MvPowerSeries (Fin tw.q) ℤ_[p] ⧸ (tw.level n).bIdeal)
        (tw.level n).M :=
    fun n => (tw.level n).freeM
  letI iFinite : ∀ n,
      Module.Finite (MvPowerSeries (Fin tw.q) ℤ_[p] ⧸ (tw.level n).bIdeal)
        (tw.level n).M :=
    fun n => (tw.level n).finiteM
  have hcoord : ∀ n, Nonempty ((tw.level n).M ≃ₗ[MvPowerSeries (Fin tw.q) ℤ_[p]]
      (Fin tw.d → MvPowerSeries (Fin tw.q) ℤ_[p] ⧸ (tw.level n).bIdeal)) :=
    fun n => nonempty_linearEquiv_fin_of_free_over_quotient
      (tw.level n).bIdeal tw.d (tw.level n).finrankM
  -- the easy inclusion of the bottom control identification: `𝔫` acts
  -- through `diamond`, and `diamond`'s image of `𝔫` dies in `Runiv`
  have hzero : ∀ (n : ℕ) (m : (tw.level n).M),
      m ∈ (taylorWilesAug p tw.q • ⊤ :
        Submodule (MvPowerSeries (Fin tw.q) ℤ_[p]) (tw.level n).M) →
      (tw.level n).projM m = 0 := by
    intro n m hm
    refine Submodule.smul_induction_on hm ?_ ?_
    · intro r hr y _
      have hker : (tw.level n).diamond r ∈
          RingHom.ker (tw.level n).toRuniv := by
        rw [(tw.level n).ker_toRuniv]; exact Ideal.mem_map_of_mem _ hr
      rw [RingHom.mem_ker] at hker
      rw [(tw.level n).diamond_smul, (tw.level n).projM_smul, hker,
        map_zero, zero_smul]
    · intro a b ha hb
      rw [map_add, ha, hb, add_zero]
  exact ⟨{ q := tw.q
           d := tw.d
           coeff := tw.coeff
           R := fun n => (tw.level n).R
           commRingR := fun n => (tw.level n).commRingR
           pres := fun n => (tw.level n).pres
           pres_surjective := fun n => (tw.level n).pres_surjective
           diamond := fun n => (tw.level n).diamond
           toRuniv := fun n => (tw.level n).toRuniv
           toRuniv_surjective := fun n => (tw.level n).toRuniv_surjective
           ker_toRuniv := fun n => (tw.level n).ker_toRuniv
           M := fun n => (tw.level n).M
           addCommGroupM := fun n => (tw.level n).addCommGroupM
           moduleRM := fun n => (tw.level n).moduleRM
           moduleCoeffM := fun n => (tw.level n).moduleCoeffM
           diamond_smul := fun n => (tw.level n).diamond_smul
           bIdeal := fun n => (tw.level n).bIdeal
           bIdeal_le := fun n => (tw.level n).bIdeal_le
           freeM := fun n => (hcoord n).some
           M0 := tw.M0
           addCommGroupM0 := tw.addCommGroupM0
           moduleM0 := tw.moduleM0
           nontrivialM0 := tw.nontrivialM0
           projM := fun n => (tw.level n).projM
           projM_surjective := fun n => (tw.level n).projM_surjective
           projM_smul := fun n => (tw.level n).projM_smul
           projM_eq_zero_iff := fun n m =>
             ⟨(tw.level n).projM_eq_zero m, hzero n m⟩ }⟩

end GaloisRepresentation.Modularity
