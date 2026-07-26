/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib.Algebra.CharP.Basic
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.Data.Finsupp.Option
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

end GaloisRepresentation.Modularity
