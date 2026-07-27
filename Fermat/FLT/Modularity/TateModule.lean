/-
Modularity/TateModule.lean — own work for the Fermat project (not
vendored from the FLT project).

# Tate modules of a geometric fibre of an abelian scheme

This module supplies the **second missing piece** of the classical
discharge of `exists_twistedHilbertBlumenthalModuli_of_five_le`
(`Modularity/KhareWintenberger.lean`), continuing
`Modularity/AbelianScheme.lean`. That module made the *torsion* of a
geometric fibre a `Γ_F`-module; this one makes the *Tate module* — the
inverse limit of the torsion along a uniformizer — an object the pin can
name, and cuts the Tate-module construction

  `nonempty_hilbertBlumenthalPoint_of_isTwistedHilbertBlumenthalModuli`

into two independently citable statements of the theory of abelian
varieties:

* `exists_tateFrame_of_levelStructure` — items 7 and 8 of that leaf's
  missing-machinery list: `T_I A` is free of rank `2` over the
  completion `𝒪_{D,I}`, with continuous `Γ_F`-action, and its reduction
  is `A[I]`, so the Frobenius characteristic polynomials of `T_I A`
  reduce to those of the level structure — and, since 2026-07-26, that
  the determinant of Frobenius on the frame is the absolute norm (the
  Weil pairing; see the DETERMINANT CLAUSE paragraph in that leaf's
  docstring for why it belongs in an existentially quantified frame and
  is false for a given one);
* `exists_weilFrobeniusSystem_of_mult` — item 9, Weil/Faltings: those
  characteristic polynomials are already defined over `D` and are
  INDEPENDENT of `I`, i.e. the `T_I A` for varying `I` are members of one
  strictly compatible system. This is the deepest statement in the
  chain. **It is currently FALSE AS STATED** — see the FAITHFULNESS
  AUDIT in its own docstring, which refutes it with two explicit
  counterexamples and gives the three-declaration seam repair. Do not
  dispatch a prover at it before the repair lands.

## Why a DEFINITION is needed here, and what it buys

The two statements above cannot be cut apart without an object that ties
them together. Each of them is an existence statement about a coefficient
ring `O` and a representation `τ : Γ_F → GL₂(O)`; but "there exists a
rank-`2` representation whose reduction is `A[I]`" and "there exists a
`D`-rational compatible system" are, taken separately, statements about
*unrelated* representations — the second is outright FALSE when applied
to an arbitrary `τ` that merely happens to have the right reduction,
since a residual condition constrains `τ` only modulo `I`. Any cut into
two leaves must therefore name the actual Tate module.

`TatePt` is that name. It is the honest inverse limit

  `T = lim ( ⋯ →  A[I³]  --·π-->  A[I²]  --·π-->  A[I] )`,

taken inside the `Γ_F`-module of geometric points supplied by
`Modularity/AbelianScheme.lean`, with the transition maps given by
multiplication by an element `π ∈ I ∖ I²` (which generates `I` in the
local ring `𝒪_{D,I}`, so the limit is the usual `I`-adic Tate module and
not a product over several primes). No completion, no topology and no
profinite machinery is needed to WRITE it: it is a subtype of
`ℕ → GeomFibrePt f x` cut out by two equations, exactly as
`Mult.torsion` is a subset cut out by one.

Both leaves below then speak about `TatePt`: the first produces a FRAME
— a `Γ_F`-equivariant additive bijection `(Fin 2 → O) ≃ T` — and the
second consumes one. That is the link, and it is what was supposed to
make the second leaf a true statement rather than a plausible-looking
false one.

**It is not enough, and the second leaf is false because of it**
(2026-07-26). An additive `Γ_F`-equivariant bijection ties `τ` to `A`
but NOT to the real multiplication `m`: the coefficient ring `O` is
pinned only up to "some commutative subring of `End_{Γ_F}(T)` over
which `T` is free of rank two", and when `A_x` has endomorphisms beyond
`𝒪_D` there are such rings that are not `𝒪_{D,I}` — including
non-domains, for which the second leaf's conclusion fails outright. The
frame notion must carry a ring map `𝒪_D →+* O` intertwining `φ` with
`m.act`; see the FAITHFULNESS AUDIT on
`exists_weilFrobeniusSystem_of_mult`.

## What is proven here

Five lemmas and one assembly.

* `isIrreducible_map_of_restrictionSurjective`: irreducibility of a
  Galois representation descends along a restriction that preserves the
  image. It is what lets the consumer supply the irreducibility
  hypothesis that the frame leaf needs at `λ` (see the FAITHFULNESS
  AUDIT there — the leaf was FALSE without it).
* `exists_mem_notMem_sq_of_isMaximal`: a nonzero maximal ideal of a
  Dedekind domain contains an element outside its square — the
  uniformizer `π` that `TatePt` is indexed by.
* `exists_finset_forall_natCast_notMem`: only finitely many places of a
  number field lie over a rational prime. This is the exceptional set
  `bad` of the determinant clause, and the only reason one is needed.
* `adicArithFrob_rootsOfUnity_pow_absNorm` and
  `cyclotomicCharacter_adicArithFrob_absNorm`: away from `ℓ` the
  arithmetic Frobenius at `w` raises `ℓ`-power roots of unity to the
  `Nw`-th power, so the `ℓ`-adic cyclotomic character takes the value
  `Nw` there. Pure algebraic number theory. (Both are reproductions of
  proofs that live in the DOWNSTREAM `Modularity/KhareWintenberger.lean`
  and are therefore unusable from here; since that module imports this
  one, the intended cleanup is to delete the downstream copies rather
  than these.)
* `exists_tateFrame_of_levelStructure` itself is PROVEN (2026-07-26),
  by assembly over four independent leaves, one per theory:
  `exists_adicCoefficientRing` (commutative algebra: the completion
  `𝒪_{D,I}` as a topological `ℤ_q`-algebra),
  `exists_tateFrame_of_adicCoefficientRing` (abelian varieties: `T_I A`
  is free of rank two over it, equivariantly),
  `exists_residualEmbedding_of_tateFrame` (representation theory: the
  reduction matches the level structure up to `Aut(k')` — the ONLY
  place `hirr` is used, and the step whose unconditional form was
  refuted) and `det_eq_cyclotomicCharacter_of_tateFrame` (the WEIL
  PAIRING: `det τ = χ_cyc`, the whole content of the determinant
  clause, cut out of the assembly on 2026-07-26).
* `exists_adicCoefficientRing` is itself PROVEN (2026-07-26): `O` is
  mathlib's `v.adicCompletionIntegers D`, all three PIN conjuncts are
  discharged here (`isAdicComplete_span_uniformizer`,
  `exists_sub_mem_span_uniformizer_pow`, `mem_span_uniformizer_pow_iff`),
  and its `ℤ_q`-algebra structure is `padicIntAlgebra`, built from a
  general `padicIntLiftHom : ℤ_[p] →+* O` for `p`-adically complete `O`
  that mathlib does not have.  Its last leaf,
  `module_finite_free_moduleTopology_padicIntAlgebra`, is PROVEN as of
  2026-07-26 by a compactness argument
  (`finite_free_moduleTopology_of_approx`) that replaces complete
  Nakayama and needs no base change of adic completions, so the whole
  subsection is now sorry-free.

`exists_weilFrobeniusSystem_of_mult` remains a single sorried leaf; it
is stated about the geometric objects of `AbelianScheme.lean` and about
nothing else.
-/
module

public import Fermat.FLT.Modularity.AbelianScheme
public import Fermat.FLT.Modularity.AbelianSchemeIsogeny
-- `AlgebraicGeometry.IsFinite`, `LocallyQuasiFinite` and
-- `IsFinite.of_isProper_of_locallyQuasiFinite` (Zariski's main theorem):
-- the multiplication-by-`n` morphism of an abelian scheme and the
-- reduction of `finite_torsion_span_natCast` to its quasi-finiteness
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Fermat.FLT.Deformations.RepresentationTheory.GaloisRep
-- `GaloisRepresentation.globalFrob` and `dense_conjClasses_globalFrob`: the
-- Chebotarev density input of `det_eq_cyclotomicCharacter_of_globalFrob`.
-- Adds only `Chebotarev` and `BrauerNesbitt` to this module's import cone,
-- and this module's sole consumer (`Modularity.KhareWintenberger`) already
-- has both; there is no cycle (`Chebotarev`'s cone does not meet `Modularity`).
public import Fermat.FLT.GaloisRepresentation.Chebotarev
-- `IsDedekindDomain.HeightOneSpectrum.natCard_under_maximalIdeal`: the residue
-- cardinality at `w` in the Frobenius specification of
-- `adicArithFrob_rootsOfUnity_pow_absNorm`
public import Fermat.FLT.Deformations.RepresentationTheory.CompletionTransport
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.NumberTheory.Padics.RingHoms
-- `IsLocalRing.isOpen_maximalIdeal_pow` and the instance
-- `IsNoetherianRing.isClosed_ideal`: the openness half of the comparison
-- between the `ℤ_q`-module topology and the `P`-adic topology in
-- `exists_galoisRep_of_isOpen_congruence`
public import Mathlib.Topology.Algebra.Ring.Compact
-- `Ideal.iInf_pow_eq_bot_of_isLocalRing` (Krull intersection): the
-- cofinality half of that comparison
public import Mathlib.RingTheory.Filtration
-- `PadicInt.compactSpace`: `ℤ_q` is compact, whence so is every finite
-- `ℤ_q`-module with the module topology
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Dimension.Constructions
-- `IsAdicComplete`: the completeness half of the pin that identifies the
-- coefficient ring of `exists_adicCoefficientRing` with `𝒪_{D,I}`
public import Mathlib.RingTheory.AdicCompletion.Basic
-- `IsAdic.isAdicComplete_iff`: `IsAdicComplete` from completeness and
-- Hausdorffness of the adic topology, used to discharge that pin for
-- `v.adicCompletionIntegers D`
public import Mathlib.RingTheory.AdicCompletion.Topology
-- `IsAdicComplete.of_finite_module` (adic completeness of a finite module
-- over a complete noetherian local ring), `HenselianRing.of_finite_algebra`,
-- `HenselianRing.exists_isIdempotentElem_mk_eq`,
-- `IsIdempotentElem.eq_zero_or_eq_one_of_isDomain` and
-- `IsLocalRing.of_isArtinianRing_isIdempotentElem`: the commutative-algebra
-- bricks behind `exists_padicAlgebra_of_additiveEquiv_sq` and
-- `span_range_eq_top_of_adicPin`
public import Fermat.FLT.Mathlib.RingTheory.AdicCompletion.Finite
-- `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers` and its
-- ring / topology / locality / discrete-valuation instances: this is
-- the coefficient ring `𝒪_{D,I}` that `exists_adicCoefficientRing`
-- produces
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
-- `Ideal.exists_mem_pow_notMem_pow_succ`: the uniformizer of
-- `exists_mem_notMem_sq_of_isMaximal`
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
-- `Ideal.absNorm`: the determinant clause of
-- `exists_tateFrame_of_levelStructure` (the Weil pairing, added
-- 2026-07-26) states the determinant of Frobenius to be the absolute
-- norm of the place, so `absNorm` occurs in a STATEMENT here
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
-- `Submodule.isInternal_prime_power_torsion_of_is_torsion_by_ideal`: the
-- CRT splitting `A[p] = ⨁_{J ∣ p} A[J^(e_J)]` used by
-- `LevelFrame.card_tors_eq_sq`.  This adds NOTHING to the import cone —
-- the module imports only `Algebra.Module.Torsion.Basic` and
-- `RingTheory.DedekindDomain.Ideal.Lemmas`, both already above.
public import Mathlib.Algebra.Module.DedekindDomain
-- the Betti input of the rank count: cardinalities of quotients of a
-- lattice by an ideal, and the rank bridge `rank_ℤ = [D:ℚ] · rank_{𝒪_D}`.
public import Fermat.FLT.Mathlib.RingTheory.DedekindDomain.LatticeQuotient
-- `NumberField.IsTotallyReal`: the real-multiplication field of a
-- Hilbert–Blumenthal family is totally real, in both leaf STATEMENTS
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
-- `basisOfTopLeSpanOfCardEqFinrank`: two spanning vectors in a rank-two
-- space are a basis — the step that turns the `ι₀`-semilinearity of the
-- comparison map into the frame `E` of
-- `exists_residualEmbedding_of_scalarCommutant`
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
-- `Module.Basis.det`, `Module.Basis.det_comp`, `Pi.basisFun_det_apply`:
-- the second-exterior-power step of the determinant clause
-- (`bilin_alternating_apply_det`) reads `LinearMap.det` off the value of
-- an alternating form on the standard basis
public import Mathlib.LinearAlgebra.Determinant
-- `Matrix.det_fin_two`: the same step, in coordinates
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
-- `Module.free_of_finite_type_torsion_free'`: over the PID `ℤ_q` a finite
-- torsion-free module is free, which is how `Module.Free` is obtained in
-- `finite_free_moduleTopology_of_approx`
public import Mathlib.LinearAlgebra.FreeModule.PID
-- `Fintype.linearCombination`: the finite-rank approximating map
-- `ℤ_q^ι → 𝒪ᵥ` of the same lemma
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.NumberTheory.NumberField.Ideal.Basic

@[expose] public section

universe u v

open CategoryTheory AlgebraicGeometry IsDedekindDomain Polynomial

namespace Fermat

/-! ### The Tate module of a geometric fibre -/

/-- **The `I`-adic Tate module of the geometric fibre of `f : A ⟶ S` at
an `F`-point `x`**, for an ideal `I` of the coefficient ring `R` acting
on `A` and an element `π ∈ I`:

  `T = lim_n A[Iⁿ]`, the transition maps being multiplication by `π`.

Concretely a point of `T` is a sequence `y : ℕ → A(F̄)` with `y n`
killed by `Iⁿ` and `π · y (n+1) = y n`. The zeroth stage is trivial —
`I⁰ = ⊤` contains `1`, so `A[I⁰] = 0` and hence `y 0 = 0` — which is the
usual indexing of the limit.

The intended `π` is an element of `I ∖ I²` for `I` maximal in the ring
of integers of a number field, so that `I` becomes principal generated
by `π` in the local ring `R_I` and the limit above is the classical
`I`-adic Tate module. Leaves stating properties of `TatePt` therefore
carry `π ∈ I` and `π ∉ I ^ 2` as hypotheses; with a `π` violating them
(most brutally `π = 0`, which forces `T = 0`) the object is not the Tate
module and no rank-`2` frame exists — which is exactly why the frame is
what the leaves below quantify over.

The Galois action is the one induced from
`Fermat.AbelianSchemeStruct.galSMul` componentwise, and the additive
structure the one induced from `Fermat.AbelianSchemeStruct.add`
componentwise; both are written out explicitly in the statements below
rather than installed as instances, in the same style as the level
structures of `IsTwistedHilbertBlumenthalModuli`, so that nothing has to
be carried through the `letI` of `AbelianSchemeStruct.addCommGroup`. -/
def TatePt {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {R : Type u} [CommRing R] (m : Mult ab R)
    {F : Type u} [Field F] (x : Spec (CommRingCat.of F) ⟶ S)
    (I : Ideal R) (π : R) : Type u :=
  {y : ℕ → GeomFibrePt f x //
    (∀ n, y n ∈ (m.torsion x (I ^ n)).1) ∧ (∀ n, m.act π (y (n + 1)) = y n)}

/-! ### Irreducibility along an image-preserving restriction -/

/-- **Irreducibility descends to a subgroup with the same image** (PROVEN).

If every value of `ρ` is already a value of `ρ.map f` — which is what the
`hrestr` hypothesis of the twisted moduli problem asserts — then the two
representations have literally the same invariant submodules, so the
lattice of subrepresentations is the same and simplicity transfers.

This is what carries the irreducibility hypothesis of
`exists_twistedHilbertBlumenthalModuli_of_five_le` from `Γ_ℚ` down to
`Γ_F`, where `exists_tateFrame_of_levelStructure` needs it; see the
FAITHFULNESS AUDIT there for why it is needed. -/
theorem isIrreducible_map_of_restrictionSurjective
    {F : Type u} [Field F]
    {k : Type u} [Field k] [TopologicalSpace k]
    {W : Type v} [AddCommGroup W] [Module k W]
    (ρ : GaloisRep ℚ k W) (f : ℚ →+* F)
    (hrestr : ∀ g : Field.absoluteGaloisGroup ℚ,
      ∃ h : Field.absoluteGaloisGroup F, (ρ.map f) h = ρ g)
    (hirr : ρ.IsIrreducible) : (ρ.map f).IsIrreducible := by
  have key : ∀ s : Submodule k W,
      (∀ (h : Field.absoluteGaloisGroup F) ⦃v : W⦄, v ∈ s → (ρ.map f) h v ∈ s) ↔
        (∀ (g : Field.absoluteGaloisGroup ℚ) ⦃v : W⦄, v ∈ s → ρ g v ∈ s) := by
    intro s
    constructor
    · intro hs g v hv
      obtain ⟨h, hh⟩ := hrestr g
      have hmem := hs h hv
      rwa [hh] at hmem
    · intro hs h v hv
      have hmem := hs (Field.absoluteGaloisGroup.map f h) hv
      rwa [← GaloisRep.map_apply] at hmem
  let e : Subrepresentation (ρ.map f).toRepresentation ≃o
      Subrepresentation ρ.toRepresentation :=
    { toFun := fun s => ⟨s.toSubmodule, (key _).mp s.apply_mem_toSubmodule⟩
      invFun := fun s => ⟨s.toSubmodule, (key _).mpr s.apply_mem_toSubmodule⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact (OrderIso.isSimpleOrder_iff e).mpr hirr

/-! ### The uniformizer -/

/-- **A nonzero maximal ideal of a Dedekind domain contains an element
outside its square** (PROVEN).

This is the `π` of `TatePt`: the strict inclusion `I² < I` holds because
the nonzero ideals of a Dedekind domain form a cancellative monoid, so
`I = I²` would force `I = 1`. Splitting this off keeps the choice of
uniformizer out of the sorried leaves below, where it is a hypothesis
rather than part of the burden. -/
theorem exists_mem_notMem_sq_of_isMaximal {R : Type*} [CommRing R] [IsDedekindDomain R]
    {I : Ideal R} (hI : I.IsMaximal) (hI0 : I ≠ ⊥) :
    ∃ π : R, π ∈ I ∧ π ∉ I ^ 2 := by
  obtain ⟨π, hπ, hπ2⟩ := Ideal.exists_mem_pow_notMem_pow_succ I hI0 hI.ne_top 1
  exact ⟨π, by simpa using hπ, by simpa using hπ2⟩

/-! ### The `I`-adic completion of `𝒪_D`

`exists_adicCoefficientRing` below is discharged by taking `O` to be
mathlib's `v.adicCompletionIntegers D` at the height-one point `v`
carved out by `I`.  Everything in this subsection except
`exists_padicIntStructure_adicCompletionIntegers` is PROVEN here; the
three "pin" conjuncts of that leaf — `IsAdicComplete`, density of
`𝒪_D`, and `j a ∈ (π)ⁿ ↔ a ∈ Iⁿ` — are
`isAdicComplete_span_uniformizer`, `exists_sub_mem_span_uniformizer_pow`
and `mem_span_uniformizer_pow_iff`.

What is NOT proven here, and is the one remaining leaf, is the
`ℤ_q`-structure: mathlib has no functoriality of adic completions along
a finite extension, so `Algebra ℤ_[q] 𝒪_v` does not exist upstream.  See
the docstring of `exists_padicIntStructure_adicCompletionIntegers`. -/

/-! ### Mapping out of `ℤ_p` into a `p`-adically complete ring

Mathlib has the universal property of `ℤ_p` as a projective LIMIT
(`PadicInt.lift`, which maps INTO `ℤ_p`) but not the one that says `ℤ_p`
is the `p`-adic COMPLETION of `ℤ`, which is what produces maps OUT of
it. This subsection supplies exactly that, from `PadicInt.appr` and
`IsAdicComplete`. It is used to give `𝒪_{D,I}` its `ℤ_q`-algebra
structure, which is otherwise unavailable at this pin. -/

section PadicIntLift

variable {p : ℕ} [hp : Fact p.Prime] {O : Type*} [CommRing O]

omit hp in
/-- Naturals congruent mod `pⁿ` have images differing by `(p)ⁿ`
(PROVEN). -/
theorem sub_mem_span_pow_of_modEq {a b n : ℕ} (h : a ≡ b [MOD p ^ n]) :
    ((a : O)) - (b : O) ∈ Ideal.span {(p : O)} ^ n := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd (n := p ^ n)).mp h
  refine ⟨-(c : O), ?_⟩
  have := congrArg (fun z : ℤ => (z : O)) hc
  push_cast at this ⊢
  linear_combination -this

/-- `PadicInt.appr x n` is the unique natural, mod `pⁿ`, congruent to
`x` (PROVEN). -/
theorem appr_modEq (x : ℤ_[p]) (a n : ℕ) (h : x - (a : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ n}) :
    x.appr n ≡ a [MOD p ^ n] := by
  have := PadicInt.zmod_congr_of_sub_mem_span n x (x.appr n) a (PadicInt.appr_spec n x) h
  rwa [ZMod.natCast_eq_natCast_iff] at this

variable (O) in
/-- The approximants of `x` form a Cauchy sequence in any ring (PROVEN). -/
theorem appr_sub_appr_mem (x : ℤ_[p]) : ∀ {m n : ℕ}, m ≤ n →
    ((x.appr m : ℕ) : O) - ((x.appr n : ℕ) : O) ∈ Ideal.span {(p : O)} ^ m := by
  intro m n hmn
  refine sub_mem_span_pow_of_modEq (O := O) ?_
  rw [Nat.modEq_iff_dvd' (x.appr_mono hmn)]
  exact PadicInt.dvd_appr_sub_appr x m n hmn

/-- Transport of `appr_modEq` into the target ring (PROVEN). -/
theorem appr_sub_natCast_mem (x : ℤ_[p]) (a n : ℕ)
    (h : x - (a : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ n}) :
    ((x.appr n : ℕ) : O) - (a : O) ∈ Ideal.span {(p : O)} ^ n :=
  sub_mem_span_pow_of_modEq (appr_modEq x a n h)

variable [IsAdicComplete (Ideal.span {(p : O)}) O]

/-- **The approximants of a `p`-adic integer converge in any
`p`-adically complete ring, to a unique limit** (PROVEN).  Existence is
`IsPrecomplete`, uniqueness is `IsHausdorff`. -/
theorem existsUnique_padicIntLift (x : ℤ_[p]) :
    ∃! L : O, ∀ n : ℕ, ((x.appr n : ℕ) : O) - L ∈ Ideal.span {(p : O)} ^ n := by
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {(p : O)}) inferInstance
    (f := fun n => ((x.appr n : ℕ) : O)) (by
      intro m n hmn
      simpa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using appr_sub_appr_mem O x hmn)
  refine ⟨L, fun n => by simpa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using hL n, ?_⟩
  intro L' hL'
  rw [IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : O)})]
  intro n
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  have h1 := hL' n
  have h2 : ((x.appr n : ℕ) : O) - L ∈ Ideal.span {(p : O)} ^ n := by
    simpa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using hL n
  have := Ideal.sub_mem _ h2 h1
  simpa using this

/-- The image of a `p`-adic integer in a `p`-adically complete ring. -/
noncomputable def padicIntLift (x : ℤ_[p]) : O := (existsUnique_padicIntLift (O := O) x).choose

theorem padicIntLift_spec (x : ℤ_[p]) (n : ℕ) :
    ((x.appr n : ℕ) : O) - padicIntLift (O := O) x ∈ Ideal.span {(p : O)} ^ n :=
  (existsUnique_padicIntLift (O := O) x).choose_spec.1 n

theorem padicIntLift_eq (x : ℤ_[p]) (L : O)
    (h : ∀ n : ℕ, ((x.appr n : ℕ) : O) - L ∈ Ideal.span {(p : O)} ^ n) :
    padicIntLift (O := O) x = L :=
  (existsUnique_padicIntLift (O := O) x).unique
    (existsUnique_padicIntLift (O := O) x).choose_spec.1 h

/-- **The canonical ring homomorphism from `ℤ_p` into a `p`-adically
complete ring** (PROVEN).  Every clause is the uniqueness half of
`existsUnique_padicIntLift` applied to a congruence between
approximants. -/
noncomputable def padicIntLiftHom : ℤ_[p] →+* O where
  toFun := padicIntLift
  map_zero' := padicIntLift_eq _ _ fun n => by
    have h : (0 : ℤ_[p]) - ((0 : ℕ) : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ n} := by simp
    simpa using appr_sub_natCast_mem (O := O) (0 : ℤ_[p]) 0 n h
  map_one' := padicIntLift_eq _ _ fun n => by
    have h : (1 : ℤ_[p]) - ((1 : ℕ) : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ n} := by simp
    simpa using appr_sub_natCast_mem (O := O) (1 : ℤ_[p]) 1 n h
  map_add' x y := padicIntLift_eq _ _ fun n => by
    have hx := PadicInt.appr_spec n x
    have hy := PadicInt.appr_spec n y
    have h : x + y - ((x.appr n + y.appr n : ℕ) : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ n} := by
      have := Ideal.add_mem (Ideal.span {(p : ℤ_[p]) ^ n}) hx hy
      push_cast
      convert this using 1
      ring
    have h1 := appr_sub_natCast_mem (O := O) (x + y) (x.appr n + y.appr n) n h
    have h2 := padicIntLift_spec (O := O) x n
    have h3 := padicIntLift_spec (O := O) y n
    have := Ideal.add_mem _ h1 (Ideal.add_mem _ h2 h3)
    push_cast at this ⊢
    convert this using 1
    ring
  map_mul' x y := padicIntLift_eq _ _ fun n => by
    have hx := PadicInt.appr_spec n x
    have hy := PadicInt.appr_spec n y
    have h : x * y - ((x.appr n * y.appr n : ℕ) : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ n} := by
      have := Ideal.add_mem (Ideal.span {(p : ℤ_[p]) ^ n})
        (Ideal.mul_mem_right y _ hx) (Ideal.mul_mem_left _ ((x.appr n : ℕ) : ℤ_[p]) hy)
      push_cast
      convert this using 1
      ring
    have h1 := appr_sub_natCast_mem (O := O) (x * y) (x.appr n * y.appr n) n h
    have h2 := padicIntLift_spec (O := O) x n
    have h3 := padicIntLift_spec (O := O) y n
    have := Ideal.add_mem _ h1 (Ideal.add_mem _
      (Ideal.mul_mem_left _ ((x.appr n : ℕ) : O) h3)
      (Ideal.mul_mem_right (padicIntLift (O := O) y) _ h2))
    push_cast at this ⊢
    convert this using 1
    ring

end PadicIntLift

section AdicCompletionIntegers

open _root_.NumberField _root_.WithZero

variable {D : Type u} [Field D] [NumberField D] (v : HeightOneSpectrum (𝓞 D))

/-- The valuation of a global integer, viewed in the completed local
ring, is its `v`-adic integral valuation (PROVEN). -/
theorem valued_algebraMap_adicCompletionIntegers (a : 𝓞 D) :
    Valued.v (algebraMap (v.adicCompletionIntegers D) (v.adicCompletion D)
        (algebraMap (𝓞 D) (v.adicCompletionIntegers D) a))
      = v.intValuation a := by
  show Valued.v ((algebraMap (𝓞 D) (v.adicCompletionIntegers D) a : v.adicCompletion D)) = _
  rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v),
    HeightOneSpectrum.valuation_of_algebraMap]

/-- An element of `I ∖ I²` has `v`-adic valuation exactly `exp (-1)`
(PROVEN).  This is what makes `π` a uniformizer of the completion. -/
theorem intValuation_eq_of_notMem_sq {π : 𝓞 D} (hπ : π ∈ v.asIdeal)
    (hπ2 : π ∉ v.asIdeal ^ 2) : v.intValuation π = exp (-1 : ℤ) := by
  have hπ0 : π ≠ 0 := by rintro rfl; exact hπ2 (Ideal.zero_mem _)
  have hne : v.intValuation π ≠ 0 := v.intValuation_ne_zero π hπ0
  obtain ⟨k, hk⟩ : ∃ k : ℤ, v.intValuation π = exp k := ⟨_, (exp_log hne).symm⟩
  have h1 : v.intValuation π ≤ exp (-((1 : ℕ) : ℤ)) :=
    (v.intValuation_le_pow_iff_mem π 1).mpr (by simpa using hπ)
  have h2 : ¬ (v.intValuation π ≤ exp (-((2 : ℕ) : ℤ))) := fun h =>
    hπ2 ((v.intValuation_le_pow_iff_mem π 2).mp h)
  rw [hk] at h1 h2 ⊢
  rw [exp_le_exp] at h1
  simp only [exp_le_exp, not_le] at h2
  congr 1
  push_cast at h1 h2
  omega

/-- **The comparison `𝒪_D / Iⁿ → 𝒪_v / (π)ⁿ` is injective** (PROVEN) —
the third pin of `exists_adicCoefficientRing`. -/
theorem mem_span_uniformizer_pow_iff (π : 𝓞 D) (hπ : π ∈ v.asIdeal)
    (hπ2 : π ∉ v.asIdeal ^ 2) (n : ℕ) (a : 𝓞 D) :
    algebraMap (𝓞 D) (v.adicCompletionIntegers D) a ∈
        Ideal.span {algebraMap (𝓞 D) (v.adicCompletionIntegers D) π} ^ n ↔
      a ∈ v.asIdeal ^ n := by
  have hv := HeightOneSpectrum.adicCompletionIntegers.integers (K := D) v
  rw [Ideal.span_singleton_pow, ← SetLike.mem_coe,
    hv.coe_span_singleton_eq_setOf_le_v_algebraMap]
  simp only [Set.mem_setOf_eq, map_pow]
  rw [valued_algebraMap_adicCompletionIntegers, valued_algebraMap_adicCompletionIntegers,
    intValuation_eq_of_notMem_sq v hπ hπ2, ← WithZero.exp_nsmul]
  simp only [nsmul_eq_mul, mul_neg, mul_one]
  rw [← v.intValuation_le_pow_iff_mem a n]

open Valuation MonoidWithZeroHom.ValueGroup₀ in
/-- Balls around a point of the completion are neighbourhoods of it
(PROVEN).  This repackages `Valued.mem_nhds`, whose statement is in
terms of the abstract `ValueGroup₀`, as a statement about `ℤᵐ⁰`; the
translation uses surjectivity of the valuation of the completion. -/
theorem mem_nhds_valued_adicCompletion {z : v.adicCompletion D}
    {γ : WithZero (Multiplicative ℤ)} (hγ : γ ≠ 0) :
    {y : v.adicCompletion D | Valued.v (y - z) < γ} ∈ nhds z := by
  obtain ⟨y₀, hy₀⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective D v γ
  have hg : (Valued.v :
      Valuation (v.adicCompletion D) (WithZero (Multiplicative ℤ))).restrict y₀ ≠ 0 := by
    simp only [ne_eq, Valuation.restrict_eq_zero_iff, hy₀]
    exact hγ
  rw [Valued.mem_nhds]
  refine ⟨Units.mk0 _ hg, fun y hy => ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0] at hy ⊢
  rwa [Valuation.restrict_lt_iff_lt_embedding, embedding_restrict, hy₀] at hy

open Valuation MonoidWithZeroHom.ValueGroup₀ in
/-- Every neighbourhood of `0` in the completion contains a ball
(PROVEN); the converse translation to `mem_nhds_valued_adicCompletion`. -/
theorem exists_ball_subset_of_mem_nhds_zero_adicCompletion
    {s : Set (v.adicCompletion D)} (hs : s ∈ nhds (0 : v.adicCompletion D)) :
    ∃ γ : WithZero (Multiplicative ℤ), γ ≠ 0 ∧
      {x : v.adicCompletion D | Valued.v x < γ} ⊆ s := by
  rw [Valued.mem_nhds_zero] at hs
  obtain ⟨γ, hγ⟩ := hs
  refine ⟨embedding γ.1, embedding_unit_ne_zero γ, fun x hx => hγ ?_⟩
  simpa only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding] using hx

/-- **`𝒪_D` is dense in its `I`-adic completion** (PROVEN) — the second
pin of `exists_adicCoefficientRing`. -/
theorem exists_sub_mem_span_uniformizer_pow (π : 𝓞 D) (hπ : π ∈ v.asIdeal)
    (hπ2 : π ∉ v.asIdeal ^ 2) (n : ℕ) (z : v.adicCompletionIntegers D) :
    ∃ a : 𝓞 D, z - algebraMap (𝓞 D) (v.adicCompletionIntegers D) a ∈
      Ideal.span {algebraMap (𝓞 D) (v.adicCompletionIntegers D) π} ^ n := by
  have hv := HeightOneSpectrum.adicCompletionIntegers.integers (K := D) v
  set γ : WithZero (Multiplicative ℤ) := exp (-(n : ℤ)) with hγdef
  have hγ : γ ≠ 0 := exp_ne_zero
  -- an element of `D` close to `z`
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap (K := D) (v := v)).mem_nhds
    (mem_nhds_valued_adicCompletion v (z := (z : v.adicCompletion D)) hγ)
  have coe_sub : ∀ x y : D, ((x - y : D) : v.adicCompletion D)
      = (x : v.adicCompletion D) - (y : v.adicCompletion D) := fun x y => by
    have h := map_sub (algebraMap D (v.adicCompletion D)) x y
    simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply] using h
  rw [Set.mem_setOf_eq, HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
    Algebra.algebraMap_self, RingHom.id_apply] at hk
  -- `k` lies in the valuation ring of `D`
  have hz1 : Valued.v (z : v.adicCompletion D) ≤ 1 := z.2
  have hγ1 : γ ≤ (1 : WithZero (Multiplicative ℤ)) := by
    have h1 : (1 : WithZero (Multiplicative ℤ)) = exp (0 : ℤ) := rfl
    rw [hγdef, h1, exp_le_exp]
    exact neg_nonpos.mpr (Int.natCast_nonneg n)
  have hk1 : v.valuation D k ≤ 1 := by
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) k]
    calc Valued.v ((k : v.adicCompletion D))
        = Valued.v (((k : v.adicCompletion D) - (z : v.adicCompletion D))
            + (z : v.adicCompletion D)) := by ring_nf
      _ ≤ max (Valued.v ((k : v.adicCompletion D) - (z : v.adicCompletion D)))
            (Valued.v (z : v.adicCompletion D)) := Valuation.map_add _ _ _
      _ ≤ 1 := max_le (le_trans hk.le hγ1) hz1
  obtain ⟨a, ha⟩ := HeightOneSpectrum.exists_valuation_sub_lt_of_integer v hk1 (Units.mk0 γ hγ)
  rw [Units.val_mk0, ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v),
    coe_sub] at ha
  refine ⟨a, ?_⟩
  rw [← SetLike.mem_coe, Ideal.span_singleton_pow,
    hv.coe_span_singleton_eq_setOf_le_v_algebraMap]
  simp only [Set.mem_setOf_eq, map_pow, map_sub]
  rw [valued_algebraMap_adicCompletionIntegers, intValuation_eq_of_notMem_sq v hπ hπ2,
    ← WithZero.exp_nsmul]
  simp only [nsmul_eq_mul, mul_neg, mul_one]
  rw [← hγdef]
  have hja : algebraMap (v.adicCompletionIntegers D) (v.adicCompletion D)
      (algebraMap (𝓞 D) (v.adicCompletionIntegers D) a)
      = ((algebraMap (𝓞 D) D a : D) : v.adicCompletion D) := rfl
  rw [hja]
  refine le_trans ?_ (le_of_lt (max_lt hk ha))
  calc Valued.v ((z : v.adicCompletion D) - ((algebraMap (𝓞 D) D a : D) : v.adicCompletion D))
      = Valued.v (-(((k : v.adicCompletion D) - (z : v.adicCompletion D))
          + (((algebraMap (𝓞 D) D a : D) : v.adicCompletion D)
            - (k : v.adicCompletion D)))) := by ring_nf
    _ ≤ max (Valued.v ((k : v.adicCompletion D) - (z : v.adicCompletion D)))
        (Valued.v (((algebraMap (𝓞 D) D a : D) : v.adicCompletion D)
          - (k : v.adicCompletion D))) := by
        rw [Valuation.map_neg]; exact Valuation.map_add _ _ _

/-- The `n`-th power of the uniformizer ideal is the closed ball of
radius `exp (-n)` (PROVEN). -/
theorem coe_span_uniformizer_pow (π : 𝓞 D) (hπ : π ∈ v.asIdeal) (hπ2 : π ∉ v.asIdeal ^ 2)
    (n : ℕ) :
    ((Ideal.span {algebraMap (𝓞 D) (v.adicCompletionIntegers D) π} ^ n :
        Ideal (v.adicCompletionIntegers D)) : Set (v.adicCompletionIntegers D))
      = {y : v.adicCompletionIntegers D |
          Valued.v (y : v.adicCompletion D) ≤ exp (-(n : ℤ))} := by
  have hv := HeightOneSpectrum.adicCompletionIntegers.integers (K := D) v
  rw [Ideal.span_singleton_pow, hv.coe_span_singleton_eq_setOf_le_v_algebraMap]
  ext y
  simp only [Set.mem_setOf_eq, map_pow]
  rw [valued_algebraMap_adicCompletionIntegers, intValuation_eq_of_notMem_sq v hπ hπ2,
    ← WithZero.exp_nsmul]
  simp

/-- Closed balls in the completion are open (PROVEN); the valuation is
nonarchimedean, so a closed ball is a union of open ones. -/
theorem isOpen_valued_le_adicCompletion (γ : WithZero (Multiplicative ℤ)) (hγ : γ ≠ 0) :
    IsOpen {x : v.adicCompletion D | Valued.v x ≤ γ} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  refine Filter.mem_of_superset (mem_nhds_valued_adicCompletion v (z := x) hγ) (fun y hy => ?_)
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  calc Valued.v y = Valued.v ((y - x) + x) := by ring_nf
    _ ≤ max (Valued.v (y - x)) (Valued.v x) := Valuation.map_add _ _ _
    _ ≤ γ := max_le hy.le hx

/-- **The topology of `𝒪_v` is the `(π)`-adic one** (PROVEN). -/
theorem isAdic_span_uniformizer (π : 𝓞 D) (hπ : π ∈ v.asIdeal) (hπ2 : π ∉ v.asIdeal ^ 2) :
    IsAdic (Ideal.span {algebraMap (𝓞 D) (v.adicCompletionIntegers D) π}) := by
  rw [isAdic_iff]
  refine ⟨fun n => ?_, fun s hs => ?_⟩
  · rw [coe_span_uniformizer_pow v π hπ hπ2 n]
    exact (isOpen_valued_le_adicCompletion v _ exp_ne_zero).preimage continuous_subtype_val
  · rw [mem_nhds_subtype] at hs
    obtain ⟨t, ht, hts⟩ := hs
    obtain ⟨γ, hγ, hγt⟩ := exists_ball_subset_of_mem_nhds_zero_adicCompletion v ht
    obtain ⟨n, hn⟩ := WithZero.exists_exp_neg_natCast_lt hγ
    refine ⟨n, ?_⟩
    rw [coe_span_uniformizer_pow v π hπ hπ2 n]
    exact fun y hy => hts (hγt (lt_of_le_of_lt hy hn))

/-- **`𝒪_v` is `(π)`-adically complete** (PROVEN) — the first pin of
`exists_adicCoefficientRing`.  The completion is a closed subset of the
complete field `D_v`, and its topology is the `(π)`-adic one. -/
theorem isAdicComplete_span_uniformizer (π : 𝓞 D) (hπ : π ∈ v.asIdeal)
    (hπ2 : π ∉ v.asIdeal ^ 2) :
    IsAdicComplete (Ideal.span {algebraMap (𝓞 D) (v.adicCompletionIntegers D) π})
      (v.adicCompletionIntegers D) :=
  (IsAdic.isAdicComplete_iff (isAdic_span_uniformizer v π hπ hπ2)).mpr
    ⟨(Valued.isClosed_valuationSubring (Γ₀ := WithZero (Multiplicative ℤ))
      (v.adicCompletion D)).completeSpace_coe, inferInstance⟩

/-- **`𝒪ᵥ` is `q`-adically complete**, `q` the residue characteristic
(PROVEN).  As ideals of `𝒪ᵥ`, `(q) = (π)ᵉ` with `e ≥ 1` the ramification
index, so this follows from `isAdic_span_uniformizer` through
`is_ideal_adic_pow`.  It is what gives `𝒪ᵥ` its `ℤ_q`-algebra structure
below. -/
theorem isAdicComplete_span_natCast (q : ℕ) [Fact q.Prime] (hqv : (q : 𝓞 D) ∈ v.asIdeal) :
    IsAdicComplete (Ideal.span {(q : v.adicCompletionIntegers D)})
      (v.adicCompletionIntegers D) := by
  obtain ⟨π, hπ, hπ2⟩ : ∃ π : 𝓞 D, π ∈ v.asIdeal ∧ π ∉ v.asIdeal ^ 2 := by
    obtain ⟨π, hπ, hπ2⟩ :=
      Ideal.exists_mem_pow_notMem_pow_succ v.asIdeal v.ne_bot v.isPrime.ne_top 1
    exact ⟨π, by simpa using hπ, by simpa using hπ2⟩
  -- the ramification index `e`, read off the valuation of `q`
  have hq0 : (q : 𝓞 D) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  have hqne : v.intValuation (q : 𝓞 D) ≠ 0 := v.intValuation_ne_zero _ hq0
  obtain ⟨k, hk⟩ : ∃ k : ℤ, v.intValuation (q : 𝓞 D) = exp k := ⟨_, (exp_log hqne).symm⟩
  have hk1 : k ≤ -1 := by
    have h := (v.intValuation_le_pow_iff_mem (q : 𝓞 D) 1).mpr (by simpa using hqv)
    rw [hk, exp_le_exp] at h
    push_cast at h
    omega
  obtain ⟨e, he, he0⟩ : ∃ e : ℕ, k = -(e : ℤ) ∧ 0 < e :=
    ⟨(-k).toNat, by omega, by omega⟩
  -- as ideals of `𝒪ᵥ`, `(q) = (π)ᵉ`
  have hIdeal : Ideal.span {(q : v.adicCompletionIntegers D)}
      = Ideal.span {algebraMap (𝓞 D) (v.adicCompletionIntegers D) π} ^ e := by
    apply SetLike.coe_injective
    rw [coe_span_uniformizer_pow v π hπ hπ2 e]
    have hv := HeightOneSpectrum.adicCompletionIntegers.integers (K := D) v
    have hcast : (q : v.adicCompletionIntegers D)
        = algebraMap (𝓞 D) (v.adicCompletionIntegers D) (q : 𝓞 D) := by
      simp
    rw [hcast, hv.coe_span_singleton_eq_setOf_le_v_algebraMap,
      valued_algebraMap_adicCompletionIntegers, hk, he]
    rfl
  rw [hIdeal]
  exact (IsAdic.isAdicComplete_iff
      (is_ideal_adic_pow (isAdic_span_uniformizer v π hπ hπ2) he0)).mpr
    ⟨(Valued.isClosed_valuationSubring (Γ₀ := WithZero (Multiplicative ℤ))
      (v.adicCompletion D)).completeSpace_coe, inferInstance⟩

/-- **The `ℤ_q`-algebra structure on `𝒪ᵥ`** — the unique one continuous
for the valuation topology, obtained by `padicIntLiftHom` from
`q`-adic completeness.  This PINS the algebra structure that
`exists_adicCoefficientRing` produces; without it the leaf would admit
any `ℤ_q`-structure whatever. -/
@[implicit_reducible]
noncomputable def padicIntAlgebra (q : ℕ) [Fact q.Prime] (hqv : (q : 𝓞 D) ∈ v.asIdeal) :
    Algebra ℤ_[q] (v.adicCompletionIntegers D) :=
  letI := isAdicComplete_span_natCast v q hqv
  (padicIntLiftHom : ℤ_[q] →+* v.adicCompletionIntegers D).toAlgebra

/-- **As ideals of `𝒪ᵥ`, `(q) = (π)ᵉ`** (PROVEN), with `e ≥ 1` the
ramification index of `v` over the rational prime `q`, read off the
`v`-adic valuation of `q`.  This is the computation inside
`isAdicComplete_span_natCast` above, isolated so that the `q`-adic and
the `π`-adic filtrations of `𝒪ᵥ` can be compared cofinally. -/
theorem exists_span_natCast_eq_span_uniformizer_pow (q : ℕ) [Fact q.Prime]
    (hqv : (q : 𝓞 D) ∈ v.asIdeal) (π : 𝓞 D) (hπ : π ∈ v.asIdeal) (hπ2 : π ∉ v.asIdeal ^ 2) :
    ∃ e : ℕ, 0 < e ∧ Ideal.span {(q : v.adicCompletionIntegers D)}
      = Ideal.span {algebraMap (𝓞 D) (v.adicCompletionIntegers D) π} ^ e := by
  have hq0 : (q : 𝓞 D) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  have hqne : v.intValuation (q : 𝓞 D) ≠ 0 := v.intValuation_ne_zero _ hq0
  obtain ⟨k, hk⟩ : ∃ k : ℤ, v.intValuation (q : 𝓞 D) = exp k := ⟨_, (exp_log hqne).symm⟩
  have hk1 : k ≤ -1 := by
    have h := (v.intValuation_le_pow_iff_mem (q : 𝓞 D) 1).mpr (by simpa using hqv)
    rw [hk, exp_le_exp] at h
    push_cast at h
    omega
  obtain ⟨e, he, he0⟩ : ∃ e : ℕ, k = -(e : ℤ) ∧ 0 < e :=
    ⟨(-k).toNat, by omega, by omega⟩
  refine ⟨e, he0, ?_⟩
  apply SetLike.coe_injective
  rw [coe_span_uniformizer_pow v π hπ hπ2 e]
  have hv := HeightOneSpectrum.adicCompletionIntegers.integers (K := D) v
  have hcast : (q : v.adicCompletionIntegers D)
      = algebraMap (𝓞 D) (v.adicCompletionIntegers D) (q : 𝓞 D) := by
    simp
  rw [hcast, hv.coe_span_singleton_eq_setOf_le_v_algebraMap,
    valued_algebraMap_adicCompletionIntegers, hk, he]
  rfl

/-- **The topology of `𝒪ᵥ` is the `q`-adic one** (PROVEN), `q` the
residue characteristic — the `q`-adic form of `isAdic_span_uniformizer`,
obtained from it through `(q) = (π)ᵉ`. -/
theorem isAdic_span_natCast (q : ℕ) [Fact q.Prime] (hqv : (q : 𝓞 D) ∈ v.asIdeal) :
    IsAdic (Ideal.span {(q : v.adicCompletionIntegers D)}) := by
  obtain ⟨π, hπ, hπ2⟩ : ∃ π : 𝓞 D, π ∈ v.asIdeal ∧ π ∉ v.asIdeal ^ 2 := by
    obtain ⟨π, hπ, hπ2⟩ :=
      Ideal.exists_mem_pow_notMem_pow_succ v.asIdeal v.ne_bot v.isPrime.ne_top 1
    exact ⟨π, by simpa using hπ, by simpa using hπ2⟩
  obtain ⟨e, he0, hIdeal⟩ := exists_span_natCast_eq_span_uniformizer_pow v q hqv π hπ hπ2
  rw [hIdeal]
  exact is_ideal_adic_pow (isAdic_span_uniformizer v π hπ hπ2) he0

/-- **The residue characteristic is nonzero in `𝒪ᵥ`** (PROVEN): `𝒪_D`
embeds into `𝒪ᵥ` and has characteristic zero. -/
theorem natCast_ne_zero_adicCompletionIntegers (q : ℕ) [Fact q.Prime] :
    (q : v.adicCompletionIntegers D) ≠ 0 := by
  have hinj : Function.Injective (algebraMap (𝓞 D) (v.adicCompletionIntegers D)) :=
    FaithfulSMul.algebraMap_injective _ _
  intro h
  have h2 : algebraMap (𝓞 D) (v.adicCompletionIntegers D) ((q : ℕ) : 𝓞 D)
      = algebraMap (𝓞 D) (v.adicCompletionIntegers D) 0 := by
    rw [map_natCast, map_zero]
    exact h
  have h3 : ((q : ℕ) : 𝓞 D) = 0 := hinj h2
  exact (Fact.out : q.Prime).ne_zero (by exact_mod_cast h3)

/-- **A `q`-adically complete domain with a dense finitely generated
`ℤ`-submodule is finite free over `ℤ_q` and carries the module
topology** (PROVEN).  This is the whole commutative-algebra content of
`module_finite_free_moduleTopology_padicIntAlgebra` below, stated for an
arbitrary target so that nothing about adic completions of number fields
enters it.

Given a topological domain `O` whose topology is the `(q)`-adic one, a
ring map `F : ℤ_q →+* O` (in practice `padicIntLiftHom`), and finitely
many elements `g i` whose `ℤ`-combinations approximate every element of
`O` to arbitrary `(q)`-adic precision, the map

  `f : ℤ_q^ι → O`,  `c ↦ ∑ i, c i • g i`

is continuous with COMPACT source (`ℤ_q` is compact) and Hausdorff
target, so its range is closed; the approximation hypothesis makes that
range dense; hence `f` is surjective.  Three conclusions follow at once:

* `Module.Finite`, since `O` is the image of the finite free `ℤ_q^ι`;
* `Module.Free`, because `ℤ_q` is a principal ideal domain and `O` is
  torsion-free over it (`F` is injective: a nonzero `x : ℤ_q` is a unit
  times `q^n`, and `q ≠ 0` in the domain `O`);
* `IsModuleTopology`, because a continuous surjection from a compact
  space onto a Hausdorff one is a closed map, hence a quotient map, and
  the module topology on `O` is exactly the topology coinduced by `f`
  from the module topology of `ℤ_q^ι`.

This is complete Nakayama replaced by a compactness argument: no
successive-approximation series is constructed anywhere, which is what
makes the proof short.  It needs no functoriality of adic completions,
and so avoids the base-change development that mathlib lacks. -/
theorem finite_free_moduleTopology_of_approx
    {O : Type*} [CommRing O] [IsDomain O] [TopologicalSpace O] [IsTopologicalRing O] [T2Space O]
    {q : ℕ} [Fact q.Prime] (F : ℤ_[q] →+* O)
    (hadic : IsAdic (Ideal.span {(q : O)}))
    (hq0 : (q : O) ≠ 0)
    {ι : Type*} [Fintype ι] (g : ι → O)
    (happrox : ∀ (z : O) (n : ℕ), ∃ c : ι → ℤ,
        z - ∑ i, (c i : O) * g i ∈ Ideal.span {(q : O)} ^ n) :
    letI := F.toAlgebra
    Module.Finite ℤ_[q] O ∧ Module.Free ℤ_[q] O ∧ IsModuleTopology ℤ_[q] O := by
  letI := F.toAlgebra
  have halg : (algebraMap ℤ_[q] O) = F := rfl
  -- `F` carries `(q^n)` into `(q)^n`
  have hkey : ∀ (n : ℕ) (x : ℤ_[q]), x ∈ Ideal.span {(q : ℤ_[q]) ^ n} →
      F x ∈ Ideal.span {(q : O)} ^ n := by
    intro n x hx
    rw [Ideal.mem_span_singleton] at hx
    obtain ⟨y, rfl⟩ := hx
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact ⟨F y, by rw [map_mul, map_pow, map_natCast]⟩
  -- `F` is continuous: it is additive and carries a basis of neighbourhoods of `0` in
  -- `ℤ_q` into one in `O`
  have hFcont : Continuous F := by
    refine continuous_of_continuousAt_zero F ?_
    simp only [ContinuousAt, map_zero]
    rw [Filter.tendsto_def]
    intro s hs
    obtain ⟨n, hn⟩ := (isAdic_iff.mp hadic).2 s hs
    have hqpos : (0 : ℝ) < (q : ℝ) := by
      exact_mod_cast (Fact.out : q.Prime).pos
    have hpos : (0 : ℝ) < (q : ℝ) ^ (-n : ℤ) := zpow_pos hqpos _
    refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : ℤ_[q]) hpos) ?_
    intro x hx
    rw [Metric.mem_ball, dist_zero_right] at hx
    exact hn (hkey n x ((PadicInt.norm_le_pow_iff_mem_span_pow x n).mp hx.le))
  haveI : ContinuousSMul ℤ_[q] O := by
    constructor
    have h : (fun p : ℤ_[q] × O => p.1 • p.2) = fun p : ℤ_[q] × O => F p.1 * p.2 := by
      funext p
      rw [Algebra.smul_def, halg]
    rw [h]
    exact (hFcont.comp continuous_fst).mul continuous_snd
  -- the finite-rank approximating map
  set f : (ι → ℤ_[q]) →ₗ[ℤ_[q]] O := Fintype.linearCombination ℤ_[q] g
  have hfapp : ⇑f = fun c : ι → ℤ_[q] => ∑ i, c i • g i := rfl
  have hfcont : Continuous f := by
    rw [hfapp]
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
  have hdense : Dense (Set.range ⇑f) := by
    intro z
    rw [mem_closure_iff_nhds]
    intro t ht
    have h0 : (fun y : O => y + z) ⁻¹' t ∈ nhds (0 : O) := by
      refine (continuous_add_const z).continuousAt.preimage_mem_nhds ?_
      simpa using ht
    obtain ⟨n, hn⟩ := (isAdic_iff.mp hadic).2 _ h0
    obtain ⟨c, hc⟩ := happrox z n
    refine ⟨∑ i, (c i : O) * g i, ?_, ⟨fun i => ((c i : ℤ) : ℤ_[q]), ?_⟩⟩
    · have hmem := hn (neg_mem hc)
      simp only [Set.mem_preimage, neg_sub] at hmem
      simpa using hmem
    · rw [hfapp]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, halg, map_intCast]
  haveI : CompactSpace (ι → ℤ_[q]) := inferInstance
  have hcl : IsClosed (Set.range ⇑f) := (isCompact_range hfcont).isClosed
  have hrange : Set.range ⇑f = Set.univ := by rw [← hcl.closure_eq, hdense.closure_eq]
  have hsurj : Function.Surjective ⇑f := Set.range_eq_univ.mp hrange
  haveI hfin : Module.Finite ℤ_[q] O := Module.Finite.of_surjective f hsurj
  -- `F` is injective, so `O` is torsion-free over `ℤ_q`, hence free (a PID)
  have hinj : Function.Injective F := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    rw [PadicInt.unitCoeff_spec hx0, map_mul, map_pow, map_natCast] at hx
    rcases mul_eq_zero.mp hx with h | h
    · exact ((PadicInt.unitCoeff hx0).isUnit.map F).ne_zero h
    · rcases Nat.eq_zero_or_pos (PadicInt.valuation x) with h0 | h0
      · rw [h0, pow_zero] at h
        exact one_ne_zero h
      · exact hq0 ((pow_eq_zero_iff h0.ne').mp h)
  haveI : Module.IsTorsionFree ℤ_[q] O := by
    refine Module.IsTorsionFree.comap (S := O) (M := O) (fun r => F r) ?_ ?_
    · intro r hr
      rw [isRegular_iff_ne_zero] at hr ⊢
      intro hcon
      exact hr (hinj (by rw [hcon, map_zero]))
    · intro r m
      rw [smul_eq_mul, Algebra.smul_def, halg]
  haveI hfree : Module.Free ℤ_[q] O := inferInstance
  -- the module topology: `f` is a continuous surjection from a compact space onto a
  -- Hausdorff one, hence a quotient map, and the module topology on `O` is exactly the
  -- topology coinduced by `f` from the module topology of `ℤ_q^ι`
  have hquot : Topology.IsQuotientMap ⇑f := hfcont.isClosedMap.isQuotientMap hfcont hsurj
  refine ⟨hfin, hfree, ⟨?_⟩⟩
  rw [ModuleTopology.eq_coinduced_of_surjective (φ := f) hsurj]
  exact hquot.eq_coinduced

/-- **`𝒪_v` is finite and free over `ℤ_q`, with the module topology**
(PROVEN 2026-07-26; commutative algebra, Serre *Local Fields* II,
Neukirch II.4).

For `v` a height-one point of `𝒪_D` lying over the rational prime `q`,
the completion `𝒪_v` is finite and free over `ℤ_q` of rank `e·f`, and
its valuation topology is the `ℤ_q`-module topology.  The `ℤ_q`-algebra
structure is not part of the burden — it is `padicIntAlgebra` above,
PROVEN; and neither are the three pin conjuncts of
`exists_adicCoefficientRing`.  This is all that leaf still needs.

WHAT WAS MISSING UPSTREAM, and how it is avoided.  Mathlib has `𝒪_v`
with its ring, topology, locality and discrete-valuation structure, and
(in `Mathlib/NumberTheory/NumberField/Completion/FinitePlace.lean`) even
`Module.Finite Kᵥ L_w` for completions of a finite extension — but that
instance takes `Algebra Kᵥ L_w` as a HYPOTHESIS.  There is no
functoriality of adic completions along a finite extension in mathlib:
no `Algebra (v.adicCompletion K) (w.adicCompletion L)`, hence no
`Module.Finite` / `Module.Free` / `IsModuleTopology` for the integers
either.  Vendoring that base change from
`~/cs/FLT/FLT/DedekindDomain/Completion/BaseChange.lean` (across a pin
drift) was the obvious route and is NOT the one taken.

HOW IT IS PROVEN (2026-07-26), with no base change and no series.  All
of the work is in `finite_free_moduleTopology_of_approx` above, which is
stated for an arbitrary `q`-adically topologised topological domain.
The three inputs supplied here are:

* `isAdic_span_natCast` — the topology of `𝒪_v` is the `(q)`-adic one,
  which is `isAdic_span_uniformizer` transported along `(q) = (π)ᵉ`
  (`exists_span_natCast_eq_span_uniformizer_pow`);
* `natCast_ne_zero_adicCompletionIntegers` — `q ≠ 0` in `𝒪_v`;
* the approximation hypothesis, which is
  `exists_sub_mem_span_uniformizer_pow` (density of `𝒪_D` in `𝒪_v`)
  read at precision `e·n` and expanded in a `ℤ`-basis of `𝒪_D`.

The engine then runs `ℤ_q^ι → 𝒪_v`, `c ↦ ∑ cᵢ · bᵢ`, over a `ℤ`-basis
`b` of `𝒪_D`: it is continuous, its source is COMPACT because `ℤ_q` is,
so its range is closed, and the approximation makes that range dense —
hence it is surjective.  Finiteness is immediate; freeness follows since
`ℤ_q` is a PID and `𝒪_v` is torsion-free over it; and the module
topology follows because a continuous surjection from a compact space
onto a Hausdorff one is a quotient map.  Compactness replaces the
complete-Nakayama successive approximation the classical proof uses. -/
theorem module_finite_free_moduleTopology_padicIntAlgebra
    (q : ℕ) [Fact q.Prime] (hqv : (q : 𝓞 D) ∈ v.asIdeal) :
    letI := padicIntAlgebra v q hqv
    Module.Finite ℤ_[q] (v.adicCompletionIntegers D) ∧
      Module.Free ℤ_[q] (v.adicCompletionIntegers D) ∧
      IsModuleTopology ℤ_[q] (v.adicCompletionIntegers D) := by
  letI := isAdicComplete_span_natCast v q hqv
  obtain ⟨π, hπ, hπ2⟩ : ∃ π : 𝓞 D, π ∈ v.asIdeal ∧ π ∉ v.asIdeal ^ 2 := by
    obtain ⟨π, hπ, hπ2⟩ :=
      Ideal.exists_mem_pow_notMem_pow_succ v.asIdeal v.ne_bot v.isPrime.ne_top 1
    exact ⟨π, by simpa using hπ, by simpa using hπ2⟩
  obtain ⟨e, _he0, hIdeal⟩ := exists_span_natCast_eq_span_uniformizer_pow v q hqv π hπ hπ2
  set bD := Module.Free.chooseBasis ℤ (𝓞 D)
  refine finite_free_moduleTopology_of_approx
    (padicIntLiftHom : ℤ_[q] →+* v.adicCompletionIntegers D)
    (isAdic_span_natCast v q hqv) (natCast_ne_zero_adicCompletionIntegers v q)
    (fun i => algebraMap (𝓞 D) (v.adicCompletionIntegers D) (bD i)) ?_
  intro z n
  obtain ⟨a, ha⟩ := exists_sub_mem_span_uniformizer_pow v π hπ hπ2 (e * n) z
  refine ⟨fun i => bD.repr a i, ?_⟩
  have hsum : ∑ i, ((bD.repr a i : ℤ) : v.adicCompletionIntegers D) *
      algebraMap (𝓞 D) (v.adicCompletionIntegers D) (bD i)
      = algebraMap (𝓞 D) (v.adicCompletionIntegers D) a := by
    conv_rhs => rw [← bD.sum_repr a]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_zsmul, zsmul_eq_mul]
  rw [hsum, hIdeal, ← pow_mul]
  exact ha

/-- **`𝒪_v` carries a topological `ℤ_q`-algebra structure that is finite
and free** (PROVEN over `module_finite_free_moduleTopology_padicIntAlgebra`;
the structure produced is the canonical one, `padicIntAlgebra`). -/
theorem exists_padicIntStructure_adicCompletionIntegers
    (q : ℕ) [Fact q.Prime] (hqv : (q : 𝓞 D) ∈ v.asIdeal) :
    ∃ (_ : Algebra ℤ_[q] (v.adicCompletionIntegers D))
      (_ : Module.Finite ℤ_[q] (v.adicCompletionIntegers D))
      (_ : Module.Free ℤ_[q] (v.adicCompletionIntegers D)),
      IsModuleTopology ℤ_[q] (v.adicCompletionIntegers D) := by
  obtain ⟨hfin, hfree, hmt⟩ := module_finite_free_moduleTopology_padicIntAlgebra v q hqv
  exact ⟨padicIntAlgebra v q hqv, hfin, hfree, hmt⟩

end AdicCompletionIntegers

/-! ### The three leaves of the Tate-module frame

`exists_tateFrame_of_levelStructure` is assembled below out of three
statements that belong to three different theories and can be attacked
independently:

* `exists_adicCoefficientRing` — COMMUTATIVE ALGEBRA. The completion
  `𝒪_{D,I}` exists as a topological `ℤ_q`-algebra: local, finite free
  over `ℤ_q`, carrying the module topology, and pinned to be the
  `I`-adic completion of `𝒪_D` by the three conditions
  `IsAdicComplete`, `π`-adic surjectivity of `j`, and
  `j a ∈ (π)ⁿ ↔ a ∈ Iⁿ`. Nothing geometric appears. **PROVEN
  2026-07-26** in the subsection above, unconditionally: its last leaf
  `module_finite_free_moduleTopology_padicIntAlgebra` was closed the
  same day.
* `exists_tateFrame_of_adicCoefficientRing` — ABELIAN VARIETIES. The
  Tate module `TatePt m x I π` is free of rank two over that ring, with
  a continuous Galois action extending the real multiplication. This is
  Mumford §18 / Silverman *AEC* III.7 plus the Hilbert–Blumenthal
  normalization of Taylor 2002 §2. **PROVEN 2026-07-26** over three
  sub-leaves of its own — `exists_levelwiseTateFrame`,
  `isOpen_stabilizer_torsion` and
  `exists_galoisRep_of_isOpen_congruence` — after its statement was
  refuted and repaired; see the FAITHFULNESS AUDIT in its docstring for
  the counterexample (an arbitrary topology on `O` makes the continuity
  demanded by `GaloisRep` unsatisfiable) and for the four `ℤ_q` binders
  that repair it.
* `exists_residualEmbedding_of_tateFrame` — REPRESENTATION THEORY. Given
  a frame, the reduction of `τ` modulo the maximal ideal is isomorphic
  to `ρ'` after an automorphism of the residue field, so the Frobenius
  characteristic polynomials match. **This is the only leaf that uses
  `hirr`**, and it is exactly the step whose unconditional form was
  refuted (see the FAITHFULNESS AUDIT below): the commutant must be
  simple before Noether–Skolem is available.

The uniformizer `π` itself is not part of any of them — it is produced
by `exists_mem_notMem_sq_of_isMaximal` above and handed to all three. -/

/-- **The `I`-adic completion of `𝒪_D` exists as a topological
`ℤ_q`-algebra** (PROVEN 2026-07-26 over the single leaf
`exists_padicIntStructure_adicCompletionIntegers`; commutative algebra,
Serre *Local Fields* II, Neukirch II.4).

For `I` a maximal ideal of `𝒪_D` containing the rational prime `q` and
`π ∈ I ∖ I²`, the completion `O = 𝒪_{D,I}` is a complete discrete
valuation ring with uniformizer `π`, finite free over `ℤ_q` of rank
`e·f`, and its topology is the `ℤ_q`-module topology.

The last three conjuncts PIN `O`: they say that `O` is `π`-adically
complete, that `𝒪_D` is dense in it, and that the comparison
`𝒪_D / Iⁿ → O / (π)ⁿ` is injective. Together with completeness these
force `𝒪_D / Iⁿ ≅ O / (π)ⁿ` for every `n`, which characterizes `O` as
the `I`-adic completion — without them the statement would be satisfied
by `ℤ_q` itself whenever `I` has residue degree one, and the consumer
`exists_tateFrame_of_adicCoefficientRing` would be FALSE.

HOW IT IS PROVEN (2026-07-26).  `O` is mathlib's
`v.adicCompletionIntegers D` at the height-one point `v = ⟨I, …⟩` and
`j` is its structure map.  The three pin conjuncts are
`isAdicComplete_span_uniformizer`, `exists_sub_mem_span_uniformizer_pow`
and `mem_span_uniformizer_pow_iff` above, all PROVEN, as is the
`ℤ_q`-algebra structure (`padicIntAlgebra`, built from the general
`padicIntLiftHom`).  `Module.Finite`, `Module.Free` and
`IsModuleTopology` over `ℤ_q` — which mathlib does not have, because it
has no functoriality of adic completions along a finite extension — are
`module_finite_free_moduleTopology_padicIntAlgebra`, PROVEN 2026-07-26
from `finite_free_moduleTopology_of_approx`: the vendoring of the
base-change development from `~/cs/FLT` proved unnecessary, since the
compactness of `ℤ_q` closes all three conjuncts at once.  So this leaf
is now unconditional.

Note that the statement does NOT tie the `ℤ_q`-structure to `j`: the
`Algebra ℤ_[q] O` conjunct and the three pin conjuncts are logically
independent halves of this leaf.  That is how it was stated by the
author of the cut and is preserved here; a consumer that needs
`ℤ_q → 𝒪_D → O` to commute must ask for it.  As it happens the witness
supplied here DOES make them commute — `padicIntAlgebra` is the unique
continuous `ℤ_q`-structure — but that is not recorded in the statement,
so no consumer may rely on it without a restatement. -/
theorem exists_adicCoefficientRing
    {D : Type u} [Field D] [NumberField D]
    (q : ℕ) [Fact q.Prime]
    (I : Ideal (NumberField.RingOfIntegers D)) (hI : I.IsMaximal)
    (hqI : (q : NumberField.RingOfIntegers D) ∈ I)
    (π : NumberField.RingOfIntegers D) (hπ : π ∈ I) (hπ2 : π ∉ I ^ 2) :
    ∃ (O : Type u) (_ : CommRing O) (_ : TopologicalSpace O) (_ : IsTopologicalRing O)
      (_ : Algebra ℤ_[q] O) (_ : IsLocalRing O) (_ : Module.Finite ℤ_[q] O)
      (_ : Module.Free ℤ_[q] O) (_ : IsModuleTopology ℤ_[q] O)
      (j : NumberField.RingOfIntegers D →+* O),
      IsAdicComplete (Ideal.span {j π}) O ∧
      (∀ (n : ℕ) (z : O), ∃ a : NumberField.RingOfIntegers D,
        z - j a ∈ Ideal.span {j π} ^ n) ∧
      (∀ (n : ℕ) (a : NumberField.RingOfIntegers D),
        j a ∈ Ideal.span {j π} ^ n ↔ a ∈ I ^ n) := by
  -- `I` is nonzero: it contains the rational prime `q`.
  have hI0 : I ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot, Nat.cast_eq_zero] at hqI
    exact (Fact.out : q.Prime).ne_zero hqI
  let v : HeightOneSpectrum (NumberField.RingOfIntegers D) := ⟨I, hI.isPrime, hI0⟩
  obtain ⟨iAlg, iFin, iFree, iMT⟩ :=
    exists_padicIntStructure_adicCompletionIntegers v q (hqv := hqI)
  exact ⟨(v.adicCompletionIntegers D), inferInstance, inferInstance, inferInstance,
    iAlg, inferInstance, iFin, iFree, iMT,
    algebraMap (NumberField.RingOfIntegers D) (v.adicCompletionIntegers D),
    isAdicComplete_span_uniformizer v π hπ hπ2,
    exists_sub_mem_span_uniformizer_pow v π hπ hπ2,
    mem_span_uniformizer_pow_iff v π hπ hπ2⟩

/-! ### The three sub-leaves of `exists_tateFrame_of_adicCoefficientRing`

The abelian-varieties leaf of the frame is itself assembled below out of
three statements belonging to three different theories, so that the
`I`-adic bookkeeping — which is pure commutative algebra over the pin
`hcplt`/`hdense`/`hker` — is separated from the two facts about abelian
varieties that no amount of algebra will supply:

* `exists_levelwiseTateFrame` — ABELIAN VARIETIES. The whole rank
  count lives here, in FINITE-LEVEL form: `A[Iⁿ]` is free of rank two
  over `𝒪_D/Iⁿ`, compatibly in `n` along multiplication by `π`. No
  completion, no topology, no Galois.
* `isOpen_stabilizer_torsion` — ARITHMETIC. The subgroup of `Γ_F`
  fixing `A[J]` pointwise is open, i.e. the `J`-torsion is defined over
  a finite extension of `F`. This is the whole content of *continuity*
  of the resulting representation. **PROVEN 2026-07-26** over the single
  residual leaf `locallyQuasiFinite_mulByNat` (multiplication by a
  nonzero `n` on the abelian scheme has finite fibres); finiteness of
  `A[N]` (`finite_torsion_span_natCast`) is PROVEN from it since
  2026-07-26, and the spreading-out half — that ONE geometric point is
  defined over a finite extension — is itself proven, as
  `exists_fixingSubgroup_le_stabilizer_geomFibrePt`.
* `exists_galoisRep_of_isOpen_congruence` — TOPOLOGY. A homomorphism
  into `End_O(O²)` all of whose congruence subgroups mod `Pⁿ` are open
  is continuous for the module topology. This is where the `ℤ_q`-module
  topology of `O` is compared with the `π`-adic one. **PROVEN
  2026-07-26** over the five commutative-algebra lemmas of the
  `CongruenceTopology` section below, whose joint content is that
  `{Pⁿ}ₙ` is a neighbourhood basis of `0` in `O`.

Everything else — the identification `𝒪_D/Iⁿ ≅ O/(π)ⁿ`, the inverse
limit, bijectivity of the frame, `O`-linearity of the Galois action and
the `j`-compatibility clause — is PROVEN in
`exists_tateFrame_of_adicCoefficientRing` from those three. -/

/-! #### The sub-leaves of `exists_levelwiseTateFrame`

The levelwise frame is itself assembled below, and the assembly is the
inverse-limit bookkeeping: what the geometry has to supply is a frame at
each SINGLE level (`exists_levelTateFrame`) and the ability to lift one
level's frame through multiplication by `π` (`exists_levelTateFrame_succ`),
and the compatible TOWER is then produced here by recursion.

Making that separation is the whole point of the cut. "Free of rank two
at every level" and "free of rank two compatibly in `n`" are genuinely
different statements — the second is a statement about the inverse limit
and is what the parent consumes — and only the first is a textbook fact
about abelian varieties.

**Both single-level statements are now PROVEN** (2026-07-26), and so is
the lifting step. The geometry beneath the levelwise frame is these two
statements, both about abelian varieties and nothing else:

* `exists_nsmul_eq_geomFibrePt` — DIVISIBILITY. It is what discharges
  `exists_mem_torsion_act_uniformizer_eq` (`·π` carries `A[Iⁿ⁺¹]` onto
  `A[Iⁿ]`), which in turn feeds both `exists_levelTateFrame_succ` and
  `exists_levelTateFrame`. No rank, no `hdim`. **PROVEN 2026-07-26** —
  it is NOT a leaf any more, so do not dispatch a prover at it. Its
  geometry was moved to `Modularity/AbelianSchemeIsogeny.lean` and now
  rests on the single leaf
  `flat_locallyOfFinitePresentation_mulByNat` there (`[N]` is flat and
  of finite presentation — the theorem of the cube).
* `card_torsion_of_isMaximal` — the RANK COUNT, in its residual form:
  `#A[I] = (#𝒪_D/I)²`, the degree formula for the isogeny `I`.
  **This is the only consumer of `hdim`**, and it is still open.

Everything between those two and `exists_levelwiseTateFrame` is
commutative algebra proven here — the tower recursion below, and the
single-level algebra collected in the `LevelFrame` namespace. -/

/-- **A level-`J` frame on the `J`-torsion of a geometric fibre**: a
parametrization

  `c : (𝒪_D ⧸ J)² → A[J]`

which is additive, `𝒪_D`-semilinear and bijective onto the `J`-torsion,
i.e. exactly the datum "`A[J]` is free of rank two over `𝒪_D ⧸ J`,
together with a choice of basis".

The five clauses are named once here so that the geometric input
(`exists_levelTateFrame`), the lifting step
(`exists_levelTateFrame_succ`) and the assembled tower
(`exists_levelwiseTateFrame`) can all be stated against the same
predicate; the tower's own statement is kept in unfolded form because it
is what the parent `exists_tateFrame_of_adicCoefficientRing` destructures. -/
def IsLevelTateFrame {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (J : Ideal (NumberField.RingOfIntegers D))
    (c : (Fin 2 → NumberField.RingOfIntegers D ⧸ J) → GeomFibrePt f x) : Prop :=
  (∀ u, c u ∈ (m.torsion x J).1) ∧
  (∀ u v, c (u + v) = ab.add (c u) (c v)) ∧
  Function.Injective c ∧
  (∀ y ∈ (m.torsion x J).1, ∃ u, c u = y) ∧
  (∀ (a : NumberField.RingOfIntegers D)
      (u : Fin 2 → NumberField.RingOfIntegers D ⧸ J),
    c (fun i => Ideal.Quotient.mk J a * u i) = m.act a (c u))

/-- **Membership in the `J`-torsion, unfolded** (PROVEN): a geometric
point of the fibre lies in `A[J]` exactly when every element of `J`
kills it.  This is `Submodule.mem_torsionBySet_iff` read through the
`𝒪_D`-module structure `Mult.module` of `Mult.torsion`. -/
theorem mem_torsion_iff {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] (x : Spec (CommRingCat.of F) ⟶ S)
    (J : Ideal (NumberField.RingOfIntegers D)) (y : GeomFibrePt f x) :
    y ∈ (m.torsion x J).1 ↔
      ∀ a ∈ J, m.act a y = ab.zero (specAlgClos F ≫ x) := by
  letI : AddCommGroup (GeomFibrePt f x) := ab.addCommGroup (specAlgClos F ≫ x)
  letI : Module (NumberField.RingOfIntegers D) (GeomFibrePt f x) :=
    m.module (specAlgClos F ≫ x)
  constructor
  · intro hy a ha
    exact (Submodule.mem_torsionBySet_iff _ _).mp hy ⟨a, ha⟩
  · intro h
    exact (Submodule.mem_torsionBySet_iff _ _).mpr fun a => h a a.2

/-- **An abelian variety is a divisible group: `[N]` is surjective on the
geometric points of a fibre** (PROVEN 2026-07-26 over the single
abelian-variety leaf `flat_locallyOfFinitePresentation_mulByNat` in
`Modularity/AbelianSchemeIsogeny.lean`; Mumford *Abelian Varieties* §6
(Application 2 of the theorem of the cube), Silverman *AEC* III.4.2 and
III.6.4).

For `N ≠ 0` multiplication by `N` on an abelian scheme is an isogeny —
finite, flat and surjective — so over the ALGEBRAICALLY CLOSED field `F̄`
it is surjective on points. Properness, smoothness and geometric
connectedness of `f`, which is exactly what makes each geometric fibre
an abelian variety, are carried by `ab`; nothing else is used.

The statement is deliberately written with the bare `ℕ`-action of the
group structure `ab.addCommGroup`, so that it mentions only `ab`: no
real multiplication, no rank count, no coefficient ring. It is the
classical divisibility statement and nothing more. Its only consumer,
`exists_mem_torsion_act_uniformizer_eq` below, converts it into
divisibility by a nonzero element of `𝒪_D` through the absolute norm.

## FAITHFULNESS: CONFIRMED TRUE (2026-07-26, audited by a later owner)

The statement is faithful, and in particular there is no counterexample
to hunt for.  Three checks:

* `GeomFibrePt f x` is `RelPoint f (specAlgClos F ≫ x)`, i.e. the
  `F̄`-points of `A ×_S Spec F̄`.  Base change of an abelian scheme is an
  abelian scheme, and `F̄` is algebraically closed, so this really is the
  point group of an abelian VARIETY, not of some larger object.
* `ab`'s `proper`, `smooth` and `connected` fields are exactly what makes
  each geometric fibre an abelian variety; the group structure is on the
  functor of points, so by Yoneda the fibre is a group scheme.
* Divisibility holds in EVERY characteristic — `[N]` is an isogeny for
  every `N ≠ 0`, inseparable but still surjective when `p ∣ N`.  So the
  absence of any characteristic hypothesis is correct and not an
  oversight.  If the fibre is empty the statement is vacuously true.

## WHERE THE GEOMETRY NOW SITS (2026-07-26 — this node HAS been decomposed)

An earlier revision of this docstring argued the node was irreducible at
this pin, on the grounds that cutting it would require `[N]` as a
morphism of schemes, then kernels as subgroup schemes, then dimension
theory.  The first of those turned out to be cheap and the last two turned
out to be unnecessary: the cut below goes through FLATNESS rather than
through a kernel dimension count, so the dimension argument lives inside
the leaf's proof and never has to be stated.  The surviving true part of
the old note is that properness is genuinely unavoidable — for a connected
commutative algebraic group that is *not* proper the statement is FALSE
(`𝔾_a` in characteristic `p` with `N = p` has `[p] = 0`) — which is why
the one remaining leaf is a theorem-of-the-cube input and not something
weaker.

**The proof, and where the geometry now sits.** By Yoneda
(`exists_nsmul_of_exists_comp`) solving `N • w = y` is exactly factoring
the morphism `y.1 : Spec F̄ ⟶ A` through `[N] : A ⟶ A`, and that
factorization is `exists_comp_mulByNat_eq`. Everything between the two —
that `[N]` is universally open, hence (with properness, which is free)
has clopen image, hence by connectedness of the fibres of `f` is
surjective, and that an `F̄`-point then lifts because the base-changed
fibre is a nonempty Jacobson space over an algebraically closed field —
is PROVEN in `Modularity/AbelianSchemeIsogeny.lean`. What is left open
there is only the flatness of `[N]`, which is the theorem of the cube. -/
theorem exists_nsmul_eq_geomFibrePt
    {A S : Scheme.{u}} {f : A ⟶ S} (ab : AbelianSchemeStruct f)
    {F : Type u} [Field F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (N : ℕ) (hN : N ≠ 0) (y : GeomFibrePt f x) :
    ∃ w : GeomFibrePt f x,
      letI := ab.addCommGroup (specAlgClos F ≫ x)
      N • w = y :=
  ab.exists_nsmul_of_exists_comp N y (exists_comp_mulByNat_eq ab N hN y.1)

open _root_.NumberField in
/-- **Multiplication by `π` carries `A[Iⁿ⁺¹]` ONTO `A[Iⁿ]`** (PROVEN
2026-07-26 over the single geometric leaf `exists_nsmul_eq_geomFibrePt`;
everything else below is commutative algebra in the Dedekind domain
`𝒪_D`).

**Only the surjectivity is asserted**, not any rank: this leaf is
independent of `exists_levelTateFrame` and does not consume `hdim`. It
is what makes the transported map `ψ` in `exists_levelTateFrame_succ`
surjective, which is the only place it is used.

The argument, and why it needs no isogeny theory beyond divisibility.
(The docstring this replaces proposed going through injectivity of
`𝒪_D → End(A_x)` and the structure of the `I`-primary part; none of that
is necessary, and both steps would have needed theory the pin lacks.)

1. `π ≠ 0`, since `0 ∈ I²` and `π ∉ I²`. So the principal ideal `(π)` is
   nonzero, and its absolute norm `N = |𝒪_D/(π)|` is a NONZERO natural
   number lying in `(π)` (`Ideal.absNorm_mem`): write `N = π·a` with
   `a ∈ 𝒪_D`.
2. `[N]` is surjective on `A_x(F̄)` — this is
   `exists_nsmul_eq_geomFibrePt`, the ONLY geometric input — hence so is
   `·π`: given `y`, choose `w` with `N·w = y` and set `z₀ = a·w`, so
   that `π·z₀ = (π a)·w = N·w = y`.
3. `z₀` need not lie in `A[Iⁿ⁺¹]`: all one knows is that `Iⁿ·(π)` kills
   it, and `(π)` may be divisible by primes other than `I`. Factor
   `(π) = I·J` in the Dedekind domain `𝒪_D` (possible because `π ∈ I`,
   i.e. `I ∣ (π)`); `π ∉ I²` says `I ∤ J`, i.e. `J ⊄ I`, so `I` and `J`
   are coprime and therefore so are `Iⁿ⁺¹` and `J`. Choose `e ∈ Iⁿ⁺¹`
   and `j ∈ J` with `e + j = 1`.
4. `z := j·z₀` is the required point. It lies in `A[Iⁿ⁺¹]` because
   `Iⁿ⁺¹·(j) ⊆ Iⁿ⁺¹·J = Iⁿ·(I·J) = Iⁿ·(π)`, which annihilates `z₀`; and
   `π·z = j·(π·z₀) = j·y = (1 − e)·y = y`, because `e ∈ Iⁿ⁺¹ ⊆ Iⁿ` kills
   `y`.

Step 3 is where `hπ2` is used, and it is the only place: it is what
makes `π` a UNIFORMIZER at `I` rather than merely an element of `I`.
The hypothesis is not decorative — for `π ∈ I²` the statement is FALSE
already at `n = 1`, since then `π·z = 0` for every `z ∈ A[I²]` while
`A[I] ≠ 0` on any abelian variety.

(2026-07-26: the base field `F` carried an unused `[NumberField F]`
instance binder, which has been dropped — nothing in the four steps
above looks at `F` beyond `Field F`, and `exists_nsmul_eq_geomFibrePt`
itself is stated for a bare field. The generalization is what lets
`exists_tatePt_val_one_eq`, whose `F` is only a field, consume this
lemma instead of duplicating its proof. Instance binders are inferred,
so no call site changes.) -/
theorem exists_mem_torsion_act_uniformizer_eq
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (I : Ideal (NumberField.RingOfIntegers D)) (hI : I.IsMaximal)
    (π : NumberField.RingOfIntegers D) (hπ : π ∈ I) (hπ2 : π ∉ I ^ 2)
    (n : ℕ) (y : GeomFibrePt f x) (hy : y ∈ (m.torsion x (I ^ n)).1) :
    ∃ z, z ∈ (m.torsion x (I ^ (n + 1))).1 ∧ m.act π z = y := by
  classical
  letI : AddCommGroup (GeomFibrePt f x) := ab.addCommGroup (specAlgClos F ≫ x)
  letI : Module (𝓞 D) (GeomFibrePt f x) := m.module (specAlgClos F ≫ x)
  haveI : I.IsMaximal := hI
  -- `π ≠ 0`, since `0 ∈ I ^ 2`
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact hπ2 (Submodule.zero_mem _)
  -- ### 1. `π` divides a nonzero rational integer, its absolute norm
  have hspan0 : Ideal.span {π} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hπ0
  have hNne : Ideal.absNorm (Ideal.span {π}) ≠ 0 := fun h =>
    hspan0 (Ideal.absNorm_eq_zero_iff.mp h)
  obtain ⟨a, ha⟩ : π ∣ ((Ideal.absNorm (Ideal.span {π}) : ℕ) : 𝓞 D) :=
    Ideal.mem_span_singleton.mp (Ideal.absNorm_mem (Ideal.span {π}))
  -- ### 2. the prime-to-`I` part `J` of the principal ideal `(π)`
  obtain ⟨J, hJ⟩ : I ∣ Ideal.span {π} :=
    Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hπ))
  have hJnotle : ¬ J ≤ I := by
    intro h
    refine hπ2 ?_
    have hle : Ideal.span {π} ≤ I ^ 2 := by
      rw [hJ, sq]; exact Ideal.mul_mono_right h
    exact hle (Ideal.mem_span_singleton_self π)
  have hsup : I ⊔ J = ⊤ := by
    rcases eq_or_lt_of_le (le_sup_left : I ≤ I ⊔ J) with h | h
    · exact absurd (le_sup_right.trans h.ge) hJnotle
    · exact hI.out.2 _ h
  have hcop : I ^ (n + 1) ⊔ J = ⊤ :=
    Ideal.isCoprime_iff_sup_eq.mp (Ideal.isCoprime_iff_sup_eq.mpr hsup).pow_left
  obtain ⟨e, he, j, hj, hej⟩ :=
    Submodule.mem_sup.mp (hcop ▸ (Submodule.mem_top : (1 : 𝓞 D) ∈ (⊤ : Ideal (𝓞 D))))
  -- ### 3. `·π` is surjective on ALL geometric points, by divisibility
  obtain ⟨w, hw⟩ := exists_nsmul_eq_geomFibrePt ab x _ hNne y
  have hw' : ((Ideal.absNorm (Ideal.span {π}) : ℕ) : 𝓞 D) • w = y := by
    rw [Nat.cast_smul_eq_nsmul]; exact hw
  have hπz₀ : π • (a • w) = y := by
    rw [smul_smul, ← ha]; exact hw'
  -- ### 4. the annihilator of `a • w` contains `Iⁿ · (π)`
  have hann : (I ^ n) * Ideal.span {π} ≤
      (Submodule.span (𝓞 D) {a • w}).annihilator := by
    rw [Ideal.mul_le]
    intro r hr s hs
    rw [Submodule.mem_annihilator_span_singleton]
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.mp hs
    have h1 : (r * (π * d)) • (a • w) = (r * d) • (π • (a • w)) := by
      simp only [← mul_smul]
      congr 1
      ring
    rw [h1, hπz₀]
    exact (mem_torsion_iff m x (I ^ n) y).mp hy (r * d) (Ideal.mul_mem_right d _ hr)
  -- ### 5. correcting `a • w` by `j` lands it in `A[Iⁿ⁺¹]` without moving `π · _`
  have hjy : j • y = y := by
    have hey : e • y = 0 :=
      (mem_torsion_iff m x (I ^ n) y).mp hy e
        (Ideal.pow_le_pow_right (Nat.le_succ n) he)
    have h := add_smul e j y
    rw [hej, one_smul, hey, zero_add] at h
    exact h.symm
  have hEq : (I ^ (n + 1)) * J = (I ^ n) * Ideal.span {π} := by
    rw [hJ, pow_succ, mul_assoc]
  refine ⟨j • (a • w), ?_, ?_⟩
  · refine (mem_torsion_iff m x (I ^ (n + 1)) _).mpr fun b hb => ?_
    show b • (j • (a • w)) = 0
    rw [smul_smul]
    refine (Submodule.mem_annihilator_span_singleton _ _).mp (hann ?_)
    rw [← hEq]
    exact Ideal.mul_mem_mul hb hj
  · show π • (j • (a • w)) = y
    rw [smul_smul, mul_comm, ← smul_smul, hπz₀, hjy]

/-! #### The commutative algebra behind a single-level frame

Everything in the `LevelFrame` namespace below is pure module theory
over a Dedekind domain `R`, stated for an ABSTRACT `R`-module `P`; it is
applied at `P = GeomFibrePt f x` in `exists_levelTateFrame`.  Keeping it
abstract is deliberate and not cosmetic: at the concrete `GeomFibrePt`
the `AddCommGroup` and `Module` instances are `letI`-introduced from
`ab`/`m`, so every intermediate statement would have to carry them, and
`Module.End`-shaped instance searches at a concrete module are the
measured performance trap of this development.

The content is the following chain.  Write `A[J]` for the `J`-torsion.
With `π ∈ I ∖ I²` a uniformizer and `·π : A[Iᵏ⁺¹] ↠ A[Iᵏ]` surjective
for every `k` (that is the sibling leaf above, and NOTHING else about
the geometry is used beyond the residual cardinality):

* `(π) ⊔ Iⁿ⁺¹ = I` — unique factorisation of ideals: the left side
  divides `Iⁿ⁺¹`, hence is a power `Iⁱ`; `i ≥ 1` because it is `≤ I`,
  and `i ≤ 1` because `π ∉ I²`.
* the kernel of `·π` on `A[Iⁿ⁺¹]` is exactly `A[I]`, since an element
  killed by `π` and by `Iⁿ⁺¹` is killed by their sum;
* hence `#A[Iⁿ] = (#A[I])ⁿ = q^{2n}` by induction, `q = #(𝒪_D/I)`;
* `I • A[Iᵏ⁺¹] = A[Iᵏ]`, so `Iᵏ • A[Iⁿ⁺ᵏ] = A[Iⁿ]`;
* two generators lift: a pair generating `A[Iⁿ]` lifts through `·π` to a
  pair generating `A[Iⁿ⁺¹]`, because the lifted span `N` satisfies
  `A[Iⁿ⁺¹] = N + A[I]` (kernel computation) and then
  `A[I] = Iⁿ • A[Iⁿ⁺¹] = Iⁿ • N + Iⁿ • A[I] ⊆ N`;
* at level one the two generators come from the cardinality: `A[I]` is a
  vector space over the residue field `k = 𝒪_D/I` with `q²` elements,
  hence of `k`-dimension two;
* finally a surjection `(𝒪_D/Iⁿ)² ↠ A[Iⁿ]` between finite sets of equal
  cardinality is a bijection, which is the frame. -/

namespace LevelFrame

section Ideals

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- **`(π) ⊔ Iⁿ⁺¹ = I` for `π ∈ I ∖ I²`** (PROVEN).  In a Dedekind
domain an ideal containing `Iⁿ⁺¹` divides it, hence is a power of the
prime `I`; being `≤ I` rules out the zeroth power and containing `π`
rules out the higher ones. -/
theorem span_singleton_sup_pow_eq {I : Ideal R} (hI : I.IsMaximal) (hI0 : I ≠ ⊥)
    {π : R} (hπ : π ∈ I) (hπ2 : π ∉ I ^ 2) (n : ℕ) :
    Ideal.span {π} ⊔ I ^ (n + 1) = I := by
  have hprime : Prime I := Ideal.prime_of_isPrime hI0 hI.isPrime
  have hJle : Ideal.span {π} ⊔ I ^ (n + 1) ≤ I :=
    sup_le (Ideal.span_le.2 (by simpa using hπ)) (Ideal.pow_le_self n.succ_ne_zero)
  obtain ⟨i, _, hass⟩ :=
    (dvd_prime_pow hprime (n + 1)).mp (Ideal.dvd_iff_le.mpr le_sup_right)
  have hJeq : Ideal.span {π} ⊔ I ^ (n + 1) = I ^ i :=
    le_antisymm (Ideal.dvd_iff_le.mp hass.symm.dvd) (Ideal.dvd_iff_le.mp hass.dvd)
  have hπJ : π ∈ Ideal.span {π} ⊔ I ^ (n + 1) :=
    Submodule.mem_sup_left (Ideal.mem_span_singleton_self π)
  match i, hJeq with
  | 0, hJeq =>
      rw [pow_zero, Ideal.one_eq_top] at hJeq
      exact absurd (top_le_iff.mp (hJeq ▸ hJle)) hI.ne_top
  | 1, hJeq => simpa using hJeq
  | (j + 2), hJeq =>
      exact absurd (Ideal.pow_le_pow_right (by omega) (hJeq ▸ hπJ)) hπ2

end Ideals

section Torsion

variable {R : Type*} [CommRing R] {P : Type*} [AddCommGroup P] [Module R P]

/-- **Membership in the `J`-torsion of an abstract module** (PROVEN). -/
theorem mem_tors_iff (J : Ideal R) (y : P) :
    y ∈ Submodule.torsionBySet R P (J : Set R) ↔ ∀ a ∈ J, a • y = 0 :=
  ⟨fun h a ha => (Submodule.mem_torsionBySet_iff _ _).mp h ⟨a, ha⟩,
    fun h => (Submodule.mem_torsionBySet_iff _ _).mpr fun a => h a a.2⟩

/-- **A bigger ideal has smaller torsion** (PROVEN). -/
theorem tors_mono {J J' : Ideal R} (h : J ≤ J') :
    Submodule.torsionBySet R P (J' : Set R) ≤ Submodule.torsionBySet R P (J : Set R) := by
  intro y hy
  rw [mem_tors_iff] at hy ⊢
  exact fun a ha => hy a (h ha)

/-- **`A[⊤] = 0`** (PROVEN): `1 ∈ ⊤` acts as the identity. -/
theorem tors_top : Submodule.torsionBySet R P ((⊤ : Ideal R) : Set R) = ⊥ := by
  ext y
  rw [mem_tors_iff]
  simp only [Submodule.mem_bot]
  refine ⟨fun h => by simpa using h 1 trivial, ?_⟩
  rintro rfl a _
  simp

variable (I : Ideal R)

/-- **`I • A[Iⁿ⁺¹] ≤ A[Iⁿ]`** (PROVEN). -/
theorem smul_tors_le (n : ℕ) :
    I • Submodule.torsionBySet R P ((I ^ (n + 1) : Ideal R) : Set R)
      ≤ Submodule.torsionBySet R P ((I ^ n : Ideal R) : Set R) := by
  rw [Submodule.smul_le]
  intro a ha y hy
  rw [mem_tors_iff] at hy ⊢
  intro b hb
  rw [smul_smul]
  exact hy _ (by rw [pow_succ]; exact Ideal.mul_mem_mul hb ha)

variable {π : R}

/-- **Surjectivity of `·π` upgrades the previous inequality to an
equality**: `I • A[Iⁿ⁺¹] = A[Iⁿ]` (PROVEN). -/
theorem smul_tors_eq (hπ : π ∈ I)
    (hsurj : ∀ (k : ℕ) (y : P), y ∈ Submodule.torsionBySet R P ((I ^ k : Ideal R) : Set R) →
      ∃ z ∈ Submodule.torsionBySet R P ((I ^ (k + 1) : Ideal R) : Set R), π • z = y)
    (n : ℕ) :
    I • Submodule.torsionBySet R P ((I ^ (n + 1) : Ideal R) : Set R)
      = Submodule.torsionBySet R P ((I ^ n : Ideal R) : Set R) := by
  refine le_antisymm (smul_tors_le I n) ?_
  intro y hy
  obtain ⟨z, hz, rfl⟩ := hsurj n y hy
  exact Submodule.smul_mem_smul hπ hz

/-- **`Iᵏ • A[Iⁿ⁺ᵏ] = A[Iⁿ]`** (PROVEN, by iterating `smul_tors_eq`). -/
theorem pow_smul_tors (hπ : π ∈ I)
    (hsurj : ∀ (k : ℕ) (y : P), y ∈ Submodule.torsionBySet R P ((I ^ k : Ideal R) : Set R) →
      ∃ z ∈ Submodule.torsionBySet R P ((I ^ (k + 1) : Ideal R) : Set R), π • z = y)
    (n k : ℕ) :
    I ^ k • Submodule.torsionBySet R P ((I ^ (n + k) : Ideal R) : Set R)
      = Submodule.torsionBySet R P ((I ^ n : Ideal R) : Set R) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Submodule.mul_smul, show n + (k + 1) = (n + k) + 1 by omega,
        smul_tors_eq I hπ hsurj (n + k)]
      exact ih

/-- **The kernel of `·π` on `A[Iⁿ⁺¹]` is `A[I]`** (PROVEN): an element
killed by `π` and by `Iⁿ⁺¹` is killed by `(π) ⊔ Iⁿ⁺¹ = I`. -/
theorem mem_tors_of_smul_eq_zero [IsDedekindDomain R] (hI : I.IsMaximal) (hI0 : I ≠ ⊥)
    (hπ : π ∈ I) (hπ2 : π ∉ I ^ 2) (n : ℕ) {z : P}
    (hz : z ∈ Submodule.torsionBySet R P ((I ^ (n + 1) : Ideal R) : Set R))
    (h : π • z = 0) :
    z ∈ Submodule.torsionBySet R P ((I : Ideal R) : Set R) := by
  rw [mem_tors_iff]
  intro a ha
  rw [← span_singleton_sup_pow_eq hI hI0 hπ hπ2 n] at ha
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp ha
  rw [add_smul]
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hu
  rw [mul_smul, h, smul_zero, zero_add]
  exact (mem_tors_iff _ _).mp hz v hv

end Torsion

section Frame

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {P : Type*} [AddCommGroup P] [Module R P]

/-- **The `Iⁿ`-torsion of an abstract module is free of rank two over
`R/Iⁿ`** (PROVEN 2026-07-26), given only that the `I`-torsion has
`(#R/I)²` elements and that multiplication by a uniformizer `π` carries
each torsion level onto the previous one.

This is the whole algebraic content of `exists_levelTateFrame`; the two
hypotheses `hsurj` and `hcard` are its two geometric inputs, supplied
there by `exists_mem_torsion_act_uniformizer_eq` and by
`card_torsion_of_isMaximal`. -/
theorem exists_linearEquiv_tors_pow
    (I : Ideal R) (hI : I.IsMaximal) (hI0 : I ≠ ⊥) [Finite (R ⧸ I)]
    {π : R} (hπ : π ∈ I) (hπ2 : π ∉ I ^ 2)
    (hsurj : ∀ (k : ℕ) (y : P), y ∈ Submodule.torsionBySet R P ((I ^ k : Ideal R) : Set R) →
      ∃ z ∈ Submodule.torsionBySet R P ((I ^ (k + 1) : Ideal R) : Set R), π • z = y)
    (hcard : Nat.card (Submodule.torsionBySet R P ((I : Ideal R) : Set R))
      = Nat.card (R ⧸ I) ^ 2)
    (n : ℕ) :
    Nonempty ((Fin 2 → R ⧸ I ^ n) ≃ₗ[R]
      (Submodule.torsionBySet R P ((I ^ n : Ideal R) : Set R))) := by
  letI : Field (R ⧸ I) := Ideal.Quotient.field I
  have hq2 : 2 ≤ Nat.card (R ⧸ I) := Finite.one_lt_card (α := R ⧸ I)
  -- the cardinality at every level, by induction along `·π`
  have hcardn : ∀ k : ℕ,
      Nat.card (Submodule.torsionBySet R P ((I ^ k : Ideal R) : Set R))
        = Nat.card (R ⧸ I) ^ (2 * k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hmem : ∀ z : (Submodule.torsionBySet R P ((I ^ (k + 1) : Ideal R) : Set R)),
            π • (z : P) ∈ Submodule.torsionBySet R P ((I ^ k : Ideal R) : Set R) := fun z =>
          smul_tors_le I k (Submodule.smul_mem_smul hπ z.2)
        set g : (Submodule.torsionBySet R P ((I ^ (k + 1) : Ideal R) : Set R)) →ₗ[R]
            (Submodule.torsionBySet R P ((I ^ k : Ideal R) : Set R)) :=
          LinearMap.codRestrict _
            ((LinearMap.lsmul R P π).comp
              (Submodule.torsionBySet R P ((I ^ (k + 1) : Ideal R) : Set R)).subtype) hmem with hg
        have hgapp : ∀ z, ((g z : _) : P) = π • (z : P) := fun z => rfl
        have hgsurj : Function.Surjective g := by
          intro y
          obtain ⟨z, hz, hzy⟩ := hsurj k (y : P) y.2
          exact ⟨⟨z, hz⟩, Subtype.ext (by rw [hgapp]; exact hzy)⟩
        have hkercard : Nat.card (LinearMap.ker g)
            = Nat.card (Submodule.torsionBySet R P ((I : Ideal R) : Set R)) := by
          refine Nat.card_congr ⟨fun z => ⟨(z.1 : P), ?_⟩, fun y => ⟨⟨(y : P), ?_⟩, ?_⟩,
            fun _ => rfl, fun _ => rfl⟩
          · refine mem_tors_of_smul_eq_zero I hI hI0 hπ hπ2 k z.1.2 ?_
            have hz0 : ((g z.1 : _) : P) = 0 := by rw [LinearMap.mem_ker.mp z.2]; rfl
            rwa [hgapp] at hz0
          · exact tors_mono (Ideal.pow_le_self k.succ_ne_zero) y.2
          · simp only [LinearMap.mem_ker]
            exact Subtype.ext (by rw [hgapp]; exact (mem_tors_iff _ _).mp y.2 π hπ)
        have hquot : Nat.card
            ((Submodule.torsionBySet R P ((I ^ (k + 1) : Ideal R) : Set R)) ⧸ LinearMap.ker g)
            = Nat.card (Submodule.torsionBySet R P ((I ^ k : Ideal R) : Set R)) :=
          Nat.card_congr (g.quotKerEquivOfSurjective hgsurj).toEquiv
        rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker g), hkercard, hquot, ih,
          hcard]
        ring
  -- two generators at every level
  have hgen : ∀ k : ℕ, ∃ a : Fin 2 → P,
      (∀ i, a i ∈ Submodule.torsionBySet R P ((I ^ k : Ideal R) : Set R)) ∧
      Submodule.torsionBySet R P ((I ^ k : Ideal R) : Set R)
        ≤ Submodule.span R (Set.range a) := by
    intro k
    induction k with
    | zero =>
        refine ⟨0, fun i => zero_mem _, ?_⟩
        rw [pow_zero, Ideal.one_eq_top, tors_top]
        exact bot_le
    | succ k ih =>
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · -- level one: the residual space is two-dimensional
          simp only [zero_add, pow_one]
          haveI hfin : Finite (Submodule.torsionBySet R P ((I : Ideal R) : Set R)) := by
            refine (Nat.card_ne_zero.mp ?_).2
            rw [hcard]
            exact pow_ne_zero 2 (by omega)
          haveI : Module.Finite (R ⧸ I)
              (Submodule.torsionBySet R P ((I : Ideal R) : Set R)) := Module.Finite.of_finite
          have hrank : Module.finrank (R ⧸ I)
              (Submodule.torsionBySet R P ((I : Ideal R) : Set R)) = 2 := by
            haveI := Fintype.ofFinite (R ⧸ I)
            haveI := Fintype.ofFinite (Submodule.torsionBySet R P ((I : Ideal R) : Set R))
            have hcc := Module.card_eq_pow_finrank (K := R ⧸ I)
              (V := (Submodule.torsionBySet R P ((I : Ideal R) : Set R)))
            rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard] at hcc
            exact (Nat.pow_right_injective hq2 hcc).symm
          set b := Module.finBasisOfFinrankEq (R ⧸ I)
            (Submodule.torsionBySet R P ((I : Ideal R) : Set R)) hrank with hb
          refine ⟨fun i => ((b i : _) : P), fun i => (b i).2, ?_⟩
          have hbspanR : Submodule.span R (Set.range (fun i => b i)) = ⊤ := by
            have hres := Submodule.restrictScalars_span R (R ⧸ I)
              Ideal.Quotient.mk_surjective (Set.range (fun i => b i))
            rw [b.span_eq] at hres
            simpa using hres.symm
          intro y hy
          have hmem : (⟨y, hy⟩ : (Submodule.torsionBySet R P ((I : Ideal R) : Set R)))
              ∈ Submodule.span R (Set.range (fun i => b i)) := by
            rw [hbspanR]; trivial
          obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hmem
          refine (Submodule.mem_span_range_iff_exists_fun R).mpr ⟨c, ?_⟩
          have h2 := Subtype.ext_iff.mp hc
          simpa using h2
        · -- inductive step: lift the generators through `·π`
          obtain ⟨a, hamem, haspan⟩ := ih
          choose b hbmem hbeq using fun i => hsurj k (a i) (hamem i)
          refine ⟨b, hbmem, ?_⟩
          have hNle : Submodule.span R (Set.range b)
              ≤ Submodule.torsionBySet R P ((I ^ (k + 1) : Ideal R) : Set R) :=
            Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hbmem i)
          have hA : Submodule.torsionBySet R P ((I ^ (k + 1) : Ideal R) : Set R)
              ≤ Submodule.span R (Set.range b)
                ⊔ Submodule.torsionBySet R P ((I : Ideal R) : Set R) := by
            intro z hz
            have hpz : π • z ∈ Submodule.torsionBySet R P ((I ^ k : Ideal R) : Set R) :=
              smul_tors_le I k (Submodule.smul_mem_smul hπ hz)
            obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp (haspan hpz)
            have hwN : (∑ i, c i • b i) ∈ Submodule.span R (Set.range b) :=
              Submodule.sum_mem _ fun i _ =>
                Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
            have hpw : π • (∑ i, c i • b i) = π • z := by
              rw [Finset.smul_sum]
              rw [show (∑ i, π • c i • b i) = ∑ i, c i • a i from
                Finset.sum_congr rfl fun i _ => by rw [smul_comm, hbeq i]]
              exact hc
            have hzw : z - (∑ i, c i • b i)
                ∈ Submodule.torsionBySet R P ((I : Ideal R) : Set R) := by
              refine mem_tors_of_smul_eq_zero I hI hI0 hπ hπ2 k (sub_mem hz (hNle hwN)) ?_
              rw [smul_sub, hpw, sub_self]
            have hz' : (∑ i, c i • b i) + (z - (∑ i, c i • b i)) = z := by abel
            rw [← hz']
            exact Submodule.add_mem_sup hwN hzw
          have hB : Submodule.torsionBySet R P ((I : Ideal R) : Set R)
              ≤ Submodule.span R (Set.range b) := by
            have h1 := pow_smul_tors I hπ hsurj 1 k
            rw [show (1 : ℕ) + k = k + 1 by omega, pow_one] at h1
            rw [← h1]
            calc I ^ k • Submodule.torsionBySet R P ((I ^ (k + 1) : Ideal R) : Set R)
                ≤ I ^ k • (Submodule.span R (Set.range b)
                    ⊔ Submodule.torsionBySet R P ((I : Ideal R) : Set R)) :=
                  Submodule.smul_mono le_rfl hA
              _ = I ^ k • Submodule.span R (Set.range b)
                    ⊔ I ^ k • Submodule.torsionBySet R P ((I : Ideal R) : Set R) :=
                  Submodule.smul_sup _ _ _
              _ ≤ Submodule.span R (Set.range b) := by
                  refine sup_le (Submodule.smul_le.mpr fun r _ y hy => Submodule.smul_mem _ _ hy)
                    (Submodule.smul_le.mpr fun r hr y hy => ?_)
                  have hry : r • y = 0 :=
                    (mem_tors_iff _ _).mp hy r (Ideal.pow_le_self (by omega) hr)
                  rw [hry]
                  exact Submodule.zero_mem _
          exact hA.trans (sup_le le_rfl hB)
  -- assemble: a surjection between finite sets of equal cardinality
  obtain ⟨a, hamem, haspan⟩ := hgen n
  have hcardQ : Nat.card (R ⧸ I ^ n) = Nat.card (R ⧸ I) ^ n := by
    haveI := hI.isPrime
    have h := _root_.cardQuot_pow_of_prime (S := R) (P := I) hI0 (i := n)
    simpa [Submodule.cardQuot_apply] using h
  haveI : Finite (R ⧸ I ^ n) := by
    refine (Nat.card_ne_zero.mp ?_).2
    rw [hcardQ]
    exact pow_ne_zero n (by omega)
  set a' : Fin 2 → (Submodule.torsionBySet R P ((I ^ n : Ideal R) : Set R)) :=
    fun i => ⟨a i, hamem i⟩ with ha'
  have hspanR : Submodule.span R (Set.range a') = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨y, hy⟩ -
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp (haspan hy)
    refine (Submodule.mem_span_range_iff_exists_fun R).mpr ⟨c, ?_⟩
    exact Subtype.ext (by simpa [ha'] using hc)
  have hspanS : Submodule.span (R ⧸ I ^ n) (Set.range a') = ⊤ := by
    have hres := Submodule.restrictScalars_span R (R ⧸ I ^ n)
      Ideal.Quotient.mk_surjective (Set.range a')
    rw [hspanR] at hres
    simpa using hres
  set φ := Fintype.linearCombination (R ⧸ I ^ n) a' with hφ
  have hsurjφ : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, hφ, Fintype.range_linearCombination, hspanS]
  have hcards : Nat.card (Fin 2 → R ⧸ I ^ n)
      = Nat.card (Submodule.torsionBySet R P ((I ^ n : Ideal R) : Set R)) := by
    rw [Nat.card_pi, hcardn n, hcardQ]
    simp [Finset.prod_const, ← pow_mul, mul_comm]
  have hbij : Function.Bijective φ :=
    (Nat.bijective_iff_surjective_and_card φ).mpr ⟨hsurjφ, hcards⟩
  exact ⟨(LinearEquiv.ofBijective φ hbij).restrictScalars R⟩

end Frame

section RankCount

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {P : Type*} [AddCommGroup P] [Module R P]

/-- **The tower count with the exponent left free** (PROVEN 2026-07-27).

This is the induction inside `exists_linearEquiv_tors_pow` with the
residual rank `r` a parameter instead of specialised to `2`.  It is what
turns a single residual count at a prime `J` into a count at every power
`J ^ n`, and it is the piece the CRT assembly of
`card_torsion_of_isMaximal` consumes at EACH prime above `p` — where the
ranks are not yet known to be equal, so the specialised version cannot be
used. -/
theorem card_tors_pow (I : Ideal R) (hI : I.IsMaximal) (hI0 : I ≠ ⊥)
    {π : R} (hπ : π ∈ I) (hπ2 : π ∉ I ^ 2)
    (hsurj : ∀ (k : ℕ) (y : P), y ∈ Submodule.torsionBySet R P ((I ^ k : Ideal R) : Set R) →
      ∃ z ∈ Submodule.torsionBySet R P ((I ^ (k + 1) : Ideal R) : Set R), π • z = y)
    (r : ℕ)
    (hcard : Nat.card (Submodule.torsionBySet R P ((I : Ideal R) : Set R))
      = Nat.card (R ⧸ I) ^ r) (n : ℕ) :
    Nat.card (Submodule.torsionBySet R P ((I ^ n : Ideal R) : Set R))
      = Nat.card (R ⧸ I) ^ (r * n) := by
  induction n with
  | zero =>
      simp only [pow_zero, Ideal.one_eq_top, Nat.mul_zero]
      rw [tors_top]
      simp
  | succ k ih =>
      have hmem : ∀ z : (Submodule.torsionBySet R P ((I ^ (k + 1) : Ideal R) : Set R)),
          π • (z : P) ∈ Submodule.torsionBySet R P ((I ^ k : Ideal R) : Set R) := fun z =>
        smul_tors_le I k (Submodule.smul_mem_smul hπ z.2)
      set g : (Submodule.torsionBySet R P ((I ^ (k + 1) : Ideal R) : Set R)) →ₗ[R]
          (Submodule.torsionBySet R P ((I ^ k : Ideal R) : Set R)) :=
        LinearMap.codRestrict _
          ((LinearMap.lsmul R P π).comp
            (Submodule.torsionBySet R P ((I ^ (k + 1) : Ideal R) : Set R)).subtype) hmem with hg
      have hgapp : ∀ z, ((g z : _) : P) = π • (z : P) := fun z => rfl
      have hgsurj : Function.Surjective g := by
        intro y
        obtain ⟨z, hz, hzy⟩ := hsurj k (y : P) y.2
        exact ⟨⟨z, hz⟩, Subtype.ext (by rw [hgapp]; exact hzy)⟩
      have hkercard : Nat.card (LinearMap.ker g)
          = Nat.card (Submodule.torsionBySet R P ((I : Ideal R) : Set R)) := by
        refine Nat.card_congr ⟨fun z => ⟨(z.1 : P), ?_⟩, fun y => ⟨⟨(y : P), ?_⟩, ?_⟩,
          fun _ => rfl, fun _ => rfl⟩
        · refine mem_tors_of_smul_eq_zero I hI hI0 hπ hπ2 k z.1.2 ?_
          have hz0 : ((g z.1 : _) : P) = 0 := by rw [LinearMap.mem_ker.mp z.2]; rfl
          rwa [hgapp] at hz0
        · exact tors_mono (Ideal.pow_le_self k.succ_ne_zero) y.2
        · simp only [LinearMap.mem_ker]
          exact Subtype.ext (by rw [hgapp]; exact (mem_tors_iff _ _).mp y.2 π hπ)
      have hquot : Nat.card
          ((Submodule.torsionBySet R P ((I ^ (k + 1) : Ideal R) : Set R)) ⧸ LinearMap.ker g)
          = Nat.card (Submodule.torsionBySet R P ((I ^ k : Ideal R) : Set R)) :=
        Nat.card_congr (g.quotKerEquivOfSurjective hgsurj).toEquiv
      rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker g), hkercard, hquot, ih,
        hcard]
      ring

/-- **Termwise equality from an equality of products under a termwise
inequality** (PROVEN): over `ℕ`, `∏ f = ∏ g` with `f i ≤ g i` throughout
and `f` positive forces `f i₀ = g i₀`.

Mathlib's `Finset.prod_eq_prod_iff_of_le` needs `IsOrderedCancelMonoid`,
which `(ℕ, *)` is NOT (`0 * a = 0 * b`), so it does not apply here; the
positivity hypothesis is what replaces cancellation. -/
theorem eq_of_prod_eq_of_le {ι : Type*} {s : Finset ι} {f g : ι → ℕ}
    (hpos : ∀ i ∈ s, 0 < f i) (hle : ∀ i ∈ s, f i ≤ g i)
    (heq : ∏ i ∈ s, f i = ∏ i ∈ s, g i) {i₀ : ι} (hi₀ : i₀ ∈ s) :
    f i₀ = g i₀ := by
  classical
  rw [← Finset.mul_prod_erase _ _ hi₀, ← Finset.mul_prod_erase _ _ hi₀] at heq
  have hA : 0 < ∏ i ∈ s.erase i₀, f i :=
    Finset.prod_pos fun i hi => hpos i (Finset.mem_of_mem_erase hi)
  have hAB : ∏ i ∈ s.erase i₀, f i ≤ ∏ i ∈ s.erase i₀, g i :=
    Finset.prod_le_prod' fun i hi => hle i (Finset.mem_of_mem_erase hi)
  by_contra hne
  have hlt : f i₀ < g i₀ := lt_of_le_of_ne (hle i₀ hi₀) hne
  have hcontr : f i₀ * (∏ i ∈ s.erase i₀, f i) < g i₀ * (∏ i ∈ s.erase i₀, g i) :=
    calc f i₀ * (∏ i ∈ s.erase i₀, f i)
        < g i₀ * (∏ i ∈ s.erase i₀, f i) := Nat.mul_lt_mul_right hA |>.mpr hlt
      _ ≤ g i₀ * (∏ i ∈ s.erase i₀, g i) := Nat.mul_le_mul_left _ hAB
  exact absurd heq (Nat.ne_of_lt hcontr)

end RankCount

section Assembly

open _root_.NumberField

variable {D : Type*} [Field D] [NumberField D]
variable {P : Type*} [AddCommGroup P] [Module (𝓞 D) P]

/-- **`#(𝒪_D ⧸ Jⁿ) = #(𝒪_D ⧸ J)ⁿ`** (PROVEN), read off the
multiplicativity of the absolute norm — `Ideal.absNorm` is a bundled
`MonoidWithZeroHom`, so `map_pow` is the whole proof. -/
theorem card_quotient_pow (J : Ideal (𝓞 D)) (n : ℕ) :
    Nat.card (𝓞 D ⧸ J ^ n) = Nat.card (𝓞 D ⧸ J) ^ n := by
  have h := map_pow (Ideal.absNorm (S := 𝓞 D)) J n
  simpa [Ideal.absNorm_apply, Submodule.cardQuot_apply] using h

/-- **THE ARITHMETIC BRIDGE: the residual rank is two, from parity plus
the integer count** (PROVEN 2026-07-27).  This is the entire non-geometric
content of `card_torsion_of_isMaximal`, isolated as a statement about an
arbitrary `𝒪_D`-module `P` — no schemes, no abelian varieties.

WHAT IT SAYS.  Write `r_J` for the `𝒪_D/J`-dimension of `P[J]`.  Given

* `hcard`  — the INTEGER count `#P[p] = p^(2g)`, `g = [D : ℚ]`;
* `hsurj`  — surjectivity of `·π` from each torsion level onto the
  previous one, at every maximal `J` (divisibility);
* `heven`  — every `r_J` is EVEN;
* `hnz`    — every `P[J]` is nonzero,

the conclusion `r_I = 2` follows for every maximal `I`.  The audit above
is right that `hcard` ALONE is insufficient — its counterexample `M₁` has
`(r_{J₁}, r_{J₂}) = (1, 3)` — and right that faithfulness and
divisibility do not rescue it; what rescues it is `heven`, which kills
`M₁` outright, together with `hnz`, which kills the surviving parity-even
distribution `(0, 4)`.

HOW IT IS PROVEN.  `p 𝒪_D = ∏_{J ∣ p} J^(e_J)` is a product of pairwise
comaximal ideals, so `P[p] = ⨁_J P[J^(e_J)]` EXACTLY — that is mathlib's
`Submodule.isInternal_prime_power_torsion_of_is_torsion_by_ideal`, with
no ramification caveat, because `p 𝒪_D` IS that product.  The tower
lemma `card_tors_pow` gives `#P[J^(e_J)] = #(𝒪_D/J)^(r_J e_J)`, and
multiplicativity of the absolute norm converts that to
`#(𝒪_D/J^(e_J))^(r_J)` and gives `∏_J #(𝒪_D/J^(e_J)) = #(𝒪_D/p𝒪_D)
= p^g`.  So writing `n_J := #(𝒪_D/J^(e_J)) ≥ 2`,

  `∏_J n_J^(r_J) = #P[p] = p^(2g) = (∏_J n_J)^2 = ∏_J n_J^2`,

while `r_J ≥ 2` for every `J` by `heven` and `hnz`.  A product of terms
each at least the corresponding term of another product can only be equal
to it termwise, so `n_J^(r_J) = n_J^2` and hence `r_J = 2`, for every `J`
at once.

NOTE THE RAMIFICATION IDENTITY IS NOT USED.  One expects to need
`Σ_J e_J f_J = g` (`Ideal.sum_ramification_inertia`); the absolute norm
supplies it implicitly through `Ideal.absNorm_span_natCast`, which is why
neither `ramificationIdx'` nor `inertiaDeg'` appears anywhere below. -/
theorem card_tors_eq_sq
    (I : Ideal (𝓞 D)) (hI : I.IsMaximal)
    (p : ℕ) (hp : p.Prime) (hpI : (p : 𝓞 D) ∈ I)
    (hsurj : ∀ J : Ideal (𝓞 D), J.IsMaximal → ∀ π ∈ J, π ∉ J ^ 2 →
      ∀ (k : ℕ) (y : P), y ∈ Submodule.torsionBySet (𝓞 D) P ((J ^ k : Ideal (𝓞 D)) : Set (𝓞 D)) →
        ∃ z ∈ Submodule.torsionBySet (𝓞 D) P ((J ^ (k + 1) : Ideal (𝓞 D)) : Set (𝓞 D)),
          π • z = y)
    (hcard : Nat.card (Submodule.torsionBySet (𝓞 D) P
        ((Ideal.span {(p : 𝓞 D)} : Ideal (𝓞 D)) : Set (𝓞 D)))
      = p ^ (2 * Module.finrank ℚ D))
    (heven : ∀ J : Ideal (𝓞 D), J.IsMaximal → (p : 𝓞 D) ∈ J →
      ∃ r, Nat.card (Submodule.torsionBySet (𝓞 D) P ((J : Ideal (𝓞 D)) : Set (𝓞 D)))
        = Nat.card (𝓞 D ⧸ J) ^ (2 * r))
    (hnz : ∀ J : Ideal (𝓞 D), J.IsMaximal → (p : 𝓞 D) ∈ J →
      Nat.card (Submodule.torsionBySet (𝓞 D) P ((J : Ideal (𝓞 D)) : Set (𝓞 D))) ≠ 1) :
    Nat.card (Submodule.torsionBySet (𝓞 D) P ((I : Ideal (𝓞 D)) : Set (𝓞 D)))
      = Nat.card (𝓞 D ⧸ I) ^ 2 := by
  classical
  set 𝔞 : Ideal (𝓞 D) := Ideal.span {(p : 𝓞 D)} with h𝔞def
  have hpne : (p : 𝓞 D) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have h𝔞 : 𝔞 ≠ ⊥ := by simpa [h𝔞def, Ideal.span_singleton_eq_bot] using hpne
  set S : Finset (Ideal (𝓞 D)) := (UniqueFactorizationMonoid.factors 𝔞).toFinset with hSdef
  set e : Ideal (𝓞 D) → ℕ := fun J => (UniqueFactorizationMonoid.factors 𝔞).count J with hedef
  -- ### basic facts about the factorisation of `p 𝒪_D`
  have hprod : ∏ J ∈ S, J ^ e J = 𝔞 := by
    rw [hSdef, hedef, ← Finset.prod_multiset_count, ← associated_iff_eq]
    exact UniqueFactorizationMonoid.factors_prod h𝔞
  have he1 : ∀ J ∈ S, 1 ≤ e J := fun J hJ =>
    Multiset.one_le_count_iff_mem.mpr (Multiset.mem_toFinset.mp hJ)
  have hprime : ∀ J ∈ S, Prime J := fun J hJ =>
    UniqueFactorizationMonoid.prime_of_factor J (Multiset.mem_toFinset.mp hJ)
  have hJbot : ∀ J ∈ S, J ≠ ⊥ := fun J hJ => (hprime J hJ).ne_zero
  have hmax : ∀ J ∈ S, J.IsMaximal := fun J hJ =>
    (Ideal.isPrime_of_prime (hprime J hJ)).isMaximal (hJbot J hJ)
  have hlepow : ∀ J ∈ S, 𝔞 ≤ J ^ e J := by
    intro J hJ
    rw [← hprod]
    exact Ideal.dvd_iff_le.mp (Finset.dvd_prod_of_mem _ hJ)
  have hmemp : ∀ J ∈ S, (p : 𝓞 D) ∈ J := by
    intro J hJ
    have h1 : 𝔞 ≤ J :=
      le_trans (hlepow J hJ) (Ideal.pow_le_self (by have := he1 J hJ; omega : e J ≠ 0))
    exact h1 (Ideal.mem_span_singleton_self _)
  have hI0 : I ≠ ⊥ := by
    intro h
    rw [h] at hpI
    exact hpne (Ideal.mem_bot.mp hpI)
  have hIS : I ∈ S := by
    rw [hSdef, Multiset.mem_toFinset]
    have hIdvd : I ∣ 𝔞 := Ideal.dvd_iff_le.mpr (by rw [h𝔞def, Ideal.span_le]; simpa using hpI)
    obtain ⟨q, hq, hassoc⟩ :=
      UniqueFactorizationMonoid.exists_mem_factors_of_dvd h𝔞
        (Ideal.prime_of_isPrime hI0 hI.isPrime).irreducible hIdvd
    rwa [associated_iff_eq.mp hassoc]
  -- ### the CRT splitting of `P[p]`, and its cardinality
  have hequiv : ∀ K : Ideal (𝓞 D), 𝔞 ≤ K →
      Nat.card (Submodule.torsionBySet (𝓞 D)
          (Submodule.torsionBySet (𝓞 D) P ((𝔞 : Ideal (𝓞 D)) : Set (𝓞 D))) (K : Set (𝓞 D)))
        = Nat.card (Submodule.torsionBySet (𝓞 D) P ((K : Ideal (𝓞 D)) : Set (𝓞 D))) := by
    intro K hK
    refine Nat.card_congr ⟨fun z => ⟨(z.1 : P), ?_⟩, fun y => ⟨⟨(y : P), tors_mono hK y.2⟩, ?_⟩,
      fun _ => rfl, fun _ => rfl⟩
    · rw [mem_tors_iff]
      intro a ha
      have h := (mem_tors_iff (P := (Submodule.torsionBySet (𝓞 D) P
        ((𝔞 : Ideal (𝓞 D)) : Set (𝓞 D)))) K z.1).mp z.2 a ha
      simpa using congrArg Subtype.val h
    · rw [mem_tors_iff]
      intro a ha
      exact Subtype.ext (by simpa using (mem_tors_iff K (y : P)).mp y.2 a ha)
  have hint := Submodule.isInternal_prime_power_torsion_of_is_torsion_by_ideal
    (M := (Submodule.torsionBySet (𝓞 D) P ((𝔞 : Ideal (𝓞 D)) : Set (𝓞 D)))) h𝔞
    (Submodule.torsionBySet_isTorsionBySet ((𝔞 : Ideal (𝓞 D)) : Set (𝓞 D)))
  have hcardprod : Nat.card (Submodule.torsionBySet (𝓞 D) P ((𝔞 : Ideal (𝓞 D)) : Set (𝓞 D)))
      = ∏ J ∈ S, Nat.card (Submodule.torsionBySet (𝓞 D) P
          ((J ^ e J : Ideal (𝓞 D)) : Set (𝓞 D))) := by
    have h1 := Nat.card_congr (Equiv.ofBijective _ hint).symm
    rw [h1, Nat.card_congr (DirectSum.linearEquivFunOnFintype (𝓞 D)
      (ι := { x // x ∈ S }) (M := fun J : S =>
        (Submodule.torsionBySet (𝓞 D)
          (Submodule.torsionBySet (𝓞 D) P ((𝔞 : Ideal (𝓞 D)) : Set (𝓞 D)))
          (((J : Ideal (𝓞 D)) ^ e (J : Ideal (𝓞 D)) : Ideal (𝓞 D)) : Set (𝓞 D))))).toEquiv,
      Nat.card_pi]
    rw [← Finset.prod_coe_sort S (fun J => Nat.card (Submodule.torsionBySet (𝓞 D) P
      ((J ^ e J : Ideal (𝓞 D)) : Set (𝓞 D))))]
    exact Finset.prod_congr rfl fun J _ => hequiv _ (hlepow J J.2)
  -- ### the count at each prime power, from the tower lemma
  have hper : ∀ J ∈ S, ∃ r : ℕ, 1 ≤ r ∧
      Nat.card (Submodule.torsionBySet (𝓞 D) P ((J : Ideal (𝓞 D)) : Set (𝓞 D)))
        = Nat.card (𝓞 D ⧸ J) ^ (2 * r) ∧
      Nat.card (Submodule.torsionBySet (𝓞 D) P ((J ^ e J : Ideal (𝓞 D)) : Set (𝓞 D)))
        = Nat.card (𝓞 D ⧸ J ^ e J) ^ (2 * r) := by
    intro J hJ
    obtain ⟨π, hπ, hπ2⟩ := exists_mem_notMem_sq_of_isMaximal (hmax J hJ) (hJbot J hJ)
    obtain ⟨r, hr⟩ := heven J (hmax J hJ) (hmemp J hJ)
    refine ⟨r, ?_, hr, ?_⟩
    · rcases Nat.eq_zero_or_pos r with h0 | h
      · exact absurd (by rw [hr, h0]; simp) (hnz J (hmax J hJ) (hmemp J hJ))
      · exact h
    · rw [card_tors_pow J (hmax J hJ) (hJbot J hJ) hπ hπ2
        (hsurj J (hmax J hJ) π hπ hπ2) (2 * r) hr (e J), card_quotient_pow, ← pow_mul]
      ring_nf
  choose! r hr1 hrlvl hrpow using hper
  -- ### the same product, computed in the RING: `∏_J #(𝒪_D/J^(e_J)) = p^g`
  have hringprod : ∏ J ∈ S, Nat.card (𝓞 D ⧸ J ^ e J) = p ^ Module.finrank ℚ D := by
    have h1 : ∏ J ∈ S, Ideal.absNorm (J ^ e J) = Ideal.absNorm 𝔞 := by
      rw [← map_prod, hprod]
    have h2 : Ideal.absNorm 𝔞 = p ^ Module.finrank ℚ D := by
      rw [h𝔞def, Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank]
    simpa [Ideal.absNorm_apply, Submodule.cardQuot_apply, h2] using h1
  -- ### each factor is at least two, which is what makes the comparison strict
  have hn2 : ∀ J ∈ S, 2 ≤ Nat.card (𝓞 D ⧸ J ^ e J) := by
    intro J hJ
    have hne0 : Ideal.absNorm (J ^ e J) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact pow_ne_zero _ (fun h0 => hJbot J hJ (by rwa [Ideal.zero_eq_bot] at h0))
    have hne1 : Ideal.absNorm (J ^ e J) ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]
      intro htop
      exact (hmax J hJ).ne_top (top_le_iff.mp
        (htop ▸ Ideal.pow_le_self (by have := he1 J hJ; omega : e J ≠ 0)))
    have := hne0; have := hne1
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hne0 hne1
    omega
  -- ### conclude: every `r J` is one, i.e. every residual rank is two
  have hkey : ∀ J ∈ S, r J = 1 := by
    intro J hJ
    have hfg : ∀ K ∈ S, Nat.card (𝓞 D ⧸ K ^ e K) ^ 2 ≤ Nat.card (𝓞 D ⧸ K ^ e K) ^ (2 * r K) :=
      fun K hK => Nat.pow_le_pow_right (by have := hn2 K hK; omega) (by have := hr1 K hK; omega)
    have hpos : ∀ K ∈ S, 0 < Nat.card (𝓞 D ⧸ K ^ e K) ^ 2 := fun K hK => by
      have := hn2 K hK; positivity
    have heqprod : ∏ K ∈ S, Nat.card (𝓞 D ⧸ K ^ e K) ^ 2
        = ∏ K ∈ S, Nat.card (𝓞 D ⧸ K ^ e K) ^ (2 * r K) := by
      have hR : ∏ K ∈ S, Nat.card (𝓞 D ⧸ K ^ e K) ^ (2 * r K)
          = p ^ (2 * Module.finrank ℚ D) := by
        rw [show (∏ K ∈ S, Nat.card (𝓞 D ⧸ K ^ e K) ^ (2 * r K))
            = ∏ K ∈ S, Nat.card (Submodule.torsionBySet (𝓞 D) P
              ((K ^ e K : Ideal (𝓞 D)) : Set (𝓞 D))) from
          Finset.prod_congr rfl fun K hK => (hrpow K hK).symm, ← hcardprod, hcard]
      rw [Finset.prod_pow, hringprod, hR, ← pow_mul, Nat.mul_comm]
    have hJeq := eq_of_prod_eq_of_le hpos hfg heqprod hJ
    have h2 := hn2 J hJ
    have h3 := hr1 J hJ
    have := Nat.pow_right_injective h2 hJeq
    omega
  rw [hrlvl I hIS, hkey I hIS]

end Assembly

end LevelFrame

/-! ### Symplectic linear algebra: a nondegenerate alternating form forces
an even dimension

This is the algebraic half of `even_dim_torsion_of_isMaximal` below, and
it is a MATHLIB GAP: there is no "nondegenerate alternating ⇒ even
`finrank`" anywhere in the pin, in `Fermat/FLT/Mathlib/` or in `~/cs/FLT`
(all three greped 2026-07-27), and no skew-symmetric-determinant result
to derive it from either.  `Mathlib/LinearAlgebra/SymplecticGroup.lean`
is about `Sp(2n)` for a GIVEN `n` and says nothing about which spaces
carry a symplectic form.

The proof is the classical hyperbolic-plane induction, run over
`LinearMap.BilinForm.orthogonal` rather than over a chosen symplectic
basis, which is what keeps it short.  Note that mathlib's
`isCompl_span_singleton_orthogonal` and
`restrict_nondegenerate_orthogonal_spanSingleton` both require
`B x x ≠ 0` and are therefore USELESS for an alternating form — that
hypothesis is exactly what alternating denies.  What does apply is
`nondegenerate_restrict_of_disjoint_orthogonal` together with
`orthogonal_orthogonal`, so the induction step only has to exhibit a
hyperbolic plane `⟨x, y⟩` meeting its own orthogonal trivially. -/

/-- **Induction step for `even_finrank_of_isAlt_nondegenerate`**: bounding
the `finrank` by `n` and inducting on `n` keeps the induction inside one
universe, which a direct induction on `Module.finrank K V` would not. -/
theorem even_finrank_of_isAlt_nondegenerate_aux {K : Type*} [Field K] (n : ℕ) :
    ∀ {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (B : LinearMap.BilinForm K V), B.IsAlt → B.Nondegenerate →
      Module.finrank K V ≤ n → Even (Module.finrank K V) := by
  induction n with
  | zero =>
    intro V _ _ _ B _ _ h
    rw [Nat.le_zero.mp h]
    exact ⟨0, rfl⟩
  | succ n ih =>
    intro V _ _ _ B halt hnd hle
    rcases Nat.eq_zero_or_pos (Module.finrank K V) with h0 | hpos
    · rw [h0]; exact ⟨0, rfl⟩
    -- pick `x ≠ 0`, and `y` pairing nontrivially with it
    have hntriv : Nontrivial V := Module.nontrivial_of_finrank_pos hpos
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hy : ∃ y : V, B x y ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hx (hnd.1 x hc)
    obtain ⟨y, hxy⟩ := hy
    have hrefl : B.IsRefl := halt.isRefl
    set W : Submodule K V := Submodule.span K {x, y} with hW
    have hxmem : x ∈ W := Submodule.subset_span (by simp)
    have hymem : y ∈ W := Submodule.subset_span (by simp)
    -- `x, y` span a hyperbolic plane
    have hli : LinearIndependent K ![x, y] := by
      rw [LinearIndependent.pair_iff]
      intro a b hab
      have h1 : a * B x x + b * B x y = 0 := by
        have := congrArg (fun v => B x v) hab
        simpa [map_add, map_smul, smul_eq_mul] using this
      rw [halt.self_eq_zero x, mul_zero, zero_add] at h1
      have hb : b = 0 := by
        rcases mul_eq_zero.mp h1 with h | h
        · exact h
        · exact absurd h hxy
      subst hb
      simp only [zero_smul, add_zero] at hab
      rcases smul_eq_zero.mp hab with h | h
      · exact ⟨h, rfl⟩
      · exact absurd h hx
    have hrank2 : Module.finrank K W = 2 := by
      have hspan : Submodule.span K (Set.range ![x, y]) = W := by
        rw [hW]; congr 1
        simp [Matrix.range_cons, Matrix.range_empty, Set.pair_comm]
      rw [← hspan, finrank_span_eq_card hli]
      simp
    have hdisj : Disjoint W (B.orthogonal W) := by
      rw [Submodule.disjoint_def]
      intro w hwW hwO
      obtain ⟨a, b, rfl⟩ : ∃ a b : K, w = a • x + b • y := by
        rw [hW, Submodule.mem_span_pair] at hwW
        obtain ⟨a, b, hab⟩ := hwW
        exact ⟨a, b, hab.symm⟩
      have h1 : B x (a • x + b • y) = 0 := hwO x hxmem
      have h2 : B y (a • x + b • y) = 0 := hwO y hymem
      have hyx : B y x = -B x y := (LinearMap.BilinForm.IsAlt.neg_eq halt x y).symm
      have e1 : b * B x y = 0 := by
        have h1' : a * B x x + b * B x y = 0 := by
          simpa [map_add, map_smul, smul_eq_mul] using h1
        rw [halt.self_eq_zero x, mul_zero, zero_add] at h1'
        exact h1'
      have e2 : a * B x y = 0 := by
        have h2' : a * B y x + b * B y y = 0 := by
          simpa [map_add, map_smul, smul_eq_mul] using h2
        rw [halt.self_eq_zero y, mul_zero, add_zero, hyx, mul_neg, neg_eq_zero] at h2'
        exact h2'
      have ha : a = 0 := by
        rcases mul_eq_zero.mp e2 with h | h
        · exact h
        · exact absurd h hxy
      have hb : b = 0 := by
        rcases mul_eq_zero.mp e1 with h | h
        · exact h
        · exact absurd h hxy
      rw [ha, hb, zero_smul, zero_smul, add_zero]
    -- the restriction to the orthogonal complement is again nondegenerate alternating
    have hnd' : (B.restrict (B.orthogonal W)).Nondegenerate := by
      refine LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal B hrefl ?_
      rw [LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl W]
      exact hdisj.symm
    have halt' : (B.restrict (B.orthogonal W)).IsAlt := fun w => halt (w : V)
    have hfr : Module.finrank K (B.orthogonal W) = Module.finrank K V - 2 := by
      rw [LinearMap.BilinForm.finrank_orthogonal hnd W, hrank2]
    have hle2 : 2 ≤ Module.finrank K V := hrank2 ▸ Submodule.finrank_le W
    have hstep : Module.finrank K (B.orthogonal W) ≤ n := by omega
    have heven := ih (B.restrict (B.orthogonal W)) halt' hnd' hstep
    rw [hfr] at heven
    obtain ⟨k, hk⟩ := heven
    exact ⟨k + 1, by omega⟩

/-- **A nondegenerate ALTERNATING bilinear form forces an EVEN dimension.**
Absent from mathlib at this pin — see the section note above.  This is the
statement that turns "`A[J]` is a symplectic space over `𝒪_D/J`" into the
parity of its residual rank. -/
theorem even_finrank_of_isAlt_nondegenerate {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (halt : B.IsAlt) (hnd : B.Nondegenerate) :
    Even (Module.finrank K V) :=
  even_finrank_of_isAlt_nondegenerate_aux (Module.finrank K V) B halt hnd le_rfl

/-- **A finite symplectic space over a finite field has `#k ^ (2r)`
elements.**  This is `even_finrank_of_isAlt_nondegenerate` in the
cardinality form that `LevelFrame.card_tors_eq_sq` consumes. -/
theorem exists_card_eq_pow_two_mul_of_isAlt_nondegenerate
    {k M : Type*} [Field k] [Finite k] [AddCommGroup M] [Module k M] [Finite M]
    (B : LinearMap.BilinForm k M) (halt : B.IsAlt) (hnd : B.Nondegenerate) :
    ∃ r, Nat.card M = Nat.card k ^ (2 * r) := by
  classical
  letI := Fintype.ofFinite k
  letI := Fintype.ofFinite M
  haveI : FiniteDimensional k M := Module.Finite.of_finite
  obtain ⟨r, hr⟩ := even_finrank_of_isAlt_nondegenerate B halt hnd
  refine ⟨r, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := k) (V := M), hr, two_mul]

/-! ### The three geometric inputs of the rank count

The audit under `card_torsion_of_isMaximal` below establishes that no
collection of INTEGER counts determines the residual ranks `r_J`, and
invites exactly one refutation: a constraint pinning `r_J` without a
rational-homology input.  PARITY is such a constraint, and
`LevelFrame.card_tors_eq_sq` is the proof that parity plus the integer
count closes the argument.  What is left is these three leaves.  Each is
a UNIVERSAL fact about abelian schemes, reusable well beyond this file. -/

/-! #### The Betti frame: one homology input for all three leaves

Each of the three leaves below was recorded as needing a different deep
theorem — the theorem of the cube for the degree of `[N]`, a
nondegenerate polarized Weil pairing for the parity, and
`End(A) ↪ End(T_p A)` for the nonvanishing.  The FAITHFULNESS CHECK under
`card_torsion_ne_one_of_isMaximal` identified what they actually share:
the single Betti input `dim_ℚ H₁(A_x, ℚ) = 2g`.  `BettiFrame` is that
input, named, and all three leaves are now theorems over it.

WHAT THE FRAME IS.  For a complex abelian variety `A_x` of dimension `g`,
`A_x(ℂ) = (H₁ ⊗ ℝ)/H₁` with `H₁ = H₁(A_x, ℤ)` a lattice of rank `2g`, and
the `I`-torsion is `I⁻¹H₁/H₁ ≅ H₁/IH₁` for every nonzero ideal `I` of
`𝒪_D` (the second isomorphism uses invertibility of `I`, and is not
canonical — which is why the clause below is stated as an equality of
CARDINALITIES rather than of Galois modules).  Everything the three
leaves need is downstream of that, by the commutative algebra in
`Fermat/FLT/Mathlib/RingTheory/DedekindDomain/LatticeQuotient.lean`:

* `rank_ℤ H₁ = 2g` gives `#A[N] = #(H₁/N H₁) = N^(2g)` directly;
* the RANK BRIDGE `rank_ℤ = [D:ℚ] · rank_{𝒪_D}` turns `rank_ℤ H₁ = 2g`
  and `g = [D:ℚ]` into `rank_{𝒪_D} H₁ = 2`, whence
  `#A[I] = #(𝒪_D/I)^2` at every maximal `I` — which is at once the
  PARITY and the NONVANISHING, with no polarization, no Rosati
  positivity and no faithfulness argument anywhere.

WHY IT IS STATED AS CARDINALITIES.  The three consumers are cardinality
statements, so this is exactly what they need, and it is the weakest
clause that supplies them — which makes the geometric leaf beneath
`exists_bettiFrame` (`card_torsion_isMaximal_of_isAlgClosed`) as easy as
it can honestly be.  A successor that
needs the GALOIS module structure of `A[I]` (rather than only its size)
should strengthen `card_torsion` to a `𝒪_D`-linear equivalence
`H₁ ⧸ I H₁ ≃ₗ A[I]`; every consumer below goes through unchanged.

TWO CLAUSES ARE DERIVABLE AND ARE STILL ASSERTED, deliberately.
`Module.IsTorsionFree (𝒪_D) H` follows from `Module.Free ℤ H` by the norm
argument (`a • h = 0` with `a ≠ 0` gives `N(a) • h = 0` with `N(a)` a
nonzero integer), and `Module.Finite (𝒪_D) H` follows from
`Module.Finite ℤ H`.  Both are immediate for anyone constructing `H₁`,
and asserting them here costs the existence leaf nothing while saving two
detours; a successor may prune them.

THE RELATIVE DIMENSION MUST BE PINNED — and this is a FAITHFULNESS
REPAIR, recorded 2026-07-27.  `AbelianSchemeStruct` requires only proper,
smooth and geometrically connected, which the IDENTITY `f = 𝟙 S`
satisfies: an abelian scheme of relative dimension `0`.  Its geometric
fibres are a single point, so `#A[I] = 1` for every `I`, and
`Mult ab (𝒪_D)` exists (the endomorphism ring of the trivial group scheme
is the zero ring, which receives a ring map from anything).  So
`card_torsion_ne_one_of_isMaximal` is **FALSE as previously stated**, and
`hdim` — which its own consumer `card_torsion_of_isMaximal` already
carries and simply did not pass on — is the repair.  It has been added to
both maximal-ideal leaves below and passed at the single call site. -/

open _root_.NumberField in
/-- **A BETTI FRAME for a geometric fibre**: the homology lattice
`H₁(A_x, ℤ)` with its `𝒪_D`-action, its Betti number, and the torsion
counts it computes.  See the section note above for what each clause is
and why it is stated this way. -/
structure BettiFrame {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S) where
  /-- the homology lattice `H₁(A_x, ℤ)` -/
  H : Type u
  [addCommGroup : AddCommGroup H]
  /-- the real multiplication acts on the homology -/
  [module : Module (NumberField.RingOfIntegers D) H]
  [finiteOD : Module.Finite (NumberField.RingOfIntegers D) H]
  [torsionFree : Module.IsTorsionFree (NumberField.RingOfIntegers D) H]
  /-- `H₁` is a LATTICE -/
  [freeInt : Module.Free ℤ H]
  [finiteInt : Module.Finite ℤ H]
  /-- **THE BETTI INPUT**: `dim_ℚ H₁(A_x, ℚ) = 2g`, with `g = [D : ℚ]`
  the relative dimension. -/
  finrank_int : Module.finrank ℤ H = 2 * Module.finrank ℚ D
  /-- **`A[I]` is `H₁/I H₁`**, in cardinality, at every nonzero ideal. -/
  card_torsion : ∀ I : Ideal (NumberField.RingOfIntegers D), I ≠ ⊥ →
    Nat.card (m.torsion x I).1
      = Nat.card (H ⧸ (I • ⊤ : Submodule (NumberField.RingOfIntegers D) H))

attribute [instance] BettiFrame.addCommGroup BettiFrame.module BettiFrame.finiteOD
  BettiFrame.torsionFree BettiFrame.freeInt BettiFrame.finiteInt

namespace LevelFrame

open _root_.NumberField

/-- **From the residual count at every MAXIMAL ideal to the count at
every NONZERO ideal** (PROVEN 2026-07-27).  Pure module theory over
`𝒪_D`: no schemes, no abelian varieties, no rank-two hypothesis beyond
the residual one.

Given, for an `𝒪_D`-module `P`,

* `hsurj` — surjectivity of `·π` from each torsion level onto the
  previous one at every maximal ideal (divisibility), and
* `hres`  — `#P[J] = #(𝒪_D/J)²` at every MAXIMAL `J`,

the same count `#P[I] = #(𝒪_D/I)²` holds at every NONZERO `I`.

THE ARGUMENT is the factorisation `I = ∏_J J^(e_J)` in the Dedekind
domain `𝒪_D`, and it reuses the two pieces the `p`-case already needed:

* `P[I] = ⨁_J P[J^(e_J)]` EXACTLY, because the `J^(e_J)` are pairwise
  comaximal — mathlib's
  `Submodule.isInternal_prime_power_torsion_of_is_torsion_by_ideal`,
  which needs only `I ≠ ⊥`;
* `#P[J^(e_J)] = #(𝒪_D/J)^(2·e_J) = #(𝒪_D/J^(e_J))²` by the tower lemma
  `card_tors_pow` at `r = 2` together with `card_quotient_pow`;
* `∏_J #(𝒪_D/J^(e_J)) = #(𝒪_D/I)` by multiplicativity of
  `Ideal.absNorm`.

WHY IT IS NOT `card_tors_eq_sq`.  That lemma *derives* the residual rank
`r_J = 2` from parity, nonvanishing and the integer count at a rational
prime `p`, and its conclusion is only at a maximal ideal.  This one takes
the residual count as given and *propagates* it to all ideals.  The two
compose in the obvious way but neither implies the other. -/
theorem card_tors_eq_sq_of_ne_bot
    {D : Type*} [Field D] [NumberField D]
    {P : Type*} [AddCommGroup P] [Module (𝓞 D) P]
    (hsurj : ∀ J : Ideal (𝓞 D), J.IsMaximal → ∀ π ∈ J, π ∉ J ^ 2 →
      ∀ (k : ℕ) (y : P), y ∈ Submodule.torsionBySet (𝓞 D) P ((J ^ k : Ideal (𝓞 D)) : Set (𝓞 D)) →
        ∃ z ∈ Submodule.torsionBySet (𝓞 D) P ((J ^ (k + 1) : Ideal (𝓞 D)) : Set (𝓞 D)),
          π • z = y)
    (hres : ∀ J : Ideal (𝓞 D), J.IsMaximal →
      Nat.card (Submodule.torsionBySet (𝓞 D) P ((J : Ideal (𝓞 D)) : Set (𝓞 D)))
        = Nat.card (𝓞 D ⧸ J) ^ 2)
    (I : Ideal (𝓞 D)) (hI0 : I ≠ ⊥) :
    Nat.card (Submodule.torsionBySet (𝓞 D) P ((I : Ideal (𝓞 D)) : Set (𝓞 D)))
      = Nat.card (𝓞 D ⧸ I) ^ 2 := by
  classical
  set S : Finset (Ideal (𝓞 D)) := (UniqueFactorizationMonoid.factors I).toFinset with hSdef
  set e : Ideal (𝓞 D) → ℕ := fun J => (UniqueFactorizationMonoid.factors I).count J with hedef
  have hprod : ∏ J ∈ S, J ^ e J = I := by
    rw [hSdef, hedef, ← Finset.prod_multiset_count, ← associated_iff_eq]
    exact UniqueFactorizationMonoid.factors_prod hI0
  have hprime : ∀ J ∈ S, Prime J := fun J hJ =>
    UniqueFactorizationMonoid.prime_of_factor J (Multiset.mem_toFinset.mp hJ)
  have hJbot : ∀ J ∈ S, J ≠ ⊥ := fun J hJ => (hprime J hJ).ne_zero
  have hmax : ∀ J ∈ S, J.IsMaximal := fun J hJ =>
    (Ideal.isPrime_of_prime (hprime J hJ)).isMaximal (hJbot J hJ)
  have hlepow : ∀ J ∈ S, I ≤ J ^ e J := by
    intro J hJ
    rw [← hprod]
    exact Ideal.dvd_iff_le.mp (Finset.dvd_prod_of_mem _ hJ)
  -- ### the CRT splitting of `P[I]`
  have hequiv : ∀ K : Ideal (𝓞 D), I ≤ K →
      Nat.card (Submodule.torsionBySet (𝓞 D)
          (Submodule.torsionBySet (𝓞 D) P ((I : Ideal (𝓞 D)) : Set (𝓞 D))) (K : Set (𝓞 D)))
        = Nat.card (Submodule.torsionBySet (𝓞 D) P ((K : Ideal (𝓞 D)) : Set (𝓞 D))) := by
    intro K hK
    refine Nat.card_congr ⟨fun z => ⟨(z.1 : P), ?_⟩,
      fun y => ⟨⟨(y : P), tors_mono hK y.2⟩, ?_⟩, fun _ => rfl, fun _ => rfl⟩
    · rw [mem_tors_iff]
      intro a ha
      have h := (mem_tors_iff (P := (Submodule.torsionBySet (𝓞 D) P
        ((I : Ideal (𝓞 D)) : Set (𝓞 D)))) K z.1).mp z.2 a ha
      simpa using congrArg Subtype.val h
    · rw [mem_tors_iff]
      intro a ha
      exact Subtype.ext (by simpa using (mem_tors_iff K (y : P)).mp y.2 a ha)
  have hint := Submodule.isInternal_prime_power_torsion_of_is_torsion_by_ideal
    (M := (Submodule.torsionBySet (𝓞 D) P ((I : Ideal (𝓞 D)) : Set (𝓞 D)))) hI0
    (Submodule.torsionBySet_isTorsionBySet ((I : Ideal (𝓞 D)) : Set (𝓞 D)))
  have hcardprod : Nat.card (Submodule.torsionBySet (𝓞 D) P ((I : Ideal (𝓞 D)) : Set (𝓞 D)))
      = ∏ J ∈ S, Nat.card (Submodule.torsionBySet (𝓞 D) P
          ((J ^ e J : Ideal (𝓞 D)) : Set (𝓞 D))) := by
    have h1 := Nat.card_congr (Equiv.ofBijective _ hint).symm
    rw [h1, Nat.card_congr (DirectSum.linearEquivFunOnFintype (𝓞 D)
      (ι := { x // x ∈ S }) (M := fun J : S =>
        (Submodule.torsionBySet (𝓞 D)
          (Submodule.torsionBySet (𝓞 D) P ((I : Ideal (𝓞 D)) : Set (𝓞 D)))
          (((J : Ideal (𝓞 D)) ^ e (J : Ideal (𝓞 D)) : Ideal (𝓞 D)) : Set (𝓞 D))))).toEquiv,
      Nat.card_pi]
    rw [← Finset.prod_coe_sort S (fun J => Nat.card (Submodule.torsionBySet (𝓞 D) P
      ((J ^ e J : Ideal (𝓞 D)) : Set (𝓞 D))))]
    exact Finset.prod_congr rfl fun J _ => hequiv _ (hlepow J J.2)
  -- ### the count at each prime power, from the tower lemma at `r = 2`
  have hper : ∀ J ∈ S, Nat.card (Submodule.torsionBySet (𝓞 D) P
      ((J ^ e J : Ideal (𝓞 D)) : Set (𝓞 D))) = Nat.card (𝓞 D ⧸ J ^ e J) ^ 2 := by
    intro J hJ
    obtain ⟨π, hπ, hπ2⟩ := exists_mem_notMem_sq_of_isMaximal (hmax J hJ) (hJbot J hJ)
    rw [card_tors_pow J (hmax J hJ) (hJbot J hJ) hπ hπ2
      (hsurj J (hmax J hJ) π hπ hπ2) 2 (hres J (hmax J hJ)) (e J),
      card_quotient_pow, ← pow_mul]
    ring_nf
  -- ### the same product, computed in the RING
  have hringprod : ∏ J ∈ S, Nat.card (𝓞 D ⧸ J ^ e J) = Nat.card (𝓞 D ⧸ I) := by
    have h1 : ∏ J ∈ S, Ideal.absNorm (J ^ e J) = Ideal.absNorm I := by
      rw [← map_prod, hprod]
    simpa [Ideal.absNorm_apply, Submodule.cardQuot_apply] using h1
  rw [hcardprod, Finset.prod_congr rfl hper, Finset.prod_pow, hringprod]

end LevelFrame

/-! #### Base change of a multiplication, and the reduction of the Betti
input to an abelian VARIETY over an algebraically closed field

The residue of `exists_bettiFrame` below is a single statement about the
torsion of a geometric FIBRE of `f : A ⟶ S`.  Every classical source
states it about an abelian VARIETY over an algebraically closed field,
and the two are separated by nothing but base change: the geometric
fibre of `f` at `x : Spec F ⟶ S` is the abelian scheme
`pullback.snd f (specAlgClos F ≫ x)` over `Spec F̄`, and its `F̄`-points
are the geometric points of the fibre.

`AbelianSchemeStruct.baseChange`
(`Modularity/AbelianSchemeIsogeny.lean`) already transports the group
law.  What was missing — and is supplied here — is the same transport
for the real multiplication, `Mult.baseChange`, together with the one
consequence the count needs: `Mult.cardTorsion_baseChange`, that the
`I`-torsion count of the base change over `h` is the `I`-torsion count of
the original over `h ≫ g`.  Nothing here is specific to abelian
varieties or to number fields; it is the `Mult` analogue of the six
`RelPoint.baseChange*` lemmas.
-/

section FibreReduction

open _root_.CategoryTheory.Limits

variable {A S : Scheme.{u}} {f : A ⟶ S}

namespace Mult

variable {ab : AbelianSchemeStruct f} {R : Type u} [CommRing R]

/-- **The number of `I`-torsion relative points over a base point `g`**,
as a bare natural number.  Bundling the two `letI`-bound instances into a
definition is what lets the torsion count be compared across a change of
base point, where the module structures on the two sides are literally
different instances on literally different types. -/
noncomputable def cardTorsion (m : Mult ab R) {T : Scheme.{u}} (g : T ⟶ S) (I : Ideal R) : ℕ :=
  letI := ab.addCommGroup g
  letI := m.module g
  Nat.card (Submodule.torsionBySet R (RelPoint f g) (I : Set R))

/-- `Mult.torsion` IS `Mult.cardTorsion` at the geometric base point —
the two are the same set, so this is `rfl`. -/
theorem cardTorsion_geomFibre (m : Mult ab R) {F : Type u} [Field F]
    (x : Spec (CommRingCat.of F) ⟶ S) (I : Ideal R) :
    Nat.card (m.torsion x I).1 = m.cardTorsion (specAlgClos F ≫ x) I := rfl

/-- **Membership in the `I`-torsion, unfolded**, at an ARBITRARY base
point: the `mem_torsion_iff` above is this at the geometric one. -/
theorem mem_torsionBySet_iff (m : Mult ab R) {T : Scheme.{u}} (g : T ⟶ S) (I : Ideal R)
    (y : RelPoint f g) :
    letI := ab.addCommGroup g
    letI := m.module g
    y ∈ Submodule.torsionBySet R (RelPoint f g) (I : Set R) ↔
      ∀ a ∈ I, m.act a y = ab.zero g := by
  letI := ab.addCommGroup g
  letI := m.module g
  constructor
  · intro hy a ha
    exact (Submodule.mem_torsionBySet_iff _ _).mp hy ⟨a, ha⟩
  · intro h
    exact (Submodule.mem_torsionBySet_iff _ _).mpr fun a => h a a.2

/-- **Base change of a multiplication along `g : T ⟶ S`**: the exact
`Mult` analogue of `AbelianSchemeStruct.baseChange`, and proven the same
way — conjugate by the bijection
`RelPoint (pullback.snd f g) h ≃ RelPoint f (h ≫ g)` and read every
axiom off the corresponding axiom of `m`. -/
noncomputable def baseChange (m : Mult ab R) {T : Scheme.{u}} (g : T ⟶ S) :
    Mult (ab.baseChange g) R where
  act := fun {_} {_} a x =>
    RelPoint.baseChangeUp g (m.act a (RelPoint.baseChangeDown g x))
  act_add := by
    intro U h a b y
    simp only [AbelianSchemeStruct.baseChange_add, RelPoint.baseChangeDown_baseChangeUp]
    rw [m.act_add]
  act_mul := by
    intro U h a b y
    rw [RelPoint.baseChangeDown_baseChangeUp, m.act_mul]
  act_one := by
    intro U h y
    rw [m.act_one, RelPoint.baseChangeUp_baseChangeDown]
  act_addPt := by
    intro U h a y z
    simp only [AbelianSchemeStruct.baseChange_add, RelPoint.baseChangeDown_baseChangeUp]
    rw [m.act_addPt]
  pre_act := by
    intro U' U h k k' hk a y
    apply RelPoint.baseChangeDown_injective g
    simp only [RelPoint.baseChangeDown_pre, RelPoint.baseChangeDown_baseChangeUp]
    exact m.pre_act h _ a _

/-- The defining equation of `Mult.baseChange`. -/
theorem baseChange_act (m : Mult ab R) {T : Scheme.{u}} (g : T ⟶ S)
    {U : Scheme.{u}} {h : U ⟶ T} (a : R) (y : RelPoint (pullback.snd f g) h) :
    (m.baseChange g).act a y
      = RelPoint.baseChangeUp g (m.act a (RelPoint.baseChangeDown g y)) := rfl

/-- **`baseChangeDown` is `R`-linear**, which is the whole point of
`Mult.baseChange`. -/
@[simp] theorem baseChangeDown_act (m : Mult ab R) {T : Scheme.{u}} (g : T ⟶ S)
    {U : Scheme.{u}} {h : U ⟶ T} (a : R) (y : RelPoint (pullback.snd f g) h) :
    RelPoint.baseChangeDown g ((m.baseChange g).act a y)
      = m.act a (RelPoint.baseChangeDown g y) :=
  RelPoint.baseChangeDown_baseChangeUp g _

/-- **`baseChangeDown` sends zero to zero.** -/
theorem baseChangeDown_zero (ab : AbelianSchemeStruct f) {T : Scheme.{u}} (g : T ⟶ S)
    {U : Scheme.{u}} (h : U ⟶ T) :
    RelPoint.baseChangeDown g ((ab.baseChange g).zero h) = ab.zero (h ≫ g) := by
  rw [AbelianSchemeStruct.baseChange_zero, RelPoint.baseChangeDown_baseChangeUp]

/-- **THE TORSION COUNT IS INSENSITIVE TO BASE CHANGE**: `A[I]` computed
on `A ×_S T` over `h` is `A[I]` computed on `A` over `h ≫ g`.  The
bijection is `RelPoint.baseChangeDown`, which is additive and `R`-linear,
so it carries torsion to torsion in both directions. -/
theorem cardTorsion_baseChange (m : Mult ab R) {T : Scheme.{u}} (g : T ⟶ S)
    {U : Scheme.{u}} (h : U ⟶ T) (I : Ideal R) :
    (m.baseChange g).cardTorsion h I = m.cardTorsion (h ≫ g) I := by
  letI := (ab.baseChange g).addCommGroup h
  letI := (m.baseChange g).module h
  letI := ab.addCommGroup (h ≫ g)
  letI := m.module (h ≫ g)
  unfold cardTorsion
  refine Nat.card_congr ⟨fun y => ⟨RelPoint.baseChangeDown g y.1, ?_⟩,
    fun z => ⟨RelPoint.baseChangeUp g z.1, ?_⟩, fun y => ?_, fun z => ?_⟩
  · refine (mem_torsionBySet_iff m (h ≫ g) I _).mpr fun a ha => ?_
    rw [← baseChangeDown_act m g a y.1,
      (mem_torsionBySet_iff (m.baseChange g) h I y.1).mp y.2 a ha]
    exact baseChangeDown_zero ab g h
  · refine (mem_torsionBySet_iff (m.baseChange g) h I _).mpr fun a ha => ?_
    apply RelPoint.baseChangeDown_injective g
    rw [baseChangeDown_act m g a _, RelPoint.baseChangeDown_baseChangeUp,
      (mem_torsionBySet_iff m (h ≫ g) I z.1).mp z.2 a ha, baseChangeDown_zero ab g h]
  · exact Subtype.ext (RelPoint.baseChangeUp_baseChangeDown g y.1)
  · exact Subtype.ext (RelPoint.baseChangeDown_baseChangeUp g z.1)

end Mult

open _root_.NumberField in
/-- **`#A[J] = #(𝒪_D/J)²` FOR AN ABELIAN VARIETY WITH REAL
MULTIPLICATION OVER AN ALGEBRAICALLY CLOSED FIELD OF CHARACTERISTIC
ZERO** (sorry leaf, created 2026-07-27; it is the whole geometric content
of `exists_bettiFrame` below, hoisted out of a sorried `have` and
restated over a FIELD.  Mumford *Abelian Varieties* §1, §6, §19, Milne
*Abelian Varieties* I.1–I.7, Shimura, Goren *Lectures on Hilbert Modular
Varieties* I.1).

`A` is an abelian variety over an algebraically closed field `K` of
characteristic zero, of dimension `g = [D : ℚ]`, with an action of `𝒪_D`;
`A(K) = RelPoint fK (𝟙 (Spec K))` is its group of points.  The claim is
that its `J`-torsion has exactly `#(𝒪_D/J)²` points, at every maximal
`J`.

**WHY IT IS TRUE, and what the residue actually is.**  `H₁(A, ℤ)` is a
lattice of rank `2g` carrying the `𝒪_D`-action, and `A[I] ≅ H₁/I H₁` for
every nonzero `I`.  Everything after that is FREE and needs no
hypothesis beyond `[D : ℚ] = g`:

* `H₁ ⊗ ℚ` is a `D`-vector space of `ℚ`-dimension `2g = 2[D : ℚ]`, hence
  of `D`-dimension exactly `2` — this is where the relative dimension is
  consumed, and it pins ALL the local ranks at once;
* `H₁` is a finitely generated torsion-free module over the Dedekind
  domain `𝒪_D`, hence projective, hence `≅ 𝒪_D ⊕ 𝔞` with `𝔞`
  invertible, so `H₁/J H₁ ≅ (𝒪_D/J)²`.

So the residue is exactly the first Betti number, `dim_ℚ H₁(A, ℚ) = 2g`,
and the three classical inputs it used to be cut into (the degree of
`[N]`, parity from a polarization, nonvanishing from
`End(A) ↪ End(T_p A)`) are three DIFFERENT ways of reaching the same
place; see the docstring of `exists_bettiFrame` for all three, and the
audit under `card_torsion_ne_one_of_isMaximal` for why no combination of
integer counts can replace the rational input.

**`[CharZero K]` IS LOAD-BEARING, AND NOTHING IN THE OLD PHRASING SHOWED
IT** (recorded 2026-07-27, at the hoist).  In characteristic `p` the
statement is FALSE at every `J` above `p`: for an ordinary abelian
variety `#A[p](K) = p^g`, not `p^(2g)`, and correspondingly `A[J]` drops
rank at `J ∣ p`.  In the scheme-level form the hypothesis arrives ONLY
through `[NumberField F]` — the geometric fibre is taken over
`F̄` — which is why the dependence deserves to be written down here
rather than inferred.  A successor must not weaken it; the honest
weakening, if one is ever wanted, is `J` above a residue characteristic
INVERTIBLE in `K`, not `IsAlgClosed` alone.

**`IsTotallyReal D` IS NOT NEEDED AND IS DELIBERATELY ABSENT.**  The
consumer has it; the classical proof does not use it.  Nor is
faithfulness of `𝒪_D → End(A)` a hypothesis: it is automatic here, since
a nonzero kernel would make `𝒪_D/ker` a FINITE ring mapping unitally
into the torsion-free `End(A)`, and `End(A) ≠ 0` because `g ≥ 1`.
Recording either as a hypothesis would record a dependence that does not
exist.

**WHAT THE HOIST BUYS, AND WHAT IT DOES NOT.**  It does not touch the
mathematics: the residue is unchanged and still needs one of the three
routes, each of which is a mathlib-scale build (there is no degree of a
finite locally free morphism, no theorem of the cube, no singular or
étale homology at this pin).  What it buys is that the statement is now
the one the sources prove — an abelian VARIETY over an algebraically
closed field, its group of points, no relative bookkeeping — and that
the descent from it to the geometric fibre of an abelian SCHEME is
PROVEN, by `Mult.cardTorsion_baseChange` above.  A prover here may work
entirely over `K`.

**DO NOT ALSO DISPATCH AT `card_torsion_of_isMaximal`.**  That theorem's
statement is this one at the geometric base point, and the whole
five-theorem cluster between them (`exists_bettiFrame`,
`card_torsion_span_natCast`, `even_dim_torsion_of_isMaximal`,
`card_torsion_ne_one_of_isMaximal`, `card_torsion_of_isMaximal`) is
PROVEN over this single leaf.  They are one node, not five. -/
theorem card_torsion_isMaximal_of_isAlgClosed {X : Scheme.{u}} {K : Type u} [Field K]
    [IsAlgClosed K] [CharZero K] {fK : X ⟶ Spec (CommRingCat.of K)}
    {abK : AbelianSchemeStruct fK} {D : Type u} [Field D] [NumberField D]
    (m : Mult abK (NumberField.RingOfIntegers D))
    (hdim : SmoothOfRelativeDimension (Module.finrank ℚ D) fK)
    (J : Ideal (NumberField.RingOfIntegers D)) (hJ : J.IsMaximal) :
    m.cardTorsion (𝟙 (Spec (CommRingCat.of K))) J
      = Nat.card (NumberField.RingOfIntegers D ⧸ J) ^ 2 := sorry

end FibreReduction

open _root_.NumberField in
/-- **The homology of a geometric fibre exists** (PROVEN 2026-07-27 over
the single geometric leaf `card_torsion_isMaximal_of_isAlgClosed` above,
which is what the sorried `have` of the 2026-07-27 decomposition became
when it was hoisted to a named statement over an algebraically closed
FIELD.  Mumford *Abelian Varieties* §1, §6, §19, Milne *Abelian
Varieties* I.1–I.7, Silverman *AEC* VI for the elliptic case).

**NO HOMOLOGY IS NEEDED, AND THIS IS THE POINT OF THE DECOMPOSITION.**
The previous docstring said a prover must build the uniformization
`A(ℂ) = (H₁ ⊗ ℝ)/H₁`, or étale homology `H₁^{ét}(A, ẑ)`, neither of
which exists at this pin.  That is not so.  `BettiFrame` is an
EXISTENTIAL over the module `H`, and every structural clause of it —
`Module.Finite`, `Module.IsTorsionFree`, `Module.Free ℤ`,
`Module.Finite ℤ` and the Betti number `finrank_int` — is satisfied
outright by the FREE module `H := Fin 2 → 𝒪_D`, whose `ℤ`-rank is
`2 · [D:ℚ]` by `NumberField.RingOfIntegers.rank`.  So the whole content
of the leaf is the single `card_torsion` clause, and the homology is
merely one way of producing it.

WHAT ACTUALLY REMAINS, in full: `#A[J] = #(𝒪_D/J)²` at every MAXIMAL
`J` — and that is now the NAMED leaf
`card_torsion_isMaximal_of_isAlgClosed` above, stated over an
algebraically closed field of characteristic zero, with the descent from
it to the geometric fibre PROVEN here by `Mult.cardTorsion_baseChange`.
Two further proven steps carry it to the stated frame:

* `LevelFrame.card_tors_eq_sq_of_ne_bot` (above) propagates the maximal
  count to every NONZERO ideal, by the factorisation `I = ∏ J^(e_J)`,
  the CRT splitting of the torsion, and the tower lemma — consuming the
  already-proven divisibility leaf
  `exists_mem_torsion_act_uniformizer_eq`;
* `Module.card_quotient_ideal_smul_top_of_basis` computes
  `#((Fin 2 → 𝒪_D) ⧸ I·(Fin 2 → 𝒪_D)) = #(𝒪_D/I)²` at an ARBITRARY
  ideal (the Dedekind lemma next to it needs `I` maximal, which is not
  enough here, since `Ideal.span {(N : 𝒪_D)}` is what
  `card_torsion_span_natCast` feeds in).

**CIRCULARITY WARNING — DO NOT DISCHARGE THE LEAF FROM THIS FILE.**  Its
statement is that of `card_torsion_of_isMaximal` below, which is proven
from `card_torsion_span_natCast`, `even_dim_torsion_of_isMaximal` and
`card_torsion_ne_one_of_isMaximal` — and all three of those are proven
from THIS theorem.  So the whole downstream chain is unavailable as an
input to the leaf; citing any of it would close the loop and prove
nothing.  This is not a defect introduced by the decomposition: it is a
fact about the cluster that the decomposition makes visible, namely that
`BettiFrame` carries exactly the information of
`card_torsion_of_isMaximal` and no more.  The five theorems named here
are ONE node with one owner, not five.

THE THREE HONEST ROUTES, all of which are inputs from OUTSIDE this
cluster, and any ONE of which closes it:

1. the classical triple, recombined by `LevelFrame.card_tors_eq_sq`:
   the integer count `#A[p] = p^(2g)` (theorem of the cube — Mumford §6,
   §18; the missing piece is a `degree` for the finite locally free
   `[N]` of `Modularity/AbelianSchemeIsogeny.lean`), PARITY from a
   nondegenerate `𝒪_D`-linear polarized Weil pairing (Mumford §16, §20,
   §23 — note `PolarizationStruct` in `Modularity/AbelianScheme.lean` is
   satisfied by the constant zero map and must be repaired first), and
   NONVANISHING from `End(A) ↪ End(T_p A)` (Mumford §19);
2. `H₁(A_x, ℤ)` itself — singular homology after an embedding
   `F̄ ↪ ℂ`, or étale homology `H₁^{ét}(A, ẑ)`.  This remains a correct
   route and it is the one the section note above describes; it is now
   optional rather than forced;
3. the rational Tate module: `V_ℓ(A)` free of rank `2` over `D ⊗ ℚ_ℓ`.

WHY `hdim` IS PRESENT, AND WHERE IT IS CONSUMED.  It is what makes the
count `#(𝒪_D/J)²` rather than `1`: without it the ambient statement is
FALSE at relative dimension `0`, where `f = 𝟙 S` gives one-point
geometric fibres (see the section note above).  It is therefore passed
INTO the geometric leaf as an explicit hypothesis rather than left
dangling — and it survives the base change to the fibre because
`SmoothOfRelativeDimension n` is stable under base change in mathlib
(`smoothOfRelativeDimension_isStableUnderBaseChange`).  Note that
nothing else in the assembly uses it: the free witness `Fin 2 → 𝒪_D` and
the propagation lemma are dimension-blind, exactly as they should be.

WHERE CHARACTERISTIC ZERO ENTERS, since it is invisible in the statement
of this theorem: only through `[NumberField F]`, which makes the
geometric fibre live over the characteristic-zero field `F̄`.  The
geometric leaf carries it as `[CharZero K]`, where it is load-bearing —
see that leaf's docstring. -/
theorem exists_bettiFrame {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (hdim : SmoothOfRelativeDimension (Module.finrank ℚ D) f) :
    Nonempty (BettiFrame m x) := by
  classical
  letI : AddCommGroup (GeomFibrePt f x) := ab.addCommGroup (specAlgClos F ≫ x)
  letI : Module (NumberField.RingOfIntegers D) (GeomFibrePt f x) :=
    m.module (specAlgClos F ≫ x)
  /- **THE ONE GEOMETRIC INPUT, read off the fibre.**  The `J`-torsion of
  the geometric fibre is the `J`-torsion of the abelian variety
  `A ×_S Spec F̄` over `F̄` — `Mult.cardTorsion_baseChange` — and that is
  the leaf `card_torsion_isMaximal_of_isAlgClosed`.  The relative
  dimension travels with the base change, and `F̄` has characteristic
  zero because `F` is a number field. -/
  have hres : ∀ J : Ideal (NumberField.RingOfIntegers D), J.IsMaximal →
      Nat.card (m.torsion x J).1
        = Nat.card (NumberField.RingOfIntegers D ⧸ J) ^ 2 := by
    intro J hJ
    haveI : CharZero (AlgebraicClosure F) :=
      charZero_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective
    haveI hdim' : SmoothOfRelativeDimension (Module.finrank ℚ D)
        (CategoryTheory.Limits.pullback.snd f (specAlgClos F ≫ x)) := by
      haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := Module.finrank ℚ D)
      exact MorphismProperty.pullback_snd f (specAlgClos F ≫ x) hdim
    have h := card_torsion_isMaximal_of_isAlgClosed (K := AlgebraicClosure F)
      (m.baseChange (specAlgClos F ≫ x)) hdim' J hJ
    rw [Mult.cardTorsion_baseChange m (specAlgClos F ≫ x) (𝟙 _) J, Category.id_comp] at h
    rw [Mult.cardTorsion_geomFibre m x J]
    exact h
  have hall : ∀ I : Ideal (NumberField.RingOfIntegers D), I ≠ ⊥ →
      Nat.card (m.torsion x I).1
        = Nat.card (NumberField.RingOfIntegers D ⧸ I) ^ 2 := fun I hI =>
    LevelFrame.card_tors_eq_sq_of_ne_bot (P := GeomFibrePt f x)
      (fun J hJ π hπ hπ2 k y hy =>
        exists_mem_torsion_act_uniformizer_eq m x J hJ π hπ hπ2 k y hy)
      hres I hI
  refine ⟨{ H := Fin 2 → NumberField.RingOfIntegers D
            finrank_int := ?_
            card_torsion := fun I hI => ?_ }⟩
  · rw [Module.finrank_pi_fintype ℤ (M := fun _ : Fin 2 => NumberField.RingOfIntegers D)]
    simp [NumberField.RingOfIntegers.rank D, two_mul]
  · rw [hall I hI, Module.card_quotient_ideal_smul_top_of_basis
      (Pi.basisFun (NumberField.RingOfIntegers D) (Fin 2)) I]
    simp

open _root_.NumberField in
/-- **A Betti frame has `𝒪_D`-rank two.**  This is the rank bridge
`rank_ℤ = [D:ℚ] · rank_{𝒪_D}` applied to the Betti number `2 · [D:ℚ]`,
and it is what makes the residual rank of `A[I]` both EVEN and NONZERO. -/
theorem BettiFrame.finrank_eq_two {A S : Scheme.{u}} {f : A ⟶ S}
    {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D]
    {m : Mult ab (NumberField.RingOfIntegers D)}
    {F : Type u} [Field F] [NumberField F]
    {x : Spec (CommRingCat.of F) ⟶ S} (bf : BettiFrame m x) :
    Module.finrank (NumberField.RingOfIntegers D) bf.H = 2 := by
  have hb := Module.finrank_int_eq_finrank_ringOfIntegers_mul D bf.H
  rw [bf.finrank_int, mul_comm 2 (Module.finrank ℚ D)] at hb
  have hg : Module.finrank ℚ D ≠ 0 := Module.finrank_pos.ne'
  exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hg) hb).symm

open _root_.NumberField in
/-- **`#A[I] = #(𝒪_D/I)²` at a maximal ideal, from a Betti frame.**  This
is the common engine of the two maximal-ideal leaves below: parity is the
exponent `2` being even, nonvanishing is it being nonzero. -/
theorem BettiFrame.card_torsion_isMaximal {A S : Scheme.{u}} {f : A ⟶ S}
    {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D]
    {m : Mult ab (NumberField.RingOfIntegers D)}
    {F : Type u} [Field F] [NumberField F]
    {x : Spec (CommRingCat.of F) ⟶ S} (bf : BettiFrame m x)
    (I : Ideal (NumberField.RingOfIntegers D)) (hI : I.IsMaximal) :
    Nat.card (m.torsion x I).1
      = Nat.card (NumberField.RingOfIntegers D ⧸ I) ^ 2 := by
  haveI : I.IsMaximal := hI
  have hIbot : I ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField hI (NumberField.RingOfIntegers.not_isField D)
  haveI : Finite (NumberField.RingOfIntegers D ⧸ I) :=
    Ring.HasFiniteQuotients.finiteQuotient hIbot
  rw [bf.card_torsion I hIbot,
    Module.card_quotient_smul_top_of_isDedekindDomain (M := bf.H) I,
    bf.finrank_eq_two]

open _root_.NumberField in
/-- **`#A[N] = N^(2g)`: the degree of `[N]`, in characteristic zero**
(PROVEN 2026-07-27 over the single geometric leaf `exists_bettiFrame`;
see STATUS below.  The references — Mumford *Abelian Varieties* §6, the
theorem of the cube, and §18, Milne *Abelian Varieties* I.7 — describe
the route that was NOT taken).

`A_x` is an abelian variety of dimension `g = [D : ℚ]` over an
algebraically closed field of characteristic zero — that is `hdim`
together with the properness, smoothness and connectedness carried by
`ab` — and `[N]` is an isogeny of degree `N^(2g)`, étale in
characteristic zero, so its kernel has exactly `N^(2g)` geometric points.

WHAT ALREADY EXISTS, and what is genuinely missing.
`Modularity/AbelianSchemeIsogeny.lean` presents `[N]` as **finite locally
free**: `flat_mulByNat`, `finite_preimage_mulByNat`,
`surjective_mulByNat` and `locallyOfFinitePresentation_mulByNat` are all
PROVEN there.  What is missing is only the DEGREE — there is no `degree`
of a finite locally free morphism at this pin, and no theorem of the
cube.  So this leaf is `AbelianSchemeIsogeny.lean`'s natural successor
rather than a fresh development.

NOTE THE REAL MULTIPLICATION IS NOT USED.  `m` enters only to phrase the
statement through `Mult.torsion`; the content is about `[N]` on `A`, and
`Ideal.span {(N : 𝒪_D)}`-torsion IS `N`-torsion because the ideal is
generated by `N`.  A successor may freely restate it over `ab` alone.

AN AVAILABLE CUT THAT REMOVES THE `∀ N` (recorded 2026-07-27; NOT taken
here, because it does not remove the degree and so is only worth doing if
a prover is actually going to attack the prime case).  The statement for
ALL `N` follows from the PRIME case `#A[p] = p^(2g)` by pure module
algebra, using two things that already exist:

* DIVISIBILITY — `exists_comp_mulByNat_eq` (with `surjective_mulByNat`)
  gives that `[n]` is surjective on geometric points.  Then `[p]` maps
  `A[p^(k+1)]` ONTO `A[p^k]` with kernel `A[p]`, so
  `#A[p^(k+1)] = #A[p^k] · #A[p]`, whence `#A[p^k] = (#A[p])^k`.  This is
  exactly the shape of `LevelFrame.card_tors_pow`, already proven above
  for ideals from a uniformizer-surjectivity hypothesis of the same form.
* CRT — `A[mn] ≅ A[m] ⊕ A[n]` for coprime `m, n`, i.e.
  `Submodule.isInternal_prime_power_torsion_of_is_torsion_by_ideal`,
  already used in `LevelFrame.card_tors_eq_sq`'s proof.

So the residue after that cut is a SINGLE geometric statement,
`#A[p] = p^(2g)` at a prime — and it still needs the degree of `[p]`,
i.e. the theorem of the cube.  That is the honest bottom: the cut
narrows the surface, it does not open a route.

THE OTHER ROUTE, and it is shared with the two sibling leaves: build
`H₁(A_x, ℤ)` and its Betti number `2g`.  See the FAITHFULNESS CHECK under
`card_torsion_ne_one_of_isMaximal` below — one homology development
closes all three of these leaves at once, and nothing else does.

STATUS 2026-07-27 — **PROVEN**, by exactly that route.  The theorem of the
cube is NOT needed and neither is any `degree` API: over a Betti frame
`A[N] = H₁/N H₁` and `H₁` is a lattice of rank `2g`, so the count is
`Module.card_quotient_ideal_span_natCast_smul_top`, whose whole content is
that `(N : 𝒪_D)·H₁` and `N·H₁` are the same subgroup.  The residual
geometric input is `exists_bettiFrame` above.  The `∀ N`-removing cut
recorded above is therefore also unnecessary and is left only as a record
of what was tried. -/
theorem card_torsion_span_natCast
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (hdim : SmoothOfRelativeDimension (Module.finrank ℚ D) f)
    (N : ℕ) (hN : N ≠ 0) :
    Nat.card (m.torsion x (Ideal.span {(N : NumberField.RingOfIntegers D)})).1
      = N ^ (2 * Module.finrank ℚ D) := by
  classical
  obtain ⟨bf⟩ := exists_bettiFrame m x hdim
  have hNbot : (Ideal.span {(N : NumberField.RingOfIntegers D)}) ≠ ⊥ := by
    simp only [ne_eq, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact hN
  rw [bf.card_torsion _ hNbot,
    Module.card_quotient_ideal_span_natCast_smul_top (Module.Free.chooseBasis ℤ bf.H) N,
    ← Module.finrank_eq_card_chooseBasisIndex, bf.finrank_int]

open _root_.NumberField in
/-- **The residual rank is EVEN at every maximal `J`** (PROVEN 2026-07-27
over the single geometric leaf `exists_bettiFrame`; see STATUS below.  The
POLARIZATION route below — Mumford *Abelian Varieties* §16, §20, §23 — was
NOT taken and is retained only as a record).

This is the input that defeats the counterexample of the audit below:
`M₁` there has `r_{J₁} = 1`, so parity alone excludes it, and parity is
drawn from the polarization rather than from `H₁(A, ℚ)`.

THE ARGUMENT.  An `𝒪_D`-linear polarization `λ : A ⟶ A^∨` induces, via
the canonical Weil pairing on `A × A^∨`, an `𝒪_D`-bilinear ALTERNATING
pairing on the `J`-torsion — that is exactly
`PolarizationStruct.pairing` together with `pairing_add_left`,
`pairing_add_right`, `pairing_self` and `pairing_act` in
`Modularity/AbelianScheme.lean`, all PROVEN there from the axioms.  If
the pairing is moreover NONDEGENERATE, `A[J]` is a symplectic vector
space over the residue field `𝒪_D/J`, and a symplectic space has even
dimension.

WHY THIS IS NOT CIRCULAR — the refuting check of the audit below, run.
The audit warns that if the `𝒪_D`-linear polarization has to be obtained
from `A^∨ ≅ A ⊗_{𝒪_D} 𝔠`, whose classical proof CLASSIFIES the
`𝒪_D`-module structure of the homology, then the rank has been smuggled
in and the route is circular.  It is not, for two independent reasons.

(i) FORMAL.  Parity is strictly weaker than `r_J = 2`: the distribution
`(r_{J₁}, r_{J₂}) = (0, 4)` satisfies parity and the integer counts, and
is excluded here only by `card_torsion_ne_one_of_isMaximal`.  An input
that leaves `(0, 4)` standing cannot presuppose `r_J = 2`.  This is a
proof, not an analogy, and it is checkable without any geometry.

(ii) MATHEMATICAL.  The `𝔠`-polarization theorem is about WHICH
polarizations exist (principality, the Steinitz class of `H₁`), not about
whether an `𝒪_D`-linear one exists at all.  For the latter: `A` is
projective, so carries SOME polarization `λ₀`; its Rosati involution is
positive, and a totally real field admits no nontrivial positive
involution — if `σ ≠ id` had order two then `D = D^σ(√d)` with `d`
totally positive, and `Tr(y σ(y)) = -Tr(d) < 0` at `y = √d`, contradicting
positivity.  So the Rosati involution is the identity on `𝒪_D`, which
says precisely `λ₀ ∘ ι(a) = ι(a)^∨ ∘ λ₀`: `λ₀` is ALREADY `𝒪_D`-linear,
with no averaging, no `𝔠` and no homology input.  This is what
`DualStruct.weil_act` axiomatises.

THE CHECK THAT WOULD REFUTE (ii), and it is the residual gap.  Exhibit an
`A` with `𝒪_D`-action whose `End⁰(A)` is strictly larger than `D` and for
which NO polarization has `D` stable under its Rosati involution — the
argument above assumes `†` preserves `D`, which is automatic when
`End⁰(A) = D` and needs Albert's classification otherwise.  Reason (i) is
independent of this and already suffices to license the cut.

STATUS 2026-07-27 — THE ALGEBRA IS DONE; TWO GEOMETRIC INPUTS REMAIN.
The linear algebra that was listed here as missing is now PROVEN above:
`even_finrank_of_isAlt_nondegenerate` (the mathlib gap — nondegenerate
alternating ⇒ even `finrank`, by the hyperbolic-plane induction over
`LinearMap.BilinForm.orthogonal`) and its cardinality form
`exists_card_eq_pow_two_mul_of_isAlt_nondegenerate`.  The body below is
the glue that consumes them, and it reduces this leaf to exactly two
sorried `have`s, both PURELY GEOMETRIC and both stated in full:

* `hfin` — `A[I]` is FINITE.  Free once `card_torsion_span_natCast` is
  available (`A[I] ⊆ A[N(I)]`, of order `N(I)^(2g)`); it is a separate
  `have` here only because that leaf is itself open, and a successor
  should discharge it from that leaf rather than from scratch.
* `hpair` — `A[I]` carries a NONDEGENERATE ALTERNATING pairing over the
  residue field `𝒪_D/I`.  This is the whole geometric content, and it is
  where the polarization enters.

WHAT `hpair` STILL NEEDS, both checkable by reading
`Modularity/AbelianScheme.lean`: nothing asserts that a
`DualStruct`/`PolarizationStruct` EXISTS for a given `ab`/`m`, and
`PolarizationStruct` does not assert its induced pairing nondegenerate
(only `DualStruct.weil_nondegenerate` is an axiom, and that is the
canonical `A × A^∨` pairing, not the polarized one).

**DO NOT BUILD ON `PolarizationStruct` AS IT STANDS** (recorded here
2026-07-27 because this leaf is where it will bite): the structure is
satisfied by the CONSTANT ZERO MAP, verified field by field, so it
carries no content over `DualStruct` and its induced pairing may be
identically `1`.  A repair task for that definition has its own owner;
`hpair` must be discharged against the REPAIRED structure, not the
current one.  Note also that `pairing` in that file is multiplicative
(valued in roots of unity) whereas `hpair` asks for an additive
`𝒪_D/I`-bilinear form, so the successor's first step is the logarithm
of the pairing along a choice of `#(𝒪_D/I)`-th root of unity — which is
where the residue field's characteristic and the `I`-part of the
polarization degree have to be handled.

NOTE the classical argument is cleanest on the RATIONAL Tate module
`V_J`, where nondegeneracy holds for ANY isogeny `λ` and the
prime-to-`J`-degree condition disappears; that is why this leaf is stated
as its CONCLUSION (parity) rather than as the existence of a
`J`-nondegenerate pairing, which would be false for a polarization whose
degree `J` divides.

STATUS 2026-07-27 — **PROVEN, AND NOT BY THE POLARIZATION.**  The route
above is superseded: over a Betti frame `#A[I] = #(𝒪_D/I)^{rank_{𝒪_D} H₁}`
and the rank is `2` by the rank bridge, so the exponent is even outright
and `r = 1`.  Neither `hfin` nor `hpair` is needed, so the warning about
`PolarizationStruct` being satisfied by the constant zero map no longer
bites here — that repair is still worth doing, but nothing in this file
waits on it.  `even_finrank_of_isAlt_nondegenerate` and
`exists_card_eq_pow_two_mul_of_isAlt_nondegenerate` above are left in
place: they are a genuine mathlib gap and are consumed by
`LevelFrame.card_tors_eq_sq`.

`hdim` IS NEW AND IS LOAD-BEARING (2026-07-27).  It is what pins the Betti
number to `2·[D:ℚ]`; see the FAITHFULNESS REPAIR in the section note above
`BettiFrame`, where relative dimension `0` refutes the sibling leaf. -/
theorem even_dim_torsion_of_isMaximal
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (hdim : SmoothOfRelativeDimension (Module.finrank ℚ D) f)
    (I : Ideal (NumberField.RingOfIntegers D)) (hI : I.IsMaximal) :
    ∃ r, Nat.card (m.torsion x I).1
      = Nat.card (NumberField.RingOfIntegers D ⧸ I) ^ (2 * r) := by
  classical
  obtain ⟨bf⟩ := exists_bettiFrame m x hdim
  exact ⟨1, by rw [bf.card_torsion_isMaximal I hI]⟩

open _root_.NumberField in
/-- **`A[J] ≠ 0` at every maximal `J`** (PROVEN 2026-07-27 over the single
geometric leaf `exists_bettiFrame`, and RESTATED with `hdim` — it was FALSE
without it; see STATUS below.  Mumford *Abelian Varieties* §19,
`End(A) ↪ End(T_p A)`, is the route that was NOT taken).

Equivalently: `𝒪_D ⊗ ℤ_p` acts FAITHFULLY on `T_p A`, so no factor of
`𝒪_D ⊗ ℤ_p = ∏_{J ∣ p} 𝒪_J` annihilates it.

THIS IS NOT THE FAITHFULNESS THE AUDIT BELOW DISMISSES.  That audit's
counterexample `M₁` is faithful as an `𝒪_D`-MODULE, and so is the
parity-even variant with `(r_{J₁}, r_{J₂}) = (0, 4)`; module-faithfulness
constrains only the SUM `Σ_J r_J e_J f_J`.  What is needed, and what this
leaf states, is nonvanishing at each SINGLE `J`.  Together with
`even_dim_torsion_of_isMaximal` it gives `r_J ≥ 2` for every `J`, which
is exactly the hypothesis `LevelFrame.card_tors_eq_sq` consumes.

The statement is a cardinality rather than "there is a nonzero point"
because that is the form the assembly uses; the two agree because `A[J]`
is finite (it embeds in `A[p]`, of order `p^(2g)`).

FAITHFULNESS CHECK, run 2026-07-27 — THE LEAF IS TRUE AS STATED, AND
NEEDS NO SATURATION HYPOTHESIS.  A natural worry is that this leaf
secretly needs `𝒪_D` to be SATURATED in `End(A)` (i.e. `End(A) ∩ D =
𝒪_D`), because the obvious elementary route does: if `a ∉ p𝒪_D` kills
`A[p]` then `[a]` factors through `[p]`, giving `a/p ∈ End(A) ∩ D`, and
one needs that to be `𝒪_D` to get the contradiction.  `Mult` asserts only
a ring map `𝒪_D → End(A)`, so that hypothesis is NOT available and the
route is unusable — but the leaf is true anyway, by a different argument
that uses no saturation:

`H₁(A, ℤ)` is a finitely generated TORSION-FREE module over the Dedekind
domain `𝒪_D`, of `ℚ`-dimension `2g` and hence of `𝒪_D`-rank
`2g/[D:ℚ] = 2`.  Over a Dedekind domain a f.g. torsion-free module is
PROJECTIVE, and a projective module of rank two localises to a FREE
rank-two module at every maximal ideal.  So `A[J] ≅ (𝒪_D/J)²` outright —
which is not merely nonvanishing but the full conclusion of
`card_torsion_of_isMaximal`, with no saturation and no Albert
classification anywhere in it.

WHAT THIS LOCATES, and it is the point of recording it: the residual gap
under BOTH this leaf and `even_dim_torsion_of_isMaximal` is the single
Betti-number input `dim_ℚ H₁(A_x, ℚ) = 2g`, not faithfulness and not
positivity of the Rosati involution.  There is no singular/étale homology
of a scheme at this pin, which is why the file instead routes parity
through the polarization; a successor that builds `H₁` would close this
leaf, its parity sibling AND `card_torsion_span_natCast` together.

THE CHECK THAT WOULD REFUTE THE ABOVE: exhibit an abelian variety of
dimension `g` with an injective `𝒪_D → End(A)`, `D` totally real of
degree `g`, whose `H₁(A, ℤ)` has `𝒪_D`-rank other than two — i.e. show
the `ℚ`-dimension count or the freeness-over-a-field step fails.  It does
not: `D` is a FIELD, so `H₁(A, ℚ)` is a `D`-vector space and its
`D`-dimension is forced.

STATUS 2026-07-27 — **PROVEN over `exists_bettiFrame`, exactly as this
check predicted**, and the check's own conclusion is now the code:
`#A[I] = #(𝒪_D/I)²`, so it is not merely `≠ 1`.

FALSITY REPAIR IN THE SAME COMMIT — `hdim` IS NOW REQUIRED, AND WITHOUT
IT THE STATEMENT WAS FALSE.  `AbelianSchemeStruct` asks only for proper,
smooth and geometrically connected, and the IDENTITY `f = 𝟙 S` satisfies
all three: an abelian scheme of relative dimension `0`.  Its geometric
fibres are a single point, so `Nat.card (m.torsion x I).1 = 1` for every
`I`, and a `Mult ab (𝒪_D)` exists because the endomorphism ring of the
trivial group scheme is the zero ring.  That is a counterexample to the
previous statement.  The repair is free: the only consumer,
`card_torsion_of_isMaximal` below, already carries `hdim` and merely was
not passing it. -/
theorem card_torsion_ne_one_of_isMaximal
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (hdim : SmoothOfRelativeDimension (Module.finrank ℚ D) f)
    (I : Ideal (NumberField.RingOfIntegers D)) (hI : I.IsMaximal) :
    Nat.card (m.torsion x I).1 ≠ 1 := by
  classical
  obtain ⟨bf⟩ := exists_bettiFrame m x hdim
  haveI : I.IsMaximal := hI
  letI : Field (NumberField.RingOfIntegers D ⧸ I) := Ideal.Quotient.field I
  have hIbot : I ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField hI (NumberField.RingOfIntegers.not_isField D)
  haveI : Finite (NumberField.RingOfIntegers D ⧸ I) :=
    Ring.HasFiniteQuotients.finiteQuotient hIbot
  have h1 : 1 < Nat.card (NumberField.RingOfIntegers D ⧸ I) :=
    Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  rw [bf.card_torsion_isMaximal I hI]
  exact (Nat.one_lt_pow (by norm_num) h1).ne'

/-- **The `I`-torsion of a geometric fibre has `(#𝒪_D/I)²` elements**
(PROVEN 2026-07-27 over the three geometric leaves
`card_torsion_span_natCast`, `even_dim_torsion_of_isMaximal` and
`card_torsion_ne_one_of_isMaximal`, and the arithmetic bridge
`LevelFrame.card_tors_eq_sq`; the audit below is preserved because it is
what forced the three-way cut, and its counterexample still stands).

**This is where the rank count lives, and it is the only genuinely
geometric input of `exists_levelTateFrame`** — everything else about a
single-level frame is the commutative algebra of the `LevelFrame`
namespace above, and everything about the TOWER is
`exists_levelTateFrame_succ` and the recursion in
`exists_levelwiseTateFrame`.

The argument. `A_x` is an abelian variety of dimension `g = [D:ℚ]` over
an algebraically closed field of characteristic zero — that is `hdim`
together with the properness, smoothness and connectedness carried by
`ab` — so `H₁(A_x, ℚ)` has `ℚ`-dimension `2g`. The real multiplication
makes it a module over the FIELD `D`, hence free, of `D`-dimension
`2g/[D:ℚ] = 2`; **this is exactly where `hdim` enters, and it is why the
rank is two over the coefficient ring rather than over `ℤ_q`.** Tensoring
with `ℚ_q` and projecting to the factor of `D ⊗ ℚ_q = ∏_{I ∣ q} D_I` cut
out by `I` gives a two-dimensional `D_I`-space; `A[I]` is its
`𝒪_{D,I}`-lattice modulo `I`, a two-dimensional vector space over the
residue field `𝒪_D/I`, whence the cardinality `(#𝒪_D/I)²`.

Equivalently, and this is the form in which the literature states it:
multiplication by `I` is an isogeny of degree `N(I)²`, since it is
`[N(I)]` up to the `D`-action on a two-dimensional `D`-space.

PIN INVENTORY (verified 2026-07-26 — do not re-survey). There is no
`AbelianVariety`, no isogeny theory, no theorem of the cube and no
`degree` of a finite morphism anywhere in mathlib at this pin; the only
group-scheme material is `Mathlib/AlgebraicGeometry/Group/{Abelian,
Smooth}.lean`. `~/cs/FLT` carries no abelian-variety material either —
its nearest files are `KnownIn1980s/EllipticCurves/WeilPairing.lean` and
`.../TateCurve.lean`, both about elliptic curves over a FIELD, hence
relative dimension one, whereas `A_x` here has dimension `[D : ℚ]`. So
neither tree can be mined for this: the rank count has to be built.

WHY THE STATEMENT IS A CARDINALITY AND NOT A FRAME.  Stating the leaf as
"`A[I]` is free of rank two over `𝒪_D/I`" would be the `n = 1` case of
its own consumer, and a consumer of a frame has to carry the frame's
five clauses through every algebraic step.  A cardinality is a single
number, it is what the degree formula actually gives, and — because
`A[I]` is killed by `I` and so is automatically a vector space over the
residue FIELD `𝒪_D/I` — it is equivalent to the rank statement at level
one with no further geometry.  The passage from level one to level `n`
is then pure algebra: see the section note above.

CUT-OBSTRUCTION AUDIT (2026-07-26 — READ BEFORE CUTTING THIS LEAF).
`Modularity/AbelianSchemeIsogeny.lean` now presents `[N]` as a finite
locally free morphism, which makes one cut look very attractive: prove
the INTEGER torsion count `#A[N] = N ^ (2g)` (the degree of `[N]`, with
`g = [D : ℚ]`) as the geometric leaf, and deduce this statement from it
by commutative algebra in the Dedekind domain `𝒪_D`. **That deduction
does not exist**, for ANY collection of integer counts, and a successor
should not spend a cycle looking for it.

COUNTEREXAMPLE. Let `D` be real quadratic, so `g = 2`, and let `p` be a
prime that SPLITS, `p 𝒪_D = J₁ J₂` with `e = f = 1` and
`𝒪_D / Jᵢ ≅ 𝔽_p`. Write `W := D / 𝒪_D`, a divisible torsion
`𝒪_D`-module with `W[N] ≅ 𝒪_D / N 𝒪_D`, so `#W[N] = N²`. The honest
module is `M₀ := W ⊕ W`: it satisfies `#M₀[N] = N⁴` for every `N` and
`#M₀[J] = #(𝒪_D/J)²` for every maximal `J`, exactly as this leaf
asserts.

Now build `M₁ := W ⊕ W'`, where `W'` agrees with `W` at every prime
other than `p`, and at `p` has `W'[p^∞] := (D_{J₂} / 𝒪_{J₂})²` in place
of `W[p^∞] = D_{J₁}/𝒪_{J₁} ⊕ D_{J₂}/𝒪_{J₂}`. Since `e = f = 1` at both
`Jᵢ` we have `#(D_{J₂}/𝒪_{J₂})[p^n] = p^n`, hence
`#W'[p^n] = p^(2n) = #W[p^n]`, and therefore `#M₁[N] = N⁴ = #M₀[N]` for
EVERY `N`. But `M₁[J₁] = W[J₁] ⊕ 0` has order `p`, not `p²`. `M₁` is
divisible, torsion, and a FAITHFUL `𝒪_D`-module, so neither a
faithfulness nor a divisibility side condition rescues the count.

WHAT THE COUNT MISSES, STATED POSITIVELY. For a divisible torsion
`𝒪_D`-module with finite `J`-power torsion one has
`M[J^∞] ≅ (D_J/𝒪_J)^(r_J)`, and the integer counts pin down only the
WEIGHTED SUM `Σ_{J ∣ p} r_J e_J f_J = 2g`, never the individual `r_J`.
This leaf is the assertion `r_J = 2` for every `J`, and what forces it
is that `H₁(A, ℚ)` is a vector space over the FIELD `D`, hence free, of
dimension `2g / [D : ℚ] = 2` — an input living over `ℚ` and invisible to
every `ℤ`-level and `ℤ_q`-level count. That is the precise sense in
which the rank enters through `hdim` TOGETHER with the real
multiplication, and the precise sense in which this leaf is atomic at
this pin.

THE CHECK THAT WOULD REFUTE THIS AUDIT. Exhibit a route pinning `r_J` at
a SINGLE maximal `J` without a rational-homology input (equivalently:
without a `D`-vector-space, Betti, or complex-uniformization step) — for
instance any constraint forcing the `r_J` to be equal to one another.
Such a route defeats the counterexample, since `M₀` and `M₁` differ only
in distributing `r_{J₁} + r_{J₂} = 4` as `2 + 2` versus `1 + 3`.

THE REFUTING CHECK HAS AN ANSWER: PARITY (2026-07-27). The audit above
is CORRECT that no collection of integer counts suffices, and its
counterexample stands. But it invites exactly one refutation — "a
constraint pinning `r_J` without a rational-homology input" — and there
is one, namely that an `𝒪_D`-LINEAR POLARIZATION forces every `r_J` to
be EVEN. `M₁` is killed by that constraint alone: it has `r_{J₁} = 1`.

The constraint. A polarization that is `𝒪_D`-linear induces an
`𝒪_D`-bilinear ALTERNATING pairing on `A[J]`; if it is moreover
NONDEGENERATE there, then `A[J]` is a symplectic vector space over the
residue field `𝒪_D/J`, and a symplectic space has even dimension. So
`r_J` is even for every maximal `J` — a purely local conclusion, drawn
from the polarization and not from `H₁(A, ℚ)`.

With parity in hand the integer counts DO close the argument, and this
is the sense in which the audit's verdict is too strong. Write
`p 𝒪_D = ∏_{J ∣ p} J^(e_J)`. The ideals `J^(e_J)` are pairwise
comaximal, so CRT splits the torsion EXACTLY —
`A[p] = ⨁_{J ∣ p} A[J^(e_J)]`, with no ramification caveat, because
`p 𝒪_D` IS that product — and the tower relation
`#A[J^(n+1)] = #A[J] · #A[J^n]` (from surjectivity of `·π`, already
proven as `exists_mem_torsion_act_uniformizer_eq`, whose kernel on
`A[J^(n+1)]` is `A[J]` because `(π) + J^(n+1) = J` for `n ≥ 1` in a
Dedekind domain) gives `#A[J^(e_J)] = #(𝒪_D/J)^(r_J e_J)`. Hence
`#A[p] = p^(Σ_J e_J f_J r_J)`, and `#A[p] = p^(2g)` forces
`Σ_J e_J f_J r_J = 2g = 2 [D : ℚ] = 2 Σ_J e_J f_J`, i.e.
`Σ_J e_J f_J (r_J − 2) = 0`. Every `r_J` is even, so `r_J ≥ 2` as soon
as `r_J ≠ 0`, every summand is then `≥ 0`, and all of them vanish:
`r_J = 2` for every `J ∣ p`, this leaf included.

SO THE LEAF IS STILL GEOMETRIC, BUT OVER THREE STANDARD INPUTS RATHER
THAN ONE BESPOKE ONE. What the route needs, and none of it exists at
this pin:

* `#A[p] = p ^ (2g)` — the degree of `[p]`, in characteristic zero. A
  UNIVERSAL fact about abelian schemes, reusable everywhere, and the
  natural successor to the finite-locally-free presentation of `[N]`
  already in `Modularity/AbelianSchemeIsogeny.lean`.
* An `𝒪_D`-linear polarization whose induced Weil pairing on `A[J]` is
  NONDEGENERATE. Classically `A^∨ ≅ A ⊗_{𝒪_D} 𝔠` for an invertible
  `𝒪_D`-module `𝔠` (a `𝔠`-polarization), which is an isomorphism and so
  nondegenerate at every `J`.
* `A[J] ≠ 0` for every maximal `J`, equivalently faithfulness of
  `𝒪_D ⊗ ℤ_p` on `T_p A` (Mumford §19, `End(A) ↪ End(T_p A)`). This is
  NOT the faithfulness the audit dismisses: the counterexample `M₁` is
  faithful as an `𝒪_D`-MODULE, and so is the variant with
  `(r_{J₁}, r_{J₂}) = (0, 4)`, which parity alone does not exclude.
  Only nonvanishing at each single `J` does.

THE CHECK THAT WOULD REFUTE THIS ROUTE — and it is the one place it can
fail, so run it before dispatching. Show that the existence of an
`𝒪_D`-linear `J`-nondegenerate polarization already PRESUPPOSES
`r_J = 2`. The classical proof that `A^∨ ≅ A ⊗_{𝒪_D} 𝔠` classifies the
`𝒪_D`-module structure of the homology, and if that classification is
what supplies the rank, the route is circular and the audit's verdict
survives unchanged. If instead the `𝔠`-polarization can be obtained
from projectivity plus `𝒪_D`-averaging (`D` totally real, so the Rosati
involution is positive and trivial on `𝒪_D` — which is exactly what
`DualStruct.weil_act` axiomatises) without a rank input, the route is
sound and this leaf splits three ways.

THE VOCABULARY NOW EXISTS — verified 2026-07-27, and it IS on `main`
(commit `4ff8dde1`, originally branch `flt-lean-169`). `DualStruct`,
`PolarizationStruct`, `PolarizationStruct.pairing` and its six lemmas
(`pairing_add_left`, `pairing_add_right`, `pairing_self` — alternating,
`pairing_gal`, `pairing_act`, `galSMul_hom`) live in
`Modularity/AbelianScheme.lean`. Of the two gaps this paragraph used to
record between that layer and this leaf, ONE IS NOW CLOSED:
`PolarizationStruct` DOES assert that its induced pairing is
nondegenerate, by the axiom `PolarizationStruct.weil_hom_nondegenerate`,
with `pairing_nondegenerate` and `exists_pairing_ne_one` as its usable
forms. (It was added 2026-07-27 because without it the whole structure
was satisfied by the CONSTANT ZERO MAP and so carried no content at all
over `DualStruct`; the standing refutation test is the proven
`PolarizationStruct.torsion_eq_zero_of_hom_eq_zero`. Note the axiom is
LEVEL-GUARDED — `PolarizationStruct d 𝒩 𝔞 𝔞pos` asserts it only at
`I ∈ 𝒩` — after a second repair the same day; an unguarded version forces
a PRINCIPAL polarization, see the docstring of
`exists_tateWeilPairing_of_mult` below.

A THIRD repair the same day added POSITIVITY, which is why the structure
now takes four parameters: the level-guard released it onto every
polarization class, which made `HasSplitHilbertBlumenthalModuli`
(`Modularity/MoretBailly.lean`) false, so the structure also carries the
polarization module `𝔞`, a positivity cone `𝔞pos`, an isomorphism
`𝔞 ≅ Hom^sym_{𝒪_D}(A, A^∨)` (`lam`, `lam_injective`, `lam_surjective`,
valued in the new `Fermat.SymHomStruct`) and the datum that `hom = λ_a`
for a POSITIVE `a`. A consumer that does not care may take
`𝔞 := ⊤`, `𝔞pos := Set.univ`; a consumer that needs the narrow class
`[𝔞] ∈ Cl⁺(D)` pinned must hold both fixed. The standing test that the
positivity datum is not junk is `PolarizationStruct.posElt_ne_zero`.) The
gap that
REMAINS is EXISTENCE: nothing asserts that a
`DualStruct`/`PolarizationStruct` EXISTS for a given `ab`/`m`. That
remaining gap is the second bullet above, and it is now the content of
`even_dim_torsion_of_isMaximal` rather than of this leaf.

RESOLUTION (2026-07-27) — THE CUT, AND WHAT SURVIVED OF THE AUDIT.
The audit's VERDICT survives verbatim: no collection of integer counts
determines the `r_J`, and its counterexample `M₁` stands. Its REASON
— "only `H₁(A, ℚ)` being a `D`-vector space can force `r_J = 2`" — was
too strong, and it named its own refutation. Parity is that refutation,
and it is drawn from the polarization, not from rational homology.

So this leaf is now PROVEN, over four pieces:

* `LevelFrame.card_tors_eq_sq` — PROVEN here, the whole arithmetic
  bridge: CRT at `p 𝒪_D = ∏_J J^(e_J)` (mathlib's
  `Submodule.isInternal_prime_power_torsion_of_is_torsion_by_ideal`),
  the tower relation from `LevelFrame.card_tors_pow`, and the
  termwise-equality argument. It needs no ramification identity — the
  absolute norm supplies `Σ_J e_J f_J = g` implicitly.
* `card_torsion_span_natCast` — `#A[N] = N^(2g)`, the degree of `[N]`.
* `even_dim_torsion_of_isMaximal` — parity, from an `𝒪_D`-linear
  polarization.
* `card_torsion_ne_one_of_isMaximal` — `A[J] ≠ 0` at each single `J`.

THE REFUTING CHECK THE AUDIT ASKED FOR WAS RUN, AND THE ROUTE IS NOT
CIRCULAR; the argument is recorded in full under
`even_dim_torsion_of_isMaximal`, and its formal half is this: parity
leaves `(r_{J₁}, r_{J₂}) = (0, 4)` standing, so an input yielding only
parity cannot presuppose `r_J = 2`. That half needs no geometry and no
`𝔠`-polarization theory to check. -/
theorem card_torsion_of_isMaximal
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (hdim : SmoothOfRelativeDimension (Module.finrank ℚ D) f)
    (I : Ideal (NumberField.RingOfIntegers D)) (hI : I.IsMaximal) :
    Nat.card (m.torsion x I).1
      = Nat.card (NumberField.RingOfIntegers D ⧸ I) ^ 2 := by
  classical
  letI : AddCommGroup (GeomFibrePt f x) := ab.addCommGroup (specAlgClos F ≫ x)
  letI : Module (NumberField.RingOfIntegers D) (GeomFibrePt f x) :=
    m.module (specAlgClos F ≫ x)
  haveI : I.IsMaximal := hI
  obtain ⟨p, n, -, hpI, hp, -⟩ := Ideal.exists_prime_and_absNorm_eq_pow I
  exact LevelFrame.card_tors_eq_sq (P := GeomFibrePt f x) I hI p hp hpI
    (fun J hJ π hπ hπ2 k y hy =>
      exists_mem_torsion_act_uniformizer_eq m x J hJ π hπ hπ2 k y hy)
    (card_torsion_span_natCast m x hdim p hp.ne_zero)
    (fun J hJ _ => even_dim_torsion_of_isMaximal m x hdim J hJ)
    (fun J hJ _ => card_torsion_ne_one_of_isMaximal m x hdim J hJ)

/-- **The `Iⁿ`-torsion is free of rank two over `𝒪_D/Iⁿ`, at each single
level `n`** (PROVEN 2026-07-26 over the single geometric leaf
`card_torsion_of_isMaximal` and the sibling
`exists_mem_torsion_act_uniformizer_eq`).

No compatibility in `n` is asserted: the frames at different levels are
chosen independently, and tying them together is the business of
`exists_levelTateFrame_succ` and of the recursion in
`exists_levelwiseTateFrame`.

HOW IT IS PROVEN.  A uniformizer `π ∈ I ∖ I²` comes from
`exists_mem_notMem_sq_of_isMaximal`; `·π` is surjective from each level
onto the previous one by the sibling leaf; and the residual cardinality
is the geometric leaf.  `LevelFrame.exists_linearEquiv_tors_pow` then
produces an `𝒪_D`-linear equivalence `(𝒪_D/Iⁿ)² ≃ A[Iⁿ]`, whose
underlying function is the frame: the five clauses of
`IsLevelTateFrame` are, in order, membership in the torsion,
additivity, injectivity, surjectivity onto the torsion, and
`𝒪_D`-semilinearity — and each of them is a clause of the linear
equivalence read through the coercion `A[Iⁿ] → GeomFibrePt f x`, because
`Mult.module` DEFINES `a • y` to be `m.act a y` and
`AbelianSchemeStruct.addCommGroup` DEFINES `y + z` to be `ab.add y z`.

At `n = 0` the statement is trivial on both sides: `I⁰ = ⊤`, the
quotient ring is trivial (so the source is a singleton), and `A[⊤] = 0`
because `1 ∈ ⊤` acts as the identity; that case is subsumed by the
general argument. -/
theorem exists_levelTateFrame
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (hdim : SmoothOfRelativeDimension (Module.finrank ℚ D) f)
    (I : Ideal (NumberField.RingOfIntegers D)) (hI : I.IsMaximal) (n : ℕ) :
    ∃ c : (Fin 2 → NumberField.RingOfIntegers D ⧸ I ^ n) → GeomFibrePt f x,
      IsLevelTateFrame m x (I ^ n) c := by
  haveI : I.IsMaximal := hI
  have hI0 : I ≠ ⊥ :=
    (I.bot_lt_of_maximal (NumberField.RingOfIntegers.not_isField D)).ne'
  obtain ⟨π, hπ, hπ2⟩ := exists_mem_notMem_sq_of_isMaximal hI hI0
  haveI : Finite (NumberField.RingOfIntegers D ⧸ I) :=
    Ideal.finiteQuotientOfFreeOfNeBot I hI0
  letI := ab.addCommGroup (specAlgClos F ≫ x)
  letI := m.module (specAlgClos F ≫ x)
  obtain ⟨e⟩ :=
    LevelFrame.exists_linearEquiv_tors_pow (P := GeomFibrePt f x) I hI hI0 hπ hπ2
      (fun k y hy => exists_mem_torsion_act_uniformizer_eq m x I hI π hπ hπ2 k y hy)
      (card_torsion_of_isMaximal m x hdim I hI) n
  refine ⟨fun u => (e u : GeomFibrePt f x), fun u => (e u).2, ?_, ?_, ?_, ?_⟩
  · intro u v
    exact congrArg Subtype.val (e.map_add u v)
  · intro u v huv
    exact e.injective (Subtype.ext huv)
  · intro y hy
    obtain ⟨u, hu⟩ := e.surjective ⟨y, hy⟩
    exact ⟨u, congrArg Subtype.val hu⟩
  · intro a u
    have hsmul : (fun i => Ideal.Quotient.mk (I ^ n) a * u i) = a • u := by
      funext i
      show Ideal.Quotient.mk (I ^ n) a * u i = a • u i
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
    rw [hsmul]
    exact congrArg Subtype.val (e.map_smul a u)

open _root_.NumberField in
/-- **A level-`n` frame lifts through multiplication by `π` to a level
`n+1` frame** (PROVEN 2026-07-26 over `exists_levelTateFrame` and
`exists_mem_torsion_act_uniformizer_eq`; commutative algebra over the
artinian local ring `𝒪_D/Iⁿ⁺¹`).

Given a frame `cn` at level `n`, this produces a frame `c'` at level
`n+1` whose composite with `·π` is `cn ∘ (reduction)`. It is the single
inductive step of the compatible tower, and it is the reason
`exists_levelwiseTateFrame` is not "levelwise and hope": the tower it
builds is a genuine inverse system.

The argument, and why it is algebra rather than geometry. Take any
level-`n+1` frame `c'₀` (from `exists_levelTateFrame`). Multiplication
by `π` carries `A[Iⁿ⁺¹]` onto `A[Iⁿ]` (divisibility of an abelian
variety, together with `π` being a uniformizer at `I`), so transporting
it through the two frames gives a SURJECTIVE `𝒪_D`-linear

  `ψ : (𝒪_D/Iⁿ⁺¹)² ↠ (𝒪_D/Iⁿ)²`,   `cn (ψ u) = π · c'₀ u`.

Choose `t j` with `ψ (t j) = ē j` and let `Ψ u = Σ_j u j • t j`; then
`ψ ∘ Ψ` is the reduction map by construction, and `c' := c'₀ ∘ Ψ` is the
required frame AS SOON AS `Ψ` is bijective — which is where the local
algebra enters.

Bijectivity of `Ψ` is bijectivity of the `2 × 2` matrix `t`, i.e.
`d := t₀₀t₁₁ − t₀₁t₁₀` being a unit of `𝒪_D/Iⁿ⁺¹`; and since
`I·(𝒪_D/Iⁿ⁺¹)` is NILPOTENT, a unit is exactly an element with nonzero
image in the residue field `k = 𝒪_D/I`. Suppose `d ↦ 0`. Feeding the two
adjugate rows `(t₁₁, −t₀₁)` and `(−t₁₀, t₀₀)` into `Ψ` produces vectors
all of whose coordinates die in `k`; `ψ` is `𝒪_D`-linear, so it carries
such a vector to one dying in `k`, and `ψ ∘ Ψ` is the reduction — whence
all four entries `tⱼᵢ` die in `k`. Feeding in `(1,0)` then gives
`1 = 0` in `k`. So `d` is a unit, and the inverse of `Ψ` is written down
explicitly from the adjugate.

The level `n = 0` is degenerate and is handled separately: `𝒪_D/I⁰` is
the zero ring, so the compatibility clause reads `π · c' u = cn 0 = 0`,
which holds for ANY level-`1` frame because `π ∈ I` kills `A[I]`. -/
theorem exists_levelTateFrame_succ
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (hdim : SmoothOfRelativeDimension (Module.finrank ℚ D) f)
    (I : Ideal (NumberField.RingOfIntegers D)) (hI : I.IsMaximal)
    (π : NumberField.RingOfIntegers D) (hπ : π ∈ I) (hπ2 : π ∉ I ^ 2)
    (n : ℕ) (cn : (Fin 2 → NumberField.RingOfIntegers D ⧸ I ^ n) → GeomFibrePt f x)
    (hcn : IsLevelTateFrame m x (I ^ n) cn) :
    ∃ c' : (Fin 2 → NumberField.RingOfIntegers D ⧸ I ^ (n + 1)) → GeomFibrePt f x,
      IsLevelTateFrame m x (I ^ (n + 1)) c' ∧
      ∀ u : Fin 2 → NumberField.RingOfIntegers D ⧸ I ^ (n + 1),
        m.act π (c' u) =
          cn (fun i => Ideal.Quotient.factor
            (Ideal.pow_le_pow_right (Nat.le_succ n)) (u i)) := by
  classical
  letI : AddCommGroup (GeomFibrePt f x) := ab.addCommGroup (specAlgClos F ≫ x)
  letI : Module (𝓞 D) (GeomFibrePt f x) := m.module (specAlgClos F ≫ x)
  haveI : I.IsMaximal := hI
  by_cases hn0 : n = 0
  · -- ### The degenerate level `n = 0`: the compatibility clause is vacuous
    subst hn0
    obtain ⟨c', hc'⟩ := exists_levelTateFrame m x hdim I hI (0 + 1)
    refine ⟨c', hc', fun u => ?_⟩
    haveI hsub : Subsingleton (𝓞 D ⧸ I ^ 0) :=
      Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.one_eq_top])
    have hcn0 : cn 0 = ab.zero (specAlgClos F ≫ x) := by
      have h := hcn.2.1 0 0
      rw [add_zero] at h
      have h2 : cn 0 = cn 0 + cn 0 := h
      have h3 : cn 0 + 0 = cn 0 + cn 0 := by rw [add_zero]; exact h2
      exact (add_left_cancel h3).symm
    have hzeroπ : m.act π (c' u) = ab.zero (specAlgClos F ≫ x) :=
      (mem_torsion_iff m x (I ^ (0 + 1)) (c' u)).mp (hc'.1 u) π (by simpa using hπ)
    rw [hzeroπ, Subsingleton.elim
      (fun i => (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ 0))) (u i))
      (0 : Fin 2 → 𝓞 D ⧸ I ^ 0), hcn0]
  · -- ### The main case `n ≥ 1`
    have hle1 : I ^ (n + 1) ≤ I := Ideal.pow_le_self (Nat.succ_ne_zero n)
    have hlen : I ^ n ≤ I := Ideal.pow_le_self hn0
    -- reduction maps between the three quotients
    set redn : (𝓞 D ⧸ I ^ (n + 1)) →+* (𝓞 D ⧸ I ^ n) :=
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ n)) with hredndef
    have hredn_mk : ∀ a : 𝓞 D,
        redn (Ideal.Quotient.mk (I ^ (n + 1)) a) = Ideal.Quotient.mk (I ^ n) a :=
      fun a => Ideal.Quotient.factor_mk _ a
    obtain ⟨redk, hredk_mk⟩ :
        ∃ g : (𝓞 D ⧸ I ^ (n + 1)) →+* (𝓞 D ⧸ I),
          ∀ a : 𝓞 D, g (Ideal.Quotient.mk (I ^ (n + 1)) a) = Ideal.Quotient.mk I a :=
      ⟨Ideal.Quotient.factor hle1, fun a => Ideal.Quotient.factor_mk _ a⟩
    obtain ⟨redkn, hredkn_mk⟩ :
        ∃ g : (𝓞 D ⧸ I ^ n) →+* (𝓞 D ⧸ I),
          ∀ a : 𝓞 D, g (Ideal.Quotient.mk (I ^ n) a) = Ideal.Quotient.mk I a :=
      ⟨Ideal.Quotient.factor hlen, fun a => Ideal.Quotient.factor_mk _ a⟩
    have hcomp : ∀ z, redkn (redn z) = redk z := by
      intro z
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
      rw [hredn_mk, hredkn_mk, hredk_mk]
    -- an arbitrary frame at level `n + 1`
    obtain ⟨c₀, hc₀⟩ := exists_levelTateFrame m x hdim I hI (n + 1)
    -- `·π` maps the level `n+1` torsion into the level `n` torsion
    have hπtors : ∀ z : GeomFibrePt f x, z ∈ (m.torsion x (I ^ (n + 1))).1 →
        m.act π z ∈ (m.torsion x (I ^ n)).1 := by
      intro z hz
      refine (mem_torsion_iff m x (I ^ n) _).mpr fun a ha => ?_
      rw [← m.act_mul]
      refine (mem_torsion_iff m x (I ^ (n + 1)) z).mp hz (a * π) ?_
      rw [pow_succ]
      exact Ideal.mul_mem_mul ha hπ
    -- transport `·π` through the two frames
    have hψex : ∀ u : Fin 2 → 𝓞 D ⧸ I ^ (n + 1), ∃ v : Fin 2 → 𝓞 D ⧸ I ^ n,
        cn v = m.act π (c₀ u) :=
      fun u => hcn.2.2.2.1 _ (hπtors _ (hc₀.1 u))
    choose ψ hψ using hψex
    have hψadd : ∀ u v, ψ (u + v) = ψ u + ψ v := by
      intro u v
      apply hcn.2.2.1
      rw [hψ, hcn.2.1, hψ, hψ, hc₀.2.1]
      exact m.act_addPt π (c₀ u) (c₀ v)
    have hψsmul : ∀ (z : 𝓞 D ⧸ I ^ (n + 1)) (u : Fin 2 → 𝓞 D ⧸ I ^ (n + 1)),
        ψ (fun i => z * u i) = fun i => redn z * ψ u i := by
      intro z u
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
      apply hcn.2.2.1
      rw [hredn_mk, hcn.2.2.2.2, hψ, hψ, hc₀.2.2.2.2, ← m.act_mul, ← m.act_mul,
        mul_comm π a]
    have hψsurj : Function.Surjective ψ := by
      intro w
      obtain ⟨z, hz, hzπ⟩ :=
        exists_mem_torsion_act_uniformizer_eq m x I hI π hπ hπ2 n (cn w) (hcn.1 w)
      obtain ⟨u, hu⟩ := hc₀.2.2.2.1 z hz
      refine ⟨u, hcn.2.2.1 ?_⟩
      rw [hψ, hu, hzπ]
    -- `ψ` kills the residue field: an `I`-divisible input has an `I`-divisible image
    have hC : ∀ u : Fin 2 → 𝓞 D ⧸ I ^ (n + 1), (∀ i, redk (u i) = 0) →
        ∀ i, redkn (ψ u i) = 0 := by
      intro u hu i
      have hdec : u = (fun j => u 0 * ![(1 : 𝓞 D ⧸ I ^ (n + 1)), 0] j)
          + (fun j => u 1 * ![(0 : 𝓞 D ⧸ I ^ (n + 1)), 1] j) :=
        funext (Fin.forall_fin_two.mpr ⟨by simp, by simp⟩)
      have h1 : ψ u
          = (fun j => redn (u 0) * ψ ![(1 : 𝓞 D ⧸ I ^ (n + 1)), 0] j)
          + (fun j => redn (u 1) * ψ ![(0 : 𝓞 D ⧸ I ^ (n + 1)), 1] j) := by
        conv_lhs => rw [hdec]
        rw [hψadd, hψsmul, hψsmul]
      rw [h1]
      simp only [Pi.add_apply, map_add, map_mul, hcomp, hu 0, hu 1, zero_mul, add_zero]
    -- a basis of the level `n+1` module lying over the standard one
    obtain ⟨t0, ht0⟩ := hψsurj ![(1 : 𝓞 D ⧸ I ^ n), 0]
    obtain ⟨t1, ht1⟩ := hψsurj ![(0 : 𝓞 D ⧸ I ^ n), 1]
    obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : (Fin 2 → 𝓞 D ⧸ I ^ (n + 1)) → (Fin 2 → 𝓞 D ⧸ I ^ (n + 1)),
        ∀ u i, Ψ u i = u 0 * t0 i + u 1 * t1 i :=
      ⟨fun u i => u 0 * t0 i + u 1 * t1 i, fun _ _ => rfl⟩
    have hΨadd : ∀ u v, Ψ (u + v) = Ψ u + Ψ v := by
      intro u v; funext i; simp only [hΨ, Pi.add_apply]; ring
    have hΨsmul : ∀ (z : 𝓞 D ⧸ I ^ (n + 1)) u,
        Ψ (fun i => z * u i) = fun i => z * Ψ u i := by
      intro z u; funext i; simp only [hΨ]; ring
    -- `ψ ∘ Ψ` is the reduction map
    have hA : ∀ u, ψ (Ψ u) = fun i => redn (u i) := by
      intro u
      have hsplit : Ψ u = (fun i => u 0 * t0 i) + (fun i => u 1 * t1 i) := by
        funext i; simp [hΨ]
      rw [hsplit, hψadd, hψsmul, hψsmul, ht0, ht1]
      exact funext (Fin.forall_fin_two.mpr ⟨by simp, by simp⟩)
    -- units of `𝒪_D/Iⁿ⁺¹` are detected in the residue field
    have hunit : ∀ z : 𝓞 D ⧸ I ^ (n + 1), redk z ≠ 0 → IsUnit z := by
      intro z hz
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
      have ha : a ∉ I := by
        intro haI
        exact hz (by rw [hredk_mk]; exact Ideal.Quotient.eq_zero_iff_mem.mpr haI)
      obtain ⟨y, i, hi, hyi⟩ := Ideal.IsMaximal.exists_inv_pow I ha (n + 1)
      have hmap := congrArg (Ideal.Quotient.mk (I ^ (n + 1))) hyi
      rw [map_add, map_mul, map_one, Ideal.Quotient.eq_zero_iff_mem.mpr hi, add_zero] at hmap
      exact ⟨⟨Ideal.Quotient.mk (I ^ (n + 1)) a, Ideal.Quotient.mk (I ^ (n + 1)) y,
        by rw [mul_comm]; exact hmap, hmap⟩, rfl⟩
    -- the determinant of the frame matrix is a unit
    have key : ∀ l0 l1 : 𝓞 D ⧸ I ^ (n + 1),
        redk (l0 * t0 0 + l1 * t1 0) = 0 → redk (l0 * t0 1 + l1 * t1 1) = 0 →
        redk l0 = 0 ∧ redk l1 = 0 := by
      intro l0 l1 h0 h1
      have hmem : ∀ i, redk (Ψ ![l0, l1] i) = 0 := by
        refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
        · simpa [hΨ] using h0
        · simpa [hΨ] using h1
      have h2 := hC (Ψ ![l0, l1]) hmem
      simp only [hA, hcomp] at h2
      exact ⟨by simpa using h2 0, by simpa using h2 1⟩
    have hdk : redk (t0 0 * t1 1 - t0 1 * t1 0) ≠ 0 := by
      intro hd
      obtain ⟨hA11, hA01⟩ := key (t1 1) (-(t0 1))
        (by rw [show t1 1 * t0 0 + -(t0 1) * t1 0 = t0 0 * t1 1 - t0 1 * t1 0 from by ring]
            exact hd)
        (by rw [show t1 1 * t0 1 + -(t0 1) * t1 1 = 0 from by ring, map_zero])
      obtain ⟨hA10, hA00⟩ := key (-(t1 0)) (t0 0)
        (by rw [show -(t1 0) * t0 0 + t0 0 * t1 0 = 0 from by ring, map_zero])
        (by rw [show -(t1 0) * t0 1 + t0 0 * t1 1 = t0 0 * t1 1 - t0 1 * t1 0 from by ring]
            exact hd)
      have hone : redk (1 : 𝓞 D ⧸ I ^ (n + 1)) = 0 :=
        (key 1 0 (by simpa using hA00) (by simpa using hA01)).1
      rw [map_one] at hone
      exact one_ne_zero hone
    obtain ⟨dinv, hdinv⟩ := (hunit _ hdk).exists_left_inv
    -- the explicit inverse of `Ψ`
    obtain ⟨Φ, hΦ⟩ : ∃ Φ : (Fin 2 → 𝓞 D ⧸ I ^ (n + 1)) → (Fin 2 → 𝓞 D ⧸ I ^ (n + 1)),
        ∀ v, Φ v = ![dinv * (v 0 * t1 1 - v 1 * t1 0), dinv * (v 1 * t0 0 - v 0 * t0 1)] :=
      ⟨fun v => ![dinv * (v 0 * t1 1 - v 1 * t1 0), dinv * (v 1 * t0 0 - v 0 * t0 1)],
        fun _ => rfl⟩
    have hΨΦ : ∀ v, Ψ (Φ v) = v := by
      intro v
      refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
      · simp only [hΨ, hΦ, Matrix.cons_val_zero, Matrix.cons_val_one]
        linear_combination (v 0) * hdinv
      · simp only [hΨ, hΦ, Matrix.cons_val_zero, Matrix.cons_val_one]
        linear_combination (v 1) * hdinv
    have hΦΨ : ∀ u, Φ (Ψ u) = u := by
      intro u
      refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
      · simp only [hΦ, hΨ, Matrix.cons_val_zero]
        linear_combination (u 0) * hdinv
      · simp only [hΦ, hΨ, Matrix.cons_val_zero, Matrix.cons_val_one]
        linear_combination (u 1) * hdinv
    -- the lifted frame
    obtain ⟨c', hc'def⟩ :
        ∃ c' : (Fin 2 → 𝓞 D ⧸ I ^ (n + 1)) → GeomFibrePt f x, ∀ u, c' u = c₀ (Ψ u) :=
      ⟨fun u => c₀ (Ψ u), fun _ => rfl⟩
    refine ⟨c', ⟨fun u => ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [hc'def]; exact hc₀.1 _
    · intro u v
      rw [hc'def, hc'def, hc'def, hΨadd]
      exact hc₀.2.1 (Ψ u) (Ψ v)
    · intro u v huv
      rw [hc'def, hc'def] at huv
      exact Function.LeftInverse.injective hΦΨ (hc₀.2.2.1 huv)
    · intro y hy
      obtain ⟨w, hw⟩ := hc₀.2.2.2.1 y hy
      exact ⟨Φ w, by rw [hc'def, hΨΦ]; exact hw⟩
    · intro a u
      rw [hc'def, hc'def, hΨsmul]
      exact hc₀.2.2.2.2 a (Ψ u)
    · intro u
      rw [hc'def, ← hψ (Ψ u), hA]

/-- **The `Iⁿ`-torsion is free of rank two over `𝒪_D/Iⁿ`, compatibly in
`n`** (PROVEN 2026-07-26 over `exists_levelTateFrame` and
`exists_levelTateFrame_succ`; abelian varieties — Mumford *Abelian
Varieties* §18, Silverman *AEC* III.7, Taylor 2002 §2).

This is the finite-level form of "the Tate module has rank two". It asks
for maps

  `c n : (𝒪_D/Iⁿ)²  →  A[Iⁿ]`

which are additive, `𝒪_D`-semilinear, bijective onto the `Iⁿ`-torsion,
and — the clause that makes the inverse limit in the parent work —
compatible with the two towers: multiplication by `π` on the abelian
variety corresponds to reduction `𝒪_D/Iⁿ⁺¹ → 𝒪_D/Iⁿ`.

HOW IT IS PROVEN. The compatibility clause is what distinguishes this
statement from "a frame exists at every level", and it is produced here
rather than assumed: `exists_levelTateFrame` supplies a frame at level
`0`, `exists_levelTateFrame_succ` lifts a frame at level `n` to one at
level `n+1` sitting over it along `·π`, and the tower is the resulting
`Nat.rec`. The dimension count `2 = 2g/[D:ℚ]` — the only place `hdim` is
used — lives entirely in `exists_levelTateFrame`; the lifting step is
commutative algebra over the artinian local ring `𝒪_D/Iⁿ⁺¹`. Both are
recorded in their own docstrings.

Note that `π` enters ONLY through the lifting step: the frames
themselves know nothing about it. -/
theorem exists_levelwiseTateFrame
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (hdim : SmoothOfRelativeDimension (Module.finrank ℚ D) f)
    (I : Ideal (NumberField.RingOfIntegers D)) (hI : I.IsMaximal)
    (π : NumberField.RingOfIntegers D) (hπ : π ∈ I) (hπ2 : π ∉ I ^ 2) :
    ∃ c : (n : ℕ) → (Fin 2 → NumberField.RingOfIntegers D ⧸ I ^ n) → GeomFibrePt f x,
      (∀ (n : ℕ) (u : Fin 2 → NumberField.RingOfIntegers D ⧸ I ^ n),
        c n u ∈ (m.torsion x (I ^ n)).1) ∧
      (∀ (n : ℕ) (u v : Fin 2 → NumberField.RingOfIntegers D ⧸ I ^ n),
        c n (u + v) = ab.add (c n u) (c n v)) ∧
      (∀ n : ℕ, Function.Injective (c n)) ∧
      (∀ (n : ℕ) (y : GeomFibrePt f x), y ∈ (m.torsion x (I ^ n)).1 → ∃ u, c n u = y) ∧
      (∀ (n : ℕ) (a : NumberField.RingOfIntegers D)
          (u : Fin 2 → NumberField.RingOfIntegers D ⧸ I ^ n),
        c n (fun i => Ideal.Quotient.mk (I ^ n) a * u i) = m.act a (c n u)) ∧
      (∀ (n : ℕ) (u : Fin 2 → NumberField.RingOfIntegers D ⧸ I ^ (n + 1)),
        m.act π (c (n + 1) u) =
          c n (fun i => Ideal.Quotient.factor
            (Ideal.pow_le_pow_right (Nat.le_succ n)) (u i))) := by
  classical
  -- the frame at level `0`, the base of the tower
  obtain ⟨c0, hc0⟩ := exists_levelTateFrame m x hdim I hI 0
  -- the lifting step, as a function by choice
  choose G hG1 hG2 using fun (n : ℕ)
      (cn : (Fin 2 → NumberField.RingOfIntegers D ⧸ I ^ n) → GeomFibrePt f x)
      (hcn : IsLevelTateFrame m x (I ^ n) cn) =>
    exists_levelTateFrame_succ m x hdim I hI π hπ hπ2 n cn hcn
  -- the tower: a frame at every level, each lying over its predecessor
  let seq : (n : ℕ) →
      {c : (Fin 2 → NumberField.RingOfIntegers D ⧸ I ^ n) → GeomFibrePt f x //
        IsLevelTateFrame m x (I ^ n) c} := fun n =>
    Nat.rec (motive := fun n =>
        {c : (Fin 2 → NumberField.RingOfIntegers D ⧸ I ^ n) → GeomFibrePt f x //
          IsLevelTateFrame m x (I ^ n) c})
      ⟨c0, hc0⟩ (fun k p => ⟨G k p.1 p.2, hG1 k p.1 p.2⟩) n
  exact ⟨fun n => (seq n).1,
    fun n u => (seq n).2.1 u,
    fun n u v => (seq n).2.2.1 u v,
    fun n => (seq n).2.2.2.1,
    fun n y hy => (seq n).2.2.2.2.1 y hy,
    fun n a u => (seq n).2.2.2.2.2 a u,
    fun n u => hG2 n (seq n).1 (seq n).2 u⟩

/-! #### The sub-leaves of `isOpen_stabilizer_torsion`

Openness of the pointwise stabilizer factors, cleanly and without loss,
into two statements that belong to two different theories, plus three
assemblies — one topological, one Galois-theoretic and one purely
ideal-theoretic — that are all PROVEN below:

* `locallyQuasiFinite_mulByNat` — ABELIAN VARIETIES, and the ONLY
  residual sorry of this cluster since 2026-07-26. Multiplication by a
  nonzero `n` on the abelian scheme has FINITE FIBRES. `A[N]`-finiteness
  itself (`finite_torsion_span_natCast`) is now PROVEN from it: see the
  paragraph *The cut through the multiplication morphism* below.
* `exists_fixingSubgroup_le_stabilizer_geomFibrePt` — SCHEME THEORY
  (spreading out). A SINGLE geometric point of the fibre is fixed by
  `Gal(F̄/E)` for some finite subextension `E/F`, i.e. it is defined over
  a finite extension of `F`. No abelian variety, no torsion, no ideal.
  **PROVEN 2026-07-26** from `LocallyOfFiniteType.stalkMap` and the
  residue-field description of `Spec F̄`-points.

The assemblies are `finite_torsion_of_ne_bot` (any nonzero ideal `J`
contains the nonzero rational integer `absNorm J`, so `A[J] ⊆ A[absNorm
J]`), `isOpen_stabilizer_geomFibrePt` (a subgroup containing an open
subgroup is open) and `isOpen_stabilizer_torsion` (a FINITE intersection
of open sets is open). It is in the last of these that finiteness of
`A[J]` is consumed: over an infinite torsion set the intersection would
not be open, which is why the first leaf cannot be dropped or weakened
to "each point is defined over a finite extension".

#### The cut through the multiplication morphism (2026-07-26)

`finite_torsion_span_natCast` used to be the sorry itself. It is now
PROVEN, over the single geometric leaf `locallyQuasiFinite_mulByNat`,
through the following chain — every step of which is proven here:

* `AbelianSchemeStruct.mulByNat n : A ⟶ A`, the multiplication-by-`n`
  MORPHISM. It exists with no fibre products and no Yoneda apparatus:
  the functor of points `RelPoint f ·` has a tautological point
  `RelPoint.self f = ⟨𝟙 A, _⟩` over the base point `f` itself, and
  `mulByNat n` is the underlying morphism of `n • RelPoint.self f`.
  Naturality of the group law (`pre_add`, `pre_zero`) upgrades to
  `pre_nsmul`, and `RelPoint.pre_self` — the Yoneda lemma in the only
  form needed — then gives `nsmul_val`: `(n • y).1 = y.1 ≫ mulByNat n`
  for EVERY relative point `y`. Likewise `zero_val` expresses the zero
  relative point through the zero section `zeroSection : S ⟶ A`.
* Hence `A_x[n] ⊆ {u : Spec F̄ ⟶ A | u ≫ mulByNat n = g ≫ zeroSection}`
  — the fibre of `mulByNat n` over one geometric point — and finiteness
  of the torsion set is finiteness of that fibre
  (`finite_nsmul_eq_zero_geomFibrePt`, `finite_fibre_mulByNat`).
* `finite_hom_fibre_of_isFinite`: a FINITE morphism has finitely many
  `Spec K`-points in each fibre. Proven by base change (`IsFinite` is
  stable under it), affineness of a finite scheme over a field, and the
  mathlib instance `Finite (S →ₐ[R] K)` for `Module.Finite R S`.
* `isProper_mulByNat`: `mulByNat n` is PROPER, for free — it commutes
  with `f` (`mulByNat_comp`), `f` is proper by `ab.proper`, and proper
  morphisms cancel on the right against a separated one
  (`IsProper.of_comp`).
* So by Zariski's main theorem in mathlib's form
  (`IsFinite.of_isProper_of_locallyQuasiFinite`) all that is left is
  QUASI-FINITENESS of `mulByNat n`, which is the leaf.

That is the honest residue: the whole arithmetic, Galois-theoretic and
commutative-algebraic content has been discharged, and what remains is
one statement of the theory of abelian varieties — `[n]` is an isogeny —
stated about a morphism of schemes, with no real multiplication, no
ideal of `𝒪_D`, no number field and no Galois action left in it.
-/

section MulByNat

variable {A S : Scheme.{u}} {f : A ⟶ S}

/-! The Yoneda layer of this section — `RelPoint.self`, `RelPoint.pre_self`,
`AbelianSchemeStruct.pre_nsmul`, `mulByNat`, `nsmul_val`, `zeroSection`,
`zero_val`, `mulByNat_comp` and `isProper_mulByNat` — now lives in
`Modularity/AbelianSchemeIsogeny.lean`, VERBATIM and under the same names,
and reaches this file through the `public import` at the top.

It had to move upstream because `exists_nsmul_eq_geomFibrePt`, far above,
is proven from it, and Lean's declaration order forbids a use before the
definition; reordering a file whose other leaves have their own owners
would have been the larger disturbance. Nothing in this section changed
otherwise: `locallyQuasiFinite_mulByNat` and everything derived from it
stay here. -/

open _root_.CategoryTheory.Limits in
/-- **A finite scheme over a field has finitely many sections** (PROVEN
2026-07-26).

`Z` is affine because a finite morphism is affine and `Spec K` is
affine, so `Z = Spec B` with `B = Γ(Z, ⊤)` a `Γ(Spec K, ⊤)`-algebra that
is `Module.Finite` — this is exactly the affine characterization of
`IsFinite`. A section `s : Spec K ⟶ Z` is determined by `s.appTop`
(`ext_of_isAffine`, since the TARGET `Z` is affine), and the section
identity `s ≫ g = 𝟙` says precisely that `s.appTop ≫ ΓSpecIso.hom` is a
`Γ(Spec K, ⊤)`-ALGEBRA map `B → K`. Mathlib's instance
`Finite (S →ₐ[R] K)` for `Module.Finite R S` and `K` a field finishes
it. -/
theorem finite_section_of_isFinite {Z : Scheme.{u}} {K : Type u} [Field K]
    (g : Z ⟶ Spec (CommRingCat.of K)) [IsFinite g] :
    {s : Spec (CommRingCat.of K) ⟶ Z | s ≫ g = 𝟙 _}.Finite := by
  classical
  haveI : IsAffine Z :=
    (HasAffineProperty.iff_of_isAffine (P := @IsAffineHom) (f := g)).mp inferInstance
  have hfin : RingHom.Finite (Scheme.Hom.appTop g).hom :=
    ((HasAffineProperty.iff_of_isAffine (P := @IsFinite) (f := g)).mp inferInstance).2
  letI : Algebra Γ(Spec (CommRingCat.of K), ⊤) K :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom.toAlgebra
  letI : Algebra Γ(Spec (CommRingCat.of K), ⊤) Γ(Z, ⊤) := (Scheme.Hom.appTop g).hom.toAlgebra
  haveI : Module.Finite Γ(Spec (CommRingCat.of K), ⊤) Γ(Z, ⊤) := hfin
  set Φ : (Spec (CommRingCat.of K) ⟶ Z) → (Γ(Z, ⊤) ⟶ CommRingCat.of K) :=
    fun s => Scheme.Hom.appTop s ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom with hΦ
  refine Set.Finite.of_finite_image (f := Φ) ?_ ?_
  · refine (Set.finite_range
      (fun ρ : Γ(Z, ⊤) →ₐ[Γ(Spec (CommRingCat.of K), ⊤)] K =>
        CommRingCat.ofHom ρ.toRingHom)).subset ?_
    rintro _ ⟨s, hs, rfl⟩
    have hcomm : Scheme.Hom.appTop g ≫ Φ s = (Scheme.ΓSpecIso (CommRingCat.of K)).hom := by
      rw [hΦ, ← Category.assoc, ← Scheme.Hom.comp_appTop, hs, Scheme.Hom.id_appTop,
        Category.id_comp]
    exact ⟨{ toRingHom := (Φ s).hom, commutes' := fun r => congrArg (fun t => t.hom r) hcomm },
      CommRingCat.ofHom_hom _⟩
  · intro s₁ _ s₂ _ h
    refine ext_of_isAffine ?_
    exact (CategoryTheory.cancel_mono (Scheme.ΓSpecIso (CommRingCat.of K)).hom).mp h

open _root_.CategoryTheory.Limits in
/-- **A finite morphism has finitely many `Spec K`-points in each
fibre** (PROVEN 2026-07-26).

The set `{u | u ≫ φ = w}` is the set of sections of the base change of
`φ` along `w`, and `IsFinite` is stable under base change, so this is
`finite_section_of_isFinite` transported through the universal property
of the pullback. -/
theorem finite_hom_fibre_of_isFinite {X Y : Scheme.{u}} (φ : X ⟶ Y) [IsFinite φ]
    {K : Type u} [Field K] (w : Spec (CommRingCat.of K) ⟶ Y) :
    {u : Spec (CommRingCat.of K) ⟶ X | u ≫ φ = w}.Finite := by
  refine ((finite_section_of_isFinite (pullback.snd φ w)).image
    (fun s => s ≫ pullback.fst φ w)).subset ?_
  intro u hu
  exact ⟨pullback.lift u (𝟙 _) (by simpa using hu), pullback.lift_snd _ _ _,
    pullback.lift_fst _ _ _⟩

/-- **Multiplication by a nonzero `n` on an abelian scheme is
QUASI-FINITE** (PROVEN 2026-07-26 over `finite_preimage_mulByNat` in
`Modularity/AbelianSchemeIsogeny.lean`; Mumford *Abelian Varieties* §6
Application 2 and §18, Milne *Abelian Varieties* I.7, Silverman *AEC*
III.6).

Every fibre of `[n] : A ⟶ A` is a finite set of points. Equivalently —
since `[n]` is PROPER for free (`isProper_mulByNat`) — `[n]` is a FINITE
morphism, of degree `n^{2g}` on each fibre of `f`.

**This used to be the leaf, and it is now one step above it.**
`LocallyQuasiFinite` is (locally of finite type) + (quasi-finite fibres),
and the first half is FREE (`locallyOfFiniteType_mulByNat`, from
`[n] ≫ f = f` and the smoothness of `f`), so stating the leaf at this
level asked a prover for something already proven. Mathlib's
`LocallyQuasiFinite.of_finite_preimage_singleton` needs exactly
`[LocallyOfFiniteType]` plus finiteness of the point-set fibres, so the
residual abelian-variety content is precisely `finite_preimage_mulByNat`,
which is where the sorry now lives.

The remaining leaf is a pure statement of the theory of abelian
varieties: no Galois action, no real multiplication, no ideal of `𝒪_D`,
no number field, no topology.

The argument. Fibrewise over `S` this is the classical statement that
`[n]` is an isogeny of abelian varieties. Fix a geometric fibre `A_s`,
of dimension `g`; for a symmetric ample line bundle `L` on `A_s` the
theorem of the cube gives `[n]^* L ≅ L^{n²}`, which is again ample, and
a morphism pulling an ample bundle back to an ample bundle has finite
fibres. The fibres of `[n]` are then torsors under `ker[n]`, which is
finite of order `n^{2g}`. The fibres of `mulByNat n` as a morphism of
schemes are the fibres of the `[n]` of each fibre of `f`, so
quasi-finiteness over `S` is exactly the fibrewise statement.

`hn` is LOAD-BEARING: `mulByNat 0 = f ≫ zeroSection` is constant on each
fibre, so its fibre over a point of the zero section is a whole fibre of
`f`, infinite as soon as `g ≥ 1`.

MISSING MACHINERY. Mathlib at this pin does have group schemes — as
`GrpObj` objects of `Over (Spec K)`, with
`AlgebraicGeometry.isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed`
(a proper geometrically integral group scheme over a field is
commutative) and `AlgebraicGeometry.smooth_of_grpObj` in
`Mathlib/AlgebraicGeometry/Group/{Abelian,Smooth}.lean`. What it does
NOT have is any isogeny theory: no `[n]`, no theorem of the cube, no
degree, no `AbelianVariety`. Supplying that package is what this leaf
asks for. (The blanket claim in the header of
`Modularity/AbelianScheme.lean` that the pin has no group-scheme notion
at all is therefore out of date; the search there predates
`Mathlib/AlgebraicGeometry/Group/`.)

THE REDUCTION TO FIBRES IS ALREADY IN THE PIN — start from it rather
than rediscover it (verified 2026-07-26 by reading
`Mathlib/AlgebraicGeometry/Morphisms/QuasiFinite.lean`):

  `AlgebraicGeometry.LocallyQuasiFinite.of_fiberToSpecResidueField`
    `(∀ x, LocallyQuasiFinite (f.fiberToSpecResidueField x)) →`
    `LocallyQuasiFinite f`

So the informal sentence above — "quasi-finiteness over `S` is exactly
the fibrewise statement" — is a NAMED LEMMA, and it carries no
quasi-compactness hypothesis. Once over a field, three further criteria
apply: `locallyQuasiFinite_iff_isFinite_fiber` (needs `QuasiCompact`,
which `isProper_mulByNat` supplies),
`locallyQuasiFinite_iff_isDiscrete_preimage_singleton` and
`locallyQuasiFinite_iff_finite_preimage_singleton`. That list is
COMPLETE: the only ways to obtain `LocallyQuasiFinite` at this pin are
`IsFinite`, `IsImmersion`, composition, base change, the
`HasRingHomProperty … RingHom.QuasiFinite` affine-local criterion, and
those fibrewise lemmas.

CONSEQUENCE FOR DISPATCH: what this leaf really asks is the classical
statement and nothing more — `[n]` on an abelian variety OVER A FIELD
has finite fibres. Do NOT cut a separate "fibrewise" node out of it:
the reduction is a single mathlib lemma, so such a node would be a
repackaging that adds a leaf without moving any mathematics, and the
theorem of the cube would remain the whole of the residual content. -/
theorem locallyQuasiFinite_mulByNat (ab : AbelianSchemeStruct f) (n : ℕ) (hn : n ≠ 0) :
    LocallyQuasiFinite (ab.mulByNat n) :=
  haveI := ab.locallyOfFiniteType_mulByNat n
  LocallyQuasiFinite.of_finite_preimage_singleton _ (finite_preimage_mulByNat ab n hn)

/-- **Multiplication by a nonzero `n` on an abelian scheme is a FINITE
morphism** (PROVEN 2026-07-26 over `locallyQuasiFinite_mulByNat`).

Properness is free (`isProper_mulByNat`), so this is Zariski's main
theorem in mathlib's form, `IsFinite.of_isProper_of_locallyQuasiFinite`:
proper plus quasi-finite is finite. -/
theorem isFinite_mulByNat (ab : AbelianSchemeStruct f) (n : ℕ) (hn : n ≠ 0) :
    IsFinite (ab.mulByNat n) :=
  haveI := ab.isProper_mulByNat n
  haveI := locallyQuasiFinite_mulByNat ab n hn
  IsFinite.of_isProper_of_locallyQuasiFinite _

/-- **The fibres of `[n]` on geometric points are finite** (PROVEN
2026-07-26). -/
theorem finite_fibre_mulByNat (ab : AbelianSchemeStruct f) (n : ℕ) (hn : n ≠ 0)
    {K : Type u} [Field K] (w : Spec (CommRingCat.of K) ⟶ A) :
    {u : Spec (CommRingCat.of K) ⟶ A | u ≫ ab.mulByNat n = w}.Finite :=
  haveI := isFinite_mulByNat ab n hn
  finite_hom_fibre_of_isFinite (ab.mulByNat n) w

/-- **The `n`-torsion of the geometric points of a fibre is finite**
(PROVEN 2026-07-26 over `locallyQuasiFinite_mulByNat`).

This is `finite_torsion_span_natCast` with everything arithmetic
stripped off: no `Mult`, no `𝒪_D`, no ideal, no number field. By
`nsmul_val` and `zero_val` the condition `n • y = 0` says exactly that
the underlying morphism `y.1` lies in the fibre of `mulByNat n` over the
geometric point `(specAlgClos F ≫ x) ≫ zeroSection`, and `y ↦ y.1` is
injective. -/
theorem finite_nsmul_eq_zero_geomFibrePt (ab : AbelianSchemeStruct f)
    {F : Type u} [Field F] (x : Spec (CommRingCat.of F) ⟶ S) (n : ℕ) (hn : n ≠ 0) :
    letI := ab.addCommGroup (specAlgClos F ≫ x)
    {y : GeomFibrePt f x | n • y = 0}.Finite := by
  letI := ab.addCommGroup (specAlgClos F ≫ x)
  refine Set.Finite.of_finite_image ?_
    (fun a _ b _ h => Subtype.ext h : Set.InjOn Subtype.val {y : GeomFibrePt f x | n • y = 0})
  refine (finite_fibre_mulByNat ab n hn ((specAlgClos F ≫ x) ≫ ab.zeroSection)).subset ?_
  rintro _ ⟨y, hy, rfl⟩
  show y.1 ≫ ab.mulByNat n = _
  rw [← ab.nsmul_val n y, hy]
  exact ab.zero_val _

end MulByNat

/-- **`A[N]` is finite for a nonzero rational integer `N`** (PROVEN
2026-07-26 over the single abelian-variety leaf
`locallyQuasiFinite_mulByNat`; Mumford *Abelian Varieties* §18,
Silverman *AEC* III.6, Milne *Abelian Varieties* I.7).

The set of geometric points of the fibre killed by `N` is finite.

HOW IT IS PROVEN. `Ideal.span {(N : 𝒪_D)}` contains `(N : 𝒪_D)`, so a
point of the torsion set satisfies `(N : 𝒪_D) • y = 0`, which is
`N • y = 0` for the underlying `ℕ`-action (`Nat.cast_smul_eq_nsmul`) —
this is the only place the real-multiplication datum `m` is used, and it
is used only through the fact that `act` is a ring action. The rest is
`finite_nsmul_eq_zero_geomFibrePt`: the `N`-torsion is a fibre of the
multiplication morphism `mulByNat N`, which is proper for free and
finite once quasi-finite. See the *cut through the multiplication
morphism* paragraph above for the full chain.

`hN` is load-bearing: `A_x[0]` is all of `A_x(F̄)`, which is infinite as
soon as `g ≥ 1`; it is consumed by `locallyQuasiFinite_mulByNat`.

Note what is NOT needed: no `hdim`, no real-multiplication hypothesis,
no totally-real assumption, and no faithfulness of `m` — the statement
is about the ideal `(N)` generated by a rational integer. That is why
this statement carries the bare binders of its consumer. -/
theorem finite_torsion_span_natCast
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (N : ℕ) (hN : N ≠ 0) :
    ((m.torsion x (Ideal.span {(N : NumberField.RingOfIntegers D)})).1).Finite := by
  letI : AddCommGroup (GeomFibrePt f x) := ab.addCommGroup (specAlgClos F ≫ x)
  letI : Module (NumberField.RingOfIntegers D) (GeomFibrePt f x) :=
    m.module (specAlgClos F ≫ x)
  refine (finite_nsmul_eq_zero_geomFibrePt ab x N hN).subset ?_
  intro y hy
  have h := (Submodule.mem_torsionBySet_iff _ _).mp hy
    ⟨(N : NumberField.RingOfIntegers D), Ideal.mem_span_singleton_self _⟩
  show N • y = 0
  rw [← Nat.cast_smul_eq_nsmul (NumberField.RingOfIntegers D)]
  exact h

/-- **The `J`-torsion of a geometric fibre is finite** (PROVEN
2026-07-26 over `finite_torsion_span_natCast`).

For `J ≠ 0` the set of geometric points of the fibre killed by every
element of `J` is finite.

The reduction to a rational integer is pure commutative algebra and is
carried out below: `𝒪_D/J` is finite, so its cardinality
`N = absNorm J` is a nonzero natural number lying in `J`
(`Ideal.absNorm_mem`, `Ideal.absNorm_eq_zero_iff`), whence
`(N) ⊆ J` and therefore `A[J] ⊆ A[N]` — torsion is ANTITONE in the
annihilating set (`Submodule.torsionBySet_le_torsionBySet_of_subset`).

`hJ` is load-bearing on both sides: for `J = 0` the "torsion" is the
whole group of geometric points of `A_x`, and `absNorm ⊥ = 0`. -/
theorem finite_torsion_of_ne_bot
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (J : Ideal (NumberField.RingOfIntegers D)) (hJ : J ≠ ⊥) :
    ((m.torsion x J).1).Finite := by
  have hN : Ideal.absNorm J ≠ 0 := fun h => hJ (Ideal.absNorm_eq_zero_iff.mp h)
  refine (finite_torsion_span_natCast m x (Ideal.absNorm J) hN).subset ?_
  letI : AddCommGroup (GeomFibrePt f x) := ab.addCommGroup (specAlgClos F ≫ x)
  letI : Module (NumberField.RingOfIntegers D) (GeomFibrePt f x) :=
    m.module (specAlgClos F ≫ x)
  exact fun y hy => Submodule.torsionBySet_le_torsionBySet_of_subset
    (SetLike.coe_subset_coe.mpr (Ideal.span_singleton_absNorm_le J)) hy

/-- **A geometric point of the fibre is defined over a finite extension
of `F`** (PROVEN 2026-07-26 — scheme theory; EGA IV 8.8, Stacks
01ZC/01ZM).

For every `y : Spec F̄ ⟶ A` lying over `Spec F̄ ⟶ Spec F --x--> S` there
is a finite subextension `E/F` inside `F̄` such that every `σ ∈ Γ_F`
fixing `E` pointwise fixes `y`.

HOW IT IS PROVEN, in the residue-field form, which avoids both affine
opens and the limit formalism. A morphism `Spec K ⟶ X` out of the
spectrum of a field is the same thing as a point `p` of `X` together
with a field map `ψ : κ(p) ⟶ K` (`Scheme.SpecToEquivOfField`,
`Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField`), and
under that description precomposition with `Spec σ` is postcomposition
of `ψ` with `σ`. So the goal becomes `σ ∘ ψ = ψ`.

Since `A.residue p : 𝒪_{A,p} ↠ κ(p)` is an epimorphism it is enough to
prove `σ ∘ Ψ = Ψ` for `Ψ := A.residue p ≫ ψ`, and now
`LocallyOfFiniteType.stalkMap` — this is the ONLY geometric input, and
it comes from `ab.proper`, which extends `LocallyOfFiniteType` — says
that `f.stalkMap p : 𝒪_{S,f p} ⟶ 𝒪_{A,p}` is ESSENTIALLY OF FINITE
TYPE. Two ring maps out of an essentially-of-finite-type extension that
agree on the base and on the finitely many essential generators are
equal (`RingHom.EssFiniteType.ext`). Taking
`E := F(Ψ g₁, …, Ψ gₙ)` for `gᵢ` those generators, each `Ψ gᵢ` is
algebraic over `F` because `F̄/F` is, so `E/F` is finite; and any `σ`
fixing `E` fixes the generators by construction and fixes the base
because the composite `𝒪_{S,f p} ⟶ 𝒪_{A,p} ⟶ F̄` factors through `F` —
that last point is exactly the hypothesis `y.2`, read through the same
residue-field description of `Spec F̄ ⟶ Spec F --x--> S`.

The group structure plays NO role: this is a statement about an
arbitrary morphism `Spec F̄ ⟶ A` over `x`, and `ab` enters only through
`ab.proper`. It is deliberately stated for a single point, because that
is the form in which spreading out is true — the uniform version over an
infinite set of points is FALSE, and it is finiteness of `A[J]`
(`finite_torsion_of_ne_bot`) that repairs it. -/
theorem exists_fixingSubgroup_le_stabilizer_geomFibrePt
    {A S : Scheme.{u}} {f : A ⟶ S} (ab : AbelianSchemeStruct f)
    {F : Type u} [Field F] (x : Spec (CommRingCat.of F) ⟶ S)
    (y : GeomFibrePt f x) :
    ∃ (E : IntermediateField F (AlgebraicClosure F)) (_ : FiniteDimensional F E),
      ∀ σ : Field.absoluteGaloisGroup F,
        σ ∈ E.fixingSubgroup → ab.galSMul x σ y = y := by
  classical
  haveI : IsProper f := ab.proper
  -- The point of `A` underlying the geometric point, and the induced map on residue fields.
  set p : A := y.1 (IsLocalRing.closedPoint (AlgebraicClosure F))
  set ψ : A.residueField p ⟶ CommRingCat.of (AlgebraicClosure F) :=
    Scheme.descResidueField (Scheme.stalkClosedPointTo y.1)
  have hy1 : Spec.map ψ ≫ A.fromSpecResidueField p = y.1 :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField _ A y.1
  -- The same data for the base point `x`, whose residue field lands in `F` itself.
  set q : S := x (IsLocalRing.closedPoint F)
  set χ : S.residueField q ⟶ CommRingCat.of F :=
    Scheme.descResidueField (Scheme.stalkClosedPointTo x)
  have hx1 : Spec.map χ ≫ S.fromSpecResidueField q = x :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField _ S x
  set ι : CommRingCat.of F ⟶ CommRingCat.of (AlgebraicClosure F) :=
    CommRingCat.ofHom (algebraMap F (AlgebraicClosure F)) with hιdef
  -- `θ` is the residue-field datum of the composite `Spec F̄ ⟶ A ⟶ S`.
  set θ : S.residueField (f p) ⟶ CommRingCat.of (AlgebraicClosure F) :=
    f.residueFieldMap p ≫ ψ with hθdef
  have hkey : Spec.map θ ≫ S.fromSpecResidueField (f p)
      = Spec.map (χ ≫ ι) ≫ S.fromSpecResidueField q := by
    have h1 : Spec.map θ ≫ S.fromSpecResidueField (f p) = y.1 ≫ f := by
      rw [hθdef, Spec.map_comp, Category.assoc,
        Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc, hy1]
    have h2 : Spec.map (χ ≫ ι) ≫ S.fromSpecResidueField q = specAlgClos F ≫ x := by
      rw [Spec.map_comp, Category.assoc, hx1, specAlgClos, hιdef]
    rw [h1, h2, y.2]
  -- Hence `θ` factors through `F`.
  have hsig : (⟨f p, θ⟩ : Σ z : S, S.residueField z ⟶ CommRingCat.of (AlgebraicClosure F))
      = ⟨q, χ ≫ ι⟩ :=
    (Scheme.SpecToEquivOfField (AlgebraicClosure F) S).symm.injective hkey
  obtain ⟨e, hθ⟩ := Scheme.SpecToEquivOfField_eq_iff.mp hsig
  replace hθ : θ = (S.residueFieldCongr e).hom ≫ (χ ≫ ι) := hθ
  have hθrange : ∀ z, ∃ w : F, θ.hom z = algebraMap F (AlgebraicClosure F) w := by
    intro z
    refine ⟨χ.hom ((S.residueFieldCongr e).hom.hom z), ?_⟩
    rw [hθ]
    rfl
  -- `f` is locally of finite type, so the stalk map is essentially of finite type.
  have hst : (f.stalkMap p).hom.EssFiniteType := LocallyOfFiniteType.stalkMap f p
  set Ψ : A.presheaf.stalk p ⟶ CommRingCat.of (AlgebraicClosure F) :=
    A.residue p ≫ ψ with hΨdef
  have hcomp : f.stalkMap p ≫ Ψ = S.residue (f p) ≫ θ := by
    rw [hΨdef, hθdef, ← Category.assoc, ← Scheme.residue_residueFieldMap, Category.assoc]
  -- The finitely many essential generators, pushed into `F̄`.
  set gens : Finset (AlgebraicClosure F) := hst.finset.image (fun z => Ψ.hom z)
  refine ⟨IntermediateField.adjoin F (gens : Set (AlgebraicClosure F)),
    IntermediateField.finiteDimensional_adjoin
      (fun z _ => Algebra.IsIntegral.isIntegral (R := F) z), ?_⟩
  intro σ hσ
  have hfix : ∀ z ∈ gens, (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) z = z := by
    intro z hz
    exact (mem_fixingSubgroup_iff _).mp hσ z
      (IntermediateField.subset_adjoin F (gens : Set (AlgebraicClosure F)) hz)
  set σr : CommRingCat.of (AlgebraicClosure F) ⟶ CommRingCat.of (AlgebraicClosure F) :=
    CommRingCat.ofHom
      ((σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F).toAlgHom.toRingHom)
  have hΨσ : Ψ ≫ σr = Ψ := by
    refine CommRingCat.hom_ext (RingHom.EssFiniteType.ext hst ?_ ?_)
    · refine RingHom.ext fun z => ?_
      have hz : Ψ.hom ((f.stalkMap p).hom z) = θ.hom ((S.residue (f p)).hom z) :=
        congrArg
          (fun t : S.presheaf.stalk (f p) ⟶ CommRingCat.of (AlgebraicClosure F) => t.hom z) hcomp
      obtain ⟨w, hw⟩ := hθrange ((S.residue (f p)).hom z)
      show (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) (Ψ.hom ((f.stalkMap p).hom z))
        = Ψ.hom ((f.stalkMap p).hom z)
      rw [hz, hw]
      exact (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F).commutes w
    · intro z hz
      exact hfix _ (Finset.mem_image_of_mem _ hz)
  have hψσ : ψ ≫ σr = ψ := by
    rw [← cancel_epi (A.residue p), ← Category.assoc]
    exact hΨσ
  refine Subtype.ext ?_
  show specGal σ ≫ y.1 = y.1
  calc specGal σ ≫ y.1
      = Spec.map σr ≫ Spec.map ψ ≫ A.fromSpecResidueField p := by rw [hy1]; rfl
    _ = Spec.map (ψ ≫ σr) ≫ A.fromSpecResidueField p := by rw [Spec.map_comp]; simp
    _ = y.1 := by rw [hψσ, hy1]

/-- **The stabilizer of a single geometric point is open in `Γ_F`**
(PROVEN over `exists_fixingSubgroup_le_stabilizer_geomFibrePt`).

The stabilizer is a SUBGROUP of `Γ_F` — that is the content of
`AbelianSchemeStruct.geomFibreAction`, which makes `galSMul` an honest
`DistribMulAction` — and by the leaf it contains `Gal(F̄/E)` for some
finite `E/F`. The Krull topology makes `Gal(F̄/E)` open
(`IntermediateField.fixingSubgroup_isOpen`), and a subgroup of a
topological group containing an open subgroup is open
(`Subgroup.isOpen_mono`, i.e. it is the union of the cosets of that open
subgroup that it contains). -/
theorem isOpen_stabilizer_geomFibrePt
    {A S : Scheme.{u}} {f : A ⟶ S} (ab : AbelianSchemeStruct f)
    {F : Type u} [Field F] (x : Spec (CommRingCat.of F) ⟶ S)
    (y : GeomFibrePt f x) :
    IsOpen {σ : Field.absoluteGaloisGroup F | ab.galSMul x σ y = y} := by
  letI : AddCommGroup (GeomFibrePt f x) := ab.addCommGroup (specAlgClos F ≫ x)
  letI : DistribMulAction (Field.absoluteGaloisGroup F) (GeomFibrePt f x) :=
    ab.geomFibreAction x
  obtain ⟨E, hEfin, hE⟩ := exists_fixingSubgroup_le_stabilizer_geomFibrePt ab x y
  have hset : {σ : Field.absoluteGaloisGroup F | ab.galSMul x σ y = y}
      = ((MulAction.stabilizer (Field.absoluteGaloisGroup F) y : Subgroup _) : Set _) :=
    rfl
  rw [hset]
  exact Subgroup.isOpen_mono (H₁ := E.fixingSubgroup) hE E.fixingSubgroup_isOpen

/-- **The pointwise stabilizer of the `J`-torsion is open in `Γ_F`**
(PROVEN 2026-07-26 over the two leaves `finite_torsion_of_ne_bot` and
`exists_fixingSubgroup_le_stabilizer_geomFibrePt`; Silverman *AEC*
III.7, Mumford §18).

For a nonzero ideal `J` of `𝒪_D` the `J`-torsion of the geometric fibre
is a FINITE set — it is contained in `A[N]` for `N` any nonzero rational
integer with `N · A[J] = 0`, and `A[N] ≅ (ℤ/N)^{2g}` — and every one of
its points is defined over a finite extension of `F`, because `f` is
locally of finite type. Hence the subgroup of `Γ_F` fixing `A[J]`
pointwise contains the open subgroup `Γ_{F'}` for `F'` a finite
extension of `F` splitting the finitely many points, and a subgroup of a
topological group containing an open subgroup is open.

The proof below is exactly that sentence, in the order: rewrite the
stabilizer as the intersection over `y ∈ A[J]` of the single-point
stabilizers; each is open by `isOpen_stabilizer_geomFibrePt`; the
intersection is over a FINITE index set by `finite_torsion_of_ne_bot`,
so `Set.Finite.isOpen_biInter` applies. Both leaves are needed and
neither can be weakened: without finiteness the intersection of opens
need not be open, and without the single-point statement there is no
open set to intersect.

This is the ONLY input needed for CONTINUITY of the `I`-adic
representation: nothing else in this development knows that the Tate
module is a profinite object. -/
theorem isOpen_stabilizer_torsion
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (J : Ideal (NumberField.RingOfIntegers D)) (hJ : J ≠ ⊥) :
    IsOpen {σ : Field.absoluteGaloisGroup F |
      ∀ y ∈ (m.torsion x J).1, ab.galSMul x σ y = y} := by
  have hset : {σ : Field.absoluteGaloisGroup F |
        ∀ y ∈ (m.torsion x J).1, ab.galSMul x σ y = y}
      = ⋂ y ∈ (m.torsion x J).1,
          {σ : Field.absoluteGaloisGroup F | ab.galSMul x σ y = y} := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
  rw [hset]
  exact (finite_torsion_of_ne_bot m x J hJ).isOpen_biInter
    fun y _ => isOpen_stabilizer_geomFibrePt ab x y

/-! ### Comparing the `ℤ_q`-module topology with the `P`-adic topology

The five lemmas below are the commutative-algebra half of
`exists_galoisRep_of_isOpen_congruence`: for a coefficient ring `O` that
is finite (and free) over `ℤ_q` and carries the `ℤ_q`-module topology,
the powers of any proper ideal `P ∋ q` form a NEIGHBOURHOOD BASIS of `0`.

The two halves of that statement are proved by different arguments.

*Openness of `Pⁿ`* comes from below: `q ∈ P` gives `(qⁿ) ≤ Pⁿ`, and the
principal ideal `(qⁿ)` is open because, read through a `ℤ_q`-basis of
`O`, it is exactly the set of vectors all of whose coordinates lie in the
open ideal `(qⁿ) ⊆ ℤ_q` — the content of `isOpen_span_natCast_pow`.

*Cofinality* comes from above, by COMPACTNESS rather than by the
nilpotence argument sketched in the leaf's original docstring: `O` is
compact (a continuous image of `ℤ_qⁿ`) and Hausdorff, the `Pⁿ` are
closed and decreasing, and `⋂ₙ Pⁿ = 0` by Krull's intersection theorem
in the Noetherian local ring `O`; so a decreasing sequence of nonempty
compact sets `Pⁿ \ U` would have nonempty intersection, which is absurd.
This avoids having to produce the Artinian structure of `O/qO`. -/

section CongruenceTopology

/-- A finite `ℤ_q`-module with the module topology is COMPACT: it is a
continuous image of `ℤ_qⁿ`, which is compact because `ℤ_q` is. -/
theorem compactSpace_of_isModuleTopology_padicInt (q : ℕ) [Fact q.Prime] (O : Type*)
    [AddCommGroup O] [Module ℤ_[q] O] [TopologicalSpace O] [Module.Finite ℤ_[q] O]
    [IsModuleTopology ℤ_[q] O] : CompactSpace O := by
  haveI : ContinuousAdd O := IsModuleTopology.toContinuousAdd ℤ_[q] O
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' ℤ_[q] O
  exact ⟨hf.range_eq ▸ isCompact_range (IsModuleTopology.continuous_of_linearMap f)⟩

/-- A finite FREE `ℤ_q`-module with the module topology is HAUSDORFF: the
coordinate map to `ℤ_qⁱ` is continuous and injective. -/
theorem t2Space_of_isModuleTopology_padicInt (q : ℕ) [Fact q.Prime] (O : Type*)
    [AddCommGroup O] [Module ℤ_[q] O] [TopologicalSpace O] [Module.Finite ℤ_[q] O]
    [Module.Free ℤ_[q] O] [IsModuleTopology ℤ_[q] O] : T2Space O := by
  classical
  haveI : Fintype (Module.Free.ChooseBasisIndex ℤ_[q] O) :=
    Module.Free.ChooseBasisIndex.fintype ℤ_[q] O
  exact T2Space.of_injective_continuous
    (Module.Free.chooseBasis ℤ_[q] O).equivFun.injective
    (IsModuleTopology.continuous_of_linearMap
      (Module.Free.chooseBasis ℤ_[q] O).equivFun.toLinearMap)

/-- A ring finite over `ℤ_q` is Noetherian. -/
theorem isNoetherianRing_of_finite_padicInt (q : ℕ) [Fact q.Prime] (O : Type*) [CommRing O]
    [Algebra ℤ_[q] O] [Module.Finite ℤ_[q] O] : IsNoetherianRing O :=
  IsNoetherianRing.of_finite ℤ_[q] O

/-- **The principal ideal `(qⁿ)` is open in `O`.** Read through a
`ℤ_q`-basis, it is the set of vectors all of whose coordinates lie in
`(qⁿ) ⊆ ℤ_q`, and that ideal is open in `ℤ_q` (it is a power of the
maximal ideal of the compact Noetherian local ring `ℤ_q`). -/
theorem isOpen_span_natCast_pow (q : ℕ) [Fact q.Prime] (O : Type*) [CommRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [Algebra ℤ_[q] O] [Module.Finite ℤ_[q] O]
    [Module.Free ℤ_[q] O] [IsModuleTopology ℤ_[q] O] (n : ℕ) :
    IsOpen ((Ideal.span {(q : O) ^ n} : Ideal O) : Set O) := by
  classical
  haveI : Fintype (Module.Free.ChooseBasisIndex ℤ_[q] O) :=
    Module.Free.ChooseBasisIndex.fintype ℤ_[q] O
  set b := Module.Free.chooseBasis ℤ_[q] O with hb
  have hmap : (algebraMap ℤ_[q] O) ((q : ℤ_[q]) ^ n) = (q : O) ^ n := by
    rw [map_pow, map_natCast]
  -- the coordinatewise description of `(qⁿ)`
  have hspan : ((Ideal.span {(q : O) ^ n} : Ideal O) : Set O) =
      b.equivFun ⁻¹' (Set.univ.pi fun _ =>
        ((Ideal.span {(q : ℤ_[q]) ^ n} : Ideal ℤ_[q]) : Set ℤ_[q])) := by
    ext x
    simp only [SetLike.mem_coe, Ideal.mem_span_singleton, Set.mem_preimage, Set.mem_pi,
      Set.mem_univ, forall_const, b.equivFun_apply]
    constructor
    · rintro ⟨y, rfl⟩ i
      refine ⟨b.repr y i, ?_⟩
      have hy : (q : O) ^ n * y = ((q : ℤ_[q]) ^ n) • y := by
        rw [Algebra.smul_def, hmap]
      rw [hy, map_smul, Finsupp.smul_apply, smul_eq_mul]
    · intro h
      choose c hc using h
      refine ⟨∑ i, c i • b i, ?_⟩
      have hy : (q : O) ^ n * ∑ i, c i • b i = ((q : ℤ_[q]) ^ n) • ∑ i, c i • b i := by
        rw [Algebra.smul_def, hmap]
      rw [hy, Finset.smul_sum]
      conv_lhs => rw [← b.sum_repr x]
      exact Finset.sum_congr rfl fun i _ => by rw [hc i, mul_smul]
  rw [hspan]
  refine IsOpen.preimage (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap)
    (isOpen_set_pi Set.finite_univ fun _ _ => ?_)
  have hpow : (Ideal.span {(q : ℤ_[q]) ^ n} : Ideal ℤ_[q])
      = IsLocalRing.maximalIdeal ℤ_[q] ^ n := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow]
  rw [hpow]
  exact IsLocalRing.isOpen_maximalIdeal_pow ℤ_[q] n

/-- **Every power of a proper ideal containing `q` is open.** -/
theorem isOpen_pow_of_natCast_mem (q : ℕ) [Fact q.Prime] {O : Type*} [CommRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [Algebra ℤ_[q] O] [Module.Finite ℤ_[q] O]
    [Module.Free ℤ_[q] O] [IsModuleTopology ℤ_[q] O] {P : Ideal O} (hPq : (q : O) ∈ P)
    (n : ℕ) : IsOpen ((P ^ n : Ideal O) : Set O) := by
  refine Submodule.isOpen_mono (U := Ideal.span {(q : O) ^ n}) (P := P ^ n) ?_
    (isOpen_span_natCast_pow q O n)
  rw [Ideal.span_le, Set.singleton_subset_iff]
  exact Ideal.pow_mem_pow hPq n

/-- **Every neighbourhood of `0` contains a power of `P`** — the
COFINALITY half of the comparison between the `ℤ_q`-module topology and
the `P`-adic one, and the only place where compactness of `O` is used.

Note that this half needs only `P ≠ ⊤`, not `q ∈ P`: it holds for the
zero ideal as well, whose powers are `{0}`. The hypothesis `q ∈ P` is
what makes the powers OPEN, and it enters through
`isOpen_pow_of_natCast_mem` in `hasBasis_pow_nhds_zero` below. -/
theorem exists_pow_subset_of_mem_nhds (q : ℕ) [Fact q.Prime] {O : Type*} [CommRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [Algebra ℤ_[q] O] [IsLocalRing O]
    [Module.Finite ℤ_[q] O] [Module.Free ℤ_[q] O] [IsModuleTopology ℤ_[q] O] {P : Ideal O}
    (hPtop : P ≠ ⊤) {V : Set O} (hV : V ∈ nhds (0 : O)) :
    ∃ n : ℕ, ((P ^ n : Ideal O) : Set O) ⊆ V := by
  haveI : CompactSpace O := compactSpace_of_isModuleTopology_padicInt q O
  haveI : T2Space O := t2Space_of_isModuleTopology_padicInt q O
  haveI : IsNoetherianRing O := isNoetherianRing_of_finite_padicInt q O
  obtain ⟨U, hUV, hUopen, hU0⟩ := mem_nhds_iff.mp hV
  by_contra hcon
  have hcon' : ∀ n : ℕ, ¬ (((P ^ n : Ideal O) : Set O) ⊆ U) := fun n hn => hcon ⟨n, hn.trans hUV⟩
  -- the sets `Pⁿ \ U` are nonempty, decreasing, closed, and compact
  set C : ℕ → Set O := fun n => ((P ^ n : Ideal O) : Set O) \ U with hC
  have hCne : ∀ n, (C n).Nonempty := by
    intro n
    obtain ⟨x, hx1, hx2⟩ := Set.not_subset.mp (hcon' n)
    exact ⟨x, hx1, hx2⟩
  have hCcl : ∀ n, IsClosed (C n) := fun n =>
    (IsNoetherianRing.isClosed_ideal (P ^ n)).inter hUopen.isClosed_compl
  have hCd : ∀ n, C (n + 1) ⊆ C n := fun n x hx =>
    ⟨Ideal.pow_le_pow_right (Nat.le_succ n) hx.1, hx.2⟩
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hCd hCne
    ((hCcl 0).isCompact) hCcl
  -- but `⋂ₙ Pⁿ = 0` and `0 ∈ U`
  have hx0 : x = 0 := by
    have hmem : x ∈ (⨅ n : ℕ, P ^ n) := Ideal.mem_iInf.mpr fun n => (Set.mem_iInter.mp hx n).1
    rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing P hPtop, Ideal.mem_bot] at hmem
  exact (Set.mem_iInter.mp hx 0).2 (hx0 ▸ hU0)

/-- **`{Pⁿ}ₙ` is a neighbourhood basis of `0` in `O`.** This is the full
comparison of the `ℤ_q`-module topology on `O` with the `P`-adic
topology, and BOTH hypotheses on `P` are used: `q ∈ P` makes each `Pⁿ`
open, and `P ≠ ⊤` makes them shrink to `0`. -/
theorem hasBasis_pow_nhds_zero (q : ℕ) [Fact q.Prime] {O : Type*} [CommRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [Algebra ℤ_[q] O] [IsLocalRing O]
    [Module.Finite ℤ_[q] O] [Module.Free ℤ_[q] O] [IsModuleTopology ℤ_[q] O] {P : Ideal O}
    (hPq : (q : O) ∈ P) (hPtop : P ≠ ⊤) :
    (nhds (0 : O)).HasBasis (fun _ : ℕ => True) fun n => ((P ^ n : Ideal O) : Set O) := by
  refine Filter.hasBasis_iff.mpr fun V => ⟨fun hV => ?_, ?_⟩
  · obtain ⟨n, hn⟩ := exists_pow_subset_of_mem_nhds q hPtop hV
    exact ⟨n, trivial, hn⟩
  · rintro ⟨n, -, hn⟩
    exact Filter.mem_of_superset
      ((isOpen_pow_of_natCast_mem q hPq n).mem_nhds (Submodule.zero_mem (P ^ n))) hn

end CongruenceTopology

/-- **A homomorphism with open congruence subgroups is a continuous
representation** (PROVEN 2026-07-26; topology and commutative algebra).

`O` is finite over `ℤ_q` and carries the `ℤ_q`-module topology, so its
topology is the `q`-adic one; and `P` is a proper ideal containing `q`,
so the `P`-adic and `q`-adic filtrations of `O` are cofinal in each
other. Hence `{Pⁿ}` is a neighbourhood basis of `0` in `O`
(`hasBasis_pow_nhds_zero` above), and openness of every congruence
subgroup is exactly continuity of `t` at `1`.

HOW IT IS PROVEN. Three steps.

1. *`{Pⁿ}` is a neighbourhood basis of `0` in `O`* —
   `hasBasis_pow_nhds_zero`. Its two halves are proved by different
   arguments; see the section docstring above. The cofinality half goes
   by COMPACTNESS of `O` plus Krull's intersection theorem, NOT by the
   nilpotence of the maximal ideal of `O/qO` sketched in the original
   version of this docstring — that route would have needed the
   Artinian structure of `O/qO`, which the compactness argument makes
   unnecessary.
2. *Continuity of `t` at `1`* — `End_O(O²)` is read through the standard
   basis as `(Fin 2 → Fin 2 → O)` with the product topology (the two
   module topologies agree because `Basis.constr` is an `O`-linear
   equivalence between two modules carrying module topologies), so
   convergence is entrywise, and step 1 turns each entry's neighbourhood
   filter into the filtration `{Pⁿ}`, which `hloc` matches exactly.
3. *Continuity everywhere* — `continuous_of_continuousAt_one`, available
   because `End_O(O²)` with the module topology is a topological ring
   (`IsModuleTopology.isTopologicalRing`, applicable since `End_O(O²)`
   is a finite `O`-algebra).

**`hPtop` is load-bearing; `hPq` turns out NOT to be.** Without `hPtop`
the `P`-adic topology can be finer than the module topology (`P = ⊤`
makes every congruence subgroup the whole group, so `hloc` says nothing
and `t` may be any homomorphism whatever): `hPtop` is exactly what
Krull's theorem needs in order to force `⋂ₙ Pⁿ = 0`.

The claim made here until 2026-07-26 that `hPq` is equally load-bearing
is WRONG, and its counterexample does not work: at `P = 0` the `n = 1`
congruence subgroup is `{σ | t σ = 1} = ker t`, whose openness is a
strong hypothesis and not a triviality — an open kernel already makes
`t` locally constant, hence continuous. In fact the theorem is provable
with `hPq` deleted outright, since the cofinality half of step 1 uses
only `P ≠ ⊤` (see `exists_pow_subset_of_mem_nhds`). The hypothesis is
kept in the statement because the call site in
`exists_tateFrame_of_adicCoefficientRing` supplies it positionally and
because it is what makes the powers of `P` OPEN, which is the natural
two-sided statement `hasBasis_pow_nhds_zero` that this proof consumes. -/
theorem exists_galoisRep_of_isOpen_congruence
    {F : Type u} [Field F] [NumberField F] (q : ℕ) [Fact q.Prime]
    {O : Type u} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [Algebra ℤ_[q] O] [IsLocalRing O] [Module.Finite ℤ_[q] O] [Module.Free ℤ_[q] O]
    [IsModuleTopology ℤ_[q] O]
    (P : Ideal O) (hPq : (q : O) ∈ P) (hPtop : P ≠ ⊤)
    (t : Field.absoluteGaloisGroup F →* Module.End O (Fin 2 → O))
    (hloc : ∀ n : ℕ, IsOpen {σ : Field.absoluteGaloisGroup F |
      ∀ (u : Fin 2 → O) (i : Fin 2), (t σ u - u) i ∈ P ^ n}) :
    ∃ τ : GaloisRep F O (Fin 2 → O), ∀ σ, τ σ = t σ := by
  classical
  -- `End_O(O²)` carries the `O`-module topology, which makes it a topological ring
  letI : TopologicalSpace (Module.End O (Fin 2 → O)) :=
    moduleTopology O (Module.End O (Fin 2 → O))
  haveI : IsModuleTopology O (Module.End O (Fin 2 → O)) := ⟨rfl⟩
  haveI : IsTopologicalRing (Module.End O (Fin 2 → O)) :=
    IsModuleTopology.isTopologicalRing O (Module.End O (Fin 2 → O))
  -- read an endomorphism through the standard basis: `End_O(O²) ≃ₗ (Fin 2 → Fin 2 → O)`
  set bb : Module.Basis (Fin 2) O (Fin 2 → O) := Pi.basisFun O (Fin 2) with hbb
  set ψ : (Fin 2 → (Fin 2 → O)) ≃ₗ[O] Module.End O (Fin 2 → O) := bb.constr O with hψdef
  have hψ : Continuous ψ := IsModuleTopology.continuous_of_linearMap ψ.toLinearMap
  have hval : ∀ (σ : Field.absoluteGaloisGroup F) (j i : Fin 2),
      ψ.symm (t σ) j i = (t σ (bb j)) i := by
    intro σ j i
    rw [hψdef]
    simp [Module.Basis.constr_symm_apply]
  -- continuity at `1`, entry by entry
  have hcont1 : ContinuousAt (fun σ : Field.absoluteGaloisGroup F => ψ.symm (t σ)) 1 := by
    rw [ContinuousAt, tendsto_pi_nhds]
    intro j
    rw [tendsto_pi_nhds]
    intro i
    rw [Filter.tendsto_def]
    intro V hV
    -- the target value is the `(j,i)` entry of the identity
    have hone : ψ.symm (t (1 : Field.absoluteGaloisGroup F)) j i = (bb j) i := by
      rw [hval]; simp
    rw [hone] at hV
    -- translate `V` back to a neighbourhood of `0` and extract a power of `P`
    have hV0 : (fun y : O => y + (bb j) i) ⁻¹' V ∈ nhds (0 : O) := by
      have hca := (continuous_add_const ((bb j) i)).continuousAt (x := (0 : O))
      rw [ContinuousAt, zero_add] at hca
      exact hca hV
    obtain ⟨n, -, hn⟩ := (hasBasis_pow_nhds_zero q hPq hPtop).mem_iff.mp hV0
    -- the `n`-th congruence subgroup is an open neighbourhood of `1` inside the preimage
    refine Filter.mem_of_superset ((hloc n).mem_nhds ?_) ?_
    · intro u k
      simp
    · intro σ hσ
      have hmem : (t σ (bb j)) i - (bb j) i ∈ P ^ n := by
        have := hσ (bb j) i
        simpa using this
      have := hn hmem
      simp only [Set.mem_preimage, sub_add_cancel] at this
      simpa [hval] using this
  -- transport back along `ψ` and propagate from `1` by the group structure
  have hcontAt : ContinuousAt (fun σ : Field.absoluteGaloisGroup F => t σ) 1 := by
    have h := hψ.continuousAt.comp hcont1
    simpa [Function.comp_def] using h
  have hcont : Continuous (fun σ : Field.absoluteGaloisGroup F => t σ) :=
    continuous_of_continuousAt_one t hcontAt
  exact ⟨⟨t, hcont⟩, fun σ => rfl⟩

/-- **The Tate module is free of rank two over the completion**, with a
continuous Galois action extending the real multiplication (PROVEN
2026-07-26 by assembly over `exists_levelwiseTateFrame`,
`isOpen_stabilizer_torsion` and `exists_galoisRep_of_isOpen_congruence`;
abelian varieties: Mumford *Abelian Varieties* §18, Silverman *AEC*
III.7, Taylor 2002 §2).

Let `A ⟶ S` be a Hilbert–Blumenthal family — an abelian scheme of
relative dimension `[D:ℚ]` with multiplication by `𝒪_D` — and let `O`
be the `I`-adic completion of `𝒪_D` in the sense pinned by
`exists_adicCoefficientRing`. Then `TatePt m x I π` is free of rank two
over `O`, `Γ_F`-equivariantly.

The classical statement is that `T_I A` is a free `𝒪_{D,I}`-module of
rank `2`: the geometric fibre `A_x` is an abelian variety of dimension
`g = [D:ℚ]` over a field of characteristic zero, so `A_x[N] ≅ (ℤ/N)^{2g}`;
the `𝒪_D`-action makes `T_q A_x` a torsion-free module over
`𝒪_D ⊗ ℤ_q = ∏_{I ∣ q} 𝒪_{D,I}`, hence free over each factor, and the
`ℤ_q`-rank count `2g = Σ_I 2·[𝒪_{D,I} : ℤ_q]` forces each rank to be
`2`. Galois acts `𝒪_D`-linearly because the multiplication is defined
over the base (`Mult.galSMul_act`), hence `O`-linearly by continuity,
which is where completeness of `O` is used.

`hdim` is what makes `A_x` `g`-dimensional and so makes the rank count
come out; without it the Tate module has the wrong `ℤ_q`-rank and no
rank-two frame exists. The conclusion produces `j`-compatibility
(`m.act a` corresponds to `j a • ·`) because the sibling
`exists_weilFrobeniusSystem_of_mult` is FALSE without it — see the
docstring there.

## FAITHFULNESS AUDIT (2026-07-26): the previous statement was FALSE,
## and the repair is the four `ℤ_q` binders

The statement as it stood until 2026-07-26 asked for `O` to be an
arbitrary topological ring — `[TopologicalSpace O] [IsTopologicalRing O]`
and nothing more — while the three conjuncts `hcplt`, `hdense`, `hker`
that pin `O` as the `I`-adic completion are PURELY ALGEBRAIC: none of
them mentions the topology (`IsAdicComplete` is `⋂ Pⁿ = 0` plus
convergence of `P`-adic Cauchy sequences, a statement about the ideal
filtration, not about the `TopologicalSpace` instance).

So the hypotheses were satisfied by `O = 𝒪_{D,I}` **with the discrete
topology**, which is a topological ring, is local, and satisfies the pin
verbatim. But `GaloisRep F O (Fin 2 → O)` demands a CONTINUOUS
homomorphism into `End_O(O²)` for the module topology, which over a
discrete `O` is discrete; `Γ_F` is compact, so a continuous map into a
discrete space has finite image; and `τ` is forced by the conclusion to
be the honest `I`-adic representation, since `φ` is required to be an
additive bijection intertwining it with `galSMul`. The `I`-adic
representation of an abelian variety over a number field has INFINITE
image — if the image were finite its kernel would cut out a single
finite extension `F'/F` containing `A[Iⁿ]` for every `n`, contradicting
finiteness of `A(F')_tors` — so no such `τ` exists. Concretely: `D = ℚ`,
`𝒪_D = ℤ`, `I = (q)`, `π = q`, `A ⟶ S` an elliptic curve over `F = ℚ`
(relative dimension `1 = [ℚ:ℚ]`, so `hdim` holds), `O = ℤ_q` discrete.
Every hypothesis of the old statement holds and its conclusion fails.

The repair, taken 2026-07-26, is to carry over the four binders that
`exists_adicCoefficientRing` already PRODUCES and that the assembly
`exists_tateFrame_of_levelStructure` already has in scope at the call
site — `[Algebra ℤ_[q] O] [Module.Finite ℤ_[q] O] [Module.Free ℤ_[q] O]`
and `[IsModuleTopology ℤ_[q] O]`, together with `q` and `hqI : q ∈ I`.
They pin the topology: a finite `ℤ_q`-module with the module topology
carries the `q`-adic topology, `hqI` and `hker` put `q` inside `(jπ)`,
and `I ≠ ⊤` keeps `(jπ)` proper, so the `(jπ)`-adic and `q`-adic
topologies agree and the `I`-adic representation is continuous. Nothing
downstream changes except the argument list of the one call site.

The lesson is the general one for this file: an ALGEBRAIC pin never
constrains a TOPOLOGICAL conclusion. Every leaf here whose conclusion
mentions `GaloisRep` must carry the topological pin explicitly. -/
theorem exists_tateFrame_of_adicCoefficientRing
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (hdim : SmoothOfRelativeDimension (Module.finrank ℚ D) f)
    (q : ℕ) [Fact q.Prime]
    (I : Ideal (NumberField.RingOfIntegers D)) (hI : I.IsMaximal)
    (hqI : (q : NumberField.RingOfIntegers D) ∈ I)
    (π : NumberField.RingOfIntegers D) (hπ : π ∈ I) (hπ2 : π ∉ I ^ 2)
    (O : Type u) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [Algebra ℤ_[q] O] [IsLocalRing O] [Module.Finite ℤ_[q] O] [Module.Free ℤ_[q] O]
    [IsModuleTopology ℤ_[q] O]
    (j : NumberField.RingOfIntegers D →+* O)
    (hcplt : IsAdicComplete (Ideal.span {j π}) O)
    (hdense : ∀ (n : ℕ) (z : O), ∃ a : NumberField.RingOfIntegers D,
      z - j a ∈ Ideal.span {j π} ^ n)
    (hker : ∀ (n : ℕ) (a : NumberField.RingOfIntegers D),
      j a ∈ Ideal.span {j π} ^ n ↔ a ∈ I ^ n) :
    ∃ (τ : GaloisRep F O (Fin 2 → O)) (φ : (Fin 2 → O) → TatePt m x I π),
      (∀ (u u' : Fin 2 → O) (n : ℕ),
        (φ (u + u')).1 n = ab.add ((φ u).1 n) ((φ u').1 n)) ∧
      Function.Bijective φ ∧
      (∀ (σ : Field.absoluteGaloisGroup F) (u : Fin 2 → O) (n : ℕ),
        (φ (τ σ u)).1 n = ab.galSMul x σ ((φ u).1 n)) ∧
      ∀ (a : NumberField.RingOfIntegers D) (u : Fin 2 → O) (n : ℕ),
        (φ (j a • u)).1 n = m.act a ((φ u).1 n) := by
  classical
  set P : Ideal O := Ideal.span {j π}
  -- `π` is nonzero and `I` is a nonzero proper ideal: `π ∉ I²` forbids `π = 0`.
  have hπ0 : π ≠ 0 := fun h => hπ2 (h ▸ Submodule.zero_mem _)
  have hIn0 : ∀ n : ℕ, I ^ n ≠ ⊥ := by
    intro n hn
    have hmem : π ^ n ∈ I ^ n := Ideal.pow_mem_pow hπ n
    rw [hn, Ideal.mem_bot] at hmem
    exact pow_ne_zero n hπ0 hmem
  -- `P` is proper: otherwise `hker` at `n = 1` makes `I` the unit ideal.
  have hPtop : P ≠ ⊤ := by
    intro h
    have h1 : j 1 ∈ P ^ 1 := by rw [pow_one, h]; exact Submodule.mem_top
    have h2 := (hker 1 1).mp h1
    rw [pow_one] at h2
    exact hI.ne_top ((Ideal.eq_top_iff_one I).mpr h2)
  have hPq : (q : O) ∈ P := by
    have h1 : j (q : NumberField.RingOfIntegers D) ∈ P ^ 1 :=
      (hker 1 _).mpr (by rwa [pow_one])
    rw [pow_one] at h1
    rwa [map_natCast] at h1
  -- the finite-level frames
  obtain ⟨c, hcmem, hcadd, hcinj, hcsurj, hcsemi, hctrans⟩ :=
    exists_levelwiseTateFrame m x hdim I hI π hπ hπ2
  -- ### The comparison `𝒪_D ⧸ Iⁿ ≃+* O ⧸ Pⁿ`
  let gq : (n : ℕ) → (NumberField.RingOfIntegers D ⧸ I ^ n) →+* (O ⧸ P ^ n) := fun n =>
    Ideal.Quotient.lift (I ^ n) ((Ideal.Quotient.mk (P ^ n)).comp j) (by
      intro a ha
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hker n a).mpr ha))
  have hgq_mk : ∀ (n : ℕ) (a : NumberField.RingOfIntegers D),
      gq n (Ideal.Quotient.mk (I ^ n) a) = Ideal.Quotient.mk (P ^ n) (j a) :=
    fun _ _ => rfl
  have hgqbij : ∀ n, Function.Bijective (gq n) := by
    intro n
    constructor
    · rw [injective_iff_map_eq_zero]
      intro z hz
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
      rw [hgq_mk] at hz
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        ((hker n a).mp (Ideal.Quotient.eq_zero_iff_mem.mp hz))
    · intro w
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective w
      obtain ⟨a, ha⟩ := hdense n z
      refine ⟨Ideal.Quotient.mk (I ^ n) a, ?_⟩
      rw [hgq_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      simpa using neg_mem ha
  let qeq : (n : ℕ) → (NumberField.RingOfIntegers D ⧸ I ^ n) ≃+* (O ⧸ P ^ n) := fun n =>
    RingEquiv.ofBijective (gq n) (hgqbij n)
  let proj : (n : ℕ) → O →+* NumberField.RingOfIntegers D ⧸ I ^ n := fun n =>
    ((qeq n).symm : (O ⧸ P ^ n) →+* _).comp (Ideal.Quotient.mk (P ^ n))
  have hproj_iff : ∀ (n : ℕ) (z w : O), proj n z = proj n w ↔ z - w ∈ P ^ n := by
    intro n z w
    show (qeq n).symm (Ideal.Quotient.mk (P ^ n) z)
        = (qeq n).symm (Ideal.Quotient.mk (P ^ n) w) ↔ _
    rw [(qeq n).symm.injective.eq_iff, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  have hproj_j : ∀ (n : ℕ) (a : NumberField.RingOfIntegers D),
      proj n (j a) = Ideal.Quotient.mk (I ^ n) a := by
    intro n a
    show (qeq n).symm (Ideal.Quotient.mk (P ^ n) (j a)) = _
    rw [RingEquiv.symm_apply_eq]
    exact (hgq_mk n a).symm
  have hproj_eq : ∀ (n : ℕ) (z : O) (a : NumberField.RingOfIntegers D),
      z - j a ∈ P ^ n → proj n z = Ideal.Quotient.mk (I ^ n) a := by
    intro n z a h
    rw [← hproj_j n a]
    exact (hproj_iff n z (j a)).mpr h
  have hproj_surj : ∀ n, Function.Surjective (proj n) := by
    intro n v
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective v
    exact ⟨j a, hproj_j n a⟩
  have hproj_factor : ∀ (n : ℕ) (z : O),
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ n)) (proj (n + 1) z)
        = proj n z := by
    intro n z
    obtain ⟨a, ha⟩ := hdense (n + 1) z
    rw [hproj_eq (n + 1) z a ha, Ideal.Quotient.factor_mk,
      hproj_eq n z a (Ideal.pow_le_pow_right (Nat.le_succ n) ha)]
  -- ### The frame `φ : O² → T`
  let φ : (Fin 2 → O) → TatePt m x I π := fun u =>
    ⟨fun n => c n (fun i => proj n (u i)),
      ⟨fun n => hcmem n _, fun n => by
        rw [hctrans n (fun i => proj (n + 1) (u i))]
        exact congrArg (c n) (funext fun i => hproj_factor n (u i))⟩⟩
  have hφval : ∀ (u : Fin 2 → O) (n : ℕ),
      (φ u).1 n = c n (fun i => proj n (u i)) := fun _ _ => rfl
  have hφadd : ∀ (u u' : Fin 2 → O) (n : ℕ),
      (φ (u + u')).1 n = ab.add ((φ u).1 n) ((φ u').1 n) := by
    intro u u' n
    rw [hφval, hφval, hφval, ← hcadd]
    exact congrArg (c n) (funext fun i => map_add (proj n) (u i) (u' i))
  have hφinj : Function.Injective φ := by
    intro u u' h
    funext i
    have hall : ∀ n : ℕ, u i - u' i ∈ P ^ n := by
      intro n
      have h1 : c n (fun k => proj n (u k)) = c n (fun k => proj n (u' k)) :=
        congrFun (congrArg Subtype.val h) n
      exact (hproj_iff n (u i) (u' i)).mp (congrFun (hcinj n h1) i)
    have hz := hcplt.toIsHausdorff.haus (u i - u' i) (fun n => by
      rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
      exact hall n)
    exact sub_eq_zero.mp hz
  have hφsurj : Function.Surjective φ := by
    intro y
    choose w hw using fun n => hcsurj n (y.1 n) (y.2.1 n)
    have hwfac : ∀ n : ℕ,
        (fun i => Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ n)) (w (n + 1) i))
          = w n := by
      intro n
      refine hcinj n ?_
      rw [← hctrans n (w (n + 1)), hw (n + 1), y.2.2 n, hw n]
    choose a ha using fun (n : ℕ) (i : Fin 2) => Ideal.Quotient.mk_surjective (w n i)
    have hstep : ∀ (n : ℕ) (i : Fin 2), a (n + 1) i - a n i ∈ I ^ n := by
      intro n i
      have hfac := congrFun (hwfac n) i
      rw [← ha (n + 1) i, Ideal.Quotient.factor_mk, ← ha n i,
        Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hfac
      exact hfac
    have hmono : ∀ (i : Fin 2) (p n : ℕ), p ≤ n → a n i - a p i ∈ I ^ p := by
      intro i p n hpn
      induction n, hpn using Nat.le_induction with
      | base => simp
      | succ n hpn ih =>
        have h1 : a (n + 1) i - a n i ∈ I ^ p :=
          Ideal.pow_le_pow_right hpn (hstep n i)
        have hsplit : a (n + 1) i - a p i = (a (n + 1) i - a n i) + (a n i - a p i) := by
          ring
        rw [hsplit]
        exact add_mem h1 ih
    have hLex : ∀ i : Fin 2, ∃ L : O, ∀ n : ℕ, L - j (a n i) ∈ P ^ n := by
      intro i
      obtain ⟨L, hL⟩ := hcplt.toIsPrecomplete.prec (f := fun n => j (a n i)) (by
        intro p n hpn
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← map_sub]
        exact (hker p _).mpr (by simpa using neg_mem (hmono i p n hpn)))
      refine ⟨L, fun n => ?_⟩
      have := hL n
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
      simpa using neg_mem this
    choose L hLmem using hLex
    refine ⟨L, ?_⟩
    refine Subtype.ext (funext fun n => ?_)
    rw [hφval, show (fun i => proj n (L i)) = w n from
      funext fun i => by rw [← ha n i]; exact hproj_eq n (L i) (a n i) (hLmem i n), hw n]
  -- ### The Galois action on the Tate module
  have hgal_add : ∀ (σ : Field.absoluteGaloisGroup F) (y z : GeomFibrePt f x),
      ab.galSMul x σ (ab.add y z) = ab.add (ab.galSMul x σ y) (ab.galSMul x σ z) :=
    fun σ y z => ab.pre_add (specGal σ) (specGal_comp_base x σ) y z
  have hgal_one : ∀ y : GeomFibrePt f x,
      ab.galSMul x (1 : Field.absoluteGaloisGroup F) y = y := by
    letI : AddCommGroup (GeomFibrePt f x) := ab.addCommGroup (specAlgClos F ≫ x)
    letI : DistribMulAction (Field.absoluteGaloisGroup F) (GeomFibrePt f x) :=
      ab.geomFibreAction x
    intro y
    show (1 : Field.absoluteGaloisGroup F) • y = y
    exact one_smul _ y
  have hgal_mul : ∀ (σ σ' : Field.absoluteGaloisGroup F) (y : GeomFibrePt f x),
      ab.galSMul x (σ * σ') y = ab.galSMul x σ (ab.galSMul x σ' y) := by
    letI : AddCommGroup (GeomFibrePt f x) := ab.addCommGroup (specAlgClos F ≫ x)
    letI : DistribMulAction (Field.absoluteGaloisGroup F) (GeomFibrePt f x) :=
      ab.geomFibreAction x
    intro σ σ' y
    show (σ * σ') • y = σ • σ' • y
    exact mul_smul σ σ' y
  let galT : Field.absoluteGaloisGroup F → TatePt m x I π → TatePt m x I π := fun σ y =>
    ⟨fun n => ab.galSMul x σ (y.1 n),
      ⟨fun n => (m.torsion x (I ^ n)).2 σ (y.1 n) (y.2.1 n),
        fun n => by rw [← m.galSMul_act x σ π (y.1 (n + 1)), y.2.2 n]⟩⟩
  -- ### `φ` is `O`-semilinear, level by level
  have hφsmul : ∀ (z : O) (u : Fin 2 → O) (n : ℕ) (a : NumberField.RingOfIntegers D),
      z - j a ∈ P ^ n → (φ (z • u)).1 n = m.act a ((φ u).1 n) := by
    intro z u n a hza
    rw [hφval, ← hcsemi n a (fun i => proj n (u i))]
    exact congrArg (c n) (funext fun i => by
      show proj n (z * u i) = _
      rw [map_mul, hproj_eq n z a hza])
  have hφj : ∀ (a : NumberField.RingOfIntegers D) (u : Fin 2 → O) (n : ℕ),
      (φ (j a • u)).1 n = m.act a ((φ u).1 n) :=
    fun a u n => hφsmul (j a) u n a (by simp)
  -- ### The representation
  let E : (Fin 2 → O) ≃ TatePt m x I π := Equiv.ofBijective φ ⟨hφinj, hφsurj⟩
  let tfun : Field.absoluteGaloisGroup F → (Fin 2 → O) → (Fin 2 → O) :=
    fun σ u => E.symm (galT σ (φ u))
  have htfun : ∀ (σ : Field.absoluteGaloisGroup F) (u : Fin 2 → O) (n : ℕ),
      (φ (tfun σ u)).1 n = ab.galSMul x σ ((φ u).1 n) := by
    intro σ u n
    have : φ (tfun σ u) = galT σ (φ u) := E.apply_symm_apply (galT σ (φ u))
    rw [this]
  have htadd : ∀ (σ : Field.absoluteGaloisGroup F) (u u' : Fin 2 → O),
      tfun σ (u + u') = tfun σ u + tfun σ u' := by
    intro σ u u'
    refine hφinj (Subtype.ext (funext fun n => ?_))
    rw [htfun, hφadd, hφadd, htfun, htfun, hgal_add]
  have htsmul : ∀ (σ : Field.absoluteGaloisGroup F) (z : O) (u : Fin 2 → O),
      tfun σ (z • u) = z • tfun σ u := by
    intro σ z u
    refine hφinj (Subtype.ext (funext fun n => ?_))
    obtain ⟨a, ha⟩ := hdense n z
    rw [htfun, hφsmul z u n a ha, hφsmul z (tfun σ u) n a ha, htfun]
    exact m.galSMul_act x σ a ((φ u).1 n)
  let tlin : Field.absoluteGaloisGroup F → Module.End O (Fin 2 → O) := fun σ =>
    { toFun := tfun σ
      map_add' := htadd σ
      map_smul' := fun z u => htsmul σ z u }
  have htlin_apply : ∀ (σ : Field.absoluteGaloisGroup F) (u : Fin 2 → O),
      tlin σ u = tfun σ u := fun _ _ => rfl
  let t : Field.absoluteGaloisGroup F →* Module.End O (Fin 2 → O) :=
    { toFun := tlin
      map_one' := by
        refine LinearMap.ext fun u => ?_
        rw [htlin_apply]
        refine hφinj (Subtype.ext (funext fun n => ?_))
        rw [htfun, hgal_one]
        rfl
      map_mul' := by
        intro σ σ'
        refine LinearMap.ext fun u => ?_
        rw [htlin_apply, Module.End.mul_apply, htlin_apply, htlin_apply]
        refine hφinj (Subtype.ext (funext fun n => ?_))
        rw [htfun, htfun, htfun, hgal_mul] }
  have ht_apply : ∀ (σ : Field.absoluteGaloisGroup F) (u : Fin 2 → O),
      t σ u = tfun σ u := fun _ _ => rfl
  -- ### Continuity: the congruence subgroups are the torsion stabilizers
  have hloc : ∀ n : ℕ, IsOpen {σ : Field.absoluteGaloisGroup F |
      ∀ (u : Fin 2 → O) (i : Fin 2), (t σ u - u) i ∈ P ^ n} := by
    intro n
    have hset : {σ : Field.absoluteGaloisGroup F |
        ∀ (u : Fin 2 → O) (i : Fin 2), (t σ u - u) i ∈ P ^ n}
        = {σ : Field.absoluteGaloisGroup F |
            ∀ y ∈ (m.torsion x (I ^ n)).1, ab.galSMul x σ y = y} := by
      ext σ
      constructor
      · intro hσ y hy
        obtain ⟨v, hv⟩ := hcsurj n y hy
        choose u hu using fun i => hproj_surj n (v i)
        have hyu : (φ u).1 n = y := by
          rw [hφval, funext hu, hv]
        have hcong : (fun i => proj n (t σ u i)) = fun i => proj n (u i) :=
          funext fun i => (hproj_iff n _ _).mpr (hσ u i)
        have := htfun σ u n
        rw [ht_apply] at hcong
        rw [hφval, hcong, ← hφval, hyu] at this
        exact this.symm
      · intro hσ u i
        have hfix : ab.galSMul x σ ((φ u).1 n) = (φ u).1 n :=
          hσ ((φ u).1 n) (hcmem n _)
        have hlev : c n (fun k => proj n (tfun σ u k)) = c n (fun k => proj n (u k)) := by
          rw [← hφval, ← hφval, htfun, hfix]
        have := congrFun (hcinj n hlev) i
        rw [ht_apply]
        exact (hproj_iff n _ _).mp this
    rw [hset]
    exact isOpen_stabilizer_torsion m x (I ^ n) (hIn0 n)
  obtain ⟨τ, hτ⟩ := exists_galoisRep_of_isOpen_congruence q P hPq hPtop t hloc
  refine ⟨τ, φ, hφadd, ⟨hφinj, hφsurj⟩, ?_, hφj⟩
  intro σ u n
  rw [hτ σ, ht_apply, htfun]

/-! ### The three sub-leaves of the residual comparison

`exists_residualEmbedding_of_tateFrame` is PROVEN below (2026-07-26) by
assembly over three statements, TWO GEOMETRIC and ONE PURELY
REPRESENTATION-THEORETIC. The cut is exactly along the seam that the
FAITHFULNESS AUDIT of `exists_tateFrame_of_levelStructure` identified as
the delicate one: everything about abelian varieties is pushed into the
two geometric leaves, and the Noether–Skolem step — the one that needs
`hirr` and that was refuted in its unconditional form — is isolated as a
statement about a Galois representation and a comparison map, with no
scheme, no `Mult` and no `TatePt` in sight.

* `exists_tatePt_val_one_eq` — the reduction `T ↠ A[I]` is SURJECTIVE.
  **PROVEN** (2026-07-26) by countable dependent choice up the tower over
  `exists_mem_torsion_act_uniformizer_eq`, which is itself proven over
  `exists_nsmul_eq_geomFibrePt` (divisibility of the group of geometric
  points of an abelian variety). It needed no new geometric input: the
  divisibility this cut was expected to introduce was already present in
  the file, as the input to the levelwise tower.

  LABEL CORRECTION (2026-07-26). Earlier text here and below called
  `exists_nsmul_eq_geomFibrePt` "the single geometric leaf". That is no
  longer accurate in either direction, and the stale label was a
  phantom-dispatch source. It is not "the single" geometric leaf of this
  FILE — `card_torsion_of_isMaximal`, `locallyQuasiFinite_mulByNat` and
  `exists_tateWeilPairing_of_mult` (the 2026-07-27 geometric residue of
  the determinant clause; `det_eq_cyclotomicCharacter_of_tateFrame` and
  `det_globalFrob_eq_absNorm_of_tateFrame` are both PROVEN) are geometric
  leaves too; the
  claim was only ever scoped to what
  `exists_mem_torsion_act_uniformizer_eq` rests on. And it is no longer a
  LEAF at all: it is PROVEN in `Modularity/AbelianSchemeIsogeny.lean`,
  which builds `[N]` as a morphism and reduces divisibility to flatness
  of `[N]`. The residual geometric leaves for divisibility are
  `flat_mulByNat` and `finite_preimage_mulByNat` THERE, not here.
* `exists_tatePt_act_eq_of_val_one_eq_zero` — its KERNEL is `π · T`
  (a shift of the inverse system, plus `I ^ n = (π ^ n) + I ^ (n+1)`,
  which holds because `π` generates the one-dimensional `𝒪_D/I`-vector
  space `I / I ^ 2`). **PROVEN** — it needed no new input beyond the
  hypotheses it was cut with.
* `exists_residualEmbedding_of_residualComparison` — the Noether–Skolem
  step, over an abstract comparison map. **PROVEN 2026-07-26** by the
  commutant dichotomy, over `exists_residualEmbedding_of_scalarCommutant`
  (the absolutely irreducible case; PROVEN, and it needs neither `hirr`
  nor any simplicity theorem) and
  `exists_residualEmbedding_of_nonScalarCommutant` (the remaining case;
  PROVEN 2026-07-26 as well, by a semilinear-eigenvector argument that
  needs neither Wedderburn nor Noether–Skolem, and in fact does not use
  the commutant hypothesis at all). Both halves are stated for an
  abstract monoid and mathlib's `Representation`, so the whole step is
  Galois-free pure algebra.

Together the first two say `T / π T ≅ A[I]` as `Γ_F`-modules, which
composed with the level structure `e` is exactly the hypothesis of the
third. -/

/-- **Every `I`-torsion point of the geometric fibre lifts to the Tate
module** (PROVEN 2026-07-26 — a countable dependent choice up the tower,
over the already-proven `exists_mem_torsion_act_uniformizer_eq`; no new
geometric input).

The inverse system

  `⋯ --·π--> A[I³] --·π--> A[I²] --·π--> A[I]`

has SURJECTIVE transition maps — that is exactly
`exists_mem_torsion_act_uniformizer_eq`, which in turn rests on
`exists_nsmul_eq_geomFibrePt` (divisibility of `A(F̄)`, Mumford *Abelian
Varieties* §6, Silverman *AEC* III.4/III.7) — so its limit
`TatePt m x I π` surjects onto its first stage `A[I]`. This is the
ONLY place where surjectivity of the reduction is used.

`exists_nsmul_eq_geomFibrePt` was called "the one geometric leaf" here
until 2026-07-26; it is PROVEN in `Modularity/AbelianSchemeIsogeny.lean`
over the flatness of `[N]`, so the live geometric leaves underneath this
chain are `flat_mulByNat` and `finite_preimage_mulByNat` in that module.
See the label correction in the section note above.

THE ARGUMENT. Choice on the transition surjectivity gives a step
function `step n : A[Iⁿ⁺¹] → A[Iⁿ⁺²]` with `π · step n w = w`, on the
SUBTYPES rather than on `GeomFibrePt` — carrying the torsion condition
in the type is what makes the recursion dependent-typed and removes any
need to re-establish membership afterwards. Iterating `step` from the
given `y ∈ A[I] = A[I¹]` by `Nat.rec` produces `u : (n : ℕ) → A[Iⁿ⁺¹]`
with `u 0 = y` and `π · u (n+1) = u n`; the point of `TatePt` is then
`u` shifted up by one with `0` inserted at index `0`.

The two defining conditions of `TatePt` hold degenerately at `0` and by
construction above it. At index `0`: `A[I⁰] = A[⊤] = 0` contains `0`,
and the relation `π · t.1 1 = t.1 0` reads `π · y = 0`, which is just
`hπ : π ∈ I` against `hy : y ∈ A[I]`. Note the indexing convention of
`TatePt`: `t.1 0 = 0` and `t.1 1 ∈ A[I]`, so `t.1 1` is the reduction.

The hypotheses `hI`, `hπ`, `hπ2` are consumed entirely inside
`exists_mem_torsion_act_uniformizer_eq`, where they are what make `π` a
genuine uniformizer at `I`; `hπ2` in particular is what makes the `n`-th
stage of the lifting stay inside `A[Iⁿ]`, and with `π = 0` (which `hπ2`
forbids) the limit is zero and the statement is false. -/
theorem exists_tatePt_val_one_eq
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (I : Ideal (NumberField.RingOfIntegers D)) (hI : I.IsMaximal)
    (π : NumberField.RingOfIntegers D) (hπ : π ∈ I) (hπ2 : π ∉ I ^ 2)
    (y : GeomFibrePt f x) (hy : y ∈ (m.torsion x I).1) :
    ∃ t : TatePt m x I π, t.1 1 = y := by
  classical
  letI : AddCommGroup (GeomFibrePt f x) := ab.addCommGroup (specAlgClos F ≫ x)
  letI : Module (NumberField.RingOfIntegers D) (GeomFibrePt f x) :=
    m.module (specAlgClos F ≫ x)
  have hy1 : y ∈ (m.torsion x (I ^ 1)).1 := by rw [pow_one]; exact hy
  -- ### One step of the tower, as a choosable relation on the torsion stages
  have key : ∀ (n : ℕ) (w : {w : GeomFibrePt f x // w ∈ (m.torsion x (I ^ (n + 1))).1}),
      ∃ z : {w : GeomFibrePt f x // w ∈ (m.torsion x (I ^ (n + 1 + 1))).1},
        m.act π z.1 = w.1 := by
    intro n w
    obtain ⟨z, hz, hzeq⟩ :=
      exists_mem_torsion_act_uniformizer_eq m x I hI π hπ hπ2 (n + 1) w.1 w.2
    exact ⟨⟨z, hz⟩, hzeq⟩
  choose step hstep using key
  -- ### The tower itself, by dependent recursion from `y` at level `1`
  obtain ⟨u, hu0, hurec⟩ :
      ∃ u : (n : ℕ) → {w : GeomFibrePt f x // w ∈ (m.torsion x (I ^ (n + 1))).1},
        (u 0).1 = y ∧ ∀ n, m.act π (u (n + 1)).1 = (u n).1 :=
    ⟨fun n => Nat.rec
      (motive := fun n => {w : GeomFibrePt f x // w ∈ (m.torsion x (I ^ (n + 1))).1})
      ⟨y, hy1⟩ step n, rfl, fun n => hstep n _⟩
  -- ### Shift up by one, inserting `0` at index `0`
  refine ⟨⟨fun n => Nat.casesOn (motive := fun _ => GeomFibrePt f x) n
      (ab.zero (specAlgClos F ≫ x)) (fun k => (u k).1), ?_, ?_⟩, hu0⟩
  · intro n
    cases n with
    | zero =>
      refine (mem_torsion_iff m x (I ^ 0) _).mpr ?_
      intro c _
      show m.act c (ab.zero (specAlgClos F ≫ x)) = ab.zero (specAlgClos F ≫ x)
      exact smul_zero c
    | succ k => exact (u k).2
  · intro n
    cases n with
    | zero =>
      show m.act π (u 0).1 = ab.zero (specAlgClos F ≫ x)
      rw [hu0]
      exact (mem_torsion_iff m x I y).mp hy π hπ
    | succ k => exact hurec k

/-- **The kernel of the reduction of the Tate module is `π · T`**
(PROVEN 2026-07-26 — the inverse-limit computation, plus one
ideal-theoretic identity).

If `t ∈ T = TatePt m x I π` reduces to zero, i.e. `t.1 1 = 0`, then `t`
is `π` times another element of `T`. The witness is the SHIFT
`t'.1 n := t.1 (n + 1)`: the compatibility `m.act π (t'.1 n) = t.1 n` is
then literally the defining relation of `TatePt`, and the only thing to
check is that the shifted sequence still satisfies the torsion condition,
namely `I ^ n · t.1 (n + 1) = 0`.

That is where the hypotheses on `π` are consumed. Since `π ∈ I ∖ I ^ 2`
and `I` is maximal, `π` generates the one-dimensional `𝒪_D / I`-vector
space `I / I ^ 2`, whence `I ^ n = (π ^ n) + I ^ (n + 1)` for every `n`.
Now `I ^ (n+1)` kills `t.1 (n+1)` by the defining torsion condition, and
`π ^ n · t.1 (n + 1) = t.1 1 = 0` by iterating the defining relation `n`
times and using the hypothesis. So `I ^ n` kills `t.1 (n + 1)`.

Together with `exists_tatePt_val_one_eq` this is the statement
`T / π T ≅ A[I]` of `Γ_F`-modules that the residual comparison needs. -/
theorem exists_tatePt_act_eq_of_val_one_eq_zero
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (I : Ideal (NumberField.RingOfIntegers D)) (hI : I.IsMaximal)
    (π : NumberField.RingOfIntegers D) (hπ : π ∈ I) (hπ2 : π ∉ I ^ 2)
    (t : TatePt m x I π) (ht : t.1 1 = ab.zero (specAlgClos F ≫ x)) :
    ∃ t' : TatePt m x I π, ∀ n, m.act π (t'.1 n) = t.1 n := by
  classical
  letI := ab.addCommGroup (specAlgClos F ≫ x)
  letI := m.module (specAlgClos F ≫ x)
  -- `I` is nonzero: it contains `π`, which is not in `I ^ 2`.
  have hI0 : I ≠ 0 := by
    rintro rfl
    rw [Ideal.zero_eq_bot, Ideal.mem_bot] at hπ
    exact hπ2 (by rw [hπ]; exact Ideal.zero_mem _)
  have hπspan : Ideal.span {π} ≤ I := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hπ)
  -- `π` generates `I / I ^ 2`: the ideal `(π) + I ^ 2` lies between `I ^ 2` and
  -- `I`, so it is `I * A` with `A ∣ I`, whence `A = I` (excluded by `hπ2`) or
  -- `A = ⊤`.
  have hbase : I ≤ Ideal.span {π} ⊔ I ^ 2 := by
    have hJI : Ideal.span {π} ⊔ I ^ 2 ≤ I := sup_le hπspan (Ideal.pow_le_self two_ne_zero)
    obtain ⟨Aa, hA⟩ : I ∣ Ideal.span {π} ⊔ I ^ 2 := Ideal.dvd_iff_le.mpr hJI
    have hdvd : I * Aa ∣ I * I := by
      rw [← hA, ← pow_two]
      exact Ideal.dvd_iff_le.mpr le_sup_right
    have hAI : I ≤ Aa := Ideal.dvd_iff_le.mp ((mul_dvd_mul_iff_left hI0).mp hdvd)
    by_cases hAtop : Aa = ⊤
    · rw [hA, hAtop, Ideal.mul_top]
    · exfalso
      have hIA : I = Aa := hI.eq_of_le hAtop hAI
      refine hπ2 ?_
      have hJ2 : Ideal.span {π} ⊔ I ^ 2 = I ^ 2 := by rw [hA, ← hIA, ← pow_two]
      exact hJ2 ▸ Submodule.mem_sup_left (Ideal.mem_span_singleton_self π)
  have hspan : ∀ n : ℕ, Ideal.span {π ^ n} ≤ I ^ n := fun n =>
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.pow_mem_pow hπ n))
  -- `I ^ n = (π ^ n) + I ^ (n + 1)`, by induction from the case `n = 1`.
  have hstep : ∀ n : ℕ, I ^ n ≤ Ideal.span {π ^ n} ⊔ I ^ (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : I ^ (n + 1) ≤ (Ideal.span {π ^ n} ⊔ I ^ (n + 1)) * (Ideal.span {π} ⊔ I ^ 2) := by
        rw [pow_succ]
        exact Ideal.mul_mono ih hbase
      refine h1.trans ?_
      rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
      refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
      · refine le_trans (le_of_eq ?_) le_sup_left
        rw [Ideal.span_singleton_mul_span_singleton, ← pow_succ]
      · refine le_trans ?_ le_sup_right
        calc Ideal.span {π ^ n} * I ^ 2 ≤ I ^ n * I ^ 2 := Ideal.mul_mono (hspan n) le_rfl
          _ = I ^ (n + 1 + 1) := by rw [← pow_add]
      · refine le_trans ?_ le_sup_right
        calc I ^ (n + 1) * Ideal.span {π} ≤ I ^ (n + 1) * I := Ideal.mul_mono le_rfl hπspan
          _ = I ^ (n + 1 + 1) := (pow_succ I (n + 1)).symm
      · refine le_trans ?_ le_sup_right
        calc I ^ (n + 1) * I ^ 2 = I ^ (n + 3) := by rw [← pow_add]
          _ ≤ I ^ (n + 1 + 1) := Ideal.pow_le_pow_right (by omega)
  -- Iterating the defining relation: `π ^ n` carries the `(n+1)`-st stage to the first.
  have hpow : ∀ n : ℕ, m.act (π ^ n) (t.1 (n + 1)) = t.1 1 := by
    intro n
    induction n with
    | zero => simpa using m.act_one (t.1 1)
    | succ n ih =>
      have hrel := t.2.2 (n + 1)
      have hsplit : m.act (π ^ (n + 1)) (t.1 (n + 1 + 1)) =
          m.act (π ^ n) (m.act π (t.1 (n + 1 + 1))) := by
        rw [← m.act_mul, pow_succ]
      rw [hsplit, hrel, ih]
  -- The shift is the witness.
  refine ⟨⟨fun n => t.1 (n + 1), ?_, fun n => t.2.2 (n + 1)⟩, fun n => t.2.2 n⟩
  intro n
  show t.1 (n + 1) ∈ (m.torsion x (I ^ n)).1
  show t.1 (n + 1) ∈ Submodule.torsionBySet (NumberField.RingOfIntegers D)
    (GeomFibrePt f x) ((I ^ n : Ideal (NumberField.RingOfIntegers D)) : Set _)
  refine (Submodule.mem_torsionBySet_iff _ _).mpr ?_
  rintro ⟨a, ha⟩
  show m.act a (t.1 (n + 1)) = 0
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hstep n ha)
  subst hyz
  rw [m.act_add]
  have h1 : m.act y (t.1 (n + 1)) = 0 := by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    rw [m.act_mul, hpow n, ht]
    exact smul_zero c
  have h2 : m.act z (t.1 (n + 1)) = 0 := by
    have ht1 : t.1 (n + 1) ∈ Submodule.torsionBySet (NumberField.RingOfIntegers D)
        (GeomFibrePt f x) ((I ^ (n + 1) : Ideal (NumberField.RingOfIntegers D)) : Set _) :=
      t.2.1 (n + 1)
    exact (Submodule.mem_torsionBySet_iff _ _).mp ht1 ⟨z, hz⟩
  rw [h1, h2]
  exact add_zero _

/-! ### The two halves of the Noether–Skolem step

`exists_residualEmbedding_of_residualComparison` (below) is cut here, on
2026-07-26, into the two cases of the commutant dichotomy, both stated for
an ABSTRACT MONOID `G` and mathlib's `Representation` rather than for
`Γ_F` and `GaloisRep`. Two things are gained by that:

* the hard half becomes a statement of pure module theory that can be
  developed against mathlib alone, in a small scratch module;
* `GaloisRep`'s `FunLike` hides a `moduleTopology A (Module.End A M)`,
  which at a CONCRETE module (`Fin 2 → O`, and a two-dimensional `V`) is
  measured at 20–90 s per elaboration step. None of that is paid here.

The dichotomy is on the commutant `C := End_{ℤ[G]}(V)`:

* `exists_residualEmbedding_of_scalarCommutant` — the case `C = k'`
  (equivalently, `ρ'` is ABSOLUTELY irreducible). **PROVEN.**
* `exists_residualEmbedding_of_nonScalarCommutant` — the case `C ⊋ k'`
  (`ρ'` irreducible but not absolutely irreducible). **PROVEN
  2026-07-26**, and it turned out NOT to need the commutant hypothesis
  at all: see the `_hC` note on that declaration.

The split was worth making — the first case is short and self-contained
— but it is no longer NECESSARY: the second half is proven for arbitrary
commutant, so a later cleanup may collapse the `Classical.em` in
`exists_residualEmbedding_of_residualComparison` and call the second
half directly. Neither half needs the Wedderburn/Noether–Skolem
apparatus that this cut was written expecting. -/

/-- **The residual comparison when the commutant is just the scalars**
(PROVEN 2026-07-26). This is the ABSOLUTELY IRREDUCIBLE case of
`exists_residualEmbedding_of_residualComparison`, stated over an abstract
monoid `G`.

Statement. Let `V` be a two-dimensional `k'`-vector space carrying a
representation `ρ'` of `G`, let `τ` be a rank-two representation of `G`
over a commutative ring `O`, and let `ψ : O² → V` be additive, surjective
and `G`-equivariant with kernel `ϖ · O²`. If EVERY additive endomorphism
of `V` commuting with `ρ'(G)` is multiplication by a scalar of `k'`, then
there is a ring map `ι₀ : O →+* k'` and a `k'`-basis of `V` in which `ρ'`
IS the `ι₀`-reduction of `τ`.

THE PROOF, and why this case needs no simplicity theorem. Transport the
`O`-action along `ψ`: for `a : O` the assignment `ψ u ↦ ψ (a • u)` is
well defined (the kernel `ϖ · O²` is an `O`-submodule), additive, and
commutes with `G` (because each `τ g` is `O`-linear). The commutant
hypothesis therefore hands us, for each `a`, a SCALAR `ι₀ a ∈ k'` with
`ψ (a • u) = ι₀ a • ψ u`; the ring axioms for `ι₀` are read off from that
identity at one nonzero vector. So `ψ` is `ι₀`-semilinear, and the two
values `ψ e₀`, `ψ e₁` span `V` over `k'` — two spanning vectors in rank
two, hence a basis. In that basis the matrix of `ρ' g` is the
`ι₀`-image of the matrix of `τ g`, because `ψ` carries `τ g eⱼ` to
`ρ' g (ψ eⱼ)` and is `ι₀`-semilinear coordinatewise.

WHAT IS *NOT* USED, and this is the point of the cut: irreducibility of
`ρ'` never appears, no ring is shown to be simple, and `O` is not assumed
local. The whole force of the absolutely irreducible case sits in `hC`,
which already says that the commutant is as small as possible; the two
coefficient rings then do not merely become conjugate, they become EQUAL.

Faithfulness of the hypothesis `hC`. For `V` irreducible over `k'[G]`,
`hC` holds exactly when `ρ'` is absolutely irreducible: the image of
`k'[G]` is then all of `End_{k'}(V)` (Burnside), whose centraliser inside
`End_{𝔽_p}(V)` is `k'` by the double-centraliser theorem. When `ρ'` is
irreducible but not absolutely irreducible the commutant is
`End_{L₀}(V)` for `L₀ = 𝔽_p[ρ'(G)] ∩ Z`, strictly larger than `k'` — that
is the complementary leaf. -/
theorem exists_residualEmbedding_of_scalarCommutant
    {G : Type*} [Monoid G]
    {O : Type*} [CommRing O] (ϖ : O)
    (τ : Representation O G (Fin 2 → O))
    {k' : Type*} [Field k']
    {V : Type*} [AddCommGroup V] [Module k' V] [Module.Finite k' V] [Module.Free k' V]
    (hV : Module.rank k' V = 2)
    (ρ' : Representation k' G V)
    (hC : ∀ c : V →+ V, (∀ (g : G) (v : V), c (ρ' g v) = ρ' g (c v)) →
      ∃ a : k', ∀ v, c v = a • v)
    (ψ : (Fin 2 → O) → V)
    (hψadd : ∀ u u' : Fin 2 → O, ψ (u + u') = ψ u + ψ u')
    (hψsurj : Function.Surjective ψ)
    (hψker : ∀ u : Fin 2 → O, ψ u = 0 ↔ ∀ i, u i ∈ Ideal.span {ϖ})
    (hψequiv : ∀ (g : G) (u : Fin 2 → O), ψ (τ g u) = ρ' g (ψ u)) :
    ∃ (ι₀ : O →+* k') (E : (Fin 2 → k') ≃ₗ[k'] V),
      ∀ g : G, ρ' g = E.conj (Matrix.toLin' ((LinearMap.toMatrix' (τ g)).map ι₀)) := by
  classical
  -- `ψ` as an additive homomorphism, so that `map_sub` is available.
  set Ψ : (Fin 2 → O) →+ V := AddMonoidHom.mk' ψ hψadd
  have hΨa : ∀ u, Ψ u = ψ u := fun _ => rfl
  -- The rank is two, so `V` is nontrivial and carries a two-element basis.
  have hfr : Module.finrank k' V = 2 := Module.finrank_eq_of_rank_eq (by exact_mod_cast hV)
  have hVnt : Nontrivial V := Module.nontrivial_of_finrank_pos (R := k') (by omega)
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  -- Scalar multiples of a fixed nonzero vector determine the scalar.
  have huniq : ∀ c c' : k', c • v₀ = c' • v₀ → c = c' := by
    intro c c' h
    have h0 : (c - c') • v₀ = 0 := by rw [sub_smul, h, sub_self]
    rcases smul_eq_zero.mp h0 with h1 | h1
    · exact sub_eq_zero.mp h1
    · exact absurd h1 hv₀
  -- Multiplication by `a : O` descends along `ψ`: the kernel is an `O`-submodule.
  have hwd : ∀ (a : O) (u u' : Fin 2 → O), ψ u = ψ u' → ψ (a • u) = ψ (a • u') := by
    intro a u u' h
    have h0 : ψ (u - u') = 0 := by
      rw [← hΨa, map_sub, hΨa, hΨa, h, sub_self]
    have h1 : ∀ i, (u - u') i ∈ Ideal.span {ϖ} := (hψker _).mp h0
    have h2 : ψ (a • (u - u')) = 0 := by
      refine (hψker _).mpr fun i => ?_
      simpa using Ideal.mul_mem_left _ a (h1 i)
    rw [smul_sub, ← hΨa, map_sub, hΨa, hΨa] at h2
    exact sub_eq_zero.mp h2
  -- A set-theoretic section of `ψ`.
  choose sec hsec using hψsurj
  -- The transported `O`-action, as additive endomorphisms of `V`.
  set T : O → (V →+ V) := fun a => AddMonoidHom.mk' (fun v => ψ (a • sec v)) (by
    intro v w
    have hvw : ψ (sec (v + w)) = ψ (sec v + sec w) := by
      rw [hsec, hψadd, hsec, hsec]
    rw [hwd a _ _ hvw, smul_add, hψadd])
  have hTapp : ∀ (a : O) (u : Fin 2 → O), T a (ψ u) = ψ (a • u) :=
    fun a u => hwd a _ _ (hsec (ψ u))
  have hTcomm : ∀ (a : O) (g : G) (v : V), T a (ρ' g v) = ρ' g (T a v) := by
    intro a g v
    obtain ⟨u, rfl⟩ : ∃ u, ψ u = v := ⟨sec v, hsec v⟩
    rw [← hψequiv, hTapp, hTapp, ← hψequiv]
    congr 1
    exact ((τ g).map_smul a u).symm
  -- The commutant hypothesis turns each of them into a `k'`-scalar.
  choose f hf using fun a : O => hC (T a) (hTcomm a)
  have hsemi : ∀ (a : O) (u : Fin 2 → O), ψ (a • u) = f a • ψ u := by
    intro a u
    rw [← hTapp]
    exact hf a (ψ u)
  -- `f` is a ring map, read off at the nonzero vector `v₀`.
  obtain ⟨u₀, hu₀⟩ : ∃ u, ψ u = v₀ := ⟨sec v₀, hsec v₀⟩
  have hone : f 1 = 1 := by
    refine huniq _ _ ?_
    have := hsemi 1 u₀
    rw [one_smul, hu₀] at this
    rw [← this, one_smul]
  have hmul : ∀ a b : O, f (a * b) = f a * f b := by
    intro a b
    refine huniq _ _ ?_
    have h1 := hsemi (a * b) u₀
    have h2 := hsemi a (b • u₀)
    have h3 := hsemi b u₀
    rw [mul_smul, h2, h3, hu₀, smul_smul] at h1
    exact h1.symm
  have hadd : ∀ a b : O, f (a + b) = f a + f b := by
    intro a b
    refine huniq _ _ ?_
    have h1 := hsemi (a + b) u₀
    have h2 := hsemi a u₀
    have h3 := hsemi b u₀
    rw [add_smul, hψadd, h2, h3, hu₀, ← add_smul] at h1
    exact h1.symm
  have hzero : f 0 = 0 := by
    have := hadd 0 0
    simpa using this
  set ι₀ : O →+* k' :=
    { toFun := f, map_one' := hone, map_mul' := hmul, map_zero' := hzero,
      map_add' := hadd }
  have hι₀a : ∀ a, ι₀ a = f a := fun _ => rfl
  -- The two images `ψ e₀`, `ψ e₁` span `V`, hence form a basis.
  set b : Fin 2 → V := fun i => ψ (Pi.single i 1) with hb
  have hcoord : ∀ u : Fin 2 → O, ψ u = ι₀ (u 0) • b 0 + ι₀ (u 1) • b 1 := by
    intro u
    have hu : u = u 0 • Pi.single (0 : Fin 2) (1 : O) + u 1 • Pi.single (1 : Fin 2) (1 : O) := by
      ext i; fin_cases i <;> simp
    calc ψ u = ψ (u 0 • Pi.single (0 : Fin 2) (1 : O) + u 1 • Pi.single (1 : Fin 2) (1 : O)) := by
              rw [← hu]
      _ = ψ (u 0 • Pi.single (0 : Fin 2) (1 : O)) + ψ (u 1 • Pi.single (1 : Fin 2) (1 : O)) :=
              hψadd _ _
      _ = ι₀ (u 0) • b 0 + ι₀ (u 1) • b 1 := by rw [hsemi, hsemi, hι₀a, hι₀a, hb]
  have hspan : ⊤ ≤ Submodule.span k' (Set.range b) := by
    rintro v -
    obtain ⟨u, rfl⟩ : ∃ u, ψ u = v := ⟨sec v, hsec v⟩
    rw [hcoord u]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  have hcard : Fintype.card (Fin 2) = Module.finrank k' V := by simp [hfr]
  set bb : Module.Basis (Fin 2) k' V := basisOfTopLeSpanOfCardEqFinrank b hspan hcard
  have hbbv : ∀ i, bb i = b i := fun i =>
    congrFun (coe_basisOfTopLeSpanOfCardEqFinrank b hspan hcard) i
  refine ⟨ι₀, bb.equivFun.symm, fun g => ?_⟩
  apply bb.ext
  intro j
  have hEsymm : bb.equivFun.symm (Pi.single j (1 : k')) = bb j := by
    rw [Module.Basis.equivFun_symm_apply]
    simp
  have hkey : (LinearEquiv.conj bb.equivFun.symm
      (Matrix.toLin' ((LinearMap.toMatrix' (τ g)).map ι₀))) (bb j) = ρ' g (bb j) := by
    rw [LinearEquiv.conj_apply_apply]
    have h1 : bb.equivFun.symm.symm (bb j) = Pi.single j (1 : k') := by
      rw [← hEsymm]; exact (bb.equivFun.symm).symm_apply_apply _
    rw [h1]
    have h2 : (Matrix.toLin' ((LinearMap.toMatrix' (τ g)).map ι₀)) (Pi.single j (1 : k')) =
        fun i => ι₀ (τ g (Pi.single j (1 : O)) i) := by
      ext i
      simp [Matrix.toLin'_apply, Matrix.map_apply, LinearMap.toMatrix'_apply]
    rw [h2, Module.Basis.equivFun_symm_apply]
    rw [Fin.sum_univ_two, hbbv, hbbv]
    rw [← hcoord (τ g (Pi.single j (1 : O))), hψequiv, hbbv, hb]
  exact hkey.symm

section ResidualEmbeddingNonScalarCommutant

open _root_.IsLocalRing

/-! ### Machinery for the non-scalar-commutant half of the Noether–Skolem step

The four lemmas below are exactly what
`exists_residualEmbedding_of_nonScalarCommutant` needs; all four are pure
module theory over mathlib, and none of them mentions `G`, a Galois group
or a scheme. Together they replace the Wedderburn / Noether–Skolem
apparatus that the leaf's original cut expected to have to build. -/

/-! ### Step 1: nonzero socle of a finite module over a local ring -/

theorem exists_ne_zero_maximalIdeal_smul_eq_zero
    {O : Type*} [CommRing O] [IsLocalRing O]
    {M : Type*} [AddCommGroup M] [Module O M] [Finite M] [Nontrivial M] :
    ∃ x : M, x ≠ 0 ∧ ∀ a ∈ maximalIdeal O, a • x = 0 := by
  classical
  have htop : (⊤ : Submodule O M) ≠ ⊥ := by
    obtain ⟨x, hx⟩ := exists_ne (0 : M)
    intro h
    exact hx (by simpa using (h ▸ Submodule.mem_top : x ∈ (⊥ : Submodule O M)))
  have hP : ∃ n, ∃ N : Submodule O M, N ≠ ⊥ ∧ Nat.card N = n := ⟨_, ⊤, htop, rfl⟩
  obtain ⟨N, hN0, hNc⟩ := Nat.find_spec hP
  by_cases hsm : (maximalIdeal O) • N = ⊥
  · obtain ⟨x, hxN, hx0⟩ := (Submodule.ne_bot_iff N).mp hN0
    refine ⟨x, hx0, fun a ha => ?_⟩
    have hmem : a • x ∈ (maximalIdeal O) • N := Submodule.smul_mem_smul ha hxN
    rw [hsm] at hmem
    simpa using hmem
  · exfalso
    set T : Submodule O M := (maximalIdeal O) • N with hT
    have hle : T ≤ N := Submodule.smul_le_right
    have hmin : Nat.find hP ≤ Nat.card T := Nat.find_le ⟨_, hsm, rfl⟩
    have hsub : (T : Set M) ⊆ (N : Set M) := hle
    have hfin : (N : Set M).Finite := Set.toFinite _
    have hcards : (N : Set M).ncard ≤ (T : Set M).ncard := by
      have h1 : (N : Set M).ncard = Nat.card N := rfl
      have h2 : (T : Set M).ncard = Nat.card T := rfl
      rw [h1, h2, hNc]
      exact hmin
    have heq : T = N :=
      SetLike.coe_injective (Set.eq_of_subset_of_ncard_le hsub hcards hfin)
    haveI : Module.Finite O N := Module.Finite.of_finite
    have hfg : N.FG := (Submodule.fg_top N).mp (Module.finite_def.mp inferInstance)
    exact hN0 (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal O) N hfg
      (by rw [← hT, heq]) (maximalIdeal_le_jacobson ⊥))

/-! ### Step 2: Lagrange for a submodule, via an explicit section -/

theorem card_eq_card_mul_card_quotient
    {O : Type*} [CommRing O]
    {M : Type u} [AddCommGroup M] [Module O M] (N : Submodule O M) :
    Nat.card M = Nat.card N * Nat.card (M ⧸ N) := by
  classical
  obtain ⟨sec, hsec⟩ :=
    Function.Surjective.hasRightInverse (Submodule.Quotient.mk_surjective N)
  have hbij : Function.Bijective (fun p : N × (M ⧸ N) => (p.1 : M) + sec p.2) := by
    constructor
    · rintro ⟨n₁, z₁⟩ ⟨n₂, z₂⟩ h
      simp only at h
      have hz : z₁ = z₂ := by
        have := congrArg (Submodule.Quotient.mk (p := N)) h
        rwa [Submodule.Quotient.mk_add, Submodule.Quotient.mk_add,
          (Submodule.Quotient.mk_eq_zero N).mpr n₁.2,
          (Submodule.Quotient.mk_eq_zero N).mpr n₂.2, zero_add, zero_add,
          hsec, hsec] at this
      subst hz
      have : (n₁ : M) = (n₂ : M) := by
        have := h
        simpa using this
      exact Prod.ext (Subtype.ext this) rfl
    · intro m
      refine ⟨⟨⟨m - sec (Submodule.Quotient.mk m), ?_⟩, Submodule.Quotient.mk m⟩, by
        show m - sec (Submodule.Quotient.mk m) + sec (Submodule.Quotient.mk m) = m
        abel⟩
      rw [← Submodule.Quotient.mk_eq_zero]
      rw [Submodule.Quotient.mk_sub, hsec, sub_self]
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective _ hbij)).symm

/-! ### Step 3: the cardinality of a finite module over a local ring is a power of `#𝔽` -/

theorem card_eq_pow_card_residue
    (O : Type*) [CommRing O] [IsLocalRing O] :
    ∀ (n : ℕ) (M : Type u) [AddCommGroup M] [Module O M] [Finite M],
      Nat.card M = n → ∃ d : ℕ, n = (Nat.card (O ⧸ maximalIdeal O)) ^ d := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M _ _ _ hM
    by_cases hnt : Nontrivial M
    · obtain ⟨x, hx0, hx⟩ := exists_ne_zero_maximalIdeal_smul_eq_zero (O := O) (M := M)
      -- the cyclic submodule generated by `x` is killed by `𝔪`, hence a copy of `𝔽`
      set f : O →ₗ[O] M := LinearMap.toSpanSingleton O M x with hf
      set N : Submodule O M := LinearMap.range f with hNdef
      have hkerne : LinearMap.ker f ≠ ⊤ := by
        intro h
        have : (1 : O) ∈ LinearMap.ker f := h ▸ Submodule.mem_top
        rw [LinearMap.mem_ker, hf] at this
        simp only [LinearMap.toSpanSingleton_apply, one_smul] at this
        exact hx0 this
      have hkerle : maximalIdeal O ≤ LinearMap.ker f := by
        intro a ha
        rw [LinearMap.mem_ker, hf]
        simpa using hx a ha
      have hker : LinearMap.ker f = maximalIdeal O :=
        ((maximalIdeal.isMaximal O).eq_of_le hkerne hkerle).symm
      have hNcard : Nat.card N = Nat.card (O ⧸ maximalIdeal O) := by
        rw [← hker]
        exact (Nat.card_congr (f.quotKerEquivRange).toEquiv).symm
      have hlag : Nat.card M = Nat.card N * Nat.card (M ⧸ N) :=
        card_eq_card_mul_card_quotient N
      haveI : Finite N := Set.toFinite _
      have hNne : 1 < Nat.card N := by
        haveI : Nontrivial N := ⟨⟨0, ⟨x, ⟨1, by simp [hf]⟩⟩,
          fun h => hx0 (congrArg Subtype.val h).symm⟩⟩
        haveI : Fintype N := Fintype.ofFinite N
        rw [Nat.card_eq_fintype_card]
        exact Fintype.one_lt_card
      haveI : Finite (M ⧸ N) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective N)
      have hpos : 0 < Nat.card (M ⧸ N) := Nat.card_pos
      have hlt : Nat.card (M ⧸ N) < n := by
        rw [← hM, hlag]
        calc Nat.card (M ⧸ N) = 1 * Nat.card (M ⧸ N) := (one_mul _).symm
          _ < Nat.card N * Nat.card (M ⧸ N) :=
              Nat.mul_lt_mul_of_lt_of_le hNne (le_refl _) hpos
      obtain ⟨e, he⟩ := ih _ hlt (M ⧸ N) rfl
      exact ⟨1 + e, by rw [← hM, hlag, hNcard, he, pow_add, pow_one]⟩
    · refine ⟨0, ?_⟩
      rw [← hM, pow_zero]
      haveI : Subsingleton M := not_nontrivial_iff_subsingleton.mp hnt
      simp

/-! ### Step 4: an eigenvector for an endomorphism with `A ^ #k' = A` -/

theorem exists_eigenvector_of_pow_card
    {k' : Type*} [Field k'] [Fintype k']
    {N : Type*} [AddCommGroup N] [Module k' N] [Nontrivial N]
    (A : Module.End k' N) (hA : A ^ (Fintype.card k') = A) :
    ∃ (lam : k') (x : N), x ≠ 0 ∧ A x = lam • x := by
  classical
  have key : ∀ (s : Finset k') (x : N),
      (Polynomial.aeval A (∏ a ∈ s, (X - C a))) x = 0 → x ≠ 0 →
      ∃ (lam : k') (y : N), y ≠ 0 ∧ A y = lam • y := by
    intro s
    induction s using Finset.induction with
    | empty => intro x hx hx0; simp at hx; exact absurd hx hx0
    | insert a s ha ih =>
      intro x hx hx0
      rw [Finset.prod_insert ha, map_mul] at hx
      by_cases hy0 : (Polynomial.aeval A (∏ b ∈ s, (X - C b))) x = 0
      · exact ih x hy0 hx0
      · refine ⟨a, (Polynomial.aeval A (∏ b ∈ s, (X - C b))) x, hy0, ?_⟩
        have hxx : (Polynomial.aeval A (X - C a))
            ((Polynomial.aeval A (∏ b ∈ s, (X - C b))) x) = 0 := hx
        rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at hxx
        have hzero : A ((Polynomial.aeval A (∏ b ∈ s, (X - C b))) x)
            - a • ((Polynomial.aeval A (∏ b ∈ s, (X - C b))) x) = 0 := by
          simpa [Module.algebraMap_end_apply] using hxx
        exact sub_eq_zero.mp hzero
  obtain ⟨x, hx0⟩ := exists_ne (0 : N)
  have hQ1 : 1 < Fintype.card k' := Fintype.one_lt_card
  have hmonic : (X ^ (Fintype.card k') - X : k'[X]).Monic :=
    Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast hQ1)
  have hroots : (X ^ (Fintype.card k') - X : k'[X]).roots = Finset.univ.val :=
    FiniteField.roots_X_pow_card_sub_X k'
  have hdeg : (X ^ (Fintype.card k') - X : k'[X]).natDegree = Fintype.card k' :=
    FiniteField.X_pow_card_sub_X_natDegree_eq k' hQ1
  have hsplit : (∏ a : k', (X - C a)) = X ^ (Fintype.card k') - X := by
    have hcount : (X ^ (Fintype.card k') - X : k'[X]).roots.card
        = (X ^ (Fintype.card k') - X : k'[X]).natDegree := by
      rw [hroots, hdeg]
      simp
    have hprod := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic hcount
    rw [hroots] at hprod
    exact hprod
  refine key Finset.univ x ?_ hx0
  rw [hsplit]
  simp [hA]

/-- **The residual comparison when the commutant is bigger than the
scalars** (PROVEN 2026-07-26 — and NOT by Wedderburn or Noether–Skolem;
see THE PROOF below, which needs neither). This is the complement of
`exists_residualEmbedding_of_scalarCommutant`: the case in which `ρ'` is
irreducible but NOT absolutely irreducible, stated over an abstract
monoid `G` so that it can be attacked with mathlib alone.

**`_hC` IS NOT USED, AND THAT IS A RESULT, NOT AN OVERSIGHT.** The proof
below never looks at the commutant, so it establishes the conclusion on
BOTH sides of the parent's `Classical.em` dichotomy. The hypothesis is
kept in the signature only so that the already-proven parent
`exists_residualEmbedding_of_residualComparison` continues to typecheck
unchanged; a later cleanup could delete the dichotomy entirely and call
this leaf directly. What IS essential is `hirr` (used exactly once, to
know that the `k'`-span of the image of the semilinear map is all of
`V`), `hψsurj` (for the cardinality count), `hϖ`, `[IsLocalRing O]` and
`[Finite k']`.

Statement. Same data as in the scalar-commutant case — a two-dimensional
`k'`-representation `ρ'` of `G`, a rank-two `O`-representation `τ`, and
an additive, surjective, `G`-equivariant `ψ : O² → V` with kernel
`ϖ · O²` — but now `ρ'` is assumed IRREDUCIBLE and the commutant
`C := End_{ℤ[G]}(V)` is assumed to contain a non-scalar. The conclusion
is unchanged: `ρ'` is the `ι₀`-reduction of `τ` in some `k'`-basis.

TRUTH AUDIT (2026-07-26, by the agent that cut this leaf; the parent was
refuted once already, so this was checked rather than assumed). The
statement is TRUE, and the following is a complete sketch, worked through
in every case that the hypotheses permit.

Write `Ō := O ⧸ (ϖ)` and transport the `O`-action along `ψ` as in the
scalar case, giving an INJECTIVE ring map `T : Ō ↪ C`; the `k'`-scalars
give a second embedding `κ : k' ↪ C`. Additively `V ≅ Ō²`, so
`#Ō² = #V = #k'²`, hence `#Ō = #k'`; and `V` is a `k'`-vector space, so
`p · V = 0` and `Ō` has characteristic `p`. Its residue field `𝔽` then
satisfies `#Ō = #𝔽 ^ ℓ` (filter `Ō` by the powers of its maximal ideal —
each graded piece is an `𝔽`-vector space), so `#𝔽 ∣ #k'` as prime powers
and `𝔽 ↪ k'` ALWAYS. Moreover every ring map `O →+* k'` automatically
kills the maximal ideal, because `k'` is finite: the image is a finite
domain, hence a field, so the kernel is maximal. So the only candidates
for `ι₀` are the embeddings `𝔽 ↪ k'`, and they form one orbit under
`Aut(k')` — that Galois ambiguity is exactly what the existential
quantifier on `ι₀` absorbs.

THE PROOF, which is where this leaf turned out to be much cheaper than
its cut expected. The structure theory sketched in the paragraph above
(isotypic decomposition, Wedderburn, Krull–Schmidt, Noether–Skolem) is
NOT NEEDED. What replaces it is the observation that the required datum
is exactly a nonzero additive `G`-equivariant `ι₀`-SEMILINEAR map out of
`O²`, and that such a map can be produced as an EIGENVECTOR:

1. *Counting.* `ψ` induces a bijection `(O ⧸ (ϖ))² ≃ V`, so
   `#(O ⧸ (ϖ)) = #k'`; and `#M` is a power of `#𝔽` for EVERY finite
   module `M` over the local ring `O` (`card_eq_pow_card_residue`, proved
   by induction on `#M`: the socle of `M` is a nonzero cyclic module
   killed by `𝔪`, hence a copy of `𝔽`, and one divides it out). Hence
   `#k' = #𝔽 ^ d`, so iterated Frobenius gives `y ^ #k' = y` for every
   `y : 𝔽` — the arithmetic form of `𝔽 ↪ k'`.
2. *A nonzero test map.* Choose `c ∈ O` with `c ∉ (ϖ)` and `𝔪·c ⊆ (ϖ)`
   (the socle of `O ⧸ (ϖ)`, from `exists_ne_zero_maximalIdeal_smul_eq_zero`).
   Then `θ₀ : u ↦ ψ (c • u)` is additive, `G`-equivariant, nonzero, and
   KILLS `𝔪 · O²`.
3. *The eigenvector.* Let `M` be the `k'`-subspace of additive maps
   `O² → V` that are `G`-equivariant and kill `𝔪 · O²`; it is nonzero by
   step 2. Precomposition by a lift `α ∈ O` of a generator of `𝔽ˣ` is a
   `k'`-linear endomorphism `A` of `M`, and `A ^ #k' = A` because
   `α ^ #k' - α ∈ 𝔪` by step 1. Since `X ^ #k' - X = ∏_{λ ∈ k'} (X - λ)`
   splits over `k'`, some factor `A - λ` is non-injective
   (`exists_eigenvector_of_pow_card`), giving `θ ≠ 0` in `M` with
   `θ (α • u) = λ • θ u`.
4. *The ring map.* `{y : O | ∃ cc, ∀ u, θ (y • u) = cc • θ u}` contains
   `𝔪` (value `0`) and every power of `α` (value `λ ^ n`), and is closed
   under sums and products; since `𝔽ˣ = ⟨ᾱ⟩` every `y : O` is congruent
   to a power of `α` mod `𝔪`, so it is ALL of `O`. The value is unique
   because `θ ≠ 0`, so `y ↦ cc` is a ring map `ι₀ : O →+* k'` and `θ` is
   `ι₀`-semilinear.
5. *The basis.* `b j := θ (e j)` spans a nonzero `ρ'`-stable
   `k'`-subspace, which is `⊤` by `hirr` — the ONLY use of
   irreducibility — hence a basis by
   `basisOfTopLeSpanOfCardEqFinrank`, and in it the matrix of `ρ' g` is
   the `ι₀`-image of the matrix of `τ g`, exactly as in the sibling.

The `𝔽_p[ε]/(ε²)` phenomenon flagged on the parent is real and is
covered: `O ⧸ (ϖ)` is nowhere assumed to be a field. Note also that
step 1 is the only place the hypothesis `hψsurj` is used, and that the
proof never needs `O` complete, `G` a group, or `V` semisimple over
`𝔽_p[G]`. -/
theorem exists_residualEmbedding_of_nonScalarCommutant
    {G : Type*} [Monoid G]
    {O : Type*} [CommRing O] [IsLocalRing O] (ϖ : O) (hϖ : ¬ IsUnit ϖ)
    (τ : Representation O G (Fin 2 → O))
    {k' : Type*} [Field k'] [Finite k']
    {V : Type*} [AddCommGroup V] [Module k' V] [Module.Finite k' V] [Module.Free k' V]
    (hV : Module.rank k' V = 2)
    (ρ' : Representation k' G V) (hirr : ρ'.IsIrreducible)
    (_hC : ¬ ∀ c : V →+ V, (∀ (g : G) (v : V), c (ρ' g v) = ρ' g (c v)) →
      ∃ a : k', ∀ v, c v = a • v)
    (ψ : (Fin 2 → O) → V)
    (hψadd : ∀ u u' : Fin 2 → O, ψ (u + u') = ψ u + ψ u')
    (hψsurj : Function.Surjective ψ)
    (hψker : ∀ u : Fin 2 → O, ψ u = 0 ↔ ∀ i, u i ∈ Ideal.span {ϖ})
    (hψequiv : ∀ (g : G) (u : Fin 2 → O), ψ (τ g u) = ρ' g (ψ u)) :
    ∃ (ι₀ : O →+* k') (E : (Fin 2 → k') ≃ₗ[k'] V),
      ∀ g : G, ρ' g = E.conj (Matrix.toLin' ((LinearMap.toMatrix' (τ g)).map ι₀)) := by
  classical
  haveI := hirr
  haveI : Fintype k' := Fintype.ofFinite k'
  set I : Ideal O := Ideal.span {ϖ} with hIdef
  set Ψ : (Fin 2 → O) →+ V := AddMonoidHom.mk' ψ hψadd with hΨdef
  have hΨa : ∀ u, Ψ u = ψ u := fun _ => rfl
  have hψsub : ∀ u u' : Fin 2 → O, ψ (u - u') = ψ u - ψ u' := by
    intro u u'; rw [← hΨa, map_sub, hΨa, hΨa]
  have hcong : ∀ u u' : Fin 2 → O, (∀ i, u i - u' i ∈ I) → ψ u = ψ u' := by
    intro u u' h
    have h0 : ψ (u - u') = 0 := (hψker _).mpr (by simpa using h)
    rw [hψsub] at h0
    exact sub_eq_zero.mp h0
  -- `V` is finite, of cardinality `(#k')²`
  have hfr : Module.finrank k' V = 2 := Module.finrank_eq_of_rank_eq (by exact_mod_cast hV)
  haveI : Finite V := Module.finite_of_finite k'
  haveI : Fintype V := Fintype.ofFinite V
  have hcardV : Nat.card V = (Nat.card k') ^ 2 := by
    rw [Nat.card_eq_fintype_card (α := V), Nat.card_eq_fintype_card (α := k'),
      Module.card_eq_pow_finrank (K := k') (V := V), hfr]
  -- a set-theoretic section of `O → O ⧸ (ϖ)`
  obtain ⟨sec, hsec⟩ :=
    Function.Surjective.hasRightInverse (Ideal.Quotient.mk_surjective (I := I))
  have hFbij : Function.Bijective (fun w : Fin 2 → O ⧸ I => ψ (fun i => sec (w i))) := by
    constructor
    · intro w w' h
      funext i
      have h0 : ψ ((fun j => sec (w j)) - fun j => sec (w' j)) = 0 := by
        rw [hψsub]
        simp only at h
        rw [h, sub_self]
      have h1 : sec (w i) - sec (w' i) ∈ I := by simpa using (hψker _).mp h0 i
      have h2 : Ideal.Quotient.mk I (sec (w i)) = Ideal.Quotient.mk I (sec (w' i)) :=
        (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr h1
      rwa [hsec, hsec] at h2
    · intro v
      obtain ⟨u, rfl⟩ := hψsurj v
      refine ⟨fun i => Ideal.Quotient.mk I (u i), hcong _ _ (fun i => ?_)⟩
      rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem, hsec]
  haveI : Finite (Fin 2 → O ⧸ I) := Finite.of_injective _ hFbij.injective
  haveI : Finite (O ⧸ I) :=
    Finite.of_injective (fun a : O ⧸ I => (fun _ => a : Fin 2 → O ⧸ I))
      (fun a b h => congrFun h 0)
  have hcardOI : Nat.card V = (Nat.card (O ⧸ I)) ^ 2 := by
    rw [← Nat.card_congr (Equiv.ofBijective _ hFbij), Nat.card_fun]
    simp
  have hcardq : Nat.card (O ⧸ I) = Nat.card k' :=
    (Nat.pow_left_injective (by norm_num) (hcardV.symm.trans hcardOI)).symm
  -- `(ϖ) ≤ 𝔪`, so the residue field is finite too
  have hϖm : ϖ ∈ maximalIdeal O := by
    by_contra h
    exact hϖ (IsLocalRing.notMem_maximalIdeal.mp h)
  have hIm : I ≤ maximalIdeal O := by
    rw [hIdef]
    exact Ideal.span_le.mpr (by simpa using hϖm)
  haveI : Finite (ResidueField O) := by
    refine Finite.of_surjective
      (Ideal.Quotient.lift I (IsLocalRing.residue O) (fun a ha => ?_)) (fun z => ?_)
    · exact (IsLocalRing.residue_eq_zero_iff a).mpr (hIm ha)
    · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := maximalIdeal O) z
      exact ⟨Ideal.Quotient.mk I a, ha⟩
  haveI : Fintype (ResidueField O) := Fintype.ofFinite _
  -- `#k'` is a power of `#𝔽`, so the Frobenius of `k'` is the identity on `𝔽`
  obtain ⟨d, hd⟩ := card_eq_pow_card_residue O (Nat.card (O ⧸ I)) (O ⧸ I) rfl
  have hQpow : Fintype.card k' = (Fintype.card (ResidueField O)) ^ d := by
    rw [← Nat.card_eq_fintype_card (α := k'), ← Nat.card_eq_fintype_card (α := ResidueField O),
      ← hcardq]
    exact hd
  have hfrobpow : ∀ (m : ℕ) (y : ResidueField O),
      y ^ ((Fintype.card (ResidueField O)) ^ m) = y := by
    intro m
    induction m with
    | zero => intro y; simp
    | succ m ih => intro y; rw [pow_succ, pow_mul, ih y, FiniteField.pow_card]
  have hfrob : ∀ y : ResidueField O, y ^ (Fintype.card k') = y := by
    intro y; rw [hQpow]; exact hfrobpow d y
  -- the socle of `O ⧸ (ϖ)`: an element `c ∉ (ϖ)` with `𝔪 c ⊆ (ϖ)`
  haveI : Nontrivial (O ⧸ I) := by
    refine ⟨⟨1, 0, fun h => hϖ ?_⟩⟩
    have h1 : (1 : O) ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_one]
      exact h
    rw [hIdef] at h1
    exact Ideal.span_singleton_eq_top.mp ((Ideal.eq_top_iff_one _).mpr h1)
  obtain ⟨cbar, hcbar0, hcbar⟩ :=
    exists_ne_zero_maximalIdeal_smul_eq_zero (O := O) (M := O ⧸ I)
  set c : O := sec cbar with hcdef
  have hmkc : Ideal.Quotient.mk I c = cbar := hsec cbar
  have hcI : c ∉ I := by
    intro h
    exact hcbar0 (by rw [← hmkc]; exact (Ideal.Quotient.eq_zero_iff_mem).mpr h)
  have hmc : ∀ a ∈ maximalIdeal O, a * c ∈ I := by
    intro a ha
    have h1 := hcbar a ha
    rw [← hmkc] at h1
    have h2 : Ideal.Quotient.mk I (a * c) = 0 := by
      rw [← h1]
      rfl
    exact (Ideal.Quotient.eq_zero_iff_mem).mp h2
  -- a generator of `𝔽ˣ` and a lift of it to `O`
  obtain ⟨gen, hgen⟩ := IsCyclic.exists_generator (α := (ResidueField O)ˣ)
  obtain ⟨α, hα⟩ := Ideal.Quotient.mk_surjective (I := maximalIdeal O) (gen : ResidueField O)
  have hαres : IsLocalRing.residue O α = (gen : ResidueField O) := hα
  -- the space of additive `G`-equivariant maps killing `𝔪 · O²`
  set Sα : (Fin 2 → O) →ₗ[ℤ] (Fin 2 → O) :=
    { toFun := fun u => α • u
      map_add' := fun u u' => smul_add _ _ _
      map_smul' := fun n u => smul_comm α n u } with hSαdef
  set Msub : Submodule k' ((Fin 2 → O) →ₗ[ℤ] V) :=
    { carrier := {θ | (∀ (g : G) (u : Fin 2 → O), θ (τ g u) = ρ' g (θ u)) ∧
        (∀ a ∈ maximalIdeal O, ∀ u : Fin 2 → O, θ (a • u) = 0)}
      add_mem' := by
        rintro θ η ⟨h1, h2⟩ ⟨h3, h4⟩
        exact ⟨fun g u => by simp [h1 g u, h3 g u], fun a ha u => by simp [h2 a ha u, h4 a ha u]⟩
      zero_mem' := ⟨fun g u => by simp, fun a ha u => by simp⟩
      smul_mem' := by
        rintro cc θ ⟨h1, h2⟩
        exact ⟨fun g u => by simp [h1 g u], fun a ha u => by simp [h2 a ha u]⟩ } with hMsubdef
  set θ₀ : (Fin 2 → O) →ₗ[ℤ] V :=
    { toFun := fun u => ψ (c • u)
      map_add' := fun u u' => by rw [smul_add, hψadd]
      map_smul' := fun n u => by
        show ψ (c • (n • u)) = n • ψ (c • u)
        rw [smul_comm, ← hΨa, ← hΨa, map_zsmul] } with hθ₀def
  have hθ₀mem : θ₀ ∈ Msub := by
    refine ⟨fun g u => ?_, fun a ha u => ?_⟩
    · show ψ (c • τ g u) = ρ' g (ψ (c • u))
      rw [← hψequiv g (c • u)]
      congr 1
      exact ((τ g).map_smul c u).symm
    · show ψ (c • (a • u)) = 0
      refine (hψker _).mpr (fun i => ?_)
      have hco : (c • (a • u)) i = (a * c) * u i := by
        show c * (a * u i) = (a * c) * u i
        ring
      rw [hco]
      exact Ideal.mul_mem_right _ _ (hmc a ha)
  have hθ₀ne : θ₀ ≠ 0 := by
    intro h
    have h1 : ψ (c • (Pi.single (0 : Fin 2) (1 : O))) = 0 := by
      have h2 := congrArg (fun (f : (Fin 2 → O) →ₗ[ℤ] V) => f (Pi.single (0 : Fin 2) (1 : O))) h
      simpa [hθ₀def] using h2
    have h3 := (hψker _).mp h1 0
    apply hcI
    have h4 : (c • (Pi.single (0 : Fin 2) (1 : O))) 0 = c := by simp
    rwa [h4] at h3
  -- precomposition by `α`
  set Aamb : Module.End k' ((Fin 2 → O) →ₗ[ℤ] V) :=
    { toFun := fun θ => θ.comp Sα
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } with hAambdef
  have hAmap : ∀ θ ∈ Msub, Aamb θ ∈ Msub := by
    rintro θ ⟨h1, h2⟩
    refine ⟨fun g u => ?_, fun a ha u => ?_⟩
    · show θ (α • τ g u) = ρ' g (θ (α • u))
      rw [← h1 g (α • u)]
      congr 1
      exact ((τ g).map_smul α u).symm
    · show θ (α • (a • u)) = 0
      rw [smul_comm]
      exact h2 a ha (α • u)
  set Ares : Module.End k' Msub := Aamb.restrict hAmap with hAresdef
  haveI : Nontrivial Msub :=
    ⟨⟨0, ⟨θ₀, hθ₀mem⟩, fun h => hθ₀ne (congrArg Subtype.val h).symm⟩⟩
  have hArest : ∀ (x : Msub) (u : Fin 2 → O),
      ((Ares x : (Fin 2 → O) →ₗ[ℤ] V)) u = (x : (Fin 2 → O) →ₗ[ℤ] V) (α • u) := by
    intro x u
    rw [hAresdef, LinearMap.restrict_apply]
    rfl
  have hpow : ∀ (n : ℕ) (x : Msub) (u : Fin 2 → O),
      ((Ares ^ n) x : (Fin 2 → O) →ₗ[ℤ] V) u = (x : (Fin 2 → O) →ₗ[ℤ] V) (α ^ n • u) := by
    intro n
    induction n with
    | zero => intro x u; simp
    | succ m ih =>
        intro x u
        rw [pow_succ, Module.End.mul_apply, ih (Ares x) u, hArest x, smul_smul, ← pow_succ']
  have hAQ : Ares ^ (Fintype.card k') = Ares := by
    refine LinearMap.ext fun x => Subtype.ext (LinearMap.ext fun u => ?_)
    rw [hpow, hArest]
    have hmem : α ^ (Fintype.card k') - α ∈ maximalIdeal O := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, hαres, hfrob, sub_self]
    have hz := x.2.2 _ hmem u
    rw [sub_smul, map_sub, sub_eq_zero] at hz
    exact hz
  obtain ⟨lam, xeig, hxeig0, hxeig⟩ := exists_eigenvector_of_pow_card Ares hAQ
  set θ : (Fin 2 → O) →ₗ[ℤ] V := (xeig : (Fin 2 → O) →ₗ[ℤ] V) with hθdef
  have hθequiv : ∀ (g : G) (u : Fin 2 → O), θ (τ g u) = ρ' g (θ u) := xeig.2.1
  have hθker : ∀ a ∈ maximalIdeal O, ∀ u : Fin 2 → O, θ (a • u) = 0 := xeig.2.2
  have hθα : ∀ u, θ (α • u) = lam • θ u := by
    intro u
    have h1 := congrArg (fun (z : Msub) => (z : (Fin 2 → O) →ₗ[ℤ] V) u) hxeig
    rw [hArest xeig u] at h1
    exact h1
  have hθne : θ ≠ 0 := fun h => hxeig0 (Subtype.ext h)
  have hθpow : ∀ (n : ℕ) (u : Fin 2 → O), θ (α ^ n • u) = lam ^ n • θ u := by
    intro n
    induction n with
    | zero => intro u; simp
    | succ m ih =>
        intro u
        rw [pow_succ', ← smul_smul, hθα, ih, smul_smul, ← pow_succ']
  -- every scalar acts on `θ` through a scalar of `k'`
  have hexc : ∀ y : O, ∃ cc : k', ∀ u, θ (y • u) = cc • θ u := by
    intro y
    by_cases hy : y ∈ maximalIdeal O
    · exact ⟨0, fun u => by rw [hθker y hy u, zero_smul]⟩
    · have hres : IsLocalRing.residue O y ≠ 0 := by
        rw [Ne, IsLocalRing.residue_eq_zero_iff]
        exact hy
      obtain ⟨yu, hyu⟩ : ∃ yu : (ResidueField O)ˣ,
          (yu : ResidueField O) = IsLocalRing.residue O y :=
        ⟨(isUnit_iff_ne_zero.mpr hres).unit, IsUnit.unit_spec _⟩
      obtain ⟨n, hn⟩ : ∃ n : ℕ, gen ^ n = yu := by
        have hmem := hgen yu
        rwa [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hmem
      refine ⟨lam ^ n, fun u => ?_⟩
      have hdiff : y - α ^ n ∈ maximalIdeal O := by
        rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, hαres, ← hyu, ← hn,
          Units.val_pow_eq_pow_val, sub_self]
      calc θ (y • u) = θ ((y - α ^ n) • u + α ^ n • u) := by rw [← add_smul]; ring_nf
        _ = θ ((y - α ^ n) • u) + θ (α ^ n • u) := map_add _ _ _
        _ = lam ^ n • θ u := by rw [hθker _ hdiff u, hθpow, zero_add]
  obtain ⟨u₀, hu₀⟩ : ∃ u, θ u ≠ 0 := by
    by_contra h
    push Not at h
    exact hθne (LinearMap.ext h)
  choose ι₀f hι₀f using hexc
  have huniq : ∀ (y : O) (cc : k'), (∀ u, θ (y • u) = cc • θ u) → cc = ι₀f y := by
    intro y cc h
    have h0 : (cc - ι₀f y) • θ u₀ = 0 := by
      rw [sub_smul, ← h u₀, ← hι₀f y u₀, sub_self]
    rcases smul_eq_zero.mp h0 with h1 | h1
    · exact sub_eq_zero.mp h1
    · exact absurd h1 hu₀
  set ι₀ : O →+* k' :=
    { toFun := ι₀f
      map_one' := (huniq 1 1 (fun u => by rw [one_smul, one_smul])).symm
      map_mul' := fun a b => (huniq (a * b) (ι₀f a * ι₀f b) (fun u => by
        rw [mul_smul, hι₀f a, hι₀f b, smul_smul])).symm
      map_zero' := (huniq 0 0 (fun u => by rw [zero_smul, zero_smul, map_zero])).symm
      map_add' := fun a b => (huniq (a + b) (ι₀f a + ι₀f b) (fun u => by
        rw [add_smul, map_add, hι₀f a, hι₀f b, ← add_smul])).symm } with hι₀def
  have hι₀a : ∀ y, ι₀ y = ι₀f y := fun _ => rfl
  -- the two images span, by irreducibility
  set b : Fin 2 → V := fun i => θ (Pi.single i 1) with hbdef
  have hcoord : ∀ u : Fin 2 → O, θ u = ι₀ (u 0) • b 0 + ι₀ (u 1) • b 1 := by
    intro u
    have hu : u = u 0 • Pi.single (0 : Fin 2) (1 : O) + u 1 • Pi.single (1 : Fin 2) (1 : O) := by
      ext i; fin_cases i <;> simp
    calc θ u
        = θ (u 0 • Pi.single (0 : Fin 2) (1 : O) + u 1 • Pi.single (1 : Fin 2) (1 : O)) := by
          rw [← hu]
      _ = θ (u 0 • Pi.single (0 : Fin 2) (1 : O)) + θ (u 1 • Pi.single (1 : Fin 2) (1 : O)) :=
          map_add _ _ _
      _ = ι₀ (u 0) • b 0 + ι₀ (u 1) • b 1 := by rw [hι₀f, hι₀f, hι₀a, hι₀a, hbdef]
  set W : Submodule k' V := Submodule.span k' (Set.range b) with hWdef
  have hmemW : ∀ u : Fin 2 → O, θ u ∈ W := by
    intro u
    rw [hcoord u]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  have hstable : ∀ (g : G) ⦃v : V⦄, v ∈ W → ρ' g v ∈ W := by
    intro g v hv
    have hle : W ≤ Submodule.comap (ρ' g) W := by
      rw [hWdef, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      show ρ' g (b j) ∈ W
      rw [hbdef]
      simp only
      rw [← hθequiv g (Pi.single j 1)]
      exact hmemW _
    exact hle hv
  have hWne : W ≠ ⊥ := by
    intro h
    apply hu₀
    have h1 := hmemW u₀
    rw [h] at h1
    simpa using h1
  have hWtop : W = ⊤ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top (⟨W, hstable⟩ : Subrepresentation ρ') with h | h
    · exact absurd (congrArg Subrepresentation.toSubmodule h) hWne
    · exact congrArg Subrepresentation.toSubmodule h
  have hcard : Fintype.card (Fin 2) = Module.finrank k' V := by simp [hfr]
  have hspan : ⊤ ≤ Submodule.span k' (Set.range b) := le_of_eq hWtop.symm
  set bb : Module.Basis (Fin 2) k' V := basisOfTopLeSpanOfCardEqFinrank b hspan hcard with hbb
  have hbbv : ∀ i, bb i = b i := fun i =>
    congrFun (coe_basisOfTopLeSpanOfCardEqFinrank b hspan hcard) i
  refine ⟨ι₀, bb.equivFun.symm, fun g => ?_⟩
  apply bb.ext
  intro j
  have hEsymm : bb.equivFun.symm (Pi.single j (1 : k')) = bb j := by
    rw [Module.Basis.equivFun_symm_apply]
    simp
  have hkey : (LinearEquiv.conj bb.equivFun.symm
      (Matrix.toLin' ((LinearMap.toMatrix' (τ g)).map ι₀))) (bb j) = ρ' g (bb j) := by
    rw [LinearEquiv.conj_apply_apply]
    have h1 : bb.equivFun.symm.symm (bb j) = Pi.single j (1 : k') := by
      rw [← hEsymm]; exact (bb.equivFun.symm).symm_apply_apply _
    rw [h1]
    have h2 : (Matrix.toLin' ((LinearMap.toMatrix' (τ g)).map ι₀)) (Pi.single j (1 : k')) =
        fun i => ι₀ (τ g (Pi.single j (1 : O)) i) := by
      ext i
      simp [Matrix.toLin'_apply, Matrix.map_apply, LinearMap.toMatrix'_apply]
    rw [h2, Module.Basis.equivFun_symm_apply]
    rw [Fin.sum_univ_two, hbbv, hbbv]
    rw [← hcoord (τ g (Pi.single j (1 : O))), hθequiv, hbbv, hbdef]
  exact hkey.symm

end ResidualEmbeddingNonScalarCommutant

/-- **Two rank-two structures on one irreducible residual representation
differ by a ring map** (PROVEN 2026-07-26 by the commutant dichotomy over
`exists_residualEmbedding_of_scalarCommutant` and
`exists_residualEmbedding_of_nonScalarCommutant`, both now PROVEN; this
is the leaf carrying `hirr`).

Statement. Let `τ` be a rank-two representation of `Γ_F` over a local
ring `O`, let `ρ'` be a two-dimensional representation over a finite
field `k'` which is IRREDUCIBLE, and suppose there is an additive,
surjective, `Γ_F`-equivariant comparison map `ψ : O² → V` whose kernel is
exactly `ϖ · O²`. Then there are a ring map `ι₀ : O →+* k'` and a
`k'`-basis of `V` in which `ρ'` IS the `ι₀`-reduction of `τ`.

This is `exists_residualEmbedding_of_tateFrame` with all the geometry
removed: `ψ` is the composite `O² ≃ T ↠ T/πT ≅ A[I] ≃ V`, and `ϖ = j π`.

THE ARGUMENT, and WHY `hirr` IS INDISPENSABLE. Write `Ō := O ⧸ (ϖ)`. The
comparison map makes `V ≅ Ō²`, so `Ō` is finite with `#Ō = #k'`, and both
`k'` and `Ō` embed in the commutant `C := End_{ℤ[Γ_F]}(V)` — `k'` by
scalars, `Ō` by transport along `ψ`. Two embeddings of coefficient rings
into `C` are conjugate only if `C` is SIMPLE, and simplicity is exactly
what irreducibility buys:

  `ρ'` irreducible ⟹ `V` is ISOTYPIC as an `𝔽_p[Γ_F]`-module
  ⟹ `C` is simple artinian.

The middle implication is the step to get right, and it is short: `V` is
`𝔽_p[Γ_F]`-semisimple because `k'/𝔽_p` is separable (so
`J(k'[Γ]) = k' ⊗ J(𝔽_p[Γ])`), and every isotypic component of a
semisimple module is preserved by EVERY endomorphism commuting with the
group — in particular by the `k'`-scalars. So if `V` had two distinct
isotypic components it would be a direct sum of two nonzero `k'`-stable
`Γ_F`-submodules, contradicting irreducibility. With `V` isotypic,
`C ≅ M_r(𝔽_q)` (Wedderburn: a finite division ring is a field), which is
simple, and Noether–Skolem applies: the two embeddings differ by an inner
automorphism of `C` composed with a field automorphism. The inner
automorphism is an additive `Γ_F`-equivariant change of basis, absorbed
into `E`; the field automorphism is absorbed into `ι₀`.

**DO NOT REACH FOR NOETHER–SKOLEM OR WEDDERBURN–MALCEV BEFORE
ESTABLISHING SIMPLICITY.** The unconditional form of this leaf — the same
statement with `hirr` deleted — is FALSE, refuted by an explicit
counterexample in the FAITHFULNESS AUDIT of
`exists_tateFrame_of_levelStructure`: for a split residual representation
`C = k' × k'` is commutative, has no inner automorphisms at all, and two
embeddings of a field of order `#k'` into it are genuinely inequivalent.

FAITHFULNESS NOTE (2026-07-26, this leaf's cut). `Ō` is NOT forced to be
a field by the hypotheses, and the prover should not assume it is: `O` is
pinned here only by locality and by the comparison map, and
`Ō = 𝔽_p[ε]/(ε²)` really does occur (take `Γ ↠ SL₂(𝔽_p)` acting through
the standard module `U`, `V := U ⊗_{𝔽_p} Ō` with `ε` nilpotent on the
`Ō`-factor and `k' := 𝔽_{p²}` acting on it — `ρ' = U ⊗ 𝔽_{p²}` is
irreducible and every hypothesis holds). The conclusion survives, because
`O` local artinian forces every ring map `O →+* k'` to kill the whole
maximal ideal, and the resulting reduction is again a two-dimensional
`k'`-representation of the right size; but a proof that silently assumes
`Ō` is a field is proving something weaker than the statement.

HOW THE PROOF BELOW SPLITS THAT (2026-07-26). The dichotomy is decided by
`Classical.em` on the single proposition "every additive endomorphism of
`V` commuting with `ρ'(Γ_F)` is a `k'`-scalar" — i.e. on whether the
commutant `C` is as small as it can be. On the affirmative side the two
coefficient rings are forced to COINCIDE, `ψ` itself is the change of
basis, and `exists_residualEmbedding_of_scalarCommutant` closes the case
outright, with `hirr` never used. The negative side is isolated in
`exists_residualEmbedding_of_nonScalarCommutant`, also PROVEN: it needs
`hirr` but, as it turned out, no simplicity apparatus and not even its
own commutant hypothesis; its docstring carries the argument.

Both halves are stated for an ABSTRACT MONOID and mathlib's
`Representation`, deliberately: `GaloisRep`'s `FunLike` hides a
`moduleTopology A (Module.End A M)` whose elaboration at a concrete
two-dimensional module is measured in tens of seconds per step, and none
of the remaining mathematics has anything to do with Galois theory. -/
theorem exists_residualEmbedding_of_residualComparison
    {F : Type u} [Field F] [NumberField F]
    {O : Type u} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [IsLocalRing O]
    (ϖ : O) (hϖ : ¬ IsUnit ϖ)
    (τ : GaloisRep F O (Fin 2 → O))
    {k' : Type u} [Field k'] [Finite k'] [TopologicalSpace k'] [DiscreteTopology k']
    {V : Type v} [AddCommGroup V] [Module k' V] [Module.Finite k' V] [Module.Free k' V]
    (hV : Module.rank k' V = 2)
    (ρ' : GaloisRep F k' V) (hirr : ρ'.IsIrreducible)
    (ψ : (Fin 2 → O) → V)
    (hψadd : ∀ u u' : Fin 2 → O, ψ (u + u') = ψ u + ψ u')
    (hψsurj : Function.Surjective ψ)
    (hψker : ∀ u : Fin 2 → O, ψ u = 0 ↔ ∀ i, u i ∈ Ideal.span {ϖ})
    (hψequiv : ∀ (σ : Field.absoluteGaloisGroup F) (u : Fin 2 → O),
      ψ (τ σ u) = ρ' σ (ψ u)) :
    ∃ (ι₀ : O →+* k') (E : (Fin 2 → k') ≃ₗ[k'] V),
      ∀ σ : Field.absoluteGaloisGroup F,
        ρ' σ = E.conj (Matrix.toLin' ((LinearMap.toMatrix' (τ σ)).map ι₀)) := by
  classical
  by_cases hC : ∀ c : V →+ V,
      (∀ (σ : Field.absoluteGaloisGroup F) (v : V),
        c (ρ'.toRepresentation σ v) = ρ'.toRepresentation σ (c v)) →
      ∃ a : k', ∀ v, c v = a • v
  · exact exists_residualEmbedding_of_scalarCommutant ϖ τ.toRepresentation hV
      ρ'.toRepresentation hC ψ hψadd hψsurj hψker hψequiv
  · exact exists_residualEmbedding_of_nonScalarCommutant ϖ hϖ τ.toRepresentation hV
      ρ'.toRepresentation hirr hC ψ hψadd hψsurj hψker hψequiv

/-- **The reduction of a Tate frame matches the level structure, up to an
automorphism of the residue field** (PROVEN 2026-07-26 by assembly over
the three leaves above; representation theory;
Noether–Skolem, and Brauer–Nesbitt for the converse direction).

Given a frame `φ` of `TatePt m x I π` by `τ` over `O` and a level
structure `e` identifying `A[I]` with an irreducible two-dimensional
representation `ρ'` over `k'`, there is a ring map `ι₀ : O →+* k'`
carrying the Frobenius characteristic polynomials of `τ` onto those of
`ρ'`, at EVERY place `w`.

The argument. Reduction along `φ` gives `T/πT ≅ A[I]` as `Γ_F`-modules
(`hker` at `n = 1` is what makes `π` cut out exactly `I`), and `e`
identifies `A[I]` with `V`. So `V` carries two structures of a vector
space over a field of order `#(𝒪_D/I)`: the `k'`-structure of `ρ'`, and
the `O/π`-structure transported from the Tate module. Both land in the
commutant `C := End_{ℤ[Γ_F]}(V)`. **Under `hirr` the commutant is simple**
— a field if `ρ'` is irreducible but not absolutely irreducible, a
central simple algebra over its centre otherwise — so Noether–Skolem
makes the two embeddings differ by an inner automorphism of `C`
composed with an element of `Aut(k')`. The inner automorphism is an
additive `Γ_F`-equivariant change of frame, absorbed into `φ`; the field
automorphism is absorbed into `ι₀`. Characteristic polynomials are
invariant under conjugation, and `charFrob` evaluates the representation
at a single group element, so the identity holds at every `w` including
the ramified ones.

**`hirr` IS LOAD-BEARING HERE AND NOWHERE ELSE.** Without it the
commutant can be `k' × k'`, which has no inner automorphisms at all, and
the conclusion is FALSE — that is the refutation recorded in the
FAITHFULNESS AUDIT of `exists_tateFrame_of_levelStructure`. Any attempt
to prove this leaf that reaches for Wedderburn–Malcev or Noether–Skolem
must establish simplicity of the commutant FIRST.

HOW THE ASSEMBLY BELOW SPLITS THAT (2026-07-26). The geometry and the
representation theory are separated completely. Everything that is about
abelian varieties — that the reduction `T ↠ A[I]` is surjective, and that
its kernel is `π T` — is delegated to `exists_tatePt_val_one_eq` and
`exists_tatePt_act_eq_of_val_one_eq_zero`; composing with the level
structure `e` (which is injective with image the `I`-torsion) turns them
into a single additive, surjective, `Γ_F`-equivariant comparison map
`ψ : O² → V` with kernel `j π · O²`, and that is *all* the geometry the
Noether–Skolem step ever sees. The step itself is
`exists_residualEmbedding_of_residualComparison`, stated over an abstract
comparison map; the simplicity discussion above is repeated there, in the
place where it is actually discharged.

The last mile — from an isomorphism of representations to the equality of
Frobenius characteristic polynomials — is done here rather than in a
leaf, because it is formal: `charFrob` evaluates at ONE group element,
`LinearEquiv.charpoly_conj` makes the charpoly blind to the change of
basis, and `Matrix.charpoly_map` is what turns the `ι₀`-reduction of the
matrix into the `ι₀`-image of the polynomial. That is also why the
conclusion holds at EVERY `w`, ramified places included.

WHAT `hker` IS FOR IN THIS PROOF. Only one thing, and it is not the
`n = 1` identification claimed above: it rules out `j π` being a UNIT
(which would make `Ideal.span {j π} = ⊤`, hence `1 ∈ I` and `I = ⊤`).
The identification `O/(j π) ≅ 𝒪_D/I` is not needed — the comparison map
already forces `#(O/(j π)) = #k'`. -/
theorem exists_residualEmbedding_of_tateFrame
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (I : Ideal (NumberField.RingOfIntegers D)) (hI : I.IsMaximal)
    (π : NumberField.RingOfIntegers D) (hπ : π ∈ I) (hπ2 : π ∉ I ^ 2)
    (O : Type u) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [IsLocalRing O]
    (j : NumberField.RingOfIntegers D →+* O)
    (hker : ∀ (n : ℕ) (a : NumberField.RingOfIntegers D),
      j a ∈ Ideal.span {j π} ^ n ↔ a ∈ I ^ n)
    (τ : GaloisRep F O (Fin 2 → O)) (φ : (Fin 2 → O) → TatePt m x I π)
    (hφadd : ∀ (u u' : Fin 2 → O) (n : ℕ),
      (φ (u + u')).1 n = ab.add ((φ u).1 n) ((φ u').1 n))
    (hφbij : Function.Bijective φ)
    (hφequiv : ∀ (σ : Field.absoluteGaloisGroup F) (u : Fin 2 → O) (n : ℕ),
      (φ (τ σ u)).1 n = ab.galSMul x σ ((φ u).1 n))
    (hφj : ∀ (a : NumberField.RingOfIntegers D) (u : Fin 2 → O) (n : ℕ),
      (φ (j a • u)).1 n = m.act a ((φ u).1 n))
    {k' : Type u} [Field k'] [Finite k'] [TopologicalSpace k'] [DiscreteTopology k']
    {V : Type v} [AddCommGroup V] [Module k' V] [Module.Finite k' V] [Module.Free k' V]
    (hV : Module.rank k' V = 2)
    (ρ' : GaloisRep F k' V)
    (hirr : ρ'.IsIrreducible)
    (e : V → GeomFibrePt f x)
    (headd : ∀ v v' : V, e (v + v') = ab.add (e v) (e v'))
    (heinj : Function.Injective e)
    (heequiv : ∀ (σ : Field.absoluteGaloisGroup F) (v : V),
      e (ρ' σ v) = ab.galSMul x σ (e v))
    (heimg : ∀ y, y ∈ (m.torsion x I).1 ↔ ∃ v, e v = y) :
    ∃ ι₀ : O →+* k',
      ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
        (τ.charFrob w).map ι₀ = ρ'.charFrob w := by
  classical
  letI := ab.addCommGroup (specAlgClos F ≫ x)
  letI := m.module (specAlgClos F ≫ x)
  -- `π` annihilates the `I`-torsion, by definition of `Mult.torsion`.
  have hkill : ∀ z : GeomFibrePt f x, z ∈ (m.torsion x I).1 → m.act π z = 0 := by
    intro z hz
    have hz' : z ∈ Submodule.torsionBySet (NumberField.RingOfIntegers D)
        (GeomFibrePt f x) ((I : Ideal (NumberField.RingOfIntegers D)) : Set _) := hz
    exact (Submodule.mem_torsionBySet_iff _ _).mp hz' ⟨π, hπ⟩
  -- The first stage of a point of the Tate module is `I`-torsion.
  have hmem : ∀ u : Fin 2 → O, (φ u).1 1 ∈ (m.torsion x I).1 := by
    intro u
    have h := (φ u).2.1 1
    rwa [pow_one] at h
  -- Hence it is `e` of a (unique) element of `V`: this is the comparison map `ψ`.
  have hex : ∀ u : Fin 2 → O, ∃ v : V, e v = (φ u).1 1 := fun u => (heimg _).1 (hmem u)
  choose ψ hψ using hex
  -- `e` kills zero.
  have he0 : e 0 = 0 := by
    have h := headd 0 0
    rw [add_zero] at h
    have h' : (0 : GeomFibrePt f x) + e 0 = e 0 + e 0 := by
      rw [zero_add]; exact h
    exact (add_right_cancel h').symm
  -- `ψ` is additive.
  have hψadd : ∀ u u' : Fin 2 → O, ψ (u + u') = ψ u + ψ u' := by
    intro u u'
    apply heinj
    rw [headd, hψ u, hψ u', hψ (u + u')]
    exact hφadd u u' 1
  -- `ψ` is `Γ_F`-equivariant, from `τ` to `ρ'`.
  have hψequiv : ∀ (σ : Field.absoluteGaloisGroup F) (u : Fin 2 → O),
      ψ (τ σ u) = ρ' σ (ψ u) := by
    intro σ u
    apply heinj
    rw [heequiv, hψ (τ σ u), hψ u]
    exact hφequiv σ u 1
  -- `ψ` is surjective: every torsion point lifts to the Tate module.
  have hψsurj : Function.Surjective ψ := by
    intro v
    obtain ⟨t, ht⟩ :=
      exists_tatePt_val_one_eq m x I hI π hπ hπ2 (e v) ((heimg (e v)).2 ⟨v, rfl⟩)
    obtain ⟨u, hu⟩ := hφbij.2 t
    exact ⟨u, heinj (by rw [hψ u, hu, ht])⟩
  -- The kernel of `ψ` is `j π • (Fin 2 → O)`.
  have hψker : ∀ u : Fin 2 → O, ψ u = 0 ↔ ∀ i, u i ∈ Ideal.span {j π} := by
    intro u
    constructor
    · intro hu i
      have h1 : (φ u).1 1 = ab.zero (specAlgClos F ≫ x) := by
        rw [← hψ u, hu, he0]
        rfl
      obtain ⟨t', ht'⟩ :=
        exists_tatePt_act_eq_of_val_one_eq_zero m x I hI π hπ hπ2 (φ u) h1
      obtain ⟨u', hu'⟩ := hφbij.2 t'
      have hEq : j π • u' = u := by
        apply hφbij.1
        apply Subtype.ext
        funext n
        show (φ (j π • u')).1 n = (φ u).1 n
        rw [hφj π u' n, hu', ht' n]
      rw [← hEq]
      exact Ideal.mem_span_singleton'.mpr ⟨u' i, by simp [mul_comm]⟩
    · intro hu
      choose c hc using fun i => Ideal.mem_span_singleton'.mp (hu i)
      have hu' : u = j π • c := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [← hc i, mul_comm]
      apply heinj
      rw [hψ u, he0, hu', hφj π c 1]
      exact hkill _ (hmem c)
  -- `j π` is not a unit: otherwise `hker` would put `1` into `I`.
  have hnu : ¬ IsUnit (j π) := by
    intro hu
    have hmem1 : j (1 : NumberField.RingOfIntegers D) ∈ Ideal.span {j π} ^ 1 := by
      rw [pow_one, Ideal.span_singleton_eq_top.mpr hu]
      exact Submodule.mem_top
    have h1 : (1 : NumberField.RingOfIntegers D) ∈ I ^ 1 := (hker 1 1).mp hmem1
    rw [pow_one] at h1
    exact hI.ne_top (Ideal.eq_top_of_isUnit_mem I h1 isUnit_one)
  -- The representation-theoretic step.
  obtain ⟨ι₀, E, hE⟩ :=
    exists_residualEmbedding_of_residualComparison (j π) hnu τ hV ρ' hirr ψ
      hψadd hψsurj hψker hψequiv
  -- Characteristic polynomials: `charFrob` evaluates at one group element.
  refine ⟨ι₀, fun w => ?_⟩
  set σw := Field.absoluteGaloisGroup.map
      (algebraMap F (IsDedekindDomain.HeightOneSpectrum.adicCompletion F w))
      (Field.AbsoluteGaloisGroup.adicArithFrob w)
  have h1 : τ.charFrob w = (τ σw).charpoly := rfl
  have h2 : ρ'.charFrob w = (ρ' σw).charpoly := rfl
  rw [h1, h2, hE σw, LinearEquiv.charpoly_conj, Matrix.charpoly_toLin', Matrix.charpoly_map]
  congr 1
  rw [← Matrix.charpoly_toLin', Matrix.toLin'_toMatrix']

/-! ### The determinant clause: the Weil pairing, and the cyclotomic
character at a Frobenius

The last conjunct of `exists_tateFrame_of_levelStructure` — that the
determinant of Frobenius on the frame is the absolute norm `Nw` — was
merged onto the assembly of that leaf on 2026-07-26 as a single opaque
sorried `have`. It is cut here into five statements, of which exactly
ONE is open and it is the only deep one:

* `det_eq_cyclotomicCharacter_of_tateFrame` (PROVEN 2026-07-27 — the
  determinant of the frame representation IS the `q`-adic cyclotomic
  character, as a character of the whole of `Γ_F`; no exceptional set and
  nothing local appears in ITS statement). Its geometric content was cut
  out on 2026-07-27 along the CHEBOTAREV axis into
  `det_globalFrob_eq_cyclotomicCharacter_of_tateFrame` (PROVEN — the
  same identity at the global Frobenius elements away from a finite set
  of places, which is where the bad places really live), the propagation
  being `det_eq_cyclotomicCharacter_of_globalFrob` (PROVEN, density).
* `det_globalFrob_eq_absNorm_of_tateFrame` (PROVEN later on 2026-07-27 —
  the residue of
  the above after the ARITHMETIC half was stripped off on 2026-07-27:
  `det (τ (Frob_v)) = N v` away from a finite set of places, with the
  cyclotomic character no longer mentioned). The arithmetic half is the
  already-proven `cyclotomicCharacter_adicArithFrob_absNorm` of this
  file; the abelian-variety geometry that remained was cut the same day
  into `exists_tateWeilPairing_of_mult` (the `I`-adic Weil
  pairing on the Tate module, stated frame-free) and
  `det_eq_cyclotomicCharacter_of_tateWeilPairing` (PROVEN — the
  transport of that pairing along the frame).  LABEL CORRECTION
  (2026-07-27, later the same day): the pairing node is no longer a
  SORRY NODE — it was cut again along the LIMIT into
  `exists_tateWeilSystem_of_mult` (DECOMPOSED 2026-07-27 into five leaves
  — the levelwise system of pairings on `A[I^k]`, i.e. dual +
  polarization + trace duality) and
  `exists_tateWeilPairing_of_tateWeilSystem` (PROVEN — the passage to the
  limit).  So the FIVE LEAVES of the levelwise-system cut are what the
  determinant clause still rests on.  The INTEGRAL-MODEL route
  described below is the OTHER axis and was not the one taken — see its docstring for the
  route audit and for what a successor must NOT do.
* `exists_weilPairing_of_tateFrame` (PROVEN 2026-07-26 over the leaf
  above): the frame carries an alternating `O`-bilinear form with unit
  discriminant on which `Γ_F` acts through the cyclotomic character.
  **The two are EQUIVALENT** — see the FORMAL-CONTENT AUDIT in its
  docstring. Until 2026-07-26 the roles were the other way round and
  the pairing was believed to be "the whole geometric input"; on a
  FRAMED (hence free rank-two) module the pairing is free, being the
  `2 × 2` determinant `stdAlternatingBilin`, and the entire content is
  the determinant identity. The leaf is now stated where the content
  is.
* `bilin_alternating_apply_det` (PROVEN here — pure linear algebra):
  an endomorphism of a free rank-two module acts on an alternating
  bilinear form by its determinant. This is the "determinant is the
  action on `∧²`" step, discharged once and for all; its all-arguments
  form is `bilin_alternating_apply_det_apply`.
* `cyclotomicCharacter_adicArithFrob_absNorm` (PROVEN here): at a place
  `w ∤ q` of `F` the `q`-adic cyclotomic character of `Γ_ℚ` takes the
  value `Nw` on the global image of the arithmetic Frobenius at `w`.
  Pure algebraic number theory, no geometry and no representation.
* `exists_finset_forall_natCast_notMem` (PROVEN here): the places of
  `F` above `q` are finite in number — this is the exceptional set
  `bad`, and it is the only reason one is needed.

Why the split is the right one. `det τ = χ_cyc` is an identity of
CHARACTERS, so it is insensitive to ramification and to the choice of
Frobenius lift; the exceptional set is an artefact of evaluating
`χ_cyc` at a Frobenius, where the value `Nw` is available only away
from `q` (at `w ∣ q` the character is ramified and no Frobenius lift
has a well-defined cyclotomic value at all). Keeping the two apart
means the geometric leaf carries no finite-set bookkeeping and the
arithmetic lemma carries no abelian varieties. -/

/-- **Only finitely many places of a number field lie above a rational
prime** (PROVEN): the places `w` with `q ∈ w` are exactly the height-one
primes dividing `(q)`, which is a nonzero ideal because `𝒪_F` has
characteristic zero, and only finitely many primes divide a nonzero
ideal of a Dedekind domain (`Ideal.finite_factors`).

This is the exceptional set `bad` of the determinant clause of
`exists_tateFrame_of_levelStructure`. It is stated in the "there is a
`Finset` outside which the property holds" shape that the clause needs,
rather than as a `Set.Finite`, so that the consumer never has to name
the set — and for a general nonzero `n`, not just for the prime `q` it
is used at, so that it is literally the same statement as the
downstream `exists_finset_forall_natCast_notMem_asIdeal` of
`Modularity/KhareWintenberger.lean` and that copy can be deleted in
favour of this one. -/
theorem exists_finset_forall_natCast_notMem {F : Type u} [Field F] [NumberField F]
    (n : ℕ) (hn : n ≠ 0) :
    ∃ bad : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)),
      ∀ w ∉ bad, (n : NumberField.RingOfIntegers F) ∉ w.asIdeal := by
  classical
  have hspan : (Ideal.span {(n : NumberField.RingOfIntegers F)}) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.mpr hn
  have hfin := Ideal.finite_factors (R := NumberField.RingOfIntegers F) hspan
  refine ⟨hfin.toFinset, fun w hw hmem => hw ?_⟩
  rw [Set.Finite.mem_toFinset]
  exact Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem))

set_option backward.isDefEq.respectTransparency false in
/-- **The arithmetic Frobenius at a place `w ∤ ℓ` of a number field `F`
raises `ℓ`-power roots of unity to the `Nw`-th power** (PROVEN): for a
root of unity `t` of `ℓ`-power order in `ℚᵃˡᵍ`, the image in `Γ_ℚ` of
the arithmetic Frobenius at `w` — pushed down the tower
`Γ_{F_w} → Γ_F → Γ_ℚ` — sends `t` to `t ^ Nw`.

The Frobenius specification at `w` is read in `F_wᵃˡᵍ`, where the
exponent is the residue cardinality — `Nw` by
`IsDedekindDomain.HeightOneSpectrum.natCard_under_maximalIdeal`
(`CompletionTransport.lean`) and `Ideal.absNorm_apply` — and then
descends TWO steps, each by `Field.absoluteGaloisGroup.lift_map`
against injectivity of `AlgebraicClosure.map`. The hypothesis `hwℓ`
enters exactly once and essentially: it makes `ℓⁿ` a unit in the
completed integers at `w`, the side condition of
`AlgHom.IsArithFrobAt.apply_of_pow_eq_one`.

PROVENANCE (2026-07-26): this proof is the one written for
`adicArithFrob_rootsOfUnity_pow_base` in `Modularity/KhareWintenberger.lean`,
which is DOWNSTREAM of this module and therefore unusable here. It is
reproduced rather than re-derived, and the intended cleanup is the
reverse direction: `KhareWintenberger.lean` imports this module, so its
copy can simply be deleted in favour of this one. -/
theorem adicArithFrob_rootsOfUnity_pow_absNorm
    {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (F : Type u) [Field F] [NumberField F]
    (w : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (hwℓ : (ℓ : NumberField.RingOfIntegers F) ∉ w.asIdeal) (n : ℕ) :
    ∀ t ∈ rootsOfUnity (ℓ ^ n) (AlgebraicClosure ℚ),
      ((Field.absoluteGaloisGroup.map (algebraMap ℚ F)
        (Field.absoluteGaloisGroup.map
          (algebraMap F (HeightOneSpectrum.adicCompletion F w))
          (Field.AbsoluteGaloisGroup.adicArithFrob w))).toRingEquiv) t =
        t ^ ((Ideal.absNorm w.asIdeal : ZMod (ℓ ^ n)).val) := by
  intro t ht
  classical
  set g : ℚ →+* F := algebraMap ℚ F with hgdef
  set h : F →+* HeightOneSpectrum.adicCompletion F w :=
    algebraMap F (HeightOneSpectrum.adicCompletion F w) with hhdef
  -- the residue cardinality of the `IsArithFrobAt` specification at `w` is `Nw`
  have hcard : Nat.card (↥(w.adicCompletionIntegers F) ⧸
      (IsLocalRing.maximalIdeal (IntegralClosure ↥(w.adicCompletionIntegers F)
        (AlgebraicClosure (w.adicCompletion F)))).under ↥(w.adicCompletionIntegers F)) =
      Ideal.absNorm w.asIdeal := by
    rw [IsDedekindDomain.HeightOneSpectrum.natCard_under_maximalIdeal w,
      Ideal.absNorm_apply, Submodule.cardQuot_apply]
  -- the root of unity and its images down the tower `ℚᵃˡᵍ → Fᵃˡᵍ → F_wᵃˡᵍ`
  have htL : ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ (ℓ ^ n) = 1 := by
    have h1 := (mem_rootsOfUnity _ _).mp ht
    calc ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ (ℓ ^ n)
        = ((t ^ (ℓ ^ n) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) := by
          push_cast; rfl
      _ = 1 := by rw [h1]; rfl
  set u : AlgebraicClosure F :=
    AlgebraicClosure.map g ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) with hudef
  have hupow : u ^ (ℓ ^ n) = 1 := by rw [hudef, ← map_pow, htL, map_one]
  set ζ : AlgebraicClosure (HeightOneSpectrum.adicCompletion F w) :=
    AlgebraicClosure.map h u with hζdef
  have hζpow : ζ ^ (ℓ ^ n) = 1 := by rw [hζdef, ← map_pow, hupow, map_one]
  -- `ζ` is integral over the completed integers (it kills `X^{ℓⁿ} - 1`)
  have hint : IsIntegral (w.adicCompletionIntegers F) ζ := by
    refine ⟨Polynomial.X ^ (ℓ ^ n) - 1, ?_, ?_⟩
    · have := Polynomial.monic_X_pow_sub_C
        (R := w.adicCompletionIntegers F) (1 : _) (n := ℓ ^ n)
        (pow_ne_zero _ hℓ.out.pos.ne')
      simpa [Polynomial.C_1] using this
    · simp [Polynomial.eval₂_sub, hζpow]
  set ζ' : IntegralClosure (w.adicCompletionIntegers F)
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion F w)) := ⟨ζ, hint⟩ with hζ'def
  have hζ'pow : ζ' ^ (ℓ ^ n) = 1 := by
    apply Subtype.ext
    push_cast [hζ'def]
    exact hζpow
  -- `ℓ` is a unit at `w` (`w ∤ ℓ`), so `ℓⁿ` avoids the maximal ideal upstairs
  have hpnotin : ((ℓ : ℕ) ^ n : IntegralClosure (w.adicCompletionIntegers F)
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion F w))) ∉
      IsLocalRing.maximalIdeal _ := by
    have hunit : IsUnit ((ℓ : ℕ) : w.adicCompletionIntegers F) := by
      by_contra hnu
      refine hwℓ ?_
      have hover : w.asIdeal =
          (HeightOneSpectrum.completionIdeal F w).under
            (NumberField.RingOfIntegers F) := Ideal.LiesOver.over
      rw [hover, Ideal.under_def, Ideal.mem_comap]
      show algebraMap (NumberField.RingOfIntegers F) (w.adicCompletionIntegers F)
        ((ℓ : ℕ) : NumberField.RingOfIntegers F) ∈ _
      rw [map_natCast]
      exact (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
    have hunitIC : IsUnit (((ℓ : ℕ) ^ n) : IntegralClosure (w.adicCompletionIntegers F)
        (AlgebraicClosure (HeightOneSpectrum.adicCompletion F w))) := by
      have h1 := hunit.map (algebraMap (w.adicCompletionIntegers F)
        (IntegralClosure (w.adicCompletionIntegers F)
          (AlgebraicClosure (HeightOneSpectrum.adicCompletion F w))))
      rw [map_natCast] at h1
      exact h1.pow n
    intro hmem
    exact ((IsLocalRing.mem_maximalIdeal _).mp hmem) hunitIC
  -- the Frobenius specification at `w`, read in `F_wᵃˡᵍ`
  have hfrob := AlgHom.IsArithFrobAt.apply_of_pow_eq_one
    (Field.AbsoluteGaloisGroup.isArithFrobAt_adicArithFrob (v := w))
    hζ'pow (by exact_mod_cast hpnotin)
  rw [hcard] at hfrob
  have hfrobK : Field.AbsoluteGaloisGroup.adicArithFrob w ζ =
      ζ ^ Ideal.absNorm w.asIdeal := by
    have h1 := hfrob
    rw [MulSemiringAction.toAlgHom_apply] at h1
    have h2 := congrArg Subtype.val h1
    rw [IntegralClosure.coe_smul] at h2
    have h3 : ((⟨ζ, hint⟩ : IntegralClosure _ _) ^ Ideal.absNorm w.asIdeal).1 =
        ζ ^ Ideal.absNorm w.asIdeal := SubmonoidClass.coe_pow _ _
    simpa [hζ'def, AlgEquiv.smul_def] using h2.trans h3
  -- descend one step: the value at `u ∈ Fᵃˡᵍ` of the image in `Γ F`
  have hstepF : (Field.absoluteGaloisGroup.map h
      (Field.AbsoluteGaloisGroup.adicArithFrob w)) u = u ^ Ideal.absNorm w.asIdeal := by
    apply (AlgebraicClosure.map h).injective
    rw [Field.absoluteGaloisGroup.lift_map h
      (Field.AbsoluteGaloisGroup.adicArithFrob w) u, map_pow]
    exact hfrobK
  -- descend the second step: the value at `t ∈ ℚᵃˡᵍ` of the image in `Γ ℚ`
  have hmain : (Field.absoluteGaloisGroup.map g
      (Field.absoluteGaloisGroup.map h (Field.AbsoluteGaloisGroup.adicArithFrob w)))
      ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
      ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ Ideal.absNorm w.asIdeal := by
    apply (AlgebraicClosure.map g).injective
    rw [Field.absoluteGaloisGroup.lift_map g
      (Field.absoluteGaloisGroup.map h (Field.AbsoluteGaloisGroup.adicArithFrob w))
      ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ), map_pow]
    exact hstepF
  show (Field.absoluteGaloisGroup.map g
      (Field.absoluteGaloisGroup.map h (Field.AbsoluteGaloisGroup.adicArithFrob w)))
      ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) = _
  rw [hmain]
  -- the exponent-mod juggle: `t^Nw = t^(Nw mod ℓⁿ)` since `t^{ℓⁿ} = 1`
  haveI : NeZero (ℓ ^ n) := ⟨pow_ne_zero _ hℓ.out.pos.ne'⟩
  have hval : ((Ideal.absNorm w.asIdeal : ZMod (ℓ ^ n))).val =
      Ideal.absNorm w.asIdeal % ℓ ^ n := ZMod.val_natCast _ _
  conv_lhs => rw [show Ideal.absNorm w.asIdeal =
    ℓ ^ n * (Ideal.absNorm w.asIdeal / ℓ ^ n) + Ideal.absNorm w.asIdeal % ℓ ^ n from
    (Nat.div_add_mod _ (ℓ ^ n)).symm]
  rw [pow_add, pow_mul, htL, one_pow, one_mul, hval]

/-- **The `ℓ`-adic cyclotomic character at a Frobenius of the base `F`**
(PROVEN — pure algebraic number theory, NO geometric or automorphic
content): at a place `w` of a number field `F` not lying over `ℓ`, the
`ℓ`-adic cyclotomic character of `Γ_ℚ` takes the value `Nw` on the
global image of the arithmetic Frobenius at `w`.

Classically this is the unramifiedness of the cyclotomic character away
from `ℓ` together with `Frob_w(ζ) = ζ^{Nw}` for roots of unity of
`ℓ`-power order (Serre, *Abelian ℓ-adic Representations*, I.1;
Neukirch IV): `PadicInt.ext_of_toZModPow` reduces the identity to every
level `ℓⁿ`, where `cyclotomicCharacter.toZModPow` and
`modularCyclotomicCharacter.unique` identify the value with the exponent
of the Frobenius action on `μ_{ℓⁿ}`, which is the lemma above.

PROVENANCE: as for `adicArithFrob_rootsOfUnity_pow_absNorm` — the same
statement is proven as `cyclotomicCharacter_adicArithFrob_base_eq_absNorm`
in the DOWNSTREAM `Modularity/KhareWintenberger.lean`, and the intended
cleanup is to delete that copy in favour of this one. -/
theorem cyclotomicCharacter_adicArithFrob_absNorm
    {ℓ : ℕ} [Fact ℓ.Prime] (F : Type u) [Field F] [NumberField F]
    (w : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (hwℓ : (ℓ : NumberField.RingOfIntegers F) ∉ w.asIdeal) :
    ((cyclotomicCharacter (AlgebraicClosure ℚ) ℓ
      ((Field.absoluteGaloisGroup.map (algebraMap ℚ F)
        (Field.absoluteGaloisGroup.map
          (algebraMap F (HeightOneSpectrum.adicCompletion F w))
          (Field.AbsoluteGaloisGroup.adicArithFrob w))).toRingEquiv) :
        ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = (Ideal.absNorm w.asIdeal : ℤ_[ℓ]) := by
  rw [← PadicInt.ext_of_toZModPow]
  intro n
  rw [map_natCast, cyclotomicCharacter.toZModPow]
  exact (modularCyclotomicCharacter.unique
    (hn := HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) (ℓ ^ n))
    _ _ (adicArithFrob_rootsOfUnity_pow_absNorm F w hwℓ n)).symm

/-- **An endomorphism of a free rank-two module acts on an alternating
bilinear form by its determinant** (PROVEN — pure linear algebra, no
hypothesis on the base ring beyond commutativity).

For an alternating `R`-bilinear form `E` on `R²` and `M : End_R(R²)`,

  `E (M e₀) (M e₁) = det M · E e₀ e₁`.

This is the second-exterior-power step of the determinant clause: an
alternating form on a free rank-two module is the same thing as a linear
functional on `∧²`, and the action of `M` on `∧²` is multiplication by
`det M`. Written in coordinates rather than through `ExteriorAlgebra`,
because both sides are then literally `Matrix.det_fin_two` and no
identification of `∧²(R²)` with `R` has to be carried.

Note that `E` is only asked to be ALTERNATING (`E u u = 0`); skew
symmetry is derived, and nondegeneracy is not used at all — the identity
holds for the zero form too. Nondegeneracy is what the CONSUMER needs,
and it appears there as `IsUnit (E e₀ e₁)`. -/
theorem bilin_alternating_apply_det {R : Type*} [CommRing R]
    (E : (Fin 2 → R) →ₗ[R] (Fin 2 → R) →ₗ[R] R)
    (halt : ∀ u, E u u = 0) (M : Module.End R (Fin 2 → R)) :
    E (M (Pi.single 0 1)) (M (Pi.single 1 1)) =
      LinearMap.det M * E (Pi.single 0 1) (Pi.single 1 1) := by
  classical
  set b : Module.Basis (Fin 2) R (Fin 2 → R) := Pi.basisFun R (Fin 2) with hb
  have hb0 : b 0 = Pi.single (0 : Fin 2) (1 : R) := by rw [hb, Pi.basisFun_apply]
  have hb1 : b 1 = Pi.single (1 : Fin 2) (1 : R) := by rw [hb, Pi.basisFun_apply]
  -- skew symmetry of an alternating form
  have hskew : ∀ x y : Fin 2 → R, E x y = - E y x := by
    intro x y
    have h := halt (x + y)
    simp only [map_add, LinearMap.add_apply, halt x, halt y, zero_add, add_zero] at h
    exact eq_neg_of_add_eq_zero_left ((add_comm _ _).trans h)
  -- coordinates in the standard basis
  have hdecomp : ∀ w : Fin 2 → R, w = w 0 • b 0 + w 1 • b 1 := by
    intro w
    funext i
    fin_cases i <;> simp [hb, Pi.basisFun_apply]
  -- an alternating form is determined by its value on the standard basis
  have key : ∀ u w : Fin 2 → R,
      E u w = (u 0 * w 1 - u 1 * w 0) * E (b 0) (b 1) := by
    intro u w
    conv_lhs => rw [hdecomp u, hdecomp w]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [halt (b 0), halt (b 1), hskew (b 1) (b 0)]
    ring
  -- the determinant in the same coordinates
  have hdetM : LinearMap.det M =
      (M (b 0)) 0 * (M (b 1)) 1 - (M (b 0)) 1 * (M (b 1)) 0 := by
    have h := Module.Basis.det_comp b M (⇑b)
    rw [Module.Basis.det_self, mul_one] at h
    rw [← h, hb, Pi.basisFun_det_apply, Matrix.det_fin_two]
    simp
  rw [← hb0, ← hb1, key (M (b 0)) (M (b 1)), hdetM]

/-- **The standard alternating form on a free rank-two module**
(PROVEN — the `2 × 2` determinant, read as an `R`-bilinear form
`E₀ u v = u₀v₁ − u₁v₀`).

Every alternating `R`-bilinear form on `R²` is an `R`-multiple of this
one — that is the `key` step inside `bilin_alternating_apply_det` — so
`stdAlternatingBilin` is the universal example, and the one with unit
discriminant `E₀ e₀ e₁ = 1`. It is what the Weil-pairing statement of
this section is discharged by; see the FORMAL-CONTENT AUDIT in
`exists_weilPairing_of_tateFrame`. -/
def stdAlternatingBilin (R : Type*) [CommRing R] :
    (Fin 2 → R) →ₗ[R] (Fin 2 → R) →ₗ[R] R :=
  LinearMap.mk₂ R (fun u v : Fin 2 → R => u 0 * v 1 - u 1 * v 0)
    (fun _ _ _ => by simp only [Pi.add_apply]; ring)
    (fun _ _ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun _ _ _ => by simp only [Pi.add_apply]; ring)
    (fun _ _ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

@[simp] lemma stdAlternatingBilin_apply {R : Type*} [CommRing R] (u v : Fin 2 → R) :
    stdAlternatingBilin R u v = u 0 * v 1 - u 1 * v 0 := rfl

/-- The standard form is alternating. -/
lemma stdAlternatingBilin_self {R : Type*} [CommRing R] (u : Fin 2 → R) :
    stdAlternatingBilin R u u = 0 := by
  simp only [stdAlternatingBilin_apply]; ring

/-- The standard form has discriminant `1` on the standard basis: this is
the perfectness (`IsUnit`) clause of the Weil-pairing statement. -/
lemma stdAlternatingBilin_single {R : Type*} [CommRing R] :
    stdAlternatingBilin R (Pi.single 0 1) (Pi.single 1 1) = 1 := by
  simp

/-- **An endomorphism of a free rank-two module acts on an alternating
bilinear form by its determinant, at EVERY pair of arguments** (PROVEN
over `bilin_alternating_apply_det` — pure linear algebra).

`bilin_alternating_apply_det` states `E (M e₀) (M e₁) = det M · E e₀ e₁`
at the standard basis pair. Because an alternating form on a free
rank-two module is determined by that single value, the identity
propagates to all arguments:

  `E (M u) (M v) = det M · E u v`.

This is the shape a `Γ_F`-equivariance statement needs, since such a
statement quantifies over all `u`, `v` and not merely over a basis. -/
theorem bilin_alternating_apply_det_apply {R : Type*} [CommRing R]
    (E : (Fin 2 → R) →ₗ[R] (Fin 2 → R) →ₗ[R] R)
    (halt : ∀ u, E u u = 0) (M : Module.End R (Fin 2 → R)) (u v : Fin 2 → R) :
    E (M u) (M v) = LinearMap.det M * E u v := by
  classical
  -- skew symmetry of an alternating form
  have hskew : ∀ x y : Fin 2 → R, E x y = - E y x := by
    intro x y
    have h := halt (x + y)
    simp only [map_add, LinearMap.add_apply, halt x, halt y, zero_add, add_zero] at h
    exact eq_neg_of_add_eq_zero_left ((add_comm _ _).trans h)
  -- coordinates in the standard basis
  have hdecomp : ∀ w : Fin 2 → R,
      w = w 0 • Pi.single (0 : Fin 2) (1 : R) + w 1 • Pi.single (1 : Fin 2) (1 : R) := by
    intro w
    funext i
    fin_cases i <;> simp
  -- an alternating form is determined by its value on the standard basis
  have key : ∀ x y : Fin 2 → R,
      E x y = (x 0 * y 1 - x 1 * y 0) *
        E (Pi.single (0 : Fin 2) (1 : R)) (Pi.single (1 : Fin 2) (1 : R)) := by
    intro x y
    conv_lhs => rw [hdecomp x, hdecomp y]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [halt (Pi.single (0 : Fin 2) (1 : R)), halt (Pi.single (1 : Fin 2) (1 : R)),
      hskew (Pi.single (1 : Fin 2) (1 : R)) (Pi.single (0 : Fin 2) (1 : R))]
    ring
  -- the image of the standard basis under `M`
  have hMu : M u = u 0 • M (Pi.single (0 : Fin 2) (1 : R)) +
      u 1 • M (Pi.single (1 : Fin 2) (1 : R)) := by
    conv_lhs => rw [hdecomp u]
    rw [map_add, map_smul, map_smul]
  have hMv : M v = v 0 • M (Pi.single (0 : Fin 2) (1 : R)) +
      v 1 • M (Pi.single (1 : Fin 2) (1 : R)) := by
    conv_lhs => rw [hdecomp v]
    rw [map_add, map_smul, map_smul]
  rw [hMu, hMv]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [halt (M (Pi.single (0 : Fin 2) (1 : R))), halt (M (Pi.single (1 : Fin 2) (1 : R))),
    hskew (M (Pi.single (1 : Fin 2) (1 : R))) (M (Pi.single (0 : Fin 2) (1 : R))),
    bilin_alternating_apply_det E halt M, key u v]
  ring

/-! ### Chebotarev density: from the Frobenius determinants to all of `Γ_F`

The determinant identity below is NOT proven from a characteristic-zero
Weil pairing.  It is CUT along the axis the elliptic analogue in this
tree already uses (`EllipticCurve/WeilPairing.lean`'s
`det_galoisRep_eq_cyclotomic`, and, in the exact continuity/density
spelling copied here, `Modularity/Interface.lean`'s
`det_eq_cyclotomicCharacter_of_charFrob_coeff_zero`): the geometry is
asked for ONLY at the global Frobenius elements away from a finite set of
places, and the value at a general `σ ∈ Γ_F` is then forced, because both
sides are continuous class functions and the Frobenius conjugacy classes
are DENSE (`GaloisRepresentation.dense_conjClasses_globalFrob`).

This is a genuine weakening, not a repackaging: the remaining leaf
constrains `τ` only at Frobenius elements, and everything below it here
is PROVEN.

A second narrowing was made on the same day, along the ARITHMETIC axis:
at a Frobenius BOTH sides equal the absolute norm `N v`, and the right
side is already proven to (`cyclotomicCharacter_adicArithFrob_absNorm`,
above).  So the cyclotomic character is discharged entirely, and what
remained was `det_globalFrob_eq_absNorm_of_tateFrame`,
`det (τ (Frob_v)) = N v`.

THIRD CUT, later on 2026-07-27: that declaration is PROVEN too.  It was
split along the PAIRING axis into `exists_tateWeilPairing_of_mult` (the
GEOMETRY — an `I`-adic Weil pairing on `TatePt`, stated WITHOUT the
frame, which is what stops the cut from collapsing) and
`det_eq_cyclotomicCharacter_of_tateWeilPairing` (the TRANSPORT along the
frame).  The transport is PROVEN, so `exists_tateWeilPairing_of_mult` —
pure abelian-variety geometry, with no frame and no cyclotomic character
in its own burden — carried the whole residue.

FOURTH CUT, later still on 2026-07-27: that declaration is PROVEN too,
along the LIMIT axis.  `exists_tateWeilSystem_of_mult` (DECOMPOSED
2026-07-27 into five leaves) is the levelwise system of `𝒪_D/I^k`-valued
Weil pairings on the finite torsion `A[I^k]` — dual, polarization, trace
duality — and `exists_tateWeilPairing_of_tateWeilSystem` (PROVEN) passes
it to the limit.  The section's remaining sorries are the five leaves of
the levelwise-system cut: `exists_qAdicWeilSystem_of_mult`,
`exists_preimage_act_of_mult`, `exists_traceDualFunctional_of_adicPin`,
`exists_cyclotomicLog` and
`exists_tateWeilSystem_of_qAdicWeilSystem`. -/

/-- **A free module carrying the module topology over a `T2Space` ring is
a `T2Space`** (PROVEN; vendored in argument from the reference project
`~/cs/FLT`'s `FLT/Mathlib/Topology/Algebra/Module/ModuleTopology.lean`,
re-checked against our pin).

`{0}` is the preimage of the closed set `{0}` under the continuous
injective linear map `M → (ι → R)` given by the coordinates of a basis,
and a topological additive group with `{0}` closed is Hausdorff.

This is what supplies `T2Space O` for the coefficient ring `O` of a Tate
frame: `exists_adicCoefficientRing` produces `O` together with
`Module.Free ℤ_[q] O` and `IsModuleTopology ℤ_[q] O`, and `ℤ_[q]` is a
metric space.  Without it the agreement locus of the two characters below
is not closed and the density argument does not start. -/
theorem t2Space_of_free_isModuleTopology (R : Type*) {M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Free R M]
    [TopologicalSpace R] [TopologicalSpace M] [T2Space R] [IsTopologicalRing R]
    [IsModuleTopology R M] : T2Space M := by
  have := IsModuleTopology.topologicalAddGroup R M
  rw [IsTopologicalAddGroup.t2Space_iff_zero_closed]
  let f := (Module.Free.chooseBasis R M).repr.toLinearMap
  let g : (Module.Free.ChooseBasisIndex R M →₀ R) →ₗ[R]
      (Module.Free.ChooseBasisIndex R M → R) :=
    { __ := Finsupp.coeFnAddHom
      map_smul' := fun _ _ => rfl }
  suffices hpre : (g.comp f) ⁻¹' {0} = {0} by
    rw [← hpre]
    exact IsClosed.preimage
      (IsModuleTopology.continuous_of_linearMap (g.comp f)) isClosed_singleton
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro hx
    have h0 : (Module.Free.chooseBasis R M).repr x = 0 :=
      Finsupp.ext fun i => congrFun hx i
    have := congrArg (Module.Free.chooseBasis R M).repr.symm h0
    simpa using this
  · rintro rfl
    simp [g, f]

/-- **Two continuous characters of `Γ K` that agree at almost every global
Frobenius agree everywhere** (PROVEN, Chebotarev density in abstract
form).

The agreement locus is CLOSED because both sides are continuous into the
Hausdorff ring `O`; it is CONJUGATION-INVARIANT because a multiplicative
`O`-valued function on a group is a class function when `O` is
commutative (`f (g x g⁻¹) = f x` after cancelling `f g · f g⁻¹ = 1`); and
it contains the union of the Frobenius conjugacy classes away from `S`,
which is DENSE by `GaloisRepresentation.dense_conjClasses_globalFrob`.
Hence it is everything.

Stated for bare multiplicative FUNCTIONS rather than bundled monoid homs,
so that a consumer need not build a `MonoidHom` out of a composite of
coercions in order to apply it. -/
theorem eq_of_eq_globalFrob_of_continuous {K : Type u} [Field K] [NumberField K]
    {O : Type*} [CommRing O] [TopologicalSpace O] [T2Space O]
    (f₁ f₂ : Field.absoluteGaloisGroup K → O)
    (hm₁ : ∀ a b, f₁ (a * b) = f₁ a * f₁ b) (ho₁ : f₁ 1 = 1)
    (hm₂ : ∀ a b, f₂ (a * b) = f₂ a * f₂ b) (ho₂ : f₂ 1 = 1)
    (hc₁ : Continuous f₁) (hc₂ : Continuous f₂)
    (Sbad : Finset (HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (h : ∀ v ∉ Sbad, f₁ (GaloisRepresentation.globalFrob v) =
      f₂ (GaloisRepresentation.globalFrob v))
    (σ : Field.absoluteGaloisGroup K) : f₁ σ = f₂ σ := by
  classical
  have hconj : ∀ (f : Field.absoluteGaloisGroup K → O)
      (_ : ∀ a b, f (a * b) = f a * f b) (_ : f 1 = 1)
      (g x : Field.absoluteGaloisGroup K), f (g * x * g⁻¹) = f x := by
    intro f hm ho g x
    have hgg : f g * f g⁻¹ = 1 := by rw [← hm, mul_inv_cancel, ho]
    calc f (g * x * g⁻¹) = f g * f x * f g⁻¹ := by rw [hm, hm]
      _ = f x * (f g * f g⁻¹) := by ring
      _ = f x := by rw [hgg, mul_one]
  have hclosed : IsClosed {x : Field.absoluteGaloisGroup K | f₁ x = f₂ x} :=
    isClosed_eq hc₁ hc₂
  have hsub : {x : Field.absoluteGaloisGroup K |
      ∃ v : HeightOneSpectrum (NumberField.RingOfIntegers K), v ∉ Sbad ∧
        ∃ g, x = g * GaloisRepresentation.globalFrob v * g⁻¹} ⊆
      {x : Field.absoluteGaloisGroup K | f₁ x = f₂ x} := by
    rintro x ⟨v, hv, g, rfl⟩
    simp only [Set.mem_setOf_eq, hconj f₁ hm₁ ho₁, hconj f₂ hm₂ ho₂]
    exact h v hv
  have hσ : σ ∈ closure {x : Field.absoluteGaloisGroup K |
      ∃ v : HeightOneSpectrum (NumberField.RingOfIntegers K), v ∉ Sbad ∧
        ∃ g, x = g * GaloisRepresentation.globalFrob v * g⁻¹} := by
    rw [(GaloisRepresentation.dense_conjClasses_globalFrob (K := K) Sbad).closure_eq]
    trivial
  exact closure_minimal hsub hclosed hσ

/-- **The determinant of a framed representation is the cyclotomic
character as soon as it is so at almost every global Frobenius** (PROVEN).

The specialization of `eq_of_eq_globalFrob_of_continuous` to the two
characters of the determinant clause.  Continuity of the left side is
`GaloisRep.det`, which is a `ContinuousMonoidHom` by
`IsModuleTopology.continuous_det`; continuity of the right side is
mathlib's `cyclotomicCharacter.continuous` pushed along the continuous
`Field.absoluteGaloisGroup.map` and the continuous `algebraMap ℤ_[q] O`
(continuous because `O` carries the `ℤ_[q]`-module topology).

Note where the topological pin is used: `Module.Free ℤ_[q] O` and
`IsModuleTopology ℤ_[q] O` are needed ONLY to know that `O` is Hausdorff,
which is what makes the agreement locus closed.  Both are supplied by
`exists_adicCoefficientRing`, so no consumer has to prove anything new. -/
theorem det_eq_cyclotomicCharacter_of_globalFrob
    {F : Type u} [Field F] [NumberField F]
    (q : ℕ) [Fact q.Prime]
    (O : Type u) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [Algebra ℤ_[q] O] [Module.Free ℤ_[q] O] [IsModuleTopology ℤ_[q] O]
    (τ : GaloisRep F O (Fin 2 → O))
    (Sbad : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (h : ∀ v ∉ Sbad,
      LinearMap.det (τ (GaloisRepresentation.globalFrob v)) =
        algebraMap ℤ_[q] O
          ((cyclotomicCharacter (AlgebraicClosure ℚ) q
            ((Field.absoluteGaloisGroup.map (algebraMap ℚ F)
              (GaloisRepresentation.globalFrob v)).toRingEquiv) : ℤ_[q]ˣ) : ℤ_[q]))
    (σ : Field.absoluteGaloisGroup F) :
    LinearMap.det (τ σ) =
      algebraMap ℤ_[q] O
        ((cyclotomicCharacter (AlgebraicClosure ℚ) q
          ((Field.absoluteGaloisGroup.map (algebraMap ℚ F) σ).toRingEquiv) :
            ℤ_[q]ˣ) : ℤ_[q]) := by
  haveI : T2Space O := t2Space_of_free_isModuleTopology ℤ_[q]
  refine eq_of_eq_globalFrob_of_continuous
    (fun γ => LinearMap.det (τ γ))
    (fun γ => algebraMap ℤ_[q] O
      ((cyclotomicCharacter (AlgebraicClosure ℚ) q
        ((Field.absoluteGaloisGroup.map (algebraMap ℚ F) γ).toRingEquiv) :
          ℤ_[q]ˣ) : ℤ_[q]))
    ?_ ?_ ?_ ?_ ?_ ?_ Sbad h σ
  · intro a b
    show τ.det (a * b) = τ.det a * τ.det b
    rw [map_mul]
  · show τ.det 1 = 1
    rw [map_one]
  · intro a b
    have hmul : ∀ x y : Field.absoluteGaloisGroup ℚ,
        (x * y).toRingEquiv = x.toRingEquiv * y.toRingEquiv := fun _ _ => rfl
    rw [map_mul, hmul, map_mul, Units.val_mul, map_mul]
  · have hone : (1 : Field.absoluteGaloisGroup ℚ).toRingEquiv = 1 := rfl
    rw [map_one, hone, map_one, Units.val_one, map_one]
  · exact (ContinuousMonoidHom.continuous_toFun τ.det).congr fun _ => rfl
  · exact ((continuous_algebraMap ℤ_[q] O).comp
      (Units.continuous_val.comp
        ((cyclotomicCharacter.continuous q ℚ (AlgebraicClosure ℚ)).comp
          (Field.absoluteGaloisGroup.map (algebraMap ℚ F)).continuous_toFun))).congr
      fun _ => rfl

/-- **Only finitely many places of `F` contain a given nonzero integer**
(PROVEN — `c ∈ w` says exactly that `w` divides the principal ideal
`(c)`, and a nonzero ideal of a Dedekind domain has finitely many prime
divisors, `Ideal.finite_factors`).

Used by `det_globalFrob_eq_cyclotomicCharacter_of_tateFrame` below to
enlarge the geometric leaf's exceptional set by the fibre over `q`,
which is where the cyclotomic character is ramified and where the
identification of `χ_cyc(Frob_v)` with `N v` fails. -/
theorem finite_places_natCast_mem_asIdeal (F : Type u) [Field F] [NumberField F]
    (c : NumberField.RingOfIntegers F) (hc : c ≠ 0) :
    {w : HeightOneSpectrum (NumberField.RingOfIntegers F) | c ∈ w.asIdeal}.Finite := by
  have hspan : (Ideal.span {c} : Ideal (NumberField.RingOfIntegers F)) ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using hc
  refine (Ideal.finite_factors hspan).subset fun w hw => ?_
  simpa [Ideal.dvd_span_singleton] using hw

/-! ### The `I`-adic Weil pairing on the Tate module

The cut of `det_globalFrob_eq_absNorm_of_tateFrame` made on 2026-07-27.
See that declaration's docstring for why every PAIRING-SHAPED cut *on the
framed module* collapses, and why this one does not: `IsTateWeilPairing`
is a predicate on the GEOMETRIC Tate module `TatePt m x I π`, and the
leaf that produces it (`exists_tateWeilPairing_of_mult`) does not receive
the frame at all. -/

/-- **The `I`-adic Weil pairing on the Tate module**, as a predicate on a
candidate `O`-valued form `E` on `TatePt m x I π`.

This is the classical statement `∧²_O T_I A ≅ O(1)` written out in the
frame-free vocabulary this file already uses for `TatePt`: since `TatePt`
carries no bundled `AddCommGroup` or `O`-module instance (deliberately —
see its docstring), each structural clause quantifies over Tate points
whose COMPONENTS satisfy the relevant identity, exactly as the frame
hypotheses `hφadd`, `hφj` and `hφequiv` do.

The clauses, in order:

* bi-additivity in each variable;
* alternating (`E t t = 0`);
* `𝒪_D`-bilinearity through `j`: scaling a Tate point by `a ∈ 𝒪_D`
  scales the pairing by `j a`.  This is the real-multiplication content,
  and it is what `[NumberField.IsTotallyReal D]` buys — see the
  FAITHFULNESS note on `det_globalFrob_eq_absNorm_of_tateFrame`;
* `Γ_F`-equivariance with multiplier `χ_cyc` and nothing else: this is
  the whole arithmetic of the pairing;
* CONTINUITY, in the only form available here: `E` is determined modulo
  `(j π)^k` by the level-`k` components of its arguments.  This clause is
  not decoration.  It is what upgrades the `𝒪_D`-bilinearity above to
  `O`-bilinearity after transport along a frame, using `hdense` and
  `hcplt`; without it an `E` that is `𝒪_D`-bilinear but wildly
  discontinuous would satisfy every other clause and the transport in
  `det_eq_cyclotomicCharacter_of_tateWeilPairing` would be false;
* PERFECTNESS, in the weakest form the determinant argument needs: some
  value of `E` is a unit.  On a rank-two module an alternating form is a
  scalar multiple of the determinant form, so a single unit value is
  exactly unimodularity, and it is what makes the multiplier cancellable.

NON-VACUITY.  The constant zero form satisfies every clause but the last;
the last is therefore the one carrying the content, in the same way that
`weil_hom_nondegenerate` carries the content of `PolarizationStruct`. -/
def IsTateWeilPairing {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (q : ℕ) [Fact q.Prime]
    (I : Ideal (NumberField.RingOfIntegers D)) (π : NumberField.RingOfIntegers D)
    {O : Type u} [CommRing O] [Algebra ℤ_[q] O]
    (j : NumberField.RingOfIntegers D →+* O)
    (E : TatePt m x I π → TatePt m x I π → O) : Prop :=
  (∀ t t' t'' s : TatePt m x I π, (∀ n, t''.1 n = ab.add (t.1 n) (t'.1 n)) →
      E t'' s = E t s + E t' s) ∧
  (∀ t s s' s'' : TatePt m x I π, (∀ n, s''.1 n = ab.add (s.1 n) (s'.1 n)) →
      E t s'' = E t s + E t s') ∧
  (∀ t : TatePt m x I π, E t t = 0) ∧
  (∀ (a : NumberField.RingOfIntegers D) (t t' s : TatePt m x I π),
      (∀ n, t'.1 n = m.act a (t.1 n)) → E t' s = j a * E t s) ∧
  (∀ (σ : Field.absoluteGaloisGroup F) (t t' s s' : TatePt m x I π),
      (∀ n, t'.1 n = ab.galSMul x σ (t.1 n)) →
      (∀ n, s'.1 n = ab.galSMul x σ (s.1 n)) →
      E t' s' = algebraMap ℤ_[q] O
        ((cyclotomicCharacter (AlgebraicClosure ℚ) q
          ((Field.absoluteGaloisGroup.map (algebraMap ℚ F) σ).toRingEquiv) : ℤ_[q]ˣ) : ℤ_[q])
        * E t s) ∧
  (∀ (k : ℕ) (t t' s s' : TatePt m x I π), t.1 k = t'.1 k → s.1 k = s'.1 k →
      E t s - E t' s' ∈ Ideal.span {j π} ^ k) ∧
  (∃ t s : TatePt m x I π, IsUnit (E t s))

/-- **A compatible system of level-`k` `I`-adic Weil pairings on the
torsion of the geometric fibre** — the LEVELWISE datum out of which the
pairing of `IsTateWeilPairing` is assembled by passage to the limit.

`e k` is the level-`k` pairing

  `A[I^k] × A[I^k] ⟶ 𝔡_D⁻¹ 𝔠 / I^k ≅ 𝒪_D / I^k`,

written additively and with values in `O` rather than in a quotient: the
target `𝒪_{D,I}/I^k` is `O / (j π)^k` under the pin `hker`, so each clause
is an identity MODULO `Ideal.span {j π} ^ k` between honest elements of
`O`.  Working with congruences in `O` rather than with a family of
quotient rings is what keeps the limit construction below elementary —
mathlib's `IsPrecomplete`/`IsHausdorff` are stated in exactly this
vocabulary.

As with `IsTateWeilPairing`, `e k` is a function on ALL geometric points
and every clause is asserted only for `I^k`-torsion arguments, in the
same style as `DualStruct.weil` in `Modularity/AbelianScheme.lean`; its
value off the torsion is unconstrained and no consumer may rely on it.

The clauses, in order: bi-additivity in each variable, alternating,
`𝒪_D`-bilinearity through `j`, `Γ_F`-equivariance with multiplier
`χ_cyc`, TOWER COMPATIBILITY, and perfectness at level one.

TOWER COMPATIBILITY IS THE ONE CLAUSE THAT IS NOT A LEVELWISE COPY OF
`IsTateWeilPairing`, and its exact shape is what makes the limit exist.
It says, for `y, z ∈ A[I^{k+1}]`,

  `e (k+1) y z ≡ e k (π y) (π z)  (mod (j π)^k)`.

That is the ADDITIVE form of the classical
`e_{q^k}(q y, q z) = e_{q^{k+1}}(y, z)^q` (Silverman *AEC* III.8.1(e)),
because under the identification `μ_{I^{k}} ≅ 𝒪_D/I^k` the transition
`x ↦ x^π` of the inverse system of roots of unity becomes REDUCTION
`𝒪_D/I^{k+1} ↠ 𝒪_D/I^k`.  Two checks worth keeping, since both are easy
to get backwards:

* it is NOT the restriction statement `e (k+1) = e k` on `A[I^k]`.  If it
  were, `𝒪_D`-bilinearity would force `e k (π y) (π z) = π² e k y z`,
  which contradicts it.  The two are consistent precisely because `y, z`
  range over `A[I^{k+1}]`, where the level-`k` bilinearity clause does
  not apply.
* the transition of `TatePt` is `m.act π`, and this clause is stated
  along exactly that transition — which is why the sequence
  `k ↦ e k (t.1 k) (s.1 k)` attached to Tate points `t, s` is Cauchy:
  `t.1 k = m.act π (t.1 (k+1))` by definition of `TatePt`.

WHY THE TARGET MUST BE `(𝒪_D/I^k)(1)` AND NOT `μ_{q^k}`.  This is the
correction recorded on `exists_tateWeilSystem_of_mult` below: a
compatibility axiom on `DualStruct.weil` would relate levels along the
RATIONAL INTEGER `q`, not along `π`, and no such axiom can be written for
the `I`-adic tower before the trace-duality refinement of the target.
Stating the system with `𝒪_D/I^k`-valued (i.e. `O`-valued) pairings is
what makes the tower compatible; that refinement is part of the burden of
the leaf, not a hypothesis of it.

NON-VACUITY.  The constant zero system satisfies every clause but the
last, exactly as for `IsTateWeilPairing`; the perfectness clause at level
one is what carries the content, and it additionally asserts that
`TatePt m x I π` is large enough to see it (it quantifies over Tate
points, not over `A[I]`, so it also encodes surjectivity of the
transition maps `A[I^{k+1}] ↠ A[I^k]`). -/
def IsTateWeilSystem {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (q : ℕ) [Fact q.Prime]
    (I : Ideal (NumberField.RingOfIntegers D)) (π : NumberField.RingOfIntegers D)
    {O : Type u} [CommRing O] [Algebra ℤ_[q] O]
    (j : NumberField.RingOfIntegers D →+* O)
    (e : ℕ → GeomFibrePt f x → GeomFibrePt f x → O) : Prop :=
  (∀ (k : ℕ) (y y' z : GeomFibrePt f x), y ∈ (m.torsion x (I ^ k)).1 →
      y' ∈ (m.torsion x (I ^ k)).1 → z ∈ (m.torsion x (I ^ k)).1 →
      e k (ab.add y y') z - (e k y z + e k y' z) ∈ Ideal.span {j π} ^ k) ∧
  (∀ (k : ℕ) (y z z' : GeomFibrePt f x), y ∈ (m.torsion x (I ^ k)).1 →
      z ∈ (m.torsion x (I ^ k)).1 → z' ∈ (m.torsion x (I ^ k)).1 →
      e k y (ab.add z z') - (e k y z + e k y z') ∈ Ideal.span {j π} ^ k) ∧
  (∀ (k : ℕ) (y : GeomFibrePt f x), y ∈ (m.torsion x (I ^ k)).1 →
      e k y y ∈ Ideal.span {j π} ^ k) ∧
  (∀ (k : ℕ) (a : NumberField.RingOfIntegers D) (y z : GeomFibrePt f x),
      y ∈ (m.torsion x (I ^ k)).1 → z ∈ (m.torsion x (I ^ k)).1 →
      e k (m.act a y) z - j a * e k y z ∈ Ideal.span {j π} ^ k) ∧
  (∀ (k : ℕ) (σ : Field.absoluteGaloisGroup F) (y z : GeomFibrePt f x),
      y ∈ (m.torsion x (I ^ k)).1 → z ∈ (m.torsion x (I ^ k)).1 →
      e k (ab.galSMul x σ y) (ab.galSMul x σ z) -
        algebraMap ℤ_[q] O
          ((cyclotomicCharacter (AlgebraicClosure ℚ) q
            ((Field.absoluteGaloisGroup.map (algebraMap ℚ F) σ).toRingEquiv) : ℤ_[q]ˣ) : ℤ_[q])
          * e k y z ∈ Ideal.span {j π} ^ k) ∧
  (∀ (k : ℕ) (y z : GeomFibrePt f x), y ∈ (m.torsion x (I ^ (k + 1))).1 →
      z ∈ (m.torsion x (I ^ (k + 1))).1 →
      e (k + 1) y z - e k (m.act π y) (m.act π z) ∈ Ideal.span {j π} ^ k) ∧
  (∃ t s : TatePt m x I π, IsUnit (e 1 (t.1 1) (s.1 1)))

/-- **A compatible system of `q`-adic Weil pairings on the torsion of a
geometric fibre** — the CLASSICAL, `μ_{q^N}`-valued datum out of which the
`I`-adic system of `IsTateWeilSystem` is refined by trace duality.

`w N y z` is the value of the `q^N`-Weil pairing attached to a fixed
`𝒪_D`-linear polarization, written as an element of `(F̄)ˣ` rather than of
`rootsOfUnity (q^N) F̄`: the subtype would force a coercion at every use and
a transport across `N` in the tower clause, and the first clause below
(`w N y z ^ q ^ N = 1`) says exactly what the subtype would.  As with
`IsTateWeilSystem`, `w N` is a function on ALL geometric points and each
clause is asserted only for `A[q^N]` arguments; its value off the torsion is
unconstrained and no consumer may rely on it.

The clauses, in order: `q^N`-torsion values, bi-multiplicativity in each
variable, `𝒪_D`-ALTERNATING, `𝒪_D`-adjointness, `Γ_F`-equivariance (the raw
action on `F̄ˣ` — the cyclotomic character enters only through
`exists_cyclotomicLog`), LEVEL COMPATIBILITY ALONG THE INTEGER TOWER, and
perfectness.

TWO CLAUSES ARE NOT THE OBVIOUS ONES AND BOTH ARE LOAD-BEARING.

*`𝒪_D`-alternating* (`w N (m.act a y) y = 1` for every `a`, not merely
`w N y y = 1`).  The weaker form is what `PolarizationStruct.weil_self`
gives, and it is NOT enough: from bi-multiplicativity and adjointness one
gets only `w N (a y) y ^ 2 = 1`, so the induced `𝒪_D`-valued form would be
alternating only up to 2-torsion and the third clause of `IsTateWeilSystem`
would fail at `q = 2`.  Classically the stronger form is immediate, because
the `𝒪_D`-valued form is alternating by construction and `w = ζ^{Tr(δ E)}`;
it is stated here because it does not follow from the weaker one.

*Level compatibility along the INTEGER tower*:

  `w (N+1) y z ^ q = w N (q y) (q z)`   for `y, z ∈ A[q^{N+1}]`.

This is Silverman *AEC* III.8.1(e) (`e_{mn}(P,Q) = e_n(mP,Q)`) read
symmetrically, and it is the classical fact that the `e_{q^N}` are the
reductions of ONE `ℤ_q`-bilinear form on `T_q A`.  **It is along `q`, not
along `π`, and that is not a defect of this statement** — see the
CORRECTION in `exists_tateWeilSystem_of_qAdicWeilSystem` for why no
`π`-indexed compatibility can be written before the trace refinement, and
why the earlier reading of that fact ("no compatibility field can be
written at all") was too strong.

NON-VACUITY.  The constant `1` system satisfies every clause but the last. -/
def IsQAdicWeilSystem {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (q : ℕ)
    (w : ℕ → GeomFibrePt f x → GeomFibrePt f x → (AlgebraicClosure F)ˣ) : Prop :=
  (∀ (N : ℕ) (y z : GeomFibrePt f x), w N y z ^ q ^ N = 1) ∧
  (∀ (N : ℕ) (y y' z : GeomFibrePt f x),
      y ∈ (m.torsion x (Ideal.span {(q : NumberField.RingOfIntegers D) ^ N})).1 →
      y' ∈ (m.torsion x (Ideal.span {(q : NumberField.RingOfIntegers D) ^ N})).1 →
      z ∈ (m.torsion x (Ideal.span {(q : NumberField.RingOfIntegers D) ^ N})).1 →
      w N (ab.add y y') z = w N y z * w N y' z) ∧
  (∀ (N : ℕ) (y z z' : GeomFibrePt f x),
      y ∈ (m.torsion x (Ideal.span {(q : NumberField.RingOfIntegers D) ^ N})).1 →
      z ∈ (m.torsion x (Ideal.span {(q : NumberField.RingOfIntegers D) ^ N})).1 →
      z' ∈ (m.torsion x (Ideal.span {(q : NumberField.RingOfIntegers D) ^ N})).1 →
      w N y (ab.add z z') = w N y z * w N y z') ∧
  (∀ (N : ℕ) (a : NumberField.RingOfIntegers D) (y : GeomFibrePt f x),
      y ∈ (m.torsion x (Ideal.span {(q : NumberField.RingOfIntegers D) ^ N})).1 →
      w N (m.act a y) y = 1) ∧
  (∀ (N : ℕ) (a : NumberField.RingOfIntegers D) (y z : GeomFibrePt f x),
      y ∈ (m.torsion x (Ideal.span {(q : NumberField.RingOfIntegers D) ^ N})).1 →
      z ∈ (m.torsion x (Ideal.span {(q : NumberField.RingOfIntegers D) ^ N})).1 →
      w N (m.act a y) z = w N y (m.act a z)) ∧
  (∀ (N : ℕ) (σ : Field.absoluteGaloisGroup F) (y z : GeomFibrePt f x),
      y ∈ (m.torsion x (Ideal.span {(q : NumberField.RingOfIntegers D) ^ N})).1 →
      z ∈ (m.torsion x (Ideal.span {(q : NumberField.RingOfIntegers D) ^ N})).1 →
      w N (ab.galSMul x σ y) (ab.galSMul x σ z)
        = Units.map
            ((σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F).toAlgHom.toRingHom.toMonoidHom)
            (w N y z)) ∧
  (∀ (N : ℕ) (y z : GeomFibrePt f x),
      y ∈ (m.torsion x (Ideal.span {(q : NumberField.RingOfIntegers D) ^ (N + 1)})).1 →
      z ∈ (m.torsion x (Ideal.span {(q : NumberField.RingOfIntegers D) ^ (N + 1)})).1 →
      w (N + 1) y z ^ q
        = w N (m.act (q : NumberField.RingOfIntegers D) y)
              (m.act (q : NumberField.RingOfIntegers D) z)) ∧
  (∀ (N : ℕ) (y : GeomFibrePt f x),
      y ∈ (m.torsion x (Ideal.span {(q : NumberField.RingOfIntegers D) ^ N})).1 →
      y ≠ ab.zero (specAlgClos F ≫ x) →
      ∃ z : GeomFibrePt f x,
        z ∈ (m.torsion x (Ideal.span {(q : NumberField.RingOfIntegers D) ^ N})).1 ∧
        w N y z ≠ 1)

/-- **A trace-duality functional for the pin `(O, j, π)`** — the
`𝒪_D`-module-theoretic half of the refinement of the `q`-adic Weil pairing
to an `I`-adic one, isolated as a statement of pure algebraic number theory
with no geometry in it.

Under the pin `hcplt`/`hdense`/`hker` the ring `O` is the `I`-adic
completion `𝒪_{D,I}`, a complete discrete valuation ring, so its inverse
different `𝔡_I⁻¹` is PRINCIPAL, say `𝔡_I⁻¹ = (δ)`.  `θ` is
`c ↦ Tr_{D_I/ℚ_q}(δ c)`, and the two substantive clauses say that the
induced pairing

  `𝒪_D/I^k × O/(j π)^k ⟶ ℤ_q/q^k`,   `(b, c) ↦ θ (j b * c)`

is PERFECT: every level-`k` additive functional on `𝒪_D` that kills `I^k`
is represented by some `c` (third clause), and the representing `c` is
unique modulo `(j π)^k` (fourth clause).  That is exactly the definition of
the different, and it is what converts an `𝒪_D`-ADJOINT `ℤ`-valued pairing
into an `𝒪_D`-BILINEAR `𝒪_D`-valued one.

The first two clauses are the ambient linearity of a trace: additivity and
`ℤ_q`-linearity.  Note the functionals `φ` of the third clause are only
required to be additive MODULO `q^k` and to kill `I^k` MODULO `q^k` —
which is what the applications supply, since they arise as
`b ↦ L k (w k (b y) z)` and `L` is itself only additive modulo `q^k`.

WHY BOTH DIRECTIONS ARE STATED even though the two finite groups have the
same order: the development never has the cardinality count in hand, and
`c` is only ever pinned modulo `(j π)^k`, so surjectivity and injectivity
must be available separately.

MATHLIB INGREDIENTS: `Submodule.traceDual`, `FractionalIdeal.dual`,
`differentIdeal`, `Algebra.traceForm_nondegenerate`, together with the
principality of a fractional ideal over a DVR. -/
def IsTraceDualFunctional {D : Type u} [Field D] [NumberField D]
    (q : ℕ) [Fact q.Prime]
    (I : Ideal (NumberField.RingOfIntegers D)) (π : NumberField.RingOfIntegers D)
    {O : Type u} [CommRing O] [Algebra ℤ_[q] O]
    (j : NumberField.RingOfIntegers D →+* O)
    (θ : O → ℤ_[q]) : Prop :=
  (∀ c c' : O, θ (c + c') = θ c + θ c') ∧
  (∀ (r : ℤ_[q]) (c : O), θ (algebraMap ℤ_[q] O r * c) = r * θ c) ∧
  (∀ (k : ℕ) (φ : NumberField.RingOfIntegers D → ℤ_[q]),
      (∀ a b : NumberField.RingOfIntegers D,
        φ (a + b) - (φ a + φ b) ∈ Ideal.span {(q : ℤ_[q])} ^ k) →
      (∀ a ∈ I ^ k, φ a ∈ Ideal.span {(q : ℤ_[q])} ^ k) →
      ∃ c : O, ∀ b : NumberField.RingOfIntegers D,
        φ b - θ (j b * c) ∈ Ideal.span {(q : ℤ_[q])} ^ k) ∧
  (∀ (k : ℕ) (c : O),
      (∀ b : NumberField.RingOfIntegers D, θ (j b * c) ∈ Ideal.span {(q : ℤ_[q])} ^ k) →
      c ∈ Ideal.span {j π} ^ k)

/-- **The geometric fibre of a Hilbert–Blumenthal abelian scheme carries a
compatible system of `q`-adic Weil pairings** (SORRY LEAF — steps 1 and 2 of
the classical route: Grothendieck representability of `Pic⁰`, an
`𝒪_D`-linear polarization, and the Weil pairing it induces; Mumford
*Abelian Varieties* §13, §16, §23, Silverman *AEC* III.8.1).

This is the purely GEOMETRIC input to `exists_tateWeilSystem_of_mult`, and
nothing about `I`, `π` or the pin appears in it: the datum is the classical
`q`-adic Weil pairing attached to a polarization, level by level, together
with the level compatibility that makes those levels the reductions of one
form on `T_q A`.

WHY IT IS STATED AS A BARE FUNCTION AND NOT AS
`∃ d : DualStruct ab m, Nonempty (PolarizationStruct d 𝒩)`.  Two reasons,
the second of them a refutation:

1. `DualStruct` carries NO cross-level axiom, so a `d` and a `p` say
   nothing whatever about how `p.pairing` at level `n` relates to
   `p.pairing` at level `n'`.  A cut that hands a successor `d` and `p` and
   asks for `IsTateWeilSystem` would be handing it hypotheses that cannot
   contribute to the tower clause — a fake decomposition.  The level
   compatibility has to be part of the geometric leaf's CONCLUSION, and it
   is the seventh clause of `IsQAdicWeilSystem`.
2. `PolarizationStruct.weil_hom_nondegenerate` demands nondegeneracy of
   `d.weil x I n hn` for EVERY `n` with `(n : 𝒪_D) ∈ I`, and at an `I`
   RAMIFIED over `q` the classical Weil pairing does not satisfy that at
   `n = q` — see the RAMIFICATION OBSTRUCTION in
   `exists_tateWeilSystem_of_qAdicWeilSystem`, which computes that the
   `q`-Weil pairing vanishes identically on `A[I]` there.  So the classical
   datum is not an instance of that structure at ramified levels, and a
   leaf demanding one would be asking for something the geometry does not
   provide.  `IsQAdicWeilSystem` indexes its perfectness by `A[q^N]`, where
   the classical pairing really is perfect, and pays for the `I`-adic
   information with the trace refinement instead.

FAITHFULNESS.  `hdim` is what makes the geometric fibre an abelian variety
of dimension `[D : ℚ]` with `𝒪_D` acting, hence `A[q^N]` free of rank two
over `𝒪_D/q^N` and the induced pairing perfect;
`[NumberField.IsTotallyReal D]` is what makes the Rosati involution trivial
on `𝒪_D`, i.e. the fourth and fifth clauses (`𝒪_D`-alternating and
`𝒪_D`-adjoint) — without it the pairing is hermitian and the `𝒪_D`-valued
refinement does not exist.  Do not drop either in a restatement. -/
theorem exists_qAdicWeilSystem_of_mult
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (hdim : SmoothOfRelativeDimension (Module.finrank ℚ D) f)
    (q : ℕ) [Fact q.Prime] :
    ∃ w : ℕ → GeomFibrePt f x → GeomFibrePt f x → (AlgebraicClosure F)ˣ,
      IsQAdicWeilSystem m x q w :=
  sorry

/-- **A nonzero element of `𝒪_D` acts surjectively on the geometric points
of a fibre** (SORRY LEAF — an abelian variety over an algebraically closed
field is a divisible group; equivalently a nonzero endomorphism of an
abelian variety is an isogeny, hence surjective on geometric points;
Mumford *Abelian Varieties* §6, Silverman *AEC* III.4.2).

Small, classical, and independent of everything else in this section.  It is
needed exactly once, and there for an unavoidable reason: the perfectness
clause of `IsTateWeilSystem` quantifies over `TatePt m x I π`, so producing a
witness means producing a COMPATIBLE SEQUENCE `y k ∈ A[I^k]` with
`π · y (k+1) = y k`, which is possible only because every point of `A[I^k]`
is `π`-divisible inside `A[I^{k+1}]`.  That is why the docstring of
`IsTateWeilSystem` records that its last clause "also encodes surjectivity of
the transition maps".

`hdim` is what makes the geometric fibre an abelian variety at all. -/
theorem exists_preimage_act_of_mult
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (hdim : SmoothOfRelativeDimension (Module.finrank ℚ D) f)
    (a : NumberField.RingOfIntegers D) (ha : a ≠ 0) (y : GeomFibrePt f x) :
    ∃ z : GeomFibrePt f x, m.act a z = y :=
  sorry

/-- **The pin `(O, j, π)` admits a trace-duality functional** (SORRY LEAF —
step 3 of the classical route, in its pure-algebra half; the inverse
different of a complete discrete valuation ring is principal and the trace
form against a generator is perfect).

No geometry occurs here.  Under `hcplt`/`hdense`/`hker` the ring `O` is the
`I`-adic completion of `𝒪_D`; `hI` and `hπ`/`hπ2` make `I` a maximal ideal
with uniformizer `π`, so `O` is a complete DVR with residue characteristic
`q` (that is `hqI`), and its inverse different over `ℤ_q` is generated by a
single `δ`.  Take `θ = Tr(δ · )`.

`[IsLocalRing O]` is carried because the argument is a local one; it is also
already implied by the pin, and is listed rather than derived so that a
successor does not have to re-derive it before starting.

See `IsTraceDualFunctional` for what the four clauses say and for the
mathlib ingredients. -/
theorem exists_traceDualFunctional_of_adicPin
    {D : Type u} [Field D] [NumberField D]
    (q : ℕ) [Fact q.Prime]
    (I : Ideal (NumberField.RingOfIntegers D)) (hI : I.IsMaximal)
    (hqI : (q : NumberField.RingOfIntegers D) ∈ I)
    (π : NumberField.RingOfIntegers D) (hπ : π ∈ I) (hπ2 : π ∉ I ^ 2)
    (O : Type u) [CommRing O] [IsLocalRing O] [Algebra ℤ_[q] O]
    (j : NumberField.RingOfIntegers D →+* O)
    (hcplt : IsAdicComplete (Ideal.span {j π}) O)
    (hdense : ∀ (n : ℕ) (z : O), ∃ a : NumberField.RingOfIntegers D,
      z - j a ∈ Ideal.span {j π} ^ n)
    (hker : ∀ (n : ℕ) (a : NumberField.RingOfIntegers D),
      j a ∈ Ideal.span {j π} ^ n ↔ a ∈ I ^ n) :
    ∃ θ : O → ℤ_[q], IsTraceDualFunctional q I π j θ :=
  sorry

/-- **A compatible system of discrete logarithms on the `q`-power roots of
unity of `F̄`, intertwining the Galois action with the cyclotomic
character** (SORRY LEAF — the trivialization `T_q μ ≅ ℤ_q` and the DEFINING
property of `cyclotomicCharacter`).

`L k` is "`log_{ζ_k}`" for a chosen compatible system `ζ_{k+1}^q = ζ_k` of
primitive `q^k`-th roots of unity in `F̄`, which exists because `F̄` is
algebraically closed of characteristic zero; the choice is non-canonical and
that is why this is an existence statement.  Everything is written on `F̄ˣ`
with the clauses guarded by `ζ ^ q ^ k = 1`, so that no `rootsOfUnity`
subtype and no transport across `k` is needed.

The five clauses: additivity modulo `q^k`; `Γ_F`-EQUIVARIANCE, i.e.
`L k (σ ζ) ≡ χ_cyc(σ) · L k ζ`, which is where the cyclotomic character
enters this development at all; compatibility along `ζ ↦ ζ^q` (this is what
makes the family a trivialization of the Tate module of `μ`, and it is what
the tower clause of `IsTateWeilSystem` is ultimately built from);
injectivity modulo `q^k`; and surjectivity modulo `q^k`.

WHY `χ_cyc` IS EVALUATED OVER `ℚ̄` AND NOT OVER `F̄`.  The consumer's
statements (`IsTateWeilPairing`, `IsTateWeilSystem`,
`det_eq_cyclotomicCharacter_of_tateFrame`) all name
`cyclotomicCharacter (AlgebraicClosure ℚ) q` composed with
`Field.absoluteGaloisGroup.map (algebraMap ℚ F)`, because that is the
character the Frobenius computations are done with.  So the equivariance
clause carries the transport across `ℚ̄ ↪ F̄` as part of its content; it is
true because the `q^k`-th roots of unity of `F̄` all lie in the image of
`ℚ̄`, so `σ` acts on them through its restriction.  That transport is the
only non-formal part of this leaf.

MATHLIB INGREDIENTS: `cyclotomicCharacter.spec`
(`g t = t ^ (χ(g) mod q^n).val` for `t ^ q^n = 1`),
`cyclotomicCharacter.toZModPow`, `IsPrimitiveRoot`, and the cyclicity of
`rootsOfUnity` in a field. -/
theorem exists_cyclotomicLog (F : Type u) [Field F] [NumberField F]
    (q : ℕ) [Fact q.Prime] :
    ∃ L : ℕ → (AlgebraicClosure F)ˣ → ℤ_[q],
      (∀ (k : ℕ) (ζ ξ : (AlgebraicClosure F)ˣ), ζ ^ q ^ k = 1 → ξ ^ q ^ k = 1 →
        L k (ζ * ξ) - (L k ζ + L k ξ) ∈ Ideal.span {(q : ℤ_[q])} ^ k) ∧
      (∀ (k : ℕ) (σ : Field.absoluteGaloisGroup F) (ζ : (AlgebraicClosure F)ˣ), ζ ^ q ^ k = 1 →
        L k (Units.map
              ((σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F).toAlgHom.toRingHom.toMonoidHom) ζ)
          - (((cyclotomicCharacter (AlgebraicClosure ℚ) q
                ((Field.absoluteGaloisGroup.map (algebraMap ℚ F) σ).toRingEquiv) : ℤ_[q]ˣ) : ℤ_[q])
            * L k ζ) ∈ Ideal.span {(q : ℤ_[q])} ^ k) ∧
      (∀ (k : ℕ) (ζ : (AlgebraicClosure F)ˣ), ζ ^ q ^ (k + 1) = 1 →
        L (k + 1) ζ - L k (ζ ^ q) ∈ Ideal.span {(q : ℤ_[q])} ^ k) ∧
      (∀ (k : ℕ) (ζ : (AlgebraicClosure F)ˣ), ζ ^ q ^ k = 1 →
        (L k ζ ∈ Ideal.span {(q : ℤ_[q])} ^ k ↔ ζ = 1)) ∧
      (∀ (k : ℕ) (r : ℤ_[q]), ∃ ζ : (AlgebraicClosure F)ˣ,
        ζ ^ q ^ k = 1 ∧ L k ζ - r ∈ Ideal.span {(q : ℤ_[q])} ^ k) :=
  sorry

/-- **Trace duality refines the `q`-adic Weil system to the `I`-adic one**
(SORRY LEAF — step 3 of the classical route, in its geometric half: the
passage from `μ_{q^N}`-valued pairings on `A[q^N]` to `𝒪_D/I^k`-valued
pairings on `A[I^k]`, along the inverse different).

Every hypothesis is consumed, and the shape of the intended proof is fixed
by two facts that took some work to establish and that a successor should
not have to rediscover.

**HOW `e` IS DEFINED.**  For `y, z ∈ A[I^k]` the map

  `φ_{y,z} : 𝒪_D ⟶ ℤ_q`,   `b ↦ L k (w k (m.act b y) z)`

is additive modulo `q^k` (bi-multiplicativity of `w` plus additivity of `L`)
and kills `I^k` modulo `q^k` (because `m.act b y = 0` there, and `L k 1 ≡ 0`).
Note `A[I^k] ⊆ A[q^k]`, since `q ∈ I` gives `q^k ∈ I^k`.  The third clause
of `IsTraceDualFunctional` then produces `c` with
`φ_{y,z} b ≡ θ (j b * c)` for all `b`, and `e k y z` is that `c`.  Each
clause of `IsTateWeilSystem` is then verified by computing `φ` for the two
sides and appealing to the FOURTH clause of `IsTraceDualFunctional`
(uniqueness) — that single pattern discharges bi-additivity,
`𝒪_D`-bilinearity (`φ_{a y, z} b = φ_{y,z} (b a)` by `Mult.act_mul`),
alternating (this is where the `𝒪_D`-ALTERNATING clause of
`IsQAdicWeilSystem` is used, and the weaker `w N y y = 1` would leave a
2-torsion error), and `Γ_F`-equivariance (`w`'s Galois clause, then `L`'s,
then `ℤ_q`-linearity of `θ`).

**THE TOWER CLAUSE NEEDS THE TATE MODULE, AND THAT IS NOT AN ACCIDENT.**
The naive derivation fails, and it is worth writing down why, because it is
the trap this cut exists to mark.  Combining `L`'s compatibility
(`L (k+1) ξ ≡ L k (ξ^q)`) with `w`'s level compatibility
(`w (k+1) u v ^ q = w k (q u) (q v)`) gives the level-`k` functional of
`e (k+1) y z` as `b ↦ L k (w k (q b y) (q z))`, whereas the functional of
`e k (π y) (π z)` is `b ↦ L k (w k (π b y) (π z))`.  These differ: by
`𝒪_D`-adjointness the first is `b q^2` and the second `b π^2` against the
same form, and `q` and `π` generate different ideals as soon as `I` is
ramified or has residue degree `> 1`.

The classical construction is therefore not levelwise.  One recovers the
`ℤ_q`-bilinear form `E_q` on `T_I A` as the limit over `N` of
`L N (w N (·) (·))` evaluated at the level-`N` components of Tate points —
this is where `TatePt` and `IsAdicComplete` (`hcplt`) are used — refines it
by trace duality to the `𝒪_D`-bilinear `E`, and sets
`e k y z := E ỹ z̃ mod I^k` for LIFTS `ỹ, z̃ ∈ T_I A` of `y, z` along
`T_I A ↠ A[I^k]`.  The tower clause is then immediate, because a lift of
`y ∈ A[I^{k+1}]` is also a lift of `π y ∈ A[I^k]`: both sides are
`E ỹ z̃` read modulo `I^k`.  The existence of the lifts is exactly `hdiv`.
This is also why the perfectness clause comes out in the `TatePt` form the
statement asks for.

**RAMIFICATION OBSTRUCTION — a refutation, and it corrects the route
recorded on `exists_tateWeilSystem_of_mult`.**  That docstring's step 3 says
to refine "the resulting `μ_{q^k}`-valued pairing" on `A[I^k]`, i.e. to
apply trace duality to `d.weil x (I^k) (q^k)`.  **At an `I` ramified over
`q` there is nothing there to refine: the `q^N`-Weil pairing vanishes
identically on `A[I^k]` for every `N` that is legal.**  Take `I` with
ramification index `e` over `q`.  For `y, z ∈ A[I^k]` the `𝒪_D`-valued form
takes values in `I^{-2k}`, so `Tr(δ E(y,z)) ∈ q^{-⌈2k/e⌉} ℤ_q` and the
`q^N`-Weil pairing `q^N Tr(δ E(y,z))` is nontrivial modulo `ℤ` only when
`N < ⌈2k/e⌉`; while `A[I^k] ⊆ A[q^N]` forces `e N ≥ k`.  For `e = 2, k = 1`
the two conditions are `N < 1` and `N ≥ 1`, so no level works and `A[I]` is
ISOTROPIC for every integer-level Weil pairing.  Since `A[I] ≠ 0`, this also
shows the classical datum is not a `PolarizationStruct d 𝒩` with such an `I`
in `𝒩`, whose `weil_hom_nondegenerate` would assert the opposite at
`n = q` — reported as a cut-level concern for
`Modularity/AbelianScheme.lean`, not repaired here.

REFUTING CHECK for the obstruction: exhibit `y ∈ A[I]` and `N` with
`e N ≥ 1` and `w N y (·)` not identically `1`, for `I` ramified over `q`.

**AND A CORRECTION IN THE OTHER DIRECTION.**  The same docstring concludes
from the `q`-versus-`π` mismatch that "no such field can be written in that
vocabulary" and that "a successor who adds the proposed axiom to
`DualStruct` will be adding a false one".  The second half is right; the
first half is too strong as usually read.  The compatibility along the
INTEGER tower — `e_{q^{N+1}}(y,z)^q = e_{q^N}(q y, q z)`, Silverman *AEC*
III.8.1(e) — IS writable in `μ`-vocabulary, IS true, and is exactly what is
missing from `DualStruct`; it is the seventh clause of `IsQAdicWeilSystem`.
What is not writable there is the `π`-indexed compatibility, and that is a
statement about the `I`-adic tower, which only exists after the refinement.
So the correct reading is: `DualStruct` is missing an integer-tower
compatibility field, and the `I`-adic one is not a field of any structure
with a `μ_n`-valued pairing. -/
theorem exists_tateWeilSystem_of_qAdicWeilSystem
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (q : ℕ) [Fact q.Prime]
    (I : Ideal (NumberField.RingOfIntegers D)) (hI : I.IsMaximal)
    (hqI : (q : NumberField.RingOfIntegers D) ∈ I)
    (π : NumberField.RingOfIntegers D) (hπ : π ∈ I) (hπ2 : π ∉ I ^ 2)
    (O : Type u) [CommRing O] [IsLocalRing O] [Algebra ℤ_[q] O]
    (j : NumberField.RingOfIntegers D →+* O)
    (hcplt : IsAdicComplete (Ideal.span {j π}) O)
    (hker : ∀ (n : ℕ) (a : NumberField.RingOfIntegers D),
      j a ∈ Ideal.span {j π} ^ n ↔ a ∈ I ^ n)
    (w : ℕ → GeomFibrePt f x → GeomFibrePt f x → (AlgebraicClosure F)ˣ)
    (hw : IsQAdicWeilSystem m x q w)
    (θ : O → ℤ_[q]) (hθ : IsTraceDualFunctional q I π j θ)
    (L : ℕ → (AlgebraicClosure F)ˣ → ℤ_[q])
    (hLadd : ∀ (k : ℕ) (ζ ξ : (AlgebraicClosure F)ˣ), ζ ^ q ^ k = 1 → ξ ^ q ^ k = 1 →
      L k (ζ * ξ) - (L k ζ + L k ξ) ∈ Ideal.span {(q : ℤ_[q])} ^ k)
    (hLgal : ∀ (k : ℕ) (σ : Field.absoluteGaloisGroup F) (ζ : (AlgebraicClosure F)ˣ),
      ζ ^ q ^ k = 1 →
      L k (Units.map
            ((σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F).toAlgHom.toRingHom.toMonoidHom) ζ)
        - (((cyclotomicCharacter (AlgebraicClosure ℚ) q
              ((Field.absoluteGaloisGroup.map (algebraMap ℚ F) σ).toRingEquiv) : ℤ_[q]ˣ) : ℤ_[q])
          * L k ζ) ∈ Ideal.span {(q : ℤ_[q])} ^ k)
    (hLtower : ∀ (k : ℕ) (ζ : (AlgebraicClosure F)ˣ), ζ ^ q ^ (k + 1) = 1 →
      L (k + 1) ζ - L k (ζ ^ q) ∈ Ideal.span {(q : ℤ_[q])} ^ k)
    (hLinj : ∀ (k : ℕ) (ζ : (AlgebraicClosure F)ˣ), ζ ^ q ^ k = 1 →
      (L k ζ ∈ Ideal.span {(q : ℤ_[q])} ^ k ↔ ζ = 1))
    (hLsurj : ∀ (k : ℕ) (r : ℤ_[q]), ∃ ζ : (AlgebraicClosure F)ˣ,
      ζ ^ q ^ k = 1 ∧ L k ζ - r ∈ Ideal.span {(q : ℤ_[q])} ^ k)
    (hdiv : ∀ (a : NumberField.RingOfIntegers D), a ≠ 0 →
      ∀ y : GeomFibrePt f x, ∃ z : GeomFibrePt f x, m.act a z = y) :
    ∃ e : ℕ → GeomFibrePt f x → GeomFibrePt f x → O, IsTateWeilSystem m x q I π j e :=
  sorry

/-- **The torsion of a Hilbert–Blumenthal abelian scheme carries a
compatible system of `I`-adic Weil pairings** (DECOMPOSED 2026-07-27 into
five leaves — the GEOMETRIC residue of `exists_tateWeilPairing_of_mult`
after the LIMIT was split off the same day; Mumford *Abelian Varieties*
§16/§20, Taylor 2002 §2, Carayol).

PROVEN HERE from `exists_qAdicWeilSystem_of_mult` (the geometry),
`exists_traceDualFunctional_of_adicPin` (the different),
`exists_cyclotomicLog` (the trivialization of `T_q μ`),
`exists_preimage_act_of_mult` (divisibility) and
`exists_tateWeilSystem_of_qAdicWeilSystem` (the refinement).  The route
recorded below is the classical one and is retained in full because the
analysis it contains is still the reason each leaf says what it says — but
**it is corrected in two places by the RAMIFICATION OBSTRUCTION and by the
CORRECTION note in `exists_tateWeilSystem_of_qAdicWeilSystem`**, which
between them show that step 3 cannot be applied levelwise to
`d.weil x (I^k) (q^k)` and that the missing `DualStruct` axiom is an
integer-tower one.  Read those before acting on the four-step list below.

This is steps 1–3 of the four-step classical route recorded below; step 4
(the passage to the limit) is `exists_tateWeilPairing_of_tateWeilSystem`
and is PROVEN.  Everything here is a statement about the FINITE torsion
group schemes `A[I^k]` and no inverse limit occurs in it, which is the
point of the split: the geometry and the completeness argument are
different subjects and only the first is open.

THIS LEAF DOES NOT RECEIVE THE FRAME, and that is inherited from its
consumer and is load-bearing for the same reason.  The standing audits on
`det_globalFrob_eq_absNorm_of_tateFrame` and on
`exists_weilPairing_of_tateFrame` show that any statement about a form on
the FRAMED module `Fin 2 → O` is a repackaging of the determinant
identity, because `bilin_alternating_apply_det_apply` makes the two
literally equivalent.  That argument needs the frame in order to run.
Here `τ`, `φ`, `hφadd`, `hφbij`, `hφequiv` and `hφj` are all ABSENT, so
`e` cannot be produced by transporting `stdAlternatingBilin` backwards
along `φ`, and the equivariance clause cannot be discharged by quoting a
determinant identity that is not in scope.  What must be built is the
pairing itself, out of the geometry of `f : A ⟶ S`.

REFUTING CHECK for that claim: look for `φ` or `τ` in the binders below.

WHAT MUST BE BUILT, and in what order (the vocabulary for the first two
steps exists in `Modularity/AbelianScheme.lean`):

1. a `DualStruct ab m` — the dual abelian scheme with its canonical
   `A[I] × A^∨[I] ⟶ μ_n` pairing.  Existence is Grothendieck
   representability of `Pic⁰` and is asserted nowhere in this tree;
2. a `PolarizationStruct d {I}` for it — an `𝒪_D`-linear symmetric
   isogeny `A ⟶ A^∨` whose induced pairing on `A[I]` is nondegenerate.
   Since 2026-07-27 that structure has content
   (`weil_hom_nondegenerate`), so this is a genuine existence obligation
   and not a formality.  Ask for the level set `{I}` and nothing wider:
   the unindexed form is the principal-polarization falsity analysed at
   the end of this docstring;
3. the TRACE-DUALITY refinement of the resulting `μ_{q^k}`-valued
   pairing to an `𝒪_D/I^k`-valued one, along the inverse different
   `𝔡_D⁻¹`.  Mathlib has the ingredients (`Submodule.traceDual`,
   `FractionalIdeal.dual`, `differentIdeal`, `traceForm_nondegenerate`).

STEP 3 IS NOT OPTIONAL, AND THIS CORRECTS THE PROPOSAL RECORDED IN
`Modularity/AbelianScheme.lean`.  That file's section docstring records a
"MISSING AXIOM ... COMPATIBILITY ALONG THE `I`-ADIC TOWER" and proposes
adding to `DualStruct` a field of the shape

    weil x (I ^ (k+1)) (q ^ (k+1)) _ (m.act π y) (dualMult.act π z)
      = weil x (I ^ k) (q ^ k) _ y' z'

Checked 2026-07-27: **no such field can be written in that vocabulary**,
and the obstruction is not a typing accident.  `DualStruct.weil x (I^k)
(q^k)` is the restriction to `A[I^k]` of the `q^k`-Weil pairing, so its
target `μ_{q^k}` is indexed by the RATIONAL INTEGER `q`, while the
transition map of `TatePt` is multiplication by `π`.  The classical
compatibility (Silverman *AEC* III.8.1(e), `e_{mn}(P,Q) = e_n(mP,Q)`)
relates levels along multiplication by an INTEGER, and gives
`e_k(q y, q z) = e_{k+1}(y,z)^q` — a correct and provable identity, and
the wrong one, because it is the transition of the `q`-adic tower, not of
the `I`-adic one.  For general `I` there is no expression of
`e_k(π y, π z)` in terms of `e_{k+1}`: `𝒪_D`-adjointness (`weil_act`) is
a level-`k` identity and does not apply to arguments that are only
`I^{k+1}`-torsion, and `π` and `q` generate different ideals of `𝒪_{D,I}`
as soon as `I` is ramified or has residue degree `> 1` over `q`.
So the `I`-adic system is compatible only AFTER the target has been
refined from `μ_{q^k} = (ℤ/q^k)(1)` to `(𝒪_D/I^k)(1)` — i.e. only after
step 3.  A successor who adds the proposed axiom to `DualStruct` will be
adding a false one.
REFUTING CHECK: exhibit `e_k(π y, π z)` as a function of `e_{k+1}(y,z)`
for `I` ramified over `q`, or find a `DualStruct` field relating levels
that does not mention the different.

That correction is exactly why the tower-compatibility clause of
`IsTateWeilSystem` is stated with `O`-VALUED pairings (i.e. with target
`𝒪_D/I^k` through `j` and `hker`) rather than with
`rootsOfUnity`-valued ones: the refinement of step 3 is built into the
STATEMENT of the system, so that the clause it has to satisfy is the
compatible one.

WHY THIS LEAF IS NOT `∃ d : DualStruct ab m, Nonempty (PolarizationStruct d)`,
WHICH WOULD HAVE BEEN FALSE (checked 2026-07-27; the defect this analysis
found has since been REPAIRED in `Modularity/AbelianScheme.lean` — see the
STATUS line at the end of this paragraph, and do not re-derive the
refutation from the current source, where the over-strength is gone).
That was the obvious shape for step 2 and it had to be avoided, because
`PolarizationStruct` was strictly stronger than "a polarization exists".
Its content field `weil_hom_nondegenerate` quantified over ALL ideals `I`
of `𝒪_D`.  By nondegeneracy of the canonical `A[I] × A^∨[I]` pairing, the
left kernel of `weil (·) (hom ·)` on `A[I]` is `hom (A[I])^⊥`, so the
axiom at `I` says exactly `ker hom ∩ A[I] = 0`; imposing it at every `I`
says `ker hom` has no torsion geometric points at all, and in
characteristic zero `ker hom` is finite étale, so this forced `hom` to be
an ISOMORPHISM.  A `PolarizationStruct` was therefore a PRINCIPAL
`𝒪_D`-polarization, and not every abelian variety with real
multiplication by `𝒪_D` admits one — the `𝒪_D`-polarizations of a
Hilbert–Blumenthal abelian variety are classified by a polarization
module, which need not be principal.  So an existence leaf in that shape
would have been a FALSE leaf.

STATUS (2026-07-27, later the same day): `PolarizationStruct` now takes a
SET `𝒩 : Set (Ideal 𝒪_D)` of levels and asserts `weil_hom_nondegenerate`
only at `I ∈ 𝒩`.  So `∃ d, Nonempty (PolarizationStruct d {I})` is the
`I`-local shape and is NOT false — it is the global-geometry counterpart
of this leaf, and a successor pursuing step 2 through
`Modularity/AbelianScheme.lean` should use that shape and no wider one.
`𝒩 = ⊤` (equivalently, dropping the guard) reinstates the falsity above
verbatim; the paragraph is kept in full because it is the reason the
guard exists.

PRECISION NOTE (2026-07-27, from the falsity audit of
`Modularity/KhareWintenberger.lean`'s `HasSplitHilbertBlumenthalModuli`;
it does not change the conclusion above, only the class group it names).
"`hom` is an ISOMORPHISM" is NOT the same as "`hom` is a PRINCIPAL
polarization". `Fermat.PolarizationStruct` carries no POSITIVITY — `hom`
and `-hom` satisfy every one of its fields alike — so `ker hom = 0` says
only that `hom` is a symmetric `𝒪_D`-linear isomorphism `A ≃ A^∨`, i.e.
that a GENERATOR of `𝔠 = Hom^{sym}_{𝒪_D}(A, A^∨)` exists, i.e. that `[𝔠]`
is trivial in the WIDE class group `Cl(D)`. It says nothing about `[𝔠]` in
`Cl⁺(D)`. The falsity above therefore needs `h(D) > 1` rather than
`h⁺(D) > 1` — still true, e.g. `D = ℚ(√15)` with `h = 2`, so the guard is
justified as recorded. But do not reuse the phrase "principal
`𝒪_D`-polarization" for what `𝒩 = ⊤` imposes: `D = ℚ(√3)` has `h = 1`
and `h⁺ = 2`, and its nontrivial-narrow-class HBAVs satisfy
`PolarizationStruct d ⊤` perfectly well.

`IsTateWeilSystem` avoids this by being an `I`-LOCAL statement, and that
is not a dodge but the mathematically correct scope: the classical
identification is `∧²_{𝒪_D} T_I A ≅ 𝔡_D⁻¹ 𝔠 (1)` for the polarization
module `𝔠`, and `𝒪_{D,I}` is a LOCAL ring, over which every invertible
module is free.  So a unit-valued alternating form exists at `I`
regardless of whether `𝔠` is globally principal — which is precisely why
the perfectness clause is stated as "some value is a unit" rather than as
a global nondegeneracy.  KEEP IT `I`-LOCAL.

FAITHFULNESS.  No exceptional set appears here: the pairing exists at
every place, and the finite bad set of the ultimate consumer comes only
from evaluating `χ_cyc` at a Frobenius, which is possible exactly away
from `q`.  `hdim` is load-bearing rather than decoration: it is what
makes the geometric fibre an abelian variety of dimension `[D : ℚ]` with
`𝒪_D` acting, hence `A[I^k]` free of rank TWO over `𝒪_D/I^k`, without
which `∧²` is not a rank-one module and no unit-valued alternating form
need exist.  `[NumberField.IsTotallyReal D]` is load-bearing for the
`𝒪_D`-bilinearity clause: it is triviality of the Rosati involution on
`𝒪_D` (`DualStruct.weil_act`), without which the polarized pairing is
hermitian rather than `𝒪_D`-bilinear and the determinant of the consumer
is a TWIST of `χ_cyc`.  Do not drop either in a restatement.

The pinning hypotheses `j`, `hcplt`, `hdense`, `hker` are what force
`O = 𝒪_{D,I}` acting canonically rather than through an exotic
embedding; they are carried verbatim from the consumer, where the
docstring of `det_globalFrob_eq_absNorm_of_tateFrame` records why
weakening them makes the determinant `χ₁ · ψ⁻¹(χ₂)` instead of
`χ_cyc`.  `hker` in particular is what identifies the level-`k` target
`O / (j π)^k` with `𝒪_D / I^k`, and so is not merely a pin here: it is
the reason the congruences of `IsTateWeilSystem` say what they are meant
to say. -/
theorem exists_tateWeilSystem_of_mult
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (hdim : SmoothOfRelativeDimension (Module.finrank ℚ D) f)
    (q : ℕ) [Fact q.Prime]
    (I : Ideal (NumberField.RingOfIntegers D)) (hI : I.IsMaximal)
    (hqI : (q : NumberField.RingOfIntegers D) ∈ I)
    (π : NumberField.RingOfIntegers D) (hπ : π ∈ I) (hπ2 : π ∉ I ^ 2)
    (O : Type u) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [IsLocalRing O]
    [Algebra ℤ_[q] O]
    (j : NumberField.RingOfIntegers D →+* O)
    (hcplt : IsAdicComplete (Ideal.span {j π}) O)
    (hdense : ∀ (n : ℕ) (z : O), ∃ a : NumberField.RingOfIntegers D,
      z - j a ∈ Ideal.span {j π} ^ n)
    (hker : ∀ (n : ℕ) (a : NumberField.RingOfIntegers D),
      j a ∈ Ideal.span {j π} ^ n ↔ a ∈ I ^ n) :
    ∃ e : ℕ → GeomFibrePt f x → GeomFibrePt f x → O, IsTateWeilSystem m x q I π j e := by
  obtain ⟨w, hw⟩ := exists_qAdicWeilSystem_of_mult m x hdim q
  obtain ⟨θ, hθ⟩ :=
    exists_traceDualFunctional_of_adicPin q I hI hqI π hπ hπ2 O j hcplt hdense hker
  obtain ⟨L, hLadd, hLgal, hLtower, hLinj, hLsurj⟩ := exists_cyclotomicLog F q
  exact exists_tateWeilSystem_of_qAdicWeilSystem m x q I hI hqI π hπ hπ2 O j hcplt hker
    w hw θ hθ L hLadd hLgal hLtower hLinj hLsurj
    (fun a ha y => exists_preimage_act_of_mult m x hdim a ha y)

/-- **A compatible system of levelwise pairings passes to the limit and
gives an `I`-adic Weil pairing on the Tate module** (PROVEN 2026-07-27 —
step 4 of the classical route, and the half of
`exists_tateWeilPairing_of_mult` that is analysis rather than geometry).

Given `t, s : TatePt m x I π`, the sequence

  `k ↦ e k (t.1 k) (s.1 k)`

is CAUCHY for the `(j π)`-adic filtration: consecutive terms differ by an
element of `(j π)^k`, because the tower-compatibility clause of
`IsTateWeilSystem` applied at `t.1 (k+1)`, `s.1 (k+1)` is exactly the
statement that `e (k+1) (t.1 (k+1)) (s.1 (k+1))` and
`e k (m.act π (t.1 (k+1))) (m.act π (s.1 (k+1))) = e k (t.1 k) (s.1 k)`
agree modulo `(j π)^k` — the second equality being the defining
transition of `TatePt`.  `E t s` is then its limit, supplied by the
`IsPrecomplete` half of `hcplt`, and every clause of
`IsTateWeilPairing` follows by writing the required difference as a sum
of three or four terms each visibly in `(j π)^k` and letting the
`IsHausdorff` half of `hcplt` upgrade "in `(j π)^k` for every `k`" to
"zero".

WHICH HYPOTHESES ARE USED WHERE.  `hcplt` is used twice and in both
halves, as just described.  `[IsLocalRing O]` and `hnu` are used ONLY for
the perfectness clause: they turn "`E t s` differs from a unit by an
element of `span {j π}`" into "`E t s` is a unit", which is false without
locality.  `hnu` (`j π` is not a unit) is what puts `span {j π}` inside
the maximal ideal; in the consumer it comes from `hker` at `n = 1`
together with `I ≠ ⊤`.  No other hypothesis of the geometric leaf is
needed here — in particular neither `hdense` nor `hdim` nor totally-real
`D`, all of which do their work upstream in producing the system.

THE CONTINUITY CLAUSE OF `IsTateWeilPairing` IS WHERE THE LEVEL STRUCTURE
SURVIVES THE LIMIT.  It says `E t s ≡ E t' s'` modulo `(j π)^k` whenever
the level-`k` components agree, and it falls straight out of the defining
property of the limit: both sides are congruent to the SAME value
`e k (t.1 k) (s.1 k)` modulo `(j π)^k`.  That clause is not decoration —
it is what `det_eq_cyclotomicCharacter_of_tateWeilPairing` uses to
upgrade `𝒪_D`-bilinearity to `O`-bilinearity — and the fact that it is
free here is the structural reason this cut is the right one. -/
theorem exists_tateWeilPairing_of_tateWeilSystem
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (q : ℕ) [Fact q.Prime]
    (I : Ideal (NumberField.RingOfIntegers D)) (π : NumberField.RingOfIntegers D)
    (O : Type u) [CommRing O] [IsLocalRing O] [Algebra ℤ_[q] O]
    (j : NumberField.RingOfIntegers D →+* O)
    (hcplt : IsAdicComplete (Ideal.span {j π}) O)
    (hnu : ¬ IsUnit (j π))
    (e : ℕ → GeomFibrePt f x → GeomFibrePt f x → O)
    (he : IsTateWeilSystem m x q I π j e) :
    ∃ E : TatePt m x I π → TatePt m x I π → O, IsTateWeilPairing m x q I π j E := by
  classical
  obtain ⟨hadd1, hadd2, halt, hact, hgal, hcompat, hunit⟩ := he
  -- STEP 1.  Consecutive levels of `k ↦ e k (t_k) (s_k)` agree modulo `(j π)^k`:
  -- the tower-compatibility clause, read along the transition of `TatePt`.
  have hstep : ∀ (t s : TatePt m x I π) (k : ℕ),
      e (k + 1) (t.1 (k + 1)) (s.1 (k + 1)) - e k (t.1 k) (s.1 k)
        ∈ Ideal.span {j π} ^ k := by
    intro t s k
    have h := hcompat k (t.1 (k + 1)) (s.1 (k + 1)) (t.2.1 (k + 1)) (s.2.1 (k + 1))
    rwa [t.2.2 k, s.2.2 k] at h
  -- STEP 2.  Telescoping turns that into the Cauchy condition.
  have hmono : ∀ (t s : TatePt m x I π) (a b : ℕ), a ≤ b →
      e a (t.1 a) (s.1 a) - e b (t.1 b) (s.1 b) ∈ Ideal.span {j π} ^ a := by
    intro t s a b hab
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
        have h2 : (Ideal.span {j π} : Ideal O) ^ n ≤ Ideal.span {j π} ^ a :=
          Ideal.pow_le_pow_right hn
        have h3 : e n (t.1 n) (s.1 n) - e (n + 1) (t.1 (n + 1)) (s.1 (n + 1))
            ∈ Ideal.span {j π} ^ a := by
          have hneg := Submodule.neg_mem (Ideal.span {j π} ^ n) (hstep t s n)
          rw [neg_sub] at hneg
          exact h2 hneg
        have hrw : e a (t.1 a) (s.1 a) - e (n + 1) (t.1 (n + 1)) (s.1 (n + 1))
            = (e a (t.1 a) (s.1 a) - e n (t.1 n) (s.1 n))
              + (e n (t.1 n) (s.1 n) - e (n + 1) (t.1 (n + 1)) (s.1 (n + 1))) := by ring
        rw [hrw]
        exact Ideal.add_mem _ ih h3
  -- STEP 3.  The `IsPrecomplete` half of `hcplt` supplies the limit.
  have hex : ∀ t s : TatePt m x I π, ∃ L : O,
      ∀ n : ℕ, e n (t.1 n) (s.1 n) - L ∈ Ideal.span {j π} ^ n := by
    intro t s
    obtain ⟨L, hL⟩ := hcplt.toIsPrecomplete.prec (f := fun n => e n (t.1 n) (s.1 n))
      (fun {a b} hab => by
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
        exact hmono t s a b hab)
    refine ⟨L, fun n => ?_⟩
    have h := hL n
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h
  choose E hEspec using hex
  -- STEP 4.  The `IsHausdorff` half turns congruences at every level into equalities.
  have haus : ∀ z : O, (∀ n : ℕ, z ∈ Ideal.span {j π} ^ n) → z = 0 := fun z hz =>
    hcplt.toIsHausdorff.haus z fun n => by
      rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]; exact hz n
  refine ⟨E, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- bi-additivity, first variable
    intro t t' t'' s ht''
    refine sub_eq_zero.mp (haus _ fun k => ?_)
    have h1 := hEspec t'' s k
    have h2 := hEspec t s k
    have h3 := hEspec t' s k
    have h4 := hadd1 k (t.1 k) (t'.1 k) (s.1 k) (t.2.1 k) (t'.2.1 k) (s.2.1 k)
    rw [← ht'' k] at h4
    have hrw : E t'' s - (E t s + E t' s)
        = -(e k (t''.1 k) (s.1 k) - E t'' s)
          + (e k (t''.1 k) (s.1 k) - (e k (t.1 k) (s.1 k) + e k (t'.1 k) (s.1 k)))
          + (e k (t.1 k) (s.1 k) - E t s) + (e k (t'.1 k) (s.1 k) - E t' s) := by ring
    rw [hrw]
    exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Submodule.neg_mem _ h1) h4) h2) h3
  · -- bi-additivity, second variable
    intro t s s' s'' hs''
    refine sub_eq_zero.mp (haus _ fun k => ?_)
    have h1 := hEspec t s'' k
    have h2 := hEspec t s k
    have h3 := hEspec t s' k
    have h4 := hadd2 k (t.1 k) (s.1 k) (s'.1 k) (t.2.1 k) (s.2.1 k) (s'.2.1 k)
    rw [← hs'' k] at h4
    have hrw : E t s'' - (E t s + E t s')
        = -(e k (t.1 k) (s''.1 k) - E t s'')
          + (e k (t.1 k) (s''.1 k) - (e k (t.1 k) (s.1 k) + e k (t.1 k) (s'.1 k)))
          + (e k (t.1 k) (s.1 k) - E t s) + (e k (t.1 k) (s'.1 k) - E t s') := by ring
    rw [hrw]
    exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Submodule.neg_mem _ h1) h4) h2) h3
  · -- alternating
    intro t
    refine haus _ fun k => ?_
    have h1 := hEspec t t k
    have h2 := halt k (t.1 k) (t.2.1 k)
    have hrw : E t t = -(e k (t.1 k) (t.1 k) - E t t) + e k (t.1 k) (t.1 k) := by ring
    rw [hrw]
    exact Ideal.add_mem _ (Submodule.neg_mem _ h1) h2
  · -- `𝒪_D`-bilinearity
    intro a t t' s ht'
    refine sub_eq_zero.mp (haus _ fun k => ?_)
    have h1 := hEspec t' s k
    have h2 := hEspec t s k
    have h4 := hact k a (t.1 k) (s.1 k) (t.2.1 k) (s.2.1 k)
    rw [← ht' k] at h4
    have hrw : E t' s - j a * E t s
        = -(e k (t'.1 k) (s.1 k) - E t' s)
          + (e k (t'.1 k) (s.1 k) - j a * e k (t.1 k) (s.1 k))
          + j a * (e k (t.1 k) (s.1 k) - E t s) := by ring
    rw [hrw]
    exact Ideal.add_mem _ (Ideal.add_mem _ (Submodule.neg_mem _ h1) h4) (Ideal.mul_mem_left _ _ h2)
  · -- `Γ_F`-equivariance
    intro σ t t' s s' ht' hs'
    refine sub_eq_zero.mp (haus _ fun k => ?_)
    have h1 := hEspec t' s' k
    have h2 := hEspec t s k
    have h4 := hgal k σ (t.1 k) (s.1 k) (t.2.1 k) (s.2.1 k)
    rw [← ht' k, ← hs' k] at h4
    have hrw : E t' s' -
        algebraMap ℤ_[q] O
          ((cyclotomicCharacter (AlgebraicClosure ℚ) q
            ((Field.absoluteGaloisGroup.map (algebraMap ℚ F) σ).toRingEquiv) : ℤ_[q]ˣ) : ℤ_[q])
          * E t s
        = -(e k (t'.1 k) (s'.1 k) - E t' s')
          + (e k (t'.1 k) (s'.1 k) -
              algebraMap ℤ_[q] O
                ((cyclotomicCharacter (AlgebraicClosure ℚ) q
                  ((Field.absoluteGaloisGroup.map (algebraMap ℚ F) σ).toRingEquiv) :
                    ℤ_[q]ˣ) : ℤ_[q])
                * e k (t.1 k) (s.1 k))
          + algebraMap ℤ_[q] O
              ((cyclotomicCharacter (AlgebraicClosure ℚ) q
                ((Field.absoluteGaloisGroup.map (algebraMap ℚ F) σ).toRingEquiv) :
                  ℤ_[q]ˣ) : ℤ_[q])
              * (e k (t.1 k) (s.1 k) - E t s) := by ring
    rw [hrw]
    exact Ideal.add_mem _ (Ideal.add_mem _ (Submodule.neg_mem _ h1) h4) (Ideal.mul_mem_left _ _ h2)
  · -- continuity: both limits are congruent to the same level-`k` value
    intro k t t' s s' hts hss
    have h1 := hEspec t s k
    have h2 := hEspec t' s' k
    rw [hts, hss] at h1
    have hrw : E t s - E t' s'
        = -(e k (t'.1 k) (s'.1 k) - E t s) + (e k (t'.1 k) (s'.1 k) - E t' s') := by ring
    rw [hrw]
    exact Ideal.add_mem _ (Submodule.neg_mem _ h1) h2
  · -- perfectness: a unit stays a unit under a perturbation by the maximal ideal
    obtain ⟨t, s, hts⟩ := hunit
    refine ⟨t, s, ?_⟩
    have h1 := hEspec t s 1
    rw [pow_one] at h1
    by_contra hv
    have hjm : j π ∈ IsLocalRing.maximalIdeal O :=
      (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
    have hsub : (Ideal.span {j π} : Ideal O) ≤ IsLocalRing.maximalIdeal O :=
      Ideal.span_le.mpr (by simpa using hjm)
    have hvm : E t s ∈ IsLocalRing.maximalIdeal O :=
      (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hv)
    have hum : e 1 (t.1 1) (s.1 1) ∈ IsLocalRing.maximalIdeal O := by
      have hrw : e 1 (t.1 1) (s.1 1) = (e 1 (t.1 1) (s.1 1) - E t s) + E t s := by ring
      rw [hrw]
      exact Ideal.add_mem _ (hsub h1) hvm
    exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hum)) hts

/-- **The Tate module of a Hilbert–Blumenthal abelian scheme carries an
`I`-adic Weil pairing** (PROVEN 2026-07-27, later the same day, over the
ONE geometric leaf `exists_tateWeilSystem_of_mult`; it was the GEOMETRIC
half of the 2026-07-27 cut of `det_globalFrob_eq_absNorm_of_tateFrame`.
Mumford *Abelian Varieties* §16/§20, Taylor 2002 §2, Carayol).

WHERE THE LEAF WENT.  The four-step classical route recorded below splits
cleanly after step 3, and the split is along the LIMIT:

* steps 1–3 — dual, polarization, trace-duality refinement — produce a
  COMPATIBLE SYSTEM of levelwise pairings on the finite torsion group
  schemes `A[I^k]`.  That is `exists_tateWeilSystem_of_mult`, which since
  2026-07-27 is PROVEN over five leaves of its own.  All of the audits
  below apply to it verbatim and are restated in its docstring, which is
  where a successor should read them — TOGETHER WITH the two corrections
  those leaves added (the RAMIFICATION OBSTRUCTION and the integer-tower
  CORRECTION, both in `exists_tateWeilSystem_of_qAdicWeilSystem`);
* step 4 — passage to the limit — is
  `exists_tateWeilPairing_of_tateWeilSystem`, and it is PROVEN.  It is
  where `hcplt` earns its keep, and it is also where the CONTINUITY
  clause of `IsTateWeilPairing` comes from, for free.

The split is not a repackaging in either direction: `IsTateWeilSystem`
mentions no inverse limit and `IsTateWeilPairing` mentions no level-`k`
torsion group, and neither statement can be obtained from the other
without the completeness argument in between.  The assembly below is
therefore three lines of glue plus the one step that is genuinely about
`O` rather than about geometry: `hker` at `n = 1` together with
`I ≠ ⊤` says `j π` is a NON-UNIT, which is what puts `span {j π}` inside
the maximal ideal of the local ring `O` and so lets the perfectness
clause survive the limit.

THIS LEAF DOES NOT RECEIVE THE FRAME, and that was the whole point of the
cut.  The standing audit on `det_globalFrob_eq_absNorm_of_tateFrame` and
on `exists_weilPairing_of_tateFrame` shows that any statement about a
form on the FRAMED module `Fin 2 → O` is a repackaging of the determinant
identity, because `bilin_alternating_apply_det_apply` makes the two
literally equivalent.  That argument needs the frame in order to run.
Here `τ`, `φ`, `hφadd`, `hφbij`, `hφequiv` and `hφj` are all ABSENT, so
`E` cannot be produced by transporting `stdAlternatingBilin` backwards
along `φ`, and the equivariance clause cannot be discharged by quoting a
determinant identity that is not in scope.  What must be built is the
pairing itself, out of the geometry of `f : A ⟶ S`.

REFUTING CHECK for that claim: look for `φ` or `τ` in the binders below.

THE CLASSICAL ROUTE, and in what order (the vocabulary for the first two
steps exists in `Modularity/AbelianScheme.lean`):

1. a `DualStruct ab m` — the dual abelian scheme with its canonical
   `A[I] × A^∨[I] ⟶ μ_n` pairing.  Existence is Grothendieck
   representability of `Pic⁰` and is asserted nowhere in this tree;
2. a `PolarizationStruct` for it — an `𝒪_D`-linear symmetric isogeny
   `A ⟶ A^∨` whose induced pairing on `A[I]` is nondegenerate.  Since
   2026-07-27 that structure has content (`weil_hom_nondegenerate`), so
   this is a genuine existence obligation and not a formality;
3. the TRACE-DUALITY refinement of the resulting `μ_{q^k}`-valued
   pairing to an `𝒪_D/I^k`-valued one, along the inverse different
   `𝔡_D⁻¹`.  Mathlib has the ingredients (`Submodule.traceDual`,
   `FractionalIdeal.dual`, `differentIdeal`, `traceForm_nondegenerate`);
4. the passage to the limit over `k`, which is where the continuity
   clause of `IsTateWeilPairing` comes from.

Steps 1–3 are `exists_tateWeilSystem_of_mult`; step 4 is
`exists_tateWeilPairing_of_tateWeilSystem` and is PROVEN.  **STEP 3 IS
NOT APPLIED LEVELWISE AND STEPS 1–2 ARE NOT `DualStruct`/
`PolarizationStruct`** — the RAMIFICATION OBSTRUCTION in
`exists_tateWeilSystem_of_qAdicWeilSystem` shows the `q^N`-Weil pairing
vanishes identically on `A[I^k]` at a ramified `I`, so there is nothing
there to refine, and the refinement has to happen on `T_I A`.  Read that
docstring before acting on the list above.  TWO STANDING
REFUTATIONS govern any further work on steps 1–3 and are recorded IN
FULL on `exists_tateWeilSystem_of_mult`, each with its refuting check:
the level-compatibility axiom proposed for `DualStruct` in
`Modularity/AbelianScheme.lean` **cannot be written in that vocabulary
and would be false** (its target `μ_{q^k}` is indexed by the rational
integer `q`, not by `π`) — though note the CORRECTION in
`exists_tateWeilSystem_of_qAdicWeilSystem`: the compatibility along the
INTEGER tower IS writable and true, and is the field `DualStruct` is
actually missing — and an existence leaf of the shape
`∃ d : DualStruct ab m, Nonempty (PolarizationStruct d)` **would be
false** (`weil_hom_nondegenerate` at every `I` forces `hom` to be an
isomorphism, i.e. a PRINCIPAL `𝒪_D`-polarization, which a
Hilbert–Blumenthal abelian variety need not admit).  Both are avoided by
staying `I`-LOCAL, which is not a dodge but the correct scope: the
classical identification is `∧²_{𝒪_D} T_I A ≅ 𝔡_D⁻¹ 𝔠 (1)` for the
polarization module `𝔠`, and `𝒪_{D,I}` is a LOCAL ring, over which every
invertible module is free — which is precisely why the perfectness clause
above is stated as "some value is a unit" rather than as a global
nondegeneracy.

FAITHFULNESS.  No exceptional set appears here: the pairing exists at
every place, and the finite bad set of the consumer comes only from
evaluating `χ_cyc` at a Frobenius, which is possible exactly away from
`q`.  `hdim` is load-bearing rather than decoration: it is what makes the
geometric fibre an abelian variety of dimension `[D : ℚ]` with `𝒪_D`
acting, hence `T_I A` free of rank TWO over `𝒪_{D,I}`, without which
`∧²` is not a rank-one module and no unit-valued alternating form need
exist.  `[NumberField.IsTotallyReal D]` is load-bearing for the
`𝒪_D`-bilinearity clause: it is triviality of the Rosati involution on
`𝒪_D`, without which the polarized pairing is hermitian rather than
`𝒪_D`-bilinear and the determinant is a TWIST of `χ_cyc`.  Do not drop
either in a restatement.

The pinning hypotheses `j`, `hcplt`, `hdense`, `hker` are what force
`O = 𝒪_{D,I}` acting canonically rather than through an exotic
embedding; they are carried verbatim from the consumer, where the
docstring of `det_globalFrob_eq_absNorm_of_tateFrame` records why
weakening them makes the determinant `χ₁ · ψ⁻¹(χ₂)` instead of
`χ_cyc`. -/
theorem exists_tateWeilPairing_of_mult
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (hdim : SmoothOfRelativeDimension (Module.finrank ℚ D) f)
    (q : ℕ) [Fact q.Prime]
    (I : Ideal (NumberField.RingOfIntegers D)) (hI : I.IsMaximal)
    (hqI : (q : NumberField.RingOfIntegers D) ∈ I)
    (π : NumberField.RingOfIntegers D) (hπ : π ∈ I) (hπ2 : π ∉ I ^ 2)
    (O : Type u) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [IsLocalRing O]
    [Algebra ℤ_[q] O]
    (j : NumberField.RingOfIntegers D →+* O)
    (hcplt : IsAdicComplete (Ideal.span {j π}) O)
    (hdense : ∀ (n : ℕ) (z : O), ∃ a : NumberField.RingOfIntegers D,
      z - j a ∈ Ideal.span {j π} ^ n)
    (hker : ∀ (n : ℕ) (a : NumberField.RingOfIntegers D),
      j a ∈ Ideal.span {j π} ^ n ↔ a ∈ I ^ n) :
    ∃ E : TatePt m x I π → TatePt m x I π → O, IsTateWeilPairing m x q I π j E := by
  obtain ⟨e, he⟩ := exists_tateWeilSystem_of_mult m x hdim q I hI hqI π hπ hπ2 O j
    hcplt hdense hker
  refine exists_tateWeilPairing_of_tateWeilSystem m x q I π O j hcplt ?_ e he
  -- `j π` is a non-unit: were `span {j π}` the unit ideal, `hker` at `n = 1`
  -- would put `1` in `I`, contradicting maximality.
  intro hu
  have h1 : (Ideal.span {j π} : Ideal O) = ⊤ := Ideal.span_singleton_eq_top.mpr hu
  have h2 : (1 : NumberField.RingOfIntegers D) ∈ I ^ 1 := by
    refine (hker 1 1).mp ?_
    rw [pow_one, h1]
    exact Submodule.mem_top
  rw [pow_one] at h2
  exact hI.ne_top ((Ideal.eq_top_iff_one I).mpr h2)

/-- **The determinant of a Tate frame is the cyclotomic character, given
an `I`-adic Weil pairing on the Tate module** (PROVEN 2026-07-27 — the
TRANSPORT half of the cut of `det_globalFrob_eq_absNorm_of_tateFrame`
made the same day).

This is where the frame enters, and it is a genuine theorem rather than a
repackaging in the other direction: `E` is given as an arbitrary form
satisfying `IsTateWeilPairing`, so the proof may neither choose it nor
ignore it.

WHICH HYPOTHESES THE PROOF ACTUALLY USES, made mechanically visible by
underscore-prefixing the rest.  `_hI`, `_hqI`, `_hπ2` and `_hker` are NOT
used here, and that is the correct division of labour rather than a sign
that they are decoration: they are the hypotheses that pin `O` as
`𝒪_{D,I}` and `π` as a uniformizer, and their work is done in
`exists_tateWeilPairing_of_mult`, which is what has to PRODUCE a pairing
satisfying `IsTateWeilPairing`.  Once such a pairing is in hand the
transport below needs only `hπ` (to know `π ^ k ∈ I ^ k`, which kills the
level-`k` component), `hdense` and `hcplt` (density and Hausdorffness,
for the `O`-bilinearity step) and the frame axioms.  Do NOT conclude from
this that the pinning hypotheses may be dropped from the leaf above; see
its docstring.

THE ARGUMENT, and where each clause of `IsTateWeilPairing` is consumed.
Set `E' u v := E (φ u) (φ v)` on `Fin 2 → O`.

* `E'` is bi-additive by the first two clauses together with `hφadd`, and
  alternating by the third.
* `E'` is `O`-BILINEAR.  This is the only step that is not immediate, and
  it is what the continuity clause exists for.  The `𝒪_D`-bilinearity
  clause plus `hφj` give `E' (j a • u) v = j a * E' u v` for `a ∈ 𝒪_D`;
  `hdense` approximates an arbitrary `c : O` by `j a` modulo `(j π)^k`;
  the continuity clause turns that approximation into a congruence of
  pairing values modulo `(j π)^k`; and `hcplt` (whose `IsHausdorff` half
  gives `⋂_k (j π)^k = 0`) upgrades the congruences to an equality.
* The equivariance clause plus `hφequiv` give
  `E' (τ σ u) (τ σ v) = χ_cyc(σ) * E' u v` for all `u`, `v`.
* `bilin_alternating_apply_det_apply` applied to the `O`-bilinear
  alternating `E'` and to `M := τ σ` gives
  `E' (τ σ u) (τ σ v) = det (τ σ) * E' u v`.
* Comparing the two at the pair supplied by the perfectness clause — for
  which `hφbij` is needed, to see that pair as `(φ u₀, φ v₀)` — and
  cancelling the unit `E' u₀ v₀` gives the identity.

`hφbij` is used ONLY at that last step and is essential there: without
surjectivity of `φ` the unit value guaranteed by the perfectness clause
might be attained at a pair of Tate points outside the image of the
frame, and nothing could be cancelled.

The identity is asserted at EVERY `σ ∈ Γ_F`, ramified places included —
the finite bad set of the consumer comes only from evaluating `χ_cyc` at
a Frobenius. -/
theorem det_eq_cyclotomicCharacter_of_tateWeilPairing
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (q : ℕ) [Fact q.Prime]
    (I : Ideal (NumberField.RingOfIntegers D)) (_hI : I.IsMaximal)
    (_hqI : (q : NumberField.RingOfIntegers D) ∈ I)
    (π : NumberField.RingOfIntegers D) (hπ : π ∈ I) (_hπ2 : π ∉ I ^ 2)
    (O : Type u) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [IsLocalRing O]
    [Algebra ℤ_[q] O]
    (j : NumberField.RingOfIntegers D →+* O)
    (hcplt : IsAdicComplete (Ideal.span {j π}) O)
    (hdense : ∀ (n : ℕ) (z : O), ∃ a : NumberField.RingOfIntegers D,
      z - j a ∈ Ideal.span {j π} ^ n)
    (_hker : ∀ (n : ℕ) (a : NumberField.RingOfIntegers D),
      j a ∈ Ideal.span {j π} ^ n ↔ a ∈ I ^ n)
    (τ : GaloisRep F O (Fin 2 → O)) (φ : (Fin 2 → O) → TatePt m x I π)
    (hφadd : ∀ (u u' : Fin 2 → O) (n : ℕ),
      (φ (u + u')).1 n = ab.add ((φ u).1 n) ((φ u').1 n))
    (hφbij : Function.Bijective φ)
    (hφequiv : ∀ (σ : Field.absoluteGaloisGroup F) (u : Fin 2 → O) (n : ℕ),
      (φ (τ σ u)).1 n = ab.galSMul x σ ((φ u).1 n))
    (hφj : ∀ (a : NumberField.RingOfIntegers D) (u : Fin 2 → O) (n : ℕ),
      (φ (j a • u)).1 n = m.act a ((φ u).1 n))
    (E : TatePt m x I π → TatePt m x I π → O)
    (hE : IsTateWeilPairing m x q I π j E)
    (σ : Field.absoluteGaloisGroup F) :
    LinearMap.det (τ σ) =
      algebraMap ℤ_[q] O
        ((cyclotomicCharacter (AlgebraicClosure ℚ) q
          ((Field.absoluteGaloisGroup.map (algebraMap ℚ F) σ).toRingEquiv) :
            ℤ_[q]ˣ) : ℤ_[q]) := by
  classical
  obtain ⟨hadd1, hadd2, halt, hact, hgal, hcont, hunit⟩ := hE
  -- STEP 0. A Tate point scaled by an element of `I ^ k` has vanishing level-`k`
  -- component: `hφj` turns the scaling into `m.act`, and the level-`k` component
  -- of a Tate point is `I ^ k`-torsion by the defining property of `TatePt`.
  have hvanish : ∀ (w : Fin 2 → O) (k : ℕ) (a : NumberField.RingOfIntegers D), a ∈ I ^ k →
      (φ (j a • w)).1 k = ab.zero (specAlgClos F ≫ x) := by
    intro w k a ha
    rw [hφj a w k]
    letI := ab.addCommGroup (specAlgClos F ≫ x)
    letI := m.module (specAlgClos F ≫ x)
    have hy' := (Submodule.mem_torsionBySet_iff _ _).mp ((φ w).2.1 k)
    exact hy' ⟨a, ha⟩
  -- STEP 1. Bi-additivity of the transported form, from the first two clauses.
  have hEaddl : ∀ u u' v : Fin 2 → O,
      E (φ (u + u')) (φ v) = E (φ u) (φ v) + E (φ u') (φ v) :=
    fun u u' v => hadd1 (φ u) (φ u') (φ (u + u')) (φ v) (hφadd u u')
  have hEaddr : ∀ u v v' : Fin 2 → O,
      E (φ u) (φ (v + v')) = E (φ u) (φ v) + E (φ u) (φ v') :=
    fun u v v' => hadd2 (φ u) (φ v) (φ v') (φ (v + v')) (hφadd v v')
  -- STEP 1b. Skew symmetry, from `alternating` at `u + v` plus bi-additivity.
  have hskew : ∀ u v : Fin 2 → O, E (φ u) (φ v) = - E (φ v) (φ u) := by
    intro u v
    have h := halt (φ (u + v))
    rw [hEaddl u v (u + v), hEaddr u u v, hEaddr v u v, halt (φ u), halt (φ v)] at h
    linear_combination h
  -- STEP 2. `𝒪_D`-scaling of the transported form.
  have hEactl : ∀ (a : NumberField.RingOfIntegers D) (u v : Fin 2 → O),
      E (φ (j a • u)) (φ v) = j a * E (φ u) (φ v) :=
    fun a u v => hact a (φ u) (φ (j a • u)) (φ v) (hφj a u)
  -- STEP 3. `O`-scaling.  This is the only step that is not immediate, and it is
  -- what the continuity clause of `IsTateWeilPairing` exists for: approximate
  -- `c : O` by `j a` modulo `(j π) ^ k` using `hdense`, note that the level-`k`
  -- components of `φ (c • u)` and `φ (j a • u)` then agree by STEP 0, convert
  -- that into a congruence of pairing values by the continuity clause, and let
  -- the `IsHausdorff` half of `hcplt` upgrade the congruences to an equality.
  have hEsmull : ∀ (c : O) (u v : Fin 2 → O),
      E (φ (c • u)) (φ v) = c * E (φ u) (φ v) := by
    intro c u v
    have key : ∀ k : ℕ,
        E (φ (c • u)) (φ v) - c * E (φ u) (φ v) ∈ Ideal.span {j π} ^ k := by
      intro k
      obtain ⟨a, ha⟩ := hdense k c
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ha
      obtain ⟨r, hr⟩ := ha
      have hsplit : c • u = (j a) • u + ((c - j a) • u) := by
        rw [← add_smul]; congr 1; ring
      have hw : (c - j a) • u = (j (π ^ k)) • (r • u) := by
        rw [← hr, map_pow, smul_smul, mul_comm]
      have hcomp : (φ (c • u)).1 k = (φ ((j a) • u)).1 k := by
        rw [hsplit, hφadd, hw, hvanish (r • u) k (π ^ k) (Ideal.pow_mem_pow hπ k),
          ab.add_comm, ab.zero_add]
      have h1 : E (φ (c • u)) (φ v) - E (φ ((j a) • u)) (φ v) ∈ Ideal.span {j π} ^ k :=
        hcont k (φ (c • u)) (φ ((j a) • u)) (φ v) (φ v) hcomp rfl
      have h3 : (c - j a) * E (φ u) (φ v) ∈ Ideal.span {j π} ^ k := by
        rw [← hr, Ideal.span_singleton_pow]
        exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
      have hrw : E (φ (c • u)) (φ v) - c * E (φ u) (φ v)
          = (E (φ (c • u)) (φ v) - E (φ ((j a) • u)) (φ v))
            - (c - j a) * E (φ u) (φ v) := by
        rw [hEactl a u v]; ring
      rw [hrw]
      exact Ideal.sub_mem _ h1 h3
    have hz := hcplt.toIsHausdorff.haus
      (E (φ (c • u)) (φ v) - c * E (φ u) (φ v)) (fun n => by
        rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
        exact key n)
    exact sub_eq_zero.mp hz
  have hEsmulr : ∀ (c : O) (u v : Fin 2 → O),
      E (φ u) (φ (c • v)) = c * E (φ u) (φ v) := by
    intro c u v
    rw [hskew u (c • v), hEsmull c v u, hskew u v]
    ring
  -- STEP 4. Bundle the transported form as an `O`-bilinear map.
  let E' : (Fin 2 → O) →ₗ[O] (Fin 2 → O) →ₗ[O] O :=
    LinearMap.mk₂ O (fun u v => E (φ u) (φ v))
      (fun u u' v => hEaddl u u' v)
      (fun c u v => by rw [smul_eq_mul]; exact hEsmull c u v)
      (fun u v v' => hEaddr u v v')
      (fun c u v => by rw [smul_eq_mul]; exact hEsmulr c u v)
  have hE'apply : ∀ u v : Fin 2 → O, E' u v = E (φ u) (φ v) := fun _ _ => rfl
  have halt' : ∀ u : Fin 2 → O, E' u u = 0 := fun u => halt (φ u)
  -- STEP 5. An endomorphism acts on an alternating form by its determinant.
  have hdet : ∀ u v : Fin 2 → O,
      E' (τ σ u) (τ σ v) = LinearMap.det (τ σ) * E' u v :=
    fun u v => bilin_alternating_apply_det_apply E' halt' (τ σ) u v
  -- STEP 6. The same quantity, computed by the equivariance clause instead.
  have hgal' : ∀ u v : Fin 2 → O,
      E' (τ σ u) (τ σ v) =
        algebraMap ℤ_[q] O
          ((cyclotomicCharacter (AlgebraicClosure ℚ) q
            ((Field.absoluteGaloisGroup.map (algebraMap ℚ F) σ).toRingEquiv) :
              ℤ_[q]ˣ) : ℤ_[q]) * E' u v := by
    intro u v
    rw [hE'apply, hE'apply]
    exact hgal σ (φ u) (φ (τ σ u)) (φ v) (φ (τ σ v)) (hφequiv σ u) (hφequiv σ v)
  -- STEP 7. Cancel the unit value supplied by perfectness; `hφbij` is what puts
  -- that value in the image of the frame, where the two computations meet.
  obtain ⟨t, s, hts⟩ := hunit
  obtain ⟨u₀, rfl⟩ := hφbij.2 t
  obtain ⟨v₀, rfl⟩ := hφbij.2 s
  have hu : IsUnit (E' u₀ v₀) := by rw [hE'apply]; exact hts
  exact hu.mul_right_cancel ((hdet u₀ v₀).symm.trans (hgal' u₀ v₀))

/-- **The determinant of a Tate frame at the global Frobenius elements is
the ABSOLUTE NORM** (PROVEN 2026-07-27 over `exists_tateWeilPairing_of_mult`
and `det_eq_cyclotomicCharacter_of_tateWeilPairing`; was cut 2026-07-27 out of
`det_eq_cyclotomicCharacter_of_tateFrame` along the CHEBOTAREV axis and
narrowed the same day along the ARITHMETIC axis; Silverman *AEC*
III.8 for the elliptic case, Mumford *Abelian Varieties* §16/§20 for the
polarized case in general, Taylor 2002 §2 and Carayol for the
Hilbert–Blumenthal normalization used here).

For a Tate frame `φ`/`τ` as in `exists_tateFrame_of_adicCoefficientRing`,
there is a FINITE set of finite places of `F` outside which

  `det (τ (Frob_v)) = N v`,   `N v = #(𝒪_F / v)`.

WHERE THE LEAF WENT (2026-07-27, later the same day).  This declaration
is no longer sorried.  It is PROVEN over the two leaves introduced just
above, and the split is along the PAIRING axis in the one shape the audit
below does NOT rule out:

* `exists_tateWeilPairing_of_mult` — the GEOMETRY.  It produces an
  `I`-adic Weil pairing on the Tate module and it does **not** receive
  the frame, so it is not a repackaging of this identity; see its
  docstring for why, and for the four-step classical route that must be
  formalized to close it.  It is itself PROVEN since later on 2026-07-27,
  over `exists_tateWeilSystem_of_mult` (steps 1–3, the LEVELWISE system
  of pairings on `A[I^k]`) and `exists_tateWeilPairing_of_tateWeilSystem`
  (step 4, the limit, PROVEN).
* `det_eq_cyclotomicCharacter_of_tateWeilPairing` — the TRANSPORT, and it
  is PROVEN.  It receives such a pairing as an arbitrary given and pushes
  it along the frame to `det (τ σ) = χ_cyc(σ)` at every `σ ∈ Γ_F`.

So the whole determinant clause now rests on ONE sorry, the levelwise
geometric one, and it is a statement about the finite torsion group
schemes of the abelian scheme alone.

The assembly below is the remaining ARITHMETIC: it manufactures the
exceptional set as the fibre over `q` (`finite_places_natCast_mem_asIdeal`,
finite because `q ≠ 0`), which is exactly where `χ_cyc(Frob_v) = N v`
fails, and then evaluates `χ_cyc` at the Frobenius by
`cyclotomicCharacter_adicArithFrob_absNorm`.  Note the exceptional set
produced here is SMALLER than the statement allows: no bad-reduction
places appear, because the pairing leaf asserts the identity at every
place.  `GaloisRepresentation.globalFrob v` is definitionally the image
of `Field.AbsoluteGaloisGroup.adicArithFrob v`, so the two meet by `rfl`
with no transport lemma.

WHY THE PAIRING CUT IS LEGITIMATE HERE, AGAINST THE AUDIT BELOW.  The
FORMAL-CONTENT AUDIT in `det_eq_cyclotomicCharacter_of_tateFrame` and the
"WHAT A SUCCESSOR SHOULD NOT DO" paragraph below both forbid cutting this
node into a statement about an alternating form **on the framed module**
`Fin 2 → O`, and they are right: `bilin_alternating_apply_det_apply`
makes such a statement literally equivalent to this identity, so the cut
collapses to three lines.  Both arguments run by *using the frame*.
`exists_tateWeilPairing_of_mult` has no frame in its binders at all — its
`E` lives on `TatePt m x I π`, an inverse limit of geometric torsion, and
cannot be obtained by transporting `stdAlternatingBilin` backwards along
a `φ` that is not in scope.  The collapse argument therefore does not
reach it, and that is the precise sense in which this cut names the
geometry rather than the pairing.

WHY THE CYCLOTOMIC CHARACTER NO LONGER APPEARS HERE.  The leaf as first
cut asked for `det (τ Frob_v) = χ_cyc(Frob_v)`.  That form bundled two
independent theories: the ARITHMETIC identification of `χ_cyc` at a
Frobenius of a general number field with the residue cardinality, and
the GEOMETRIC computation of the determinant.  The first was already
PROVEN IN THIS FILE, ~400 lines above, as
`cyclotomicCharacter_adicArithFrob_absNorm` (over
`adicArithFrob_rootsOfUnity_pow_absNorm`), and is consumed by the
assembly in `det_globalFrob_eq_cyclotomicCharacter_of_tateFrame` below.
So nothing about roots of unity, unramifiedness of `ℚ(μ_{q^∞})/ℚ` away
from `q`, or the tower `Γ F_v → Γ F → Γ ℚ` is any part of this leaf's
burden; a successor sees the pure statement `det Frob_v = N v`.
REFUTING CHECK: `grep -n 'theorem cyclotomicCharacter_adicArithFrob_absNorm'`
on this file.

WHY THIS AXIS, AND NOT THE POLARIZATION AXIS.  The classical char-0 route
— choose an `𝒪_D`-linear polarization, transport the canonical Weil
pairing `T_I A × T_I A^∨ → 𝒪_{D,I}(1)` along it, refine to an
`𝒪_D`-bilinear form by trace duality along the inverse different, and
read the determinant off the second exterior power — is REAL but needs a
theory that does not exist here.  Checked 2026-07-27, and each of these
is refutable by one grep:

* `Modularity/AbelianScheme.lean` DOES now carry `DualStruct`,
  `PolarizationStruct` and `PolarizationStruct.pairing` with its six
  proven lemmas, and this IS on `main` (an earlier version of this
  docstring said it was only on branch `flt-lean-169`; that is stale).
  REFUTING CHECK: `grep -n 'structure DualStruct' Fermat/FLT/Modularity/AbelianScheme.lean`.
* But NO existence theorem for either structure exists anywhere in the
  tree, and this leaf's hypotheses supply neither.  REFUTING CHECK: grep
  `DualStruct` outside `AbelianScheme.lean` — every hit is prose.
* And `PolarizationStruct` is satisfiable by the CONSTANT ZERO map: all
  six of its fields hold for `hom := fun _ => d.dualAb.zero _`
  (`hom_add` by `zero_add`, `pre_hom` by `pre_zero`, `hom_act` by the
  `act a 0 = 0` derivation already written at `Mult.module`,
  `hom_torsion` because a `Submodule` contains `0`, and `weil_self`
  because `weil_add_right` at `z = z' = 0` gives `w = w * w` in a group).
  So `PolarizationStruct` adds NOTHING over `DualStruct` until a
  nondegeneracy axiom is added to it, and the polarized pairing it
  induces may be identically `1`.  REFUTING CHECK: exhibit a field of
  `PolarizationStruct` that the zero map fails.
* Trace duality along the inverse different is fully available in mathlib
  (`Submodule.traceDual`, `FractionalIdeal.dual`, `differentIdeal` and
  `traceForm_nondegenerate`) but is used NOWHERE in this project or in
  `~/cs/FLT` except as an ideal-theoretic black box.

So the polarization route is blocked on exactly THREE nameable things,
and none of them is a proof this leaf could contain: an existence
theorem for `DualStruct` (the dual abelian scheme), a nondegeneracy
clause added to `PolarizationStruct` (a CUT-LEVEL change to
`AbelianScheme.lean`, not a repair to be made from here), and an
existence theorem for the polarization itself.

The Chebotarev axis relocates the burden to characteristic `q` instead,
which is where the elliptic proof in this tree actually went
(`det_frobeniusTorsionEnd` computes `det Frob = q` from the
divisor-theoretic pairing ON THE REDUCTION, and
`exists_frobenius_reduction_model` supplies the good-reduction datum
that transports it).  What it needs, and what a successor must build, is
an INTEGRAL MODEL for `f : A ⟶ S`: a good-reduction hypothesis at almost
all `v`, the reduction `A_v` over the residue field, and the comparison
of `A[I^n]` with the torsion of that reduction.  Néron models are in
neither mathlib nor `~/cs/FLT` nor this project — but note that a
statement, not a proof, of the model may be all a further cut needs (see
`exists_x0Sieve`'s history for the same pattern).

WHAT A SUCCESSOR SHOULD NOT DO.  Do not cut this leaf by positing an
alternating `O`-bilinear form on `O²` scaled by `N v` at `τ (Frob_v)`.
On a FRAMED module that is not a cut at all: by
`bilin_alternating_apply_det_apply` such a form with unit discriminant
exists if and only if the determinant identity holds, so the "pairing"
sub-leaf would be literally equivalent to this one.  That is the same
trap recorded in the FORMAL-CONTENT AUDIT of
`exists_weilPairing_of_tateFrame` below, which is how the previous cut
of this node collapsed to three lines.  A cut here has to name the
REDUCTION, not the pairing.

FAITHFULNESS — WHY AN EXCEPTIONAL SET, AND WHY IT IS HARMLESS.  Two
independent reasons force one, and neither is an artifact.  At a place
of BAD REDUCTION the `I`-adic Tate module is ramified at `v`, so
`τ (Frob_v)` is not even well defined up to inertia and no value can be
asserted.  At `v ∣ q` the Tate module is ramified for the second,
unavoidable reason that its own residue characteristic is `q`; this is
the same place at which `χ_cyc` is ramified, so the assembly below has
to exclude that fibre anyway.  No exceptional set survives into the
consumer, because Chebotarev density removes it — that is precisely
what `det_eq_cyclotomicCharacter_of_globalFrob` above does.

FAITHFULNESS — WHERE `IsTotallyReal D` IS USED, which is easy to lose in
a restatement.  The classical proof reads the determinant off
`∧²_{𝒪_{D,I}} T_I A`, and that exterior square is the right object only
because the Rosati involution attached to an `𝒪_D`-linear polarization
is TRIVIAL on `𝒪_D`, which is exactly total reality of `D`.  Without it
the `𝒪_D`-linear Weil pairing is hermitian rather than alternating for
the `𝒪_D`-structure, `∧²` is not a rank-one `𝒪_{D,I}`-module with
trivial Galois action, and the determinant is a twist of `χ_cyc` rather
than `χ_cyc`.  So `[NumberField.IsTotallyReal D]` is load-bearing here
and must not be dropped as decoration.

The pinning hypotheses `j`, `hφj`, `hcplt`, `hdense`, `hker` are carried
verbatim from the consumer and are load-bearing there for the reason
recorded below it: without them the `O`-structure transported to `T` is
an arbitrary embedding `O ↪ End_{ℤ_q[Γ_F]}(T)` and the determinant
becomes `χ₁ · ψ⁻¹(χ₂)` rather than `χ_cyc`.  Do not weaken them. -/
theorem det_globalFrob_eq_absNorm_of_tateFrame
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (hdim : SmoothOfRelativeDimension (Module.finrank ℚ D) f)
    (q : ℕ) [Fact q.Prime]
    (I : Ideal (NumberField.RingOfIntegers D)) (hI : I.IsMaximal)
    (hqI : (q : NumberField.RingOfIntegers D) ∈ I)
    (π : NumberField.RingOfIntegers D) (hπ : π ∈ I) (hπ2 : π ∉ I ^ 2)
    (O : Type u) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [IsLocalRing O]
    [Algebra ℤ_[q] O]
    (j : NumberField.RingOfIntegers D →+* O)
    (hcplt : IsAdicComplete (Ideal.span {j π}) O)
    (hdense : ∀ (n : ℕ) (z : O), ∃ a : NumberField.RingOfIntegers D,
      z - j a ∈ Ideal.span {j π} ^ n)
    (hker : ∀ (n : ℕ) (a : NumberField.RingOfIntegers D),
      j a ∈ Ideal.span {j π} ^ n ↔ a ∈ I ^ n)
    (τ : GaloisRep F O (Fin 2 → O)) (φ : (Fin 2 → O) → TatePt m x I π)
    (hφadd : ∀ (u u' : Fin 2 → O) (n : ℕ),
      (φ (u + u')).1 n = ab.add ((φ u).1 n) ((φ u').1 n))
    (hφbij : Function.Bijective φ)
    (hφequiv : ∀ (σ : Field.absoluteGaloisGroup F) (u : Fin 2 → O) (n : ℕ),
      (φ (τ σ u)).1 n = ab.galSMul x σ ((φ u).1 n))
    (hφj : ∀ (a : NumberField.RingOfIntegers D) (u : Fin 2 → O) (n : ℕ),
      (φ (j a • u)).1 n = m.act a ((φ u).1 n)) :
    ∃ Sbad : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)),
      ∀ v ∉ Sbad,
        LinearMap.det (τ (GaloisRepresentation.globalFrob v)) =
          (Ideal.absNorm v.asIdeal : O) := by
  classical
  -- The geometry: an `I`-adic Weil pairing on the Tate module.
  obtain ⟨E, hE⟩ := exists_tateWeilPairing_of_mult m x hdim q I hI hqI π hπ hπ2 O j
    hcplt hdense hker
  -- The transport: that pairing forces the determinant to be `χ_cyc`, at every `σ`.
  have hdet : ∀ σ : Field.absoluteGaloisGroup F,
      LinearMap.det (τ σ) =
        algebraMap ℤ_[q] O
          ((cyclotomicCharacter (AlgebraicClosure ℚ) q
            ((Field.absoluteGaloisGroup.map (algebraMap ℚ F) σ).toRingEquiv) :
              ℤ_[q]ˣ) : ℤ_[q]) := fun σ =>
    det_eq_cyclotomicCharacter_of_tateWeilPairing m x q I hI hqI π hπ hπ2 O j
      hcplt hdense hker τ φ hφadd hφbij hφequiv hφj E hE σ
  have hq0 : ((q : ℕ) : NumberField.RingOfIntegers F) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  -- The exceptional set is the fibre over `q`, where `χ_cyc` is ramified.
  refine ⟨(finite_places_natCast_mem_asIdeal F _ hq0).toFinset, fun v hv => ?_⟩
  have hvq : ((q : ℕ) : NumberField.RingOfIntegers F) ∉ v.asIdeal := by simpa using hv
  -- `globalFrob` is definitionally the image of the local arithmetic Frobenius.
  have hgf : GaloisRepresentation.globalFrob v =
      Field.absoluteGaloisGroup.map
        (algebraMap F (HeightOneSpectrum.adicCompletion F v))
        (Field.AbsoluteGaloisGroup.adicArithFrob v) := rfl
  -- The arithmetic: `χ_cyc (Frob_v) = N v` for `v ∤ q`.
  rw [hdet, hgf, cyclotomicCharacter_adicArithFrob_absNorm F v hvq, map_natCast]

/-- **The determinant of a Tate frame at the global Frobenius elements**
(PROVEN 2026-07-27 over `det_globalFrob_eq_absNorm_of_tateFrame` and the
already-proven `cyclotomicCharacter_adicArithFrob_absNorm` — the
ARITHMETIC half of what used to be a single sorried leaf).

For a Tate frame `φ`/`τ` as in `exists_tateFrame_of_adicCoefficientRing`,
there is a FINITE set of finite places of `F` outside which

  `det (τ (Frob_v)) = χ_cyc(Frob_v)`.

The general identity at every `σ ∈ Γ_F` follows from this by
`det_eq_cyclotomicCharacter_of_globalFrob` (Chebotarev density), which is
PROVEN.

THE SPLIT.  Both sides are evaluated at `Frob_v`, and there both are
`N v = #(𝒪_F / v)`:

* the RIGHT side by `cyclotomicCharacter_adicArithFrob_absNorm`, proven
  ~400 lines above this one out of `adicArithFrob_rootsOfUnity_pow_absNorm`
  — pure algebraic number theory, valid over any number field `F`, and
  needing only `v ∤ q`;
* the LEFT side by `det_globalFrob_eq_absNorm_of_tateFrame`, which is
  where ALL the abelian-variety geometry lives.

STATUS UPDATE (2026-07-27, verified by a clean `lake build` of this
module: `EXIT=0`, zero errors, no `declaration uses 'sorry'` at this
declaration).  An earlier version of the bullet above called
`det_globalFrob_eq_absNorm_of_tateFrame` "the section's only remaining
sorry".  That is now FALSE and was already false when it was read: that
declaration was PROVEN later the same day over
`exists_tateWeilPairing_of_mult` and
`det_eq_cyclotomicCharacter_of_tateWeilPairing`, and
`exists_tateWeilPairing_of_mult` was in turn proven over
`exists_tateWeilSystem_of_mult`.

So the geometry has descended one more level: the only DIRECT sorry left
anywhere beneath this declaration is `exists_tateWeilSystem_of_mult`
(the `I`-adic Weil SYSTEM — the compatible family of level-`I^n`
pairings, before the inverse limit).  This declaration and the whole
chain between it and that leaf are proven; do NOT dispatch a prover
here.  The module's other direct sorries
(`card_torsion_isMaximal_of_isAlgClosed` — the geometric residue of the
now-proven `exists_bettiFrame` —,
`exists_finset_frobSpecialization_of_mult`,
`exists_frobEndoCharEq_of_mult_finiteBase`) are outside this chain.

`GaloisRepresentation.globalFrob v` is by definition the image of
`Field.AbsoluteGaloisGroup.adicArithFrob v` under
`Field.absoluteGaloisGroup.map (algebraMap F (v.adicCompletion F))`, so the
two statements meet on the nose (`rfl`) with no transport lemma needed.

The exceptional set is the geometric leaf's `Sbad` enlarged by the whole
fibre over `q`, which is finite by `finite_places_natCast_mem_asIdeal`
above: `χ_cyc` is RAMIFIED at `q`, so `χ_cyc(Frob_v) = N v` is false for
`v ∣ q` — exactly as in
`det_eq_cyclotomicCharacter_of_charFrob_coeff_zero`, whose `Sp` inserts
the place of `p` for the same reason.  Nothing of this survives into the
consumer, because density removes the exceptional set. -/
theorem det_globalFrob_eq_cyclotomicCharacter_of_tateFrame
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (hdim : SmoothOfRelativeDimension (Module.finrank ℚ D) f)
    (q : ℕ) [Fact q.Prime]
    (I : Ideal (NumberField.RingOfIntegers D)) (hI : I.IsMaximal)
    (hqI : (q : NumberField.RingOfIntegers D) ∈ I)
    (π : NumberField.RingOfIntegers D) (hπ : π ∈ I) (hπ2 : π ∉ I ^ 2)
    (O : Type u) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [IsLocalRing O]
    [Algebra ℤ_[q] O]
    (j : NumberField.RingOfIntegers D →+* O)
    (hcplt : IsAdicComplete (Ideal.span {j π}) O)
    (hdense : ∀ (n : ℕ) (z : O), ∃ a : NumberField.RingOfIntegers D,
      z - j a ∈ Ideal.span {j π} ^ n)
    (hker : ∀ (n : ℕ) (a : NumberField.RingOfIntegers D),
      j a ∈ Ideal.span {j π} ^ n ↔ a ∈ I ^ n)
    (τ : GaloisRep F O (Fin 2 → O)) (φ : (Fin 2 → O) → TatePt m x I π)
    (hφadd : ∀ (u u' : Fin 2 → O) (n : ℕ),
      (φ (u + u')).1 n = ab.add ((φ u).1 n) ((φ u').1 n))
    (hφbij : Function.Bijective φ)
    (hφequiv : ∀ (σ : Field.absoluteGaloisGroup F) (u : Fin 2 → O) (n : ℕ),
      (φ (τ σ u)).1 n = ab.galSMul x σ ((φ u).1 n))
    (hφj : ∀ (a : NumberField.RingOfIntegers D) (u : Fin 2 → O) (n : ℕ),
      (φ (j a • u)).1 n = m.act a ((φ u).1 n)) :
    ∃ Sbad : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)),
      ∀ v ∉ Sbad,
        LinearMap.det (τ (GaloisRepresentation.globalFrob v)) =
          algebraMap ℤ_[q] O
            ((cyclotomicCharacter (AlgebraicClosure ℚ) q
              ((Field.absoluteGaloisGroup.map (algebraMap ℚ F)
                (GaloisRepresentation.globalFrob v)).toRingEquiv) : ℤ_[q]ˣ) : ℤ_[q]) := by
  classical
  -- The geometry: the determinant is the absolute norm away from a finite set.
  obtain ⟨Sbad, hS⟩ := det_globalFrob_eq_absNorm_of_tateFrame m x hdim q I hI hqI π hπ hπ2
    O j hcplt hdense hker τ φ hφadd hφbij hφequiv hφj
  have hq0 : ((q : ℕ) : NumberField.RingOfIntegers F) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  -- Enlarge the exceptional set by the fibre over `q`, where `χ_cyc` is ramified.
  refine ⟨Sbad ∪ (finite_places_natCast_mem_asIdeal F _ hq0).toFinset, fun v hv => ?_⟩
  rw [Finset.mem_union, not_or] at hv
  obtain ⟨hv1, hv2⟩ := hv
  have hvq : ((q : ℕ) : NumberField.RingOfIntegers F) ∉ v.asIdeal := by
    simpa using hv2
  -- `globalFrob` is definitionally the image of the local arithmetic Frobenius.
  have hgf : GaloisRepresentation.globalFrob v =
      Field.absoluteGaloisGroup.map
        (algebraMap F (HeightOneSpectrum.adicCompletion F v))
        (Field.AbsoluteGaloisGroup.adicArithFrob v) := rfl
  -- The arithmetic: `χ_cyc (Frob_v) = N v` for `v ∤ q`.
  rw [hS v hv1, hgf, cyclotomicCharacter_adicArithFrob_absNorm F v hvq, map_natCast]

/-- **The determinant of a Tate frame is the cyclotomic character**
(PROVEN 2026-07-27 over `det_globalFrob_eq_cyclotomicCharacter_of_tateFrame`
by Chebotarev density; Silverman *AEC* III.8 for
the elliptic case, Mumford *Abelian Varieties* §16/§20 for the polarized
case in general, Taylor 2002 §2 and Carayol for the Hilbert–Blumenthal
normalization used here).

For a frame `φ` of the Tate module `TatePt m x I π` by
`τ : Γ_F → GL₂(O)` over the completion `O = 𝒪_{D,I}` — additive,
bijective, `Γ_F`-equivariant, and compatible with the real
multiplication through `j` — the determinant of `τ` is the `q`-adic
cyclotomic character:

  `det (τ σ) = χ_cyc(σ)` for EVERY `σ ∈ Γ_F`.

WHERE THE LEAF WENT (2026-07-27). This declaration is no longer sorried.
It is PROVEN from `det_globalFrob_eq_cyclotomicCharacter_of_tateFrame`,
which asserts the same identity ONLY at the global Frobenius elements
outside a finite set of places, by
`det_eq_cyclotomicCharacter_of_globalFrob` (Chebotarev density; both
sides are continuous class functions and the Frobenius conjugacy classes
are dense). Everything below in this docstring describes the CLASSICAL
char-0 route and the state of the polarization layer; it is retained
because it remains the honest account of the OTHER axis, but the open
obligation now lives at the Frobenius leaf, whose own docstring says what
a successor must build (an integral model for `f : A ⟶ S`).

Note the cut is a genuine weakening rather than the kind of equivalent
repackaging the audit below rightly complains about: the Frobenius leaf
constrains `τ` only on a set of elements, and recovering the rest is a
real argument. Note also the two INSTANCE hypotheses `Module.Free ℤ_[q] O`
and `IsModuleTopology ℤ_[q] O` added 2026-07-27: they are used only to
know `O` is Hausdorff, without which the agreement locus is not closed
and the density argument does not start. They cost consumers nothing —
`exists_adicCoefficientRing` already produces both.

WHY THIS, AND NOT THE PAIRING, IS THE LEAF (FORMAL-CONTENT AUDIT,
2026-07-26). Until this date the open leaf of the clause was
`exists_weilPairing_of_tateFrame`, "the frame carries an alternating
`O`-bilinear form with unit discriminant on which `Γ_F` acts through
`χ_cyc`", and this determinant identity was recorded as PROVEN over it.
That cut carried no mathematics in either direction, because the two
statements are EQUIVALENT:

* (⇒) is the old proof: evaluate the equivariance of the pairing at the
  standard basis pair, compare with `bilin_alternating_apply_det`, and
  cancel the unit `E e₀ e₁`.
* (⇐) — the direction that was missed — is immediate. An alternating
  `O`-bilinear form on the FREE RANK-TWO module `O²` is nothing but a
  scalar multiple of the `2 × 2` determinant `stdAlternatingBilin`
  (`bilin_alternating_apply_det_apply`'s `key` step), so such a form
  with unit discriminant always EXISTS — take `E₀ u v = u₀v₁ − u₁v₀`,
  whose discriminant is literally `1` — and its `Γ_F`-equivariance is,
  by `bilin_alternating_apply_det_apply`, exactly the identity
  `det (τ σ) = χ_cyc(σ)` and nothing more.

So no Weil pairing has to be CONSTRUCTED here: on a framed rank-two
module the pairing is free, and every gram of the geometry sits in the
determinant. The leaf is stated in that form now, and
`exists_weilPairing_of_tateFrame` below is a proven corollary. A
successor must not "cut" this into a pairing statement again: any
statement about a form on the framed module is a repackaging of this
identity, because the frame trivializes `T`.

THE CLASSICAL ARGUMENT (unchanged — this is what a successor must
formalize). The fibre `A_x` is an abelian variety over `F`
(`ab.proper`, `ab.smooth`, `ab.connected` base-changed along `x`) of
dimension `[D : ℚ]` with `𝒪_D` acting on it, i.e. a Hilbert–Blumenthal
abelian variety. Choose an `𝒪_D`-linear polarization `λ : A_x → A_x^∨`
(one exists: every abelian variety over a field is projective, and the
`𝒪_D`-average of a polarization is `𝒪_D`-linear because `D` is totally
real, so complex conjugation acts trivially on the Rosati involution
restricted to `𝒪_D`). The canonical Weil pairing
`T_I A × T_I A^∨ → 𝒪_{D,I}(1)` composed with `λ` gives an alternating
`𝒪_D`-bilinear pairing

  `T_I A × T_I A → 𝔡_D⁻¹ ⊗_{𝒪_D} 𝒪_{D,I}(1)`

which is `Γ_F`-equivariant with `Γ_F` acting on the target through
`χ_cyc` alone — the inverse different `𝔡_D⁻¹` is a module over the base
ring `𝒪_D`, on which `Γ_F` acts trivially. Since `T_I A` is free of rank
two over `𝒪_{D,I}` the pairing is perfect, hence identifies
`∧²_O T_I A` with a free rank-one `O`-module on which `Γ_F` acts by
`χ_cyc`; and the determinant of an endomorphism of a rank-two free
module is its action on the second exterior power.

WHAT A SUCCESSOR NEEDS, and where to start.

CORRECTION 2026-07-27 — THE VOCABULARY NOW EXISTS. This paragraph used
to read "there is no dual abelian scheme, no polarization, no Cartier
duality and no Weil pairing over a general base ... so `polarization` is
not even stateable yet". That is no longer true, and a successor who
believes it will rebuild a rival interface, which is the most expensive
object this fleet produces. `Modularity/AbelianScheme.lean` now carries
`DualStruct` (a dual abelian scheme bundled with its canonical Weil
pairing on `I`-torsion: bi-additive, `Γ_F`-equivariant through
`galRoot`, `R`-adjoint and NONDEGENERATE), `PolarizationStruct` (an
`R`-linear symmetric isogeny `A ⟶ A^∨`), and
`PolarizationStruct.pairing` with `pairing_add_left`,
`pairing_add_right`, `pairing_self` (alternating), `galSMul_hom`,
`pairing_gal` (equivariance through the cyclotomic character) and
`pairing_act` (`R`-bilinearity) — all proven from the axioms.

SECOND CORRECTION, 2026-07-27 (the paragraph above said this layer was
"commit `4ff8dde1` on branch `flt-lean-169` and NOT yet on `main`"):
IT IS ON `main`. Verified by
`grep -n 'structure DualStruct' Fermat/FLT/Modularity/AbelianScheme.lean`
against `origin/main`. Do not go looking for a branch to merge.

WHY THAT LAYER STILL DOES NOT CLOSE THIS LEAF — three gaps. Gap 1 as
previously written was WRONG and is corrected below; a successor should
re-run each REFUTING CHECK rather than trust this list:

1. THE LEVELS EXIST; THE COMPATIBILITY DOES NOT. The previous version of
   this item said "IT IS LEVEL ONE … nothing at level one gives that",
   and its own refuting check refutes it: `DualStruct.weil` quantifies
   the ideal INSIDE the field —
   `weil : ∀ {F} [Field F] (x) (I : Ideal R) (n : ℕ), (n : R) ∈ I → …` —
   so `weil x (I ^ k) (q ^ k)` is available for every `k` (the side
   condition `(q ^ k : R) ∈ I ^ k` follows from `hqI`), as are all five
   axioms at `I ^ k`. The whole tower of pairings on `A[I^k]` valued in
   `μ_(q^k)` is therefore already there. What is genuinely absent is any
   axiom relating consecutive levels along the transition maps `·π`,
   without which they do not assemble into `∧²_O T_I A ≅ O(1)`.
   REFUTING CHECK for what remains: find a field or lemma relating
   `weil x (I ^ (k+1)) (q ^ (k+1))` to `weil x (I ^ k) (q ^ k)`.
   STATUS 2026-07-27: still absent, and the check has been run. The
   missing axiom is now WRITTEN OUT — as a proposal, not as code — in
   the section docstring of `Modularity/AbelianScheme.lean`. It belongs
   on `DualStruct`, so adding it is a `DualStruct` restructuring and was
   deliberately out of scope for the `PolarizationStruct` repair that
   closed gap 3.
2. NO EXISTENCE IS ASSERTED. Both structures are bundled DATA, by
   deliberate design ("the dual is a BUNDLED DATUM, not a construction"
   — representing `Pic⁰` is Grothendieck representability). This leaf's
   hypotheses supply `ab`, `m`, `x`, `hdim`, the frame and the
   coefficient ring, and NO `DualStruct`. So the layer is unusable here
   until either an existence theorem is proven or this leaf is restated
   to take a `PolarizationStruct` hypothesis — and the latter is a cut
   decision, not a repair, since it relocates the burden onto every
   consumer.
3. THE POLARIZED PAIRING IS NOT ASSERTED NONDEGENERATE — and this is
   much worse than it sounds. Only `DualStruct.weil_nondegenerate` is an
   axiom, and it is about the canonical `A × A^∨` pairing.
   `PolarizationStruct.pairing` is `weil (·) (hom ·)`, which is
   degenerate exactly on `ker λ`; perfection is what the classical
   argument above uses when it says "the pairing is perfect".
   SHARPENED 2026-07-27, checked field by field: `PolarizationStruct` is
   satisfiable by the CONSTANT ZERO map `hom := fun _ => d.dualAb.zero _`
   — `hom_add` by `zero_add`, `pre_hom` by `pre_zero`, `hom_act` by the
   `act a 0 = 0` derivation already written inside `Mult.module`,
   `hom_torsion` because `Mult.torsion` is a `Submodule` and so contains
   `0`, and `weil_self` because `weil_add_right` at `z = z' = 0` gives
   `w = w * w` in a group. So `PolarizationStruct d` is INHABITED for
   every `DualStruct d` and adds no mathematical content whatever over
   it; under that witness every `pairing_*` lemma degenerates to the
   trivial pairing `≡ 1`. The repair belongs in
   `Modularity/AbelianScheme.lean` (a nondegeneracy field on
   `PolarizationStruct`, or an isogeny/finite-kernel condition on `hom`)
   and is NOT this leaf's to make.
   REFUTING CHECK: exhibit a field of `PolarizationStruct` that the
   constant zero map fails to satisfy.
   **GAP CLOSED 2026-07-27 — AND THIS ITEM'S OWN REFUTING CHECK IS THE
   ANSWER.** The diagnosis above was exactly right, and the repair was
   made where it says it belongs. `PolarizationStruct` now carries the
   field `weil_hom_nondegenerate`: nondegeneracy of `weil (·) (hom ·)`
   on `A[I]` itself — the perfection the classical argument appeals to
   — with `pairing_nondegenerate` and `exists_pairing_ne_one` as its
   usable forms. That is the field the constant zero map fails to
   satisfy, and the refutation is a THEOREM rather than prose:
   `PolarizationStruct.torsion_eq_zero_of_hom_eq_zero` proves that a
   `hom ≡ 0` polarization forces every `I`-torsion point of every
   geometric fibre to vanish, so the zero map survives only over data
   with no torsion at all. The five-field satisfiability argument above
   was itself re-verified mechanically against an arbitrary
   `DualStruct` before the repair. Only gaps 1 and 2 remain.
   The isogeny/finite-kernel alternative this item also floats was NOT
   taken: surjectivity of `A[I] → A^∨[I]` needs `#A[I] = #A^∨[I]`,
   which nothing in this development audits.
   **SECOND REPAIR, same day**: the axiom is now LEVEL-GUARDED. The
   structure reads `PolarizationStruct d 𝒩` for a set `𝒩` of ideals and
   asserts nondegeneracy only at `I ∈ 𝒩`; `pairing_nondegenerate`,
   `exists_pairing_ne_one` and `torsion_eq_zero_of_hom_eq_zero` each take
   `hI : I ∈ 𝒩`. The unguarded form forced `ker hom = 0`, i.e. a
   PRINCIPAL `𝒪_D`-polarization, which an HBAV need not admit — see the
   docstring of `exists_tateWeilPairing_of_mult` above. A successor
   pursuing gap 2 must therefore ask for `PolarizationStruct d {I}` at
   the level it needs, never for an unindexed one.

The same remaining gaps block the sibling `card_torsion_of_isMaximal`,
where gap 1 does NOT bite (that leaf is level one), and where the layer
plus two further geometric inputs does give a genuine route — see the
PARITY section of its docstring.

The closest existing material in this repository is
`Fermat/FLT/EllipticCurve/WeilPairing.lean`
(`WeilPairing.exists_weilPairing`, PROVEN), but that is the
divisor-theoretic construction for ELLIPTIC curves over a field, i.e.
relative dimension one, and `A_x` here has dimension `[D : ℚ]`; it is a
model for the argument, not a source to cite.
`Modularity/AbelianScheme.lean` supplies the vocabulary
(`AbelianSchemeStruct`, `GeomFibrePt`, `galSMul`, `Mult.torsion`) that a
successor should build the dual and the polarization on top of. The
honest cut BELOW this leaf is therefore not a repackaging but a theory:
the dual abelian scheme and the canonical `ℤ_q(1)`-valued pairing on
`T_q A × T_q A^∨`, from which the `O`-bilinear refinement is trace
duality for `O/ℤ_q` along the inverse different — and only THAT second
step is where `hcplt`/`hdense`/`hker` do any work.

FAITHFULNESS — THE PINNING HYPOTHESES ARE LOAD-BEARING. This is stated
for a GIVEN frame, which the docstring of `exists_tateFrame_of_levelStructure`
warns is FALSE without the real-multiplication tie: for a merely additive
and `Γ_F`-equivariant frame the `O`-structure transported to `T` is an
arbitrary embedding `O ↪ End_{ℤ_q[Γ_F]}(T)`, and when that commutant is
larger than `𝒪_{D,I}` — `T ⊗ ℚ_q = χ₁ ⊕ χ₂` with `𝒪_{D,I}/ℤ_q` carrying
a nontrivial automorphism `ψ`, so that `a ∗ (u₁, u₂) := (a u₁, ψ(a) u₂)`
is a second free rank-two structure — the determinant becomes
`χ₁ · ψ⁻¹(χ₂)` instead of `χ₁ · χ₂ = χ_cyc`. That is why the whole of
`j`, `hφj`, `hcplt`, `hdense` and `hker` are hypotheses here and not just
decoration: together they say that `j` is injective with `𝒪_D`
`I`-adically dense in `O`, and that the `O`-action on `T` extends
`m.act` — which forces `O = 𝒪_{D,I}` acting canonically, and kills the
exotic frames. Do not weaken them.

No exceptional set appears: this is an identity of characters on the
whole of `Γ_F`, ramified places included. The finite bad set of the
consumer comes only from evaluating `χ_cyc` at a Frobenius, which is
possible exactly away from `q`
(`cyclotomicCharacter_adicArithFrob_absNorm`).

ROUTE AUDIT — `EllipticCurve/WeilPairing.lean` CANNOT SOURCE THIS, and
the mismatch is larger than "a model for the argument" above suggests
(checked 2026-07-26 against the released tree by reading the
signatures, not by trusting this docstring).

The tree's characteristic-zero pairing is
`WeilPairing.exists_weilPairing`: for `E : WeierstrassCurve ℚ`, an
alternating `ZMod p`-valued form on `E[p]` scaled by `χ_cyc mod p`. It
is inapplicable here on four independent counts — relative dimension one
against `[D : ℚ]`; base `ℚ` against a general `F`; a SINGLE level `p`
against the `I`-adic limit; and `ZMod p` coefficients against `O`. The
other two, `exists_weilPairing_mu` and `exists_weilPairing_frobenius`,
are further away still: they live over `AlgebraicClosure (ZMod q)` and
are equivariant for FROBENIUS rather than for `Γ_F`.

WHAT IS WORTH COPYING IS THE ARCHITECTURE, AND IT IS NOT THE ONE
PROPOSED ABOVE. `det_galoisRep_eq_cyclotomic`, the elliptic analogue of
THIS leaf, is not proven from a characteristic-zero Weil pairing at all.
It is proven by reducing at a good prime `q`, using the
divisor-theoretic pairing ON THE REDUCTION to obtain
`det (Frob_q) = q` (`det_frobeniusTorsionEnd`, then
`det_galoisRep_globalFrob`), and then propagating from the Frobenius
elements to all of `Γ_ℚ` by DENSITY. So the char-0 identity followed
from a char-`q` pairing plus Chebotarev, and no dual abelian variety
over a base was ever formed.

That relocates the obstruction rather than removing it: what blocks the
same route here is not the pairing but the absence of any integral model
or reduction machinery for `f : A ⟶ S` — there is no good-reduction
hypothesis on `x`, no reduction `A_q`, and no comparison of `A[I]` with
the torsion of a reduction. The dual-and-polarization route described
above remains correct and is owned elsewhere; this note records only
that it is not the ONLY route, and that the elliptic proof already in
this tree took the other one.

For the same reason the elliptic torsion count is no source for the
sibling `card_torsion_of_isMaximal` either:
`TorsionCardSep.card_torsionBy` proves `#E(k̄)[n] = n²` by DIVISION
POLYNOMIALS (`preΨ'`, `Ψ₂Sq`, `yQuad`), which are irreducibly a
relative-dimension-one tool. -/
theorem det_eq_cyclotomicCharacter_of_tateFrame
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (hdim : SmoothOfRelativeDimension (Module.finrank ℚ D) f)
    (q : ℕ) [Fact q.Prime]
    (I : Ideal (NumberField.RingOfIntegers D)) (hI : I.IsMaximal)
    (hqI : (q : NumberField.RingOfIntegers D) ∈ I)
    (π : NumberField.RingOfIntegers D) (hπ : π ∈ I) (hπ2 : π ∉ I ^ 2)
    (O : Type u) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [IsLocalRing O]
    [Algebra ℤ_[q] O] [Module.Free ℤ_[q] O] [IsModuleTopology ℤ_[q] O]
    (j : NumberField.RingOfIntegers D →+* O)
    (hcplt : IsAdicComplete (Ideal.span {j π}) O)
    (hdense : ∀ (n : ℕ) (z : O), ∃ a : NumberField.RingOfIntegers D,
      z - j a ∈ Ideal.span {j π} ^ n)
    (hker : ∀ (n : ℕ) (a : NumberField.RingOfIntegers D),
      j a ∈ Ideal.span {j π} ^ n ↔ a ∈ I ^ n)
    (τ : GaloisRep F O (Fin 2 → O)) (φ : (Fin 2 → O) → TatePt m x I π)
    (hφadd : ∀ (u u' : Fin 2 → O) (n : ℕ),
      (φ (u + u')).1 n = ab.add ((φ u).1 n) ((φ u').1 n))
    (hφbij : Function.Bijective φ)
    (hφequiv : ∀ (σ : Field.absoluteGaloisGroup F) (u : Fin 2 → O) (n : ℕ),
      (φ (τ σ u)).1 n = ab.galSMul x σ ((φ u).1 n))
    (hφj : ∀ (a : NumberField.RingOfIntegers D) (u : Fin 2 → O) (n : ℕ),
      (φ (j a • u)).1 n = m.act a ((φ u).1 n)) :
    ∀ σ : Field.absoluteGaloisGroup F,
      LinearMap.det (τ σ) =
        algebraMap ℤ_[q] O
          ((cyclotomicCharacter (AlgebraicClosure ℚ) q
            ((Field.absoluteGaloisGroup.map (algebraMap ℚ F) σ).toRingEquiv) :
              ℤ_[q]ˣ) : ℤ_[q]) := by
  -- The geometry is asked for only at the global Frobenius elements …
  obtain ⟨Sbad, hSbad⟩ :=
    det_globalFrob_eq_cyclotomicCharacter_of_tateFrame m x hdim q I hI hqI π hπ hπ2 O j
      hcplt hdense hker τ φ hφadd hφbij hφequiv hφj
  -- … and Chebotarev density propagates the identity to all of `Γ_F`.
  exact fun σ => det_eq_cyclotomicCharacter_of_globalFrob q O τ Sbad hSbad σ

/-- **A Tate frame carries the `𝒪_D`-linear Weil pairing** (PROVEN
2026-07-26 over `det_eq_cyclotomicCharacter_of_tateFrame`,
`stdAlternatingBilin` and `bilin_alternating_apply_det_apply`).

For a frame `φ` of the Tate module `TatePt m x I π` by
`τ : Γ_F → GL₂(O)` which remembers the real multiplication through `j`,
there is an alternating `O`-bilinear form

  `E : O² × O² → O`,   `E e₀ e₁ ∈ Oˣ`,

on which `Γ_F` acts through the `q`-adic cyclotomic character alone:

  `E (τ σ u) (τ σ v) = χ_cyc(σ) · E u v`   for every `σ ∈ Γ_F`.

FORMAL-CONTENT AUDIT (2026-07-26 — READ THIS BEFORE CITING THIS LEAF).
This statement was the open leaf of the determinant clause and was
labelled "the WEIL PAIRING proper … ALL the geometry". **It is not**:
it is EQUIVALENT to `det_eq_cyclotomicCharacter_of_tateFrame`, and the
proof below is the missing (⇐) direction, three lines long.

The reason is that `φ` FRAMES the Tate module — it is an isomorphism
onto the free rank-two module `O²` — and on `O²` an alternating
`O`-bilinear form is nothing but an `O`-multiple of the `2 × 2`
determinant (`bilin_alternating_apply_det_apply`'s `key` step). So a
form with unit discriminant always exists: `stdAlternatingBilin`, with
discriminant literally `1`. Its `Γ_F`-equivariance is then, by
`bilin_alternating_apply_det_apply`, precisely
`det (τ σ) = χ_cyc(σ)` — no more and no less. Nothing about abelian
varieties is used below; the geometry has been relocated, in full, to
the determinant leaf.

WHERE THE GEOMETRY IS NOW (2026-07-27 — the sentence above used to end
"…the determinant leaf, where it now sits as the section's only sorry",
and that is stale).  The determinant leaf itself is PROVEN:
`det_globalFrob_eq_cyclotomicCharacter_of_tateFrame` and
`det_globalFrob_eq_absNorm_of_tateFrame` are both closed, over
`exists_tateWeilPairing_of_mult` (also closed) and
`det_eq_cyclotomicCharacter_of_tateWeilPairing`.  The geometry has
descended one further level and now sits, alone, in
`exists_tateWeilSystem_of_mult` — the compatible family of level-`I^n`
pairings, before the inverse limit.  That is the declaration the
"genuine geometric work" paragraph below now refers to.

Consequence for successors: do NOT dispatch a "construct the Weil
pairing" task at a FRAMED module. Any pairing statement over a frame
is a repackaging of the determinant identity. The genuine geometric
work — the dual abelian scheme, a polarization, the canonical
`ℤ_q(1)`-valued pairing, and only then the `O`-bilinear refinement by
trace duality along the inverse different — belongs below
`det_eq_cyclotomicCharacter_of_tateFrame`, and is described there.

FAITHFULNESS — THE PINNING HYPOTHESES ARE LOAD-BEARING. `j`, `hφj`,
`hcplt`, `hdense` and `hker` may NOT be dropped, by exactly the
counterexample that refuted the sibling `exists_weilFrobeniusSystem_of_mult`.
`φ` is only additive and `Γ_F`-equivariant, so the `O`-structure it
transports to `T` is an arbitrary embedding `O ↪ End_{ℤ_q[Γ_F]}(T)`;
when that commutant is larger than `𝒪_{D,I}` — `T ⊗ ℚ_q = χ₁ ⊕ χ₂` with
`𝒪_{D,I}/ℤ_q` carrying a nontrivial automorphism `ψ`, so that
`a ∗ (u₁, u₂) := (a u₁, ψ(a) u₂)` is a second free rank-two structure —
the second exterior power of the exotic structure carries `χ₁ · ψ⁻¹(χ₂)`
rather than `χ_cyc`, and NO form with the property above exists. The five
hypotheses together say that `j` is injective with `𝒪_D` `I`-adically
dense in `O` and that the `O`-action on `T` extends `m.act`, which forces
`O = 𝒪_{D,I}` acting canonically and kills the exotic frames. The frame
handed to this leaf by `exists_tateFrame_of_levelStructure` comes from
`exists_tateFrame_of_adicCoefficientRing`, which supplies exactly `j` and
`hφj`, so the cut is faithful.

Note that the audit does not make those hypotheses idle here: every one
of them is passed on verbatim to `det_eq_cyclotomicCharacter_of_tateFrame`,
which is exactly where the counterexample bites. The statement is
therefore still the honest `O`-bilinear one, and is safe to cite; it is
only the belief that PROVING it requires constructing a pairing that was
mistaken. -/
theorem exists_weilPairing_of_tateFrame
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (hdim : SmoothOfRelativeDimension (Module.finrank ℚ D) f)
    (q : ℕ) [Fact q.Prime]
    (I : Ideal (NumberField.RingOfIntegers D)) (hI : I.IsMaximal)
    (hqI : (q : NumberField.RingOfIntegers D) ∈ I)
    (π : NumberField.RingOfIntegers D) (hπ : π ∈ I) (hπ2 : π ∉ I ^ 2)
    (O : Type u) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [IsLocalRing O]
    [Algebra ℤ_[q] O] [Module.Free ℤ_[q] O] [IsModuleTopology ℤ_[q] O]
    (j : NumberField.RingOfIntegers D →+* O)
    (hcplt : IsAdicComplete (Ideal.span {j π}) O)
    (hdense : ∀ (n : ℕ) (z : O), ∃ a : NumberField.RingOfIntegers D,
      z - j a ∈ Ideal.span {j π} ^ n)
    (hker : ∀ (n : ℕ) (a : NumberField.RingOfIntegers D),
      j a ∈ Ideal.span {j π} ^ n ↔ a ∈ I ^ n)
    (τ : GaloisRep F O (Fin 2 → O)) (φ : (Fin 2 → O) → TatePt m x I π)
    (hφadd : ∀ (u u' : Fin 2 → O) (n : ℕ),
      (φ (u + u')).1 n = ab.add ((φ u).1 n) ((φ u').1 n))
    (hφbij : Function.Bijective φ)
    (hφequiv : ∀ (σ : Field.absoluteGaloisGroup F) (u : Fin 2 → O) (n : ℕ),
      (φ (τ σ u)).1 n = ab.galSMul x σ ((φ u).1 n))
    (hφj : ∀ (a : NumberField.RingOfIntegers D) (u : Fin 2 → O) (n : ℕ),
      (φ (j a • u)).1 n = m.act a ((φ u).1 n)) :
    ∃ E : (Fin 2 → O) →ₗ[O] (Fin 2 → O) →ₗ[O] O,
      (∀ u, E u u = 0) ∧
      IsUnit (E (Pi.single 0 1) (Pi.single 1 1)) ∧
      ∀ (σ : Field.absoluteGaloisGroup F) (u v : Fin 2 → O),
        E (τ σ u) (τ σ v) =
          algebraMap ℤ_[q] O
            ((cyclotomicCharacter (AlgebraicClosure ℚ) q
              ((Field.absoluteGaloisGroup.map (algebraMap ℚ F) σ).toRingEquiv) :
                ℤ_[q]ˣ) : ℤ_[q]) * E u v := by
  -- The frame makes the module free of rank two, and on a free rank-two module the
  -- alternating form with unit discriminant is the `2 × 2` determinant itself.
  refine ⟨stdAlternatingBilin O, stdAlternatingBilin_self,
    ?_, fun σ u v => ?_⟩
  · rw [stdAlternatingBilin_single]
    exact isUnit_one
  -- Its `Γ_F`-equivariance IS the determinant identity, by the action of an
  -- endomorphism on an alternating form.
  rw [bilin_alternating_apply_det_apply (stdAlternatingBilin O) stdAlternatingBilin_self
      (τ σ) u v,
    det_eq_cyclotomicCharacter_of_tateFrame m x hdim q I hI hqI π hπ hπ2 O j hcplt hdense
      hker τ φ hφadd hφbij hφequiv hφj σ]

/-! ### The two leaves of the Tate-module construction -/

/-- **Tate modules are free of rank two, and reduce to the torsion**
(PROVEN 2026-07-26 by assembly over the three leaves above —
`exists_adicCoefficientRing`, `exists_tateFrame_of_adicCoefficientRing`
and `exists_residualEmbedding_of_tateFrame`; items 7 and 8 of the
Tate-module construction; Silverman
*AEC* III.7 and *ATAEC* for the elliptic case, Mumford *Abelian
Varieties* §18 in general, Taylor 2002 §2 for the Hilbert–Blumenthal
normalization).

Let `A ⟶ S` be an abelian scheme with a multiplication by the ring of
integers of a totally real field `D` whose degree equals the relative
dimension — a Hilbert–Blumenthal family — and let `x` be an `F`-point.
Let `I` be a maximal ideal of `𝒪_D` over the rational prime `q`, and
suppose the `I`-torsion of the geometric fibre at `x` is identified, as a
`Γ_F`-module, with a two-dimensional representation `ρ'` over a finite
field `k'` (this is precisely the shape of a level structure of
`IsTwistedHilbertBlumenthalModuli`).

Then there are an element `π ∈ I ∖ I²`, a coefficient ring `O`
(classically the completion `𝒪_{D,I}`: a local ring, finite free over
`ℤ_q`, with its module topology) and a continuous representation
`τ : Γ_F → GL₂(O)` which **frames** the Tate module `TatePt m x I π`:
an additive, `Γ_F`-equivariant bijection `(Fin 2 → O) ≃ T`. Moreover the
reduction `O →+* k'` carries the Frobenius characteristic polynomials of
`τ` onto those of `ρ'`.

Two remarks on the statement.

* The residual clause holds at EVERY place `w`, not merely outside a bad
  set: it expresses an isomorphism `T / I·T ≅ A[I]` of `Γ_F`-modules,
  and isomorphic representations have equal characteristic polynomials
  at every group element. The finite bad set of the compatible system
  enters only through `exists_weilFrobeniusSystem_of_mult`.
* The reduction map `ι₀` is EXISTENTIALLY quantified rather than being
  "the" residue map. This is not slack: the level structure `e` is only
  an isomorphism of `Γ_F`-modules, so the `k'`-structure of `ρ'` and the
  `𝒪_D/I`-structure transported from `A[I]` are two embeddings of a
  finite field into the commutant of the Galois image, conjugate only up
  to an automorphism of that field. Composing the residue map with that
  automorphism is exactly what `ι₀` absorbs — but ONLY under `hirr`; see
  the audit below. It is also why the two-dimensionality hypothesis `hV`
  cannot be dropped: see the FAITHFULNESS AUDIT in
  `nonempty_hilbertBlumenthalPoint_of_isTwistedHilbertBlumenthalModuli`,
  where dropping it makes the consumer FALSE.

THE FRAME REMEMBERS THE REAL MULTIPLICATION (2026-07-26, requested by
the owner of `exists_weilFrobeniusSystem_of_mult`, whose leaf is FALSE
without it). The conclusion also produces a ring map
`j : 𝒪_D →+* O` together with `hj`, saying that the `O`-action
transported to `TatePt` along `φ` EXTENDS the real multiplication
`m.act`. Without that clause `O` ranges over every commutative subring
of `End_{Γ_F}(T)` of the right `ℤ_q`-rank over which `T` is free of rank
two, and when `A_x` has endomorphisms beyond `𝒪_D` such rings exist and
are not `𝒪_{D,I}`: for `D = ℚ(√5)`, `A = E × E` with `𝒪_D` acting by the
companion matrix of `X² - X - 1` and `q = 13` inert, `O = ℤ₁₃[N] ≅
ℤ₁₃[ε]/(ε²)` with `N` nilpotent satisfies every other clause of this
conclusion and admits NO injective ring map into `AlgebraicClosure ℚ₁₃`.
With `j` and `hj` the image of `𝒪_D ⊗ ℤ_q` lies in `O`, and with the
rank count and integral closedness `O = 𝒪_{D,I}`; then `τ.charFrob` is
the reduced rank-two Frobenius polynomial that Weil/Faltings is about.
This is free for the prover, who constructs `𝒪_{D,I}` anyway: `j` is its
structure map and `hj` is how the action was built.

FAITHFULNESS AUDIT (2026-07-26): **THE LEAF WAS FALSE AS STATED**, and
is repaired here by the hypothesis `hirr : ρ'.IsIrreducible`.

The refuted claim is the one recorded in the ASSEMBLY docstring of
`nonempty_hilbertBlumenthalPoint_of_isTwistedHilbertBlumenthalModuli`:
that the `k'`-structure of `ρ'` and the `𝒪_D/I`-structure transported
from `A[I]` are "two embeddings of `𝔽_q` into the commutant of the
Galois image, conjugate up to an automorphism of `𝔽_q` by
Wedderburn–Malcev". That is not a theorem. Wedderburn–Malcev and
Noether–Skolem conjugate embeddings inside a SIMPLE algebra, and the
commutant `C := End_{ℤ[Γ_F]}(A[I])` need not be simple; when it is
commutative it has no inner automorphisms at all, and two embeddings of
`𝔽_q` into it are genuinely inequivalent.

COUNTEREXAMPLE (no hypothesis of the previous statement is violated).
Let `A₀/ℚ` be a Hilbert–Blumenthal abelian surface with real
multiplication by `𝒪_D`, `D` real quadratic, `A₀` without complex
multiplication — e.g. `J₀(23)`, with `D = ℚ(√5)`. By Ribet's big-image
theorem the mod-`I` image contains `SL₂(𝒪_D/I)` for all but finitely
many `I`, and the `I`-adic image is open in `GL₂(𝒪_{D,I})`. Choose such
an `I` with `q` INERT in `D`, so `k := 𝒪_D/I ≅ 𝔽_{q²}`. Let `F` be the
fixed field of the preimage under `ρ̄ := ρ̄_{A₀,I}` of the diagonal
torus and `A := A₀ ×_ℚ F`; then `ρ̄|_{Γ_F} = α ⊕ β` with `(α,β)`
surjecting onto `{(a, a⁻¹) : a ∈ 𝔽_{q²}ˣ}`.

Take `V := A[I]` as an abelian group, `e := id`, and give `V` the
`k' := 𝔽_{q²}`-structure `λ ∗ (a₁, a₂) := (λ a₁, λ^q a₂)` in the
eigenbasis. It commutes with the diagonal Galois action, so `e` is an
additive `Γ_F`-equivariant bijection onto `(m.torsion x I).1`,
`Module.rank k' V = 2`, and `ρ'` is the `k'`-linear representation
`diag(α, β^q)`. Every hypothesis of the previous statement holds.

But openness of the `I`-adic image forces `End_{ℤ[Γ_F]}(T_I A) =
𝒪_{D,I}`, so any frame forces `O ≅ 𝒪_{D,I}` and `charpoly (τ σ)` to be
a `ψ`-twist of the canonical one, `ψ ∈ Aut(𝒪_{D,I}/ℤ_q)`; and every ring
map `ι₀ : O →+* k'` is the residue map followed by a field isomorphism
`k ≅ k'`. So the achievable residual characteristic polynomials are
exactly `(X - θα)(X - θβ)` for `θ ∈ Aut(k)`, while the conclusion
demands `(X - α)(X - β^q)` at every `w`. Pick `w` with `α(Frob_w)` of
order `q² - 1` (Chebotarev): `θ = id` would need `β = β^q` and
`θ = Frob` would need `α = α^q`, both false. No `ι₀` exists.

THE REPAIR, and why it is exactly right. If `ρ'` is irreducible then
`A[I]` is a semisimple `𝔽_p[Γ_F]`-module (`k'/𝔽_p` is separable, so
`J(k'[Γ]) = k' ⊗ J(𝔽_p[Γ])`) and the `𝒪_D/I`-structure representation
`ρ̄` is irreducible as well: a split `ρ̄ = α ⊕ β` with `α ≠ β` has
commutant `k × k` and a scalar `ρ̄` has commutant `M₂(k)`, and in both
every field structure of order `#k` makes `ρ'` REDUCIBLE. With `ρ̄`
irreducible, `C` is either a finite field — when `ρ̄` is irreducible but
not absolutely irreducible — or a central simple algebra over its centre
in which `k` is self-centralizing; in both cases the two embeddings of
`k` into `C` differ by an inner automorphism of `C` composed with an
element of `Aut(k)`. The inner automorphism is an additive
`Γ_F`-equivariant change of frame, absorbed by `φ`; the field
automorphism is absorbed by `ι₀`. That is the argument the previous
docstring intended, and irreducibility is exactly what makes it
available.

`hirr` costs the consumers nothing: at `𝔭` the moduli condition
`IsTwistedHilbertBlumenthalModuli` already carries `ρbarp.IsIrreducible`,
and at `λ` the irreducibility of `ρbar` is a hypothesis of
`exists_twistedHilbertBlumenthalModuli_of_five_le`, transported to `Γ_F`
along `hrestr` by `isIrreducible_map_of_restrictionSurjective` above.

DETERMINANT CLAUSE, ADDED 2026-07-26 (the WEIL PAIRING; one extra
existential `bad` and one extra conjunct, nothing else changed).  The
frame now also reports that the determinant of Frobenius on it is the
absolute norm,

  `∀ w ∉ bad, LinearMap.det (τ.toLocal w Frobᵥ) = (Nw : O)`,

away from a finite set (the places of bad reduction of `A_x` together
with those above `q`, where the `I`-adic representation is ramified).
Classically this is the `𝒪_D`-linear Weil pairing: a polarization makes
`∧²_{𝒪_{D,I}} T_I A` the inverse different twisted by the cyclotomic
character, so `det τ = χ_cyc` and `χ_cyc(Frob_w) = Nw` (Taylor 2002 §2;
Carayol's normalization).  Nothing else in the tree can see it —
`Modularity/AbelianScheme.lean` has geometric points and Galois-stable
torsion but no pairing — which is why it rides here rather than being
derived.

WHY IT IS SOUND TO PUT IT HERE AND NOT IN A LEAF OF ITS OWN
(faithfulness, checked 2026-07-26).  The frame is EXISTENTIALLY
quantified, so the clause constrains only the frame this leaf chooses,
and the honest Tate frame satisfies it.  Stated instead for a GIVEN
frame it would be **FALSE**, by exactly the counterexample that refuted
the sibling `exists_weilFrobeniusSystem_of_mult`: `φ` is only additive
and `Γ_F`-equivariant, so the `O`-structure it transports to `T` is an
arbitrary embedding `O ↪ End_{ℤ_q[Γ_F]}(T)`, and when that commutant is
larger than `𝒪_{D,I}` — e.g. `T ⊗ ℚ_q = χ₁ ⊕ χ₂` with `𝒪_{D,I}/ℤ_q`
carrying a nontrivial automorphism `ψ`, so that `a ∗ (u₁, u₂) :=
(a u₁, ψ(a) u₂)` is a second rank-`2` free structure — the determinant
becomes `χ₁ · ψ⁻¹(χ₂)` instead of `χ₁ · χ₂ = Nw`.  A determinant leaf
over a given frame therefore needs the real-multiplication tie
(`j`/`hj`) that the sibling was repaired with; over a frame the prover
chooses, it needs nothing.  Its consumer is the field
`HilbertBlumenthalPoint.detσ`.

DETERMINANT CLAUSE, DISCHARGED 2026-07-26 (later the same day).  The
clause survived the merge of the two branches as a single opaque sorried
`have` inside this assembly.  It is now cut into the three statements of
the section "The determinant clause" above, and the assembly is closed
over them:

* the exceptional set is exactly the set of places over `q`, finite by
  `exists_finset_forall_natCast_notMem` — the places of bad reduction do
  NOT have to be excluded, since `det τ = χ_cyc` is an identity of
  characters and is insensitive to ramification of `τ`;
* `det τ = χ_cyc` on the whole of `Γ_F` is the one open leaf
  `det_eq_cyclotomicCharacter_of_tateFrame` (the Weil pairing);
* `χ_cyc(Frob_w) = Nw` for `w ∤ q` is PROVEN here as
  `cyclotomicCharacter_adicArithFrob_absNorm`.

Note the frame used for the geometric leaf is the one produced by
`exists_tateFrame_of_adicCoefficientRing`, so it comes WITH `j` and
`hφj`; that is what makes a given-frame determinant leaf faithful, per
the audit above, and every one of `j`, `hφj`, `hcplt`, `hdense`, `hker`
is passed to it. -/
theorem exists_tateFrame_of_levelStructure
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (hdim : SmoothOfRelativeDimension (Module.finrank ℚ D) f)
    (q : ℕ) [Fact q.Prime]
    (I : Ideal (NumberField.RingOfIntegers D)) (hI : I.IsMaximal)
    (hqI : (q : NumberField.RingOfIntegers D) ∈ I)
    {k' : Type u} [Field k'] [Finite k'] [TopologicalSpace k'] [DiscreteTopology k']
    {V : Type v} [AddCommGroup V] [Module k' V] [Module.Finite k' V] [Module.Free k' V]
    (hV : Module.rank k' V = 2)
    (ρ' : GaloisRep F k' V)
    (hirr : ρ'.IsIrreducible)
    (e : V → GeomFibrePt f x)
    (headd : ∀ v v' : V, e (v + v') = ab.add (e v) (e v'))
    (heinj : Function.Injective e)
    (heequiv : ∀ (σ : Field.absoluteGaloisGroup F) (v : V),
      e (ρ' σ v) = ab.galSMul x σ (e v))
    (heimg : ∀ y, y ∈ (m.torsion x I).1 ↔ ∃ v, e v = y) :
    ∃ (π : NumberField.RingOfIntegers D) (_ : π ∈ I) (_ : π ∉ I ^ 2)
      (O : Type u) (_ : CommRing O) (_ : TopologicalSpace O) (_ : IsTopologicalRing O)
      (_ : Algebra ℤ_[q] O) (_ : IsLocalRing O) (_ : Module.Finite ℤ_[q] O)
      (_ : Module.Free ℤ_[q] O) (_ : IsModuleTopology ℤ_[q] O)
      (τ : GaloisRep F O (Fin 2 → O))
      (φ : (Fin 2 → O) → TatePt m x I π) (ι₀ : O →+* k')
      (j : NumberField.RingOfIntegers D →+* O)
      (bad : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F))),
      (∀ (u u' : Fin 2 → O) (n : ℕ),
        (φ (u + u')).1 n = ab.add ((φ u).1 n) ((φ u').1 n)) ∧
      Function.Bijective φ ∧
      (∀ (σ : Field.absoluteGaloisGroup F) (u : Fin 2 → O) (n : ℕ),
        (φ (τ σ u)).1 n = ab.galSMul x σ ((φ u).1 n)) ∧
      (∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
        (τ.charFrob w).map ι₀ = ρ'.charFrob w) ∧
      (∀ (a : NumberField.RingOfIntegers D) (u : Fin 2 → O) (n : ℕ),
        (φ (j a • u)).1 n = m.act a ((φ u).1 n)) ∧
      ∀ w ∉ bad,
        LinearMap.det (τ.toLocal w (Field.AbsoluteGaloisGroup.adicArithFrob w)) =
          (Ideal.absNorm w.asIdeal : O) := by
  -- `I` is nonzero: it contains the rational prime `q`.
  have hI0 : I ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot, Nat.cast_eq_zero] at hqI
    exact (Fact.out : q.Prime).ne_zero hqI
  obtain ⟨π, hπ, hπ2⟩ := exists_mem_notMem_sq_of_isMaximal hI hI0
  obtain ⟨O, iCR, iTS, iTR, iAlg, iLoc, iFin, iFree, iMT, j, hcplt, hdense, hker⟩ :=
    exists_adicCoefficientRing q I hI hqI π hπ hπ2
  letI := iCR; letI := iTS; letI := iTR; letI := iAlg
  letI := iLoc; letI := iFin; letI := iFree; letI := iMT
  obtain ⟨τ, φ, hφadd, hφbij, hφequiv, hφj⟩ :=
    exists_tateFrame_of_adicCoefficientRing m x hdim q I hI hqI π hπ hπ2 O j hcplt hdense hker
  obtain ⟨ι₀, hι₀⟩ :=
    exists_residualEmbedding_of_tateFrame m x I hI π hπ hπ2 O j hker τ φ hφadd hφbij hφequiv
      hφj hV ρ' hirr e headd heinj heequiv heimg
  -- The determinant (Weil-pairing) clause, added 2026-07-26 by another owner and
  -- merged onto this assembly.  It is now discharged from the three-way cut
  -- above the leaf: the exceptional set is the (finite) set of places over `q`,
  -- the identity `det τ = χ_cyc` is the Weil-pairing leaf
  -- `det_eq_cyclotomicCharacter_of_tateFrame`, and the value of `χ_cyc` at an
  -- arithmetic Frobenius away from `q` is `Nw` by
  -- `cyclotomicCharacter_adicArithFrob_absNorm`.
  obtain ⟨bad, hbad⟩ :=
    exists_finset_forall_natCast_notMem (F := F) q (Fact.out : q.Prime).ne_zero
  have hdet : ∀ w ∉ bad,
      LinearMap.det (τ.toLocal w (Field.AbsoluteGaloisGroup.adicArithFrob w)) =
        (Ideal.absNorm w.asIdeal : O) := by
    intro w hw
    rw [GaloisRep.toLocal_apply,
      det_eq_cyclotomicCharacter_of_tateFrame m x hdim q I hI hqI π hπ hπ2 O j hcplt hdense
        hker τ φ hφadd hφbij hφequiv hφj _,
      cyclotomicCharacter_adicArithFrob_absNorm F w (hbad w hw), map_natCast]
  exact ⟨π, hπ, hπ2, O, iCR, iTS, iTR, iAlg, iLoc, iFin, iFree, iMT, τ, φ, ι₀, j, bad,
    hφadd, hφbij, hφequiv, hι₀, hφj, hdet⟩

/-! ### The compatible system, cut into its two inputs

`exists_weilFrobeniusSystem_of_mult` below — item 9, the Weil/Faltings
citation — is no longer a single opaque leaf.  Once the frame is pinned
to the real multiplication by `j`/`hj` (the repair recorded in its
FAITHFULNESS AUDIT), the statement splits along an entirely mechanical
seam into two mathematically distinct inputs:

* `exists_algebraicClosureEmbedding_of_tateFrame_mult` — *the frame's
  coefficient ring is `𝒪_{D,I}`*.  This is what supplies the embeddings
  `ψ` and `ι` and, in particular, the INJECTIVITY of `ι`, which the
  audit shows is not available for an unpinned frame at all.  Pure
  commutative algebra: no Frobenius, no compatible system.
* `exists_intWeilPolynomial_of_mult` — *the Frobenius characteristic
  polynomial is `X² - a_w X + b_w` with `a_w, b_w ∈ 𝒪_D` independent of
  `I`*.  This is the arithmetic: Weil's Riemann hypothesis for abelian
  varieties over finite fields (the coefficients are algebraic integers
  of the right size) together with independence of `λ` (they do not
  depend on the residue characteristic).  **Itself PROVEN 2026-07-27**
  by a further cut into rationality and independence — see the section
  note at that statement, which also corrects the attribution of the
  independence half to Faltings: at a place of good reduction it is
  classical.

Why this is the right seam, and not an arbitrary one.  The old statement
buried BOTH inputs inside one existential over `AlgebraicClosure ℚ_[q]`,
where they are hard to tell apart — which is precisely how the false
`Function.Injective ι` clause got in unnoticed, since an assertion about
the SHAPE of `O` was hiding inside an assertion about Frobenius.  Cutting
here separates them: the injectivity now lives in a statement that
mentions no Frobenius, and the compatible system now lives in a statement
whose coefficients are `𝒪_D`-integral BY CONSTRUCTION, so no embedding
into `ℚ̄_q` is needed to say what `D`-rationality means.  The polynomial
`P` of the conclusion is then not existential magic but the explicit
`X² - a_w X + b_w` read in `D`, and the two leaves meet only through the
compatibility `ι ∘ j = ψ ∘ (𝒪_D ↪ D)`.

Both leaves inherit the pinning hypotheses `j`/`hj` verbatim; neither is
provable without them, by the two counterexamples in the audit below. -/

/-! ### Pinning the coefficient ring: the frame COMPARISON

`exists_algebraicClosureEmbedding_of_tateFrame_mult` below is PROVEN
(2026-07-27) over the two leaves of this subsection, and the move that
makes that possible is worth stating separately because it removes ALL
geometry from the remaining obligation.

The leaf quantifies over an arbitrary frame `(O, τ, φ, j)` of
`TatePt m x I π`.  But the HONEST frame at the very same `(q, I, π)`
already exists and is PROVEN: instantiate `exists_tateFrame_of_adicCoefficientRing`
at `O₁ := v.adicCompletionIntegers D` (`v = ⟨I, …⟩`), whose three pin
conjuncts are `isAdicComplete_span_uniformizer`,
`exists_sub_mem_span_uniformizer_pow` and `mem_span_uniformizer_pow_iff`
and whose `ℤ_q`-structure is `padicIntAlgebra`.  That produces
`φ₁ : (Fin 2 → O₁) → TatePt m x I π`, additive, bijective and
`𝒪_D`-equivariant along `j₁ = algebraMap`.

Composing, `g := φ⁻¹ ∘ φ₁ : (Fin 2 → O₁) → (Fin 2 → O)` is an ADDITIVE
BIJECTION intertwining the two `𝒪_D`-actions,

    g (j₁ a • u) = j a • g u,

and `TatePt`, `ab`, `m`, `x`, `hdim`, `τ`, `hφequiv` all disappear from
the problem: what is left is a question about two commutative rings
related by an additive bijection of their squares.  That is the content
of this subsection, and it is why the leaves below mention no scheme.

Note in passing what this settles about faithfulness.  A frame is only
hypothesised, never constructed, so a priori `O` could be the ZERO ring
— and then no `ι : O →+* ℚ̄_q` exists at all and the leaf would be
FALSE, since a ring hom must send `1` to `1`.  The comparison rules
that out unconditionally: `O₁ = 𝒪_{D,I}` is nontrivial and
`(Fin 2 → O) ≃ TatePt m x I π ≃ (Fin 2 → O₁)`, so `O` is nontrivial too.
The hypothesis block is therefore satisfiable and the leaf is not
vacuous.

The remaining algebra splits at a clean seam:

* `exists_padicAlgebra_ringHom_of_frameComparison` — TRANSPORT.  `O`
  inherits from `O₁`, along `g`, everything that makes it a coefficient
  ring: `q`-adic completeness (hence a `ℤ_q`-algebra structure through
  `padicIntLiftHom`), finiteness and freeness over `ℤ_q` of the SAME
  rank as `O₁`, and an injective ring map `ρ : O₁ →+* O` with
  `ρ ∘ j₁ = j`.  **`[IsDomain O₁]` was ADDED to it on 2026-07-27,
  after the leaf was REFUTED without it by an explicit
  counterexample** — see the FALSITY AUDIT in its docstring.  The
  hypothesis is free at the only call site, `exists_ringEquiv_of_frameComparison`
  below, which already assumes it.  The leaf is now PROVEN over three
  sub-leaves, `exists_padicAlgebra_of_additiveEquiv_sq`,
  `span_range_eq_top_of_adicPin` and `exists_ringHom_of_span_range_eq_top`.
* `surjective_of_finrank_eq_of_isIntegrallyClosed` — CLOSURE.  Such a
  `ρ` is automatically surjective.  Pure commutative algebra over
  `ℤ_q`, with no `𝒪_D`, no frame and no `g`.  **PROVEN 2026-07-27.**

Together they give `O ≃+* 𝒪_{D,I}` over `𝒪_D`, which is exactly the
conclusion the FAITHFULNESS AUDIT below demands be DERIVED rather than
assumed. -/

/-! #### The shared adic bricks

The two leaves below were both recorded as gated on one missing lemma,
`IsAdicComplete (Ideal.span {(q : O₁)}) O₁` for `O₁` finite over `ℤ_q`.
**That lemma was not missing.**  `IsAdicComplete.of_finite_module` has
been in this project since 2026-07-26, in
`Fermat/FLT/Mathlib/RingTheory/AdicCompletion/Finite.lean`, together with
`HenselianRing.of_finite_algebra`, idempotent lifting along a henselian
pair, and `IsLocalRing.of_isArtinianRing_isIdempotentElem`.  The
"MISSING MACHINERY" notes that used to stand here were correct about
MATHLIB (a grep of `Mathlib/RingTheory/AdicCompletion/` really does turn
up instances only for `⊥`, `⊤`, subsingletons, `PowerSeries` and the
completion of a noetherian local ring) and wrong about this development;
the file they needed is imported above and the gate is
`isAdicComplete_span_natCast_of_moduleFinite`, six lines.

Everything in this subsection is stated over an arbitrary base and is
independent of the Tate-module development. -/

/-- `aⁿ • y` lies in the `n`-th step of the `a`-adic filtration. -/
theorem pow_smul_mem_span_singleton_pow_smul_top {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] (a : R) (n : ℕ) (y : M) :
    a ^ n • y ∈ ((Ideal.span {a}) ^ n • ⊤ : Submodule R M) := by
  rw [Ideal.span_singleton_pow]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

/-- An `R`-linear map carries the `I`-adic filtration into the `I`-adic
filtration (`Submodule.map_smul''`, then `⊤` is the largest submodule). -/
theorem map_mem_pow_smul_top {R : Type*} [CommRing R] {I : Ideal R} {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (t : M →ₗ[R] N) (n : ℕ) {x : M} (hx : x ∈ (I ^ n • ⊤ : Submodule R M)) :
    t x ∈ (I ^ n • ⊤ : Submodule R N) := by
  have hmem : t x ∈ Submodule.map t (I ^ n • ⊤ : Submodule R M) := ⟨x, hx, rfl⟩
  rw [Submodule.map_smul''] at hmem
  exact Submodule.smul_le.mpr (fun r hr m _ => Submodule.smul_mem_smul hr Submodule.mem_top) hmem

/-- **Adic completeness passes to a module retract** (PROVEN).  If
`f ∘ s = id` then `s` embeds `N`'s filtration into `M`'s and `f` pushes
`M`'s back, so both Hausdorffness and precompleteness transfer.  Applied
twice below: once along an additive bijection (a `ℤ`-linear equivalence,
which is a retract of itself), once along `Fin 2 → O ↠ O`. -/
theorem isAdicComplete_of_retract {R : Type*} [CommRing R] (I : Ideal R)
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [IsAdicComplete I M] (f : M →ₗ[R] N) (s : N →ₗ[R] M) (hfs : ∀ x, f (s x) = x) :
    IsAdicComplete I N := by
  haveI hh : IsHausdorff I N := by
    refine ⟨fun x hx => ?_⟩
    have h0 : s x = 0 :=
      IsHausdorff.haus (inferInstance : IsHausdorff I M) (s x) fun n =>
        SModEq.zero.mpr (map_mem_pow_smul_top s n (SModEq.zero.mp (hx n)))
    have h := hfs x
    rw [h0, map_zero] at h
    exact h.symm
  haveI hp : IsPrecomplete I N := by
    refine ⟨fun a ha => ?_⟩
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete I M)
      (f := fun n => s (a n)) (by
        intro m n hmn
        rw [SModEq.sub_mem, ← map_sub]
        exact map_mem_pow_smul_top s m (SModEq.sub_mem.mp (ha hmn)))
    refine ⟨f L, fun n => ?_⟩
    rw [SModEq.sub_mem]
    have heq : a n - f L = f (s (a n) - L) := by rw [map_sub, hfs]
    rw [heq]
    exact map_mem_pow_smul_top f n (SModEq.sub_mem.mp (hL n))
  exact ⟨⟩

/-- **The `k`-adic filtration of a module does not see its base ring**
(PROVEN).  `Ideal.span {(k : R)} = (Ideal.span {(k : ℤ)}).map (algebraMap ℤ R)`,
so `IsAdicComplete.map_algebraMap_iff` identifies the two conditions.  This
is what lets an additive (i.e. `ℤ`-linear) bijection transport `q`-adic
completeness between rings that carry no common algebra structure yet. -/
theorem isAdicComplete_span_natCast_iff_int {R : Type*} [CommRing R] (k : ℕ)
    (M : Type*) [AddCommGroup M] [Module R M] :
    IsAdicComplete (Ideal.span {(k : R)}) M ↔ IsAdicComplete (Ideal.span {(k : ℤ)}) M := by
  have h : (Ideal.span {(k : ℤ)}).map (algebraMap ℤ R) = Ideal.span {(k : R)} := by
    rw [Ideal.map_span]; simp
  rw [← h, IsAdicComplete.map_algebraMap_iff]

/-- **THE SHARED GATE, and it was never missing**: a module-finite
`ℤ_q`-algebra is `q`-adically complete (PROVEN).  `ℤ_q` is a complete
noetherian local ring, so `IsAdicComplete.of_finite_module` applies at
its maximal ideal, and `PadicInt.maximalIdeal_eq_span_p` rewrites that
ideal as `(q)`; the base of the filtration is then switched by
`isAdicComplete_span_natCast_iff_int`.  `Module.Free` is NOT needed —
`Module.Finite` alone suffices. -/
theorem isAdicComplete_span_natCast_of_moduleFinite (q : ℕ) [Fact q.Prime]
    (A : Type*) [CommRing A] [Algebra ℤ_[q] A] [Module.Finite ℤ_[q] A] :
    IsAdicComplete (Ideal.span {(q : A)}) A := by
  haveI h1 : IsAdicComplete (IsLocalRing.maximalIdeal ℤ_[q]) A :=
    IsAdicComplete.of_finite_module
  rw [PadicInt.maximalIdeal_eq_span_p] at h1
  rw [isAdicComplete_span_natCast_iff_int]
  exact (isAdicComplete_span_natCast_iff_int (R := ℤ_[q]) q A).mp h1

/-- The image of `c : ℤ_q` in any `ℤ_q`-algebra is `q`-adically close to
the natural number `PadicInt.appr c n` (PROVEN — apply `algebraMap` to
`PadicInt.appr_spec`).  The `ℤ_q`-algebra analogue of
`appr_sub_natCast_mem` above, which is about naturals only. -/
theorem algebraMap_sub_appr_mem {q : ℕ} [Fact q.Prime] (A : Type*) [CommRing A]
    [Algebra ℤ_[q] A] (c : ℤ_[q]) (n : ℕ) :
    algebraMap ℤ_[q] A c - ((c.appr n : ℕ) : A) ∈ Ideal.span {(q : A)} ^ n := by
  have h := PadicInt.appr_spec n c
  rw [Ideal.mem_span_singleton] at h
  obtain ⟨d, hd⟩ := h
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  refine ⟨algebraMap ℤ_[q] A d, ?_⟩
  have h2 := congrArg (algebraMap ℤ_[q] A) hd
  simpa using h2

/-- **An additive bijection of squares transports the `ℤ_q`-structure**
(PROVEN 2026-07-27 — pure `ℤ_q`-module theory; no `𝒪_D`, no frame, no
number field, no pinning appears).

If `O₁` is a finite free `ℤ_q`-algebra and
`g : (Fin 2 → O₁) → (Fin 2 → O)` is an additive bijection onto the
square of an ARBITRARY commutative ring `O`, then `O` is itself a finite
free `ℤ_q`-algebra of the same rank, and `g` is `ℤ_q`-LINEAR for that
structure.

THE ARGUMENT.

1. *`Fin 2 → O` is `q`-adically complete and separated as an abelian
   group.*  `O₁` is finite free over `ℤ_q`, so `Fin 2 → O₁` is
   `ℤ_q`-free of finite rank, hence `q`-adically complete and separated;
   `g` is additive and bijective, hence `ℤ`-linear and carrying
   `qⁿ · (Fin 2 → O₁)` ONTO `qⁿ · (Fin 2 → O)`, so it transports both
   properties.  `O` is an additive direct summand of `Fin 2 → O`, and
   both properties pass to summands.
2. *Hence `Algebra ℤ_[q] O`*, namely `padicIntLiftHom` of the
   `PadicIntLift` section above, whose only hypothesis is exactly
   `IsAdicComplete (Ideal.span {(q : O)}) O`.  This is the same
   construction that gives `𝒪ᵥ` its `ℤ_q`-structure in
   `padicIntAlgebra`.
3. *`g` is `ℤ_q`-linear.*  For `c : ℤ_q` with natural approximants `cₖ`
   (`PadicInt.appr`, and `appr_sub_natCast_mem` above), one has
   `c • u - cₖ • u ∈ qᵏ · (Fin 2 → O₁)` and
   `c • g u - cₖ • g u ∈ qᵏ · (Fin 2 → O)`, while
   `g (cₖ • u) = cₖ • g u` because `g` is additive and `cₖ` is a NATURAL
   number.  Subtracting, `g (c • u) - c • g u ∈ qᵏ · (Fin 2 → O)` for
   every `k`, hence is `0` by separatedness.
4. *Rank.*  `g` is then a `ℤ_q`-linear bijection, so
   `(Fin 2 → O) ≃ₗ[ℤ_q] (Fin 2 → O₁)` and
   `2 · finrank O = 2 · finrank O₁`; `O` is a `ℤ_q`-direct summand of
   `Fin 2 → O`, hence finite over `ℤ_q`, and torsion-free over the PID
   `ℤ_q`, hence free.

This is the half of `exists_padicAlgebra_ringHom_of_frameComparison`
that survives verbatim when the pinning hypotheses are dropped.

STALE-AUDIT CORRECTION, 2026-07-27.  This docstring used to carry a
"MISSING MACHINERY" note demanding
`IsAdicComplete (Ideal.span {(q : O₁)}) O₁` be built by hand from
`Module.Free.chooseBasis`, and instructing the reader not to look in
mathlib again.  The note was right about mathlib and wrong about this
project: `IsAdicComplete.of_finite_module` was already in
`Fermat/FLT/Mathlib/RingTheory/AdicCompletion/Finite.lean`, and the gate
is now `isAdicComplete_span_natCast_of_moduleFinite` above.  No basis is
chosen anywhere in the proof.

HOW THE STEPS ARE REALISED.  Step 1 does not go through `O₁`'s own
completeness at all: `Fin 2 → O₁` is `q`-adically complete over `ℤ_q`
(`IsAdicComplete.of_finite_module`), the filtration is re-based to `ℤ`
by `isAdicComplete_span_natCast_iff_int` — which is what makes the merely
ADDITIVE `g` usable, since at this point `Fin 2 → O` has no `ℤ_q`-action
— and `isAdicComplete_of_retract` transports it first along `g`, then
along `Fin 2 → O ↠ O`.  Step 2 is `padicIntLiftHom` verbatim.  Step 3
compares `c • u` with `PadicInt.appr c n • u` on both sides through
`algebraMap_sub_appr_mem` and concludes by Hausdorffness of `Fin 2 → O`.
Step 4 is `Module.finrank_pi_fintype` on `L := g` viewed as a
`ℤ_q`-linear equivalence, with freeness from
`Module.free_of_finite_type_torsion_free'` over the PID `ℤ_q`. -/
theorem exists_padicAlgebra_of_additiveEquiv_sq
    (q : ℕ) [Fact q.Prime]
    (O₁ : Type u) [CommRing O₁] [Algebra ℤ_[q] O₁] [Module.Finite ℤ_[q] O₁]
    [Module.Free ℤ_[q] O₁]
    (O : Type u) [CommRing O]
    (g : (Fin 2 → O₁) → (Fin 2 → O))
    (hgadd : ∀ u u' : Fin 2 → O₁, g (u + u') = g u + g u')
    (hgbij : Function.Bijective g) :
    ∃ (_ : Algebra ℤ_[q] O) (_ : Module.Finite ℤ_[q] O) (_ : Module.Free ℤ_[q] O),
      Module.finrank ℤ_[q] O = Module.finrank ℤ_[q] O₁ ∧
      ∀ (c : ℤ_[q]) (u : Fin 2 → O₁), g (c • u) = c • g u := by
  classical
  let G : (Fin 2 → O₁) →+ (Fin 2 → O) := AddMonoidHom.mk' g hgadd
  let e : (Fin 2 → O₁) ≃+ (Fin 2 → O) := AddEquiv.ofBijective G hgbij
  have hGg : ∀ u, G u = g u := fun _ => rfl
  have heg : ∀ u, e u = g u := fun _ => rfl
  -- Step 1: `q`-adic completeness of `O`, transported along `g` over `ℤ`.
  have hA1 : IsAdicComplete (IsLocalRing.maximalIdeal ℤ_[q]) (Fin 2 → O₁) :=
    IsAdicComplete.of_finite_module
  rw [PadicInt.maximalIdeal_eq_span_p] at hA1
  haveI hZ1 : IsAdicComplete (Ideal.span {(q : ℤ)}) (Fin 2 → O₁) :=
    (isAdicComplete_span_natCast_iff_int (R := ℤ_[q]) q (Fin 2 → O₁)).mp hA1
  haveI hZ2 : IsAdicComplete (Ideal.span {(q : ℤ)}) (Fin 2 → O) :=
    isAdicComplete_of_retract _ e.toIntLinearEquiv.toLinearMap
      e.toIntLinearEquiv.symm.toLinearMap (fun x => e.toIntLinearEquiv.apply_symm_apply x)
  haveI hZ3 : IsAdicComplete (Ideal.span {(q : ℤ)}) O :=
    isAdicComplete_of_retract _ (LinearMap.proj (0 : Fin 2))
      (LinearMap.single ℤ (fun _ : Fin 2 => O) 0) (fun x => by simp)
  haveI hcO : IsAdicComplete (Ideal.span {(q : O)}) O :=
    (isAdicComplete_span_natCast_iff_int (R := O) q O).mpr hZ3
  -- Step 2: the `ℤ_q`-algebra structure.
  letI algO : Algebra ℤ_[q] O := (padicIntLiftHom (p := q) (O := O)).toAlgebra
  -- Step 3: `ℤ_q`-linearity of `g`.
  have hlin : ∀ (c : ℤ_[q]) (u : Fin 2 → O₁), g (c • u) = c • g u := by
    intro c u
    have hh : ∀ n : ℕ, g (c • u) - c • g u ∈
        ((Ideal.span {(q : ℤ)}) ^ n • ⊤ : Submodule ℤ (Fin 2 → O)) := by
      intro n
      have hO₁ := algebraMap_sub_appr_mem O₁ c n
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hO₁
      obtain ⟨d, hd⟩ := hO₁
      have hO := algebraMap_sub_appr_mem O c n
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hO
      obtain ⟨d', hd'⟩ := hO
      have hu : c • u - ((c.appr n : ℕ) • u) = ((q : ℤ) ^ n) • (d • u) := by
        funext i
        show c • u i - (c.appr n : ℕ) • u i = ((q : ℤ) ^ n) • (d • u i)
        rw [Algebra.smul_def, nsmul_eq_mul, smul_eq_mul, zsmul_eq_mul]
        push_cast
        linear_combination (u i) * hd
      have hv : c • g u - ((c.appr n : ℕ) • g u) = ((q : ℤ) ^ n) • (d' • g u) := by
        funext i
        show c • g u i - (c.appr n : ℕ) • g u i = ((q : ℤ) ^ n) • (d' • g u i)
        rw [Algebra.smul_def, nsmul_eq_mul, smul_eq_mul, zsmul_eq_mul]
        push_cast
        linear_combination (g u i) * hd'
      have hG1 : g (c • u) - g ((c.appr n : ℕ) • u) = ((q : ℤ) ^ n) • g (d • u) := by
        have h1 : G (c • u - ((c.appr n : ℕ) • u)) = G (((q : ℤ) ^ n) • (d • u)) := by rw [hu]
        rw [map_sub, map_zsmul] at h1
        simpa only [hGg] using h1
      have hG2 : g ((c.appr n : ℕ) • u) = (c.appr n : ℕ) • g u := by
        have h2 := map_nsmul G (c.appr n) u
        simpa only [hGg] using h2
      have hfin : g (c • u) - c • g u = ((q : ℤ) ^ n) • (g (d • u) - d' • g u) := by
        rw [smul_sub, ← hG1, ← hv, hG2]
        abel
      rw [hfin]
      exact pow_smul_mem_span_singleton_pow_smul_top _ n _
    have hzero := IsHausdorff.haus
      (inferInstance : IsHausdorff (Ideal.span {(q : ℤ)}) (Fin 2 → O))
      (g (c • u) - c • g u) fun n => SModEq.zero.mpr (hh n)
    exact sub_eq_zero.mp hzero
  -- Step 4: finiteness, freeness and the rank.
  let L : (Fin 2 → O₁) ≃ₗ[ℤ_[q]] (Fin 2 → O) := e.toLinearEquiv (fun c x => by
    simpa only [heg] using hlin c x)
  haveI hfinO2 : Module.Finite ℤ_[q] (Fin 2 → O) := Module.Finite.equiv L
  haveI hfinO : Module.Finite ℤ_[q] O :=
    Module.Finite.of_surjective (LinearMap.proj (0 : Fin 2) : (Fin 2 → O) →ₗ[ℤ_[q]] O)
      (fun x => ⟨fun _ => x, rfl⟩)
  haveI htfO : Module.IsTorsionFree ℤ_[q] O := by
    have h1 : Function.Injective (L.symm.toLinearMap : (Fin 2 → O) →ₗ[ℤ_[q]] (Fin 2 → O₁)) :=
      L.symm.injective
    have h2 : Function.Injective
        (LinearMap.single ℤ_[q] (fun _ : Fin 2 => O) 0 : O →ₗ[ℤ_[q]] (Fin 2 → O)) := by
      intro x y hxy
      simpa using congrFun hxy 0
    refine Function.Injective.moduleIsTorsionFree
      (L.symm.toLinearMap ∘ₗ (LinearMap.single ℤ_[q] (fun _ : Fin 2 => O) 0)) ?_ ?_
    · intro x y hxy
      simp only [LinearMap.coe_comp, Function.comp_apply] at hxy
      exact h2 (h1 hxy)
    · intro r m
      simp
  haveI hfreeO : Module.Free ℤ_[q] O := Module.free_of_finite_type_torsion_free'
  have hrank : Module.finrank ℤ_[q] O = Module.finrank ℤ_[q] O₁ := by
    have h1 : Module.finrank ℤ_[q] (Fin 2 → O₁) = Module.finrank ℤ_[q] (Fin 2 → O) :=
      L.finrank_eq
    rw [Module.finrank_pi_fintype, Module.finrank_pi_fintype] at h1
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
    omega
  exact ⟨algO, hfinO, hfreeO, hrank, hlin⟩

open _root_.NumberField in
/-- **The pinned image SPANS: `𝒪_{D,I}` is the `ℤ_q`-span of `j₁(𝒪_D)`**
(PROVEN 2026-07-27 — commutative algebra over a complete local domain).

`hdense` says `j₁(𝒪_D)` is dense in the `(j₁ π)`-adic topology.  That is
NOT the `q`-adic topology in general, and this is precisely where
`[IsDomain O₁]` is load-bearing: the counterexample recorded in the
FALSITY AUDIT of `exists_padicAlgebra_ringHom_of_frameComparison` below
satisfies `hdense` and `hker` verbatim, and there `j₁(𝒪_D)` spans a
PROPER `ℤ_q`-submodule of `O₁`.  So the "complete Nakayama" step of the
original argument was wrong as stated, and the domain hypothesis is what
repairs it.

THE ARGUMENT, as actually carried out.  Write `J := 𝔪_{ℤ_q} · O₁`,
which is `(q)` as an ideal of `O₁`, and `S := O₁ ⧸ J`.

1. *`j₁ π` is a non-unit.*  If it were a unit then `(j₁ π)¹ = ⊤`, so
   `j₁ 1 ∈ (j₁ π)¹` and `hker` at `n = 1`, `a = 1` gives `1 ∈ I`,
   contradicting `hI.ne_top`.  (Nonvanishing of `j₁ π` is NOT needed;
   see the HYPOTHESIS AUDIT below.)
2. *`S` is local artinian.*  `(O₁, J)` is a henselian pair
   (`HenselianRing.of_finite_algebra`, whose hypothesis is exactly
   `Module.Finite ℤ_[q] O₁`), so idempotents of `S` lift to `O₁`
   (`HenselianRing.exists_isIdempotentElem_mk_eq`); `O₁` is a DOMAIN, so
   the lift is `0` or `1` and hence so is the idempotent.  `S` is a
   module-finite algebra over the residue FIELD of `ℤ_q`, hence artinian
   (`IsArtinianRing.of_finite`), and an artinian ring with no nontrivial
   idempotents is local (`IsLocalRing.of_isArtinianRing_isIdempotentElem`).
   This is the ONLY place `[IsDomain O₁]` is used, and it is exactly the
   step that the counterexample above breaks: there `O₁ = ℤ₅ × ℤ₅ × ℤ₅`
   has idempotents, `S` is not local, and `j₁ π` stays a unit in two
   factors at every precision.
3. *`(j₁ π)ᴺ ⊆ (q)`.*  `J` sits in the Jacobson radical, so a unit mod
   `J` is a unit; by step 1 the image of `j₁ π` in `S` is therefore a
   non-unit, i.e. lies in `𝔪_S`.  `𝔪_S = jacobson ⊥` is nilpotent
   (`IsArtinianRing.isNilpotent_jacobson_bot`), say `𝔪_S ᴺ = ⊥`, so
   `(j₁ π)ᴺ ∈ J`.  `hdense` at precision `N` then gives, for every
   `z : O₁`, an `a : 𝒪_D` with `z - j₁ a ∈ (q)`.
4. *Nakayama.*  Let `M` be the `ℤ_q`-span of `j₁(𝒪_D)`.  Step 3 says
   `⊤ ≤ 𝔪_{ℤ_q} · ⊤` in the finite `ℤ_q`-module `O₁ ⧸ M`, and
   `𝔪_{ℤ_q} ≤ jacobson ⊥`, so `O₁ ⧸ M = 0`
   (`Submodule.eq_bot_of_le_smul_of_le_jacobson_bot`).

HYPOTHESIS AUDIT, 2026-07-27.  The statement is unchanged, but the proof
found is strictly stronger than the route sketched above ever needed:
`hqI`, `hπ` and `hπ2` are **not consumed at all**, and are underscored in
the binder list so that this is mechanically visible rather than merely
asserted.  The earlier sketch spent them on "`j₁ π ≠ 0`" and on the
reverse inclusion `(q) ⊆ (j₁ π)` (cofinality of the two filtrations in
BOTH directions); only the inclusion `(j₁ π)ᴺ ⊆ (q)` is actually used,
and it survives `j₁ π = 0` trivially.  `Module.Free ℤ_[q] O₁` is likewise
unused — `Module.Finite` alone drives steps 2–4.  The hypotheses are kept
because the caller
(`exists_padicAlgebra_ringHom_of_frameComparison`) supplies them for free
and a future consumer may want the pinning; nothing here should be read
as a claim that they are needed.

STALE-AUDIT CORRECTION.  The "MISSING MACHINERY" note that used to close
this docstring said step 2 was blocked on
`IsAdicComplete (Ideal.span {(q : O₁)}) O₁` "not in mathlib at this
pin".  True of mathlib, false of this project: see the correction in the
docstring of `exists_padicAlgebra_of_additiveEquiv_sq` above.  In the
event the proof does not even need the gate in that form — the henselian
pair `(O₁, J)` comes straight from `HenselianRing.of_finite_algebra`. -/
theorem span_range_eq_top_of_adicPin
    {D : Type u} [Field D] [NumberField D]
    (q : ℕ) [Fact q.Prime]
    (I : Ideal (𝓞 D)) (hI : I.IsMaximal) (_hqI : (q : 𝓞 D) ∈ I)
    (π : 𝓞 D) (_hπ : π ∈ I) (_hπ2 : π ∉ I ^ 2)
    (O₁ : Type u) [CommRing O₁] [IsDomain O₁] [Algebra ℤ_[q] O₁]
    [Module.Finite ℤ_[q] O₁] [Module.Free ℤ_[q] O₁]
    (j₁ : 𝓞 D →+* O₁)
    (hdense : ∀ (n : ℕ) (z : O₁), ∃ a : 𝓞 D, z - j₁ a ∈ Ideal.span {j₁ π} ^ n)
    (hker : ∀ (n : ℕ) (a : 𝓞 D), j₁ a ∈ Ideal.span {j₁ π} ^ n ↔ a ∈ I ^ n) :
    Submodule.span ℤ_[q] (Set.range (j₁ : 𝓞 D → O₁)) = ⊤ := by
  classical
  set J : Ideal O₁ := (IsLocalRing.maximalIdeal ℤ_[q]).map (algebraMap ℤ_[q] O₁) with hJdef
  haveI hHen : HenselianRing O₁ J := HenselianRing.of_finite_algebra ℤ_[q] O₁
  have hJjac : J ≤ Ideal.jacobson (⊥ : Ideal O₁) := hHen.jac
  have hJne : J ≠ ⊤ := by
    intro htop
    have h1 : (1 : O₁) ∈ J := by rw [htop]; trivial
    simpa using Ideal.mem_jacobson_bot.mp (hJjac h1) (-1)
  haveI hntq : Nontrivial (O₁ ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJne
  haveI hlies : J.LiesOver (IsLocalRing.maximalIdeal ℤ_[q]) := by
    constructor
    refine le_antisymm Ideal.le_comap_map (IsLocalRing.le_maximalIdeal ?_)
    intro htop
    have h1 : (1 : ℤ_[q]) ∈ Ideal.under ℤ_[q] J := by rw [htop]; trivial
    have h2 : (1 : O₁) ∈ J := by simpa using h1
    exact hJne (Ideal.eq_top_of_isUnit_mem _ h2 isUnit_one)
  letI : Field (ℤ_[q] ⧸ IsLocalRing.maximalIdeal ℤ_[q]) := Ideal.Quotient.field _
  haveI hart : IsArtinianRing (O₁ ⧸ J) :=
    IsArtinianRing.of_finite (ℤ_[q] ⧸ IsLocalRing.maximalIdeal ℤ_[q]) (O₁ ⧸ J)
  haveI hloc : IsLocalRing (O₁ ⧸ J) := by
    refine IsLocalRing.of_isArtinianRing_isIdempotentElem ?_
    intro x hx
    obtain ⟨y, hy, hmk⟩ := HenselianRing.exists_isIdempotentElem_mk_eq (J := J) hx
    rcases IsIdempotentElem.eq_zero_or_eq_one_of_isDomain hy with h | h
    · exact Or.inl (by rw [← hmk, h, map_zero])
    · exact Or.inr (by rw [← hmk, h, map_one])
  -- Step 1: `j₁ π` is a non-unit.
  have hnu : ¬ IsUnit (j₁ π) := by
    intro hu
    have htop : Ideal.span {j₁ π} = ⊤ := Ideal.span_singleton_eq_top.mpr hu
    have h1 : j₁ 1 ∈ Ideal.span {j₁ π} ^ 1 := by rw [pow_one, htop]; trivial
    have h2 := (hker 1 1).mp h1
    rw [pow_one] at h2
    exact hI.ne_top (Ideal.eq_top_of_isUnit_mem _ h2 isUnit_one)
  -- Steps 2–3: its image in the local artinian quotient is a non-unit, hence nilpotent.
  have hnub : ¬ IsUnit (Ideal.Quotient.mk J (j₁ π)) := by
    intro hu
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective v
    rw [← map_mul, ← map_one (Ideal.Quotient.mk J), ← sub_eq_zero, ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem] at hv
    have hjac := hJjac hv
    have hunit : IsUnit (j₁ π * s) := by
      have h := Ideal.mem_jacobson_bot.mp hjac 1
      simpa using h
    exact hnu (isUnit_of_mul_isUnit_left hunit)
  have hmem : Ideal.Quotient.mk J (j₁ π) ∈ IsLocalRing.maximalIdeal (O₁ ⧸ J) :=
    (IsLocalRing.mem_maximalIdeal _).mpr hnub
  obtain ⟨N, hN⟩ : IsNilpotent (Ideal.jacobson (⊥ : Ideal (O₁ ⧸ J))) :=
    IsArtinianRing.isNilpotent_jacobson_bot
  rw [IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal (O₁ ⧸ J)) bot_ne_top] at hN
  have hpow : Ideal.Quotient.mk J (j₁ π ^ N) = 0 := by
    rw [map_pow]
    have hp2 : (Ideal.Quotient.mk J (j₁ π)) ^ N ∈ (IsLocalRing.maximalIdeal (O₁ ⧸ J)) ^ N :=
      Ideal.pow_mem_pow hmem N
    rw [hN] at hp2
    simpa using hp2
  have hstep : Ideal.span {j₁ π} ^ N ≤ J := by
    rw [Ideal.span_singleton_pow, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.Quotient.eq_zero_iff_mem.mp hpow
  -- Step 4: Nakayama over `ℤ_q`.
  set M : Submodule ℤ_[q] O₁ := Submodule.span ℤ_[q] (Set.range (j₁ : 𝓞 D → O₁)) with hMdef
  have hkey : (⊤ : Submodule ℤ_[q] (O₁ ⧸ M)) ≤
      (IsLocalRing.maximalIdeal ℤ_[q]) • (⊤ : Submodule ℤ_[q] (O₁ ⧸ M)) := by
    intro x _
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective M x
    obtain ⟨a, ha⟩ := hdense N z
    have haJ : z - j₁ a ∈ J := hstep ha
    have hsm : z - j₁ a ∈ (IsLocalRing.maximalIdeal ℤ_[q]) • (⊤ : Submodule ℤ_[q] O₁) := by
      rw [Ideal.smul_top_eq_map]
      exact haJ
    have h1 : (Submodule.Quotient.mk z : O₁ ⧸ M) = Submodule.Quotient.mk (z - j₁ a) := by
      rw [Submodule.Quotient.eq]
      have hja : (j₁ a : O₁) ∈ M := by
        rw [hMdef]
        exact Submodule.subset_span (Set.mem_range_self a)
      simpa using hja
    rw [h1]
    have hmem2 : M.mkQ (z - j₁ a) ∈
        Submodule.map M.mkQ ((IsLocalRing.maximalIdeal ℤ_[q]) • (⊤ : Submodule ℤ_[q] O₁)) :=
      Submodule.mem_map_of_mem hsm
    rwa [Submodule.map_smul'', Submodule.map_top, M.range_mkQ] at hmem2
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
    (IsLocalRing.maximalIdeal ℤ_[q]) (⊤ : Submodule ℤ_[q] (O₁ ⧸ M))
    (Module.Finite.fg_top) hkey (IsLocalRing.maximalIdeal_le_jacobson _)
  refine Submodule.eq_top_iff'.mpr fun z => ?_
  have hz0 : (Submodule.Quotient.mk z : O₁ ⧸ M) = 0 := by
    have hz : (Submodule.Quotient.mk z : O₁ ⧸ M) ∈ (⊤ : Submodule ℤ_[q] (O₁ ⧸ M)) := trivial
    rw [hbot] at hz
    simpa using hz
  exact (Submodule.Quotient.mk_eq_zero M).mp hz0

open _root_.NumberField in
/-- **A SPANNING pinned image turns the frame comparison into a ring
map** (PROVEN 2026-07-27 — a conjugation argument; no topology, no
completion, no pinning).

Given the `ℤ_q`-linearity of `g` (supplied by
`exists_padicAlgebra_of_additiveEquiv_sq`) and the spanning statement
(supplied by `span_range_eq_top_of_adicPin`), the ring map `ρ` is
FORCED, and no further input about `O` is needed.

THE ARGUMENT.  `O₁` acts faithfully on `Fin 2 → O₁` by scalars — test on
`u = 1` — and likewise `O` on `Fin 2 → O`.  Conjugation by `g` is a ring
isomorphism `Φ` between the `ℤ_q`-endomorphism rings of the two squares,
and it carries "multiplication by `j₁ a`" to "multiplication by `j a`"
(that is `hgj`).  The set of `b : O₁` for which `Φ (b • ·)` is again a
scalar multiplication is a `ℤ_q`-SUBMODULE of `O₁` containing
`j₁(𝒪_D)`, hence is all of `O₁` by `hspan`; `ρ b` is the scalar.  It is
additive and multiplicative because `Φ` is, injective because the
`O`-action is faithful, and it sends `algebraMap c = c • 1` to
`c • 1 = algebraMap c` by `hgsmul`. -/
theorem exists_ringHom_of_span_range_eq_top
    {D : Type u} [Field D] [NumberField D]
    (q : ℕ) [Fact q.Prime]
    (O₁ : Type u) [CommRing O₁] [Algebra ℤ_[q] O₁]
    (j₁ : 𝓞 D →+* O₁)
    (hspan : Submodule.span ℤ_[q] (Set.range (j₁ : 𝓞 D → O₁)) = ⊤)
    (O : Type u) [CommRing O] [Algebra ℤ_[q] O] (j : 𝓞 D →+* O)
    (g : (Fin 2 → O₁) → (Fin 2 → O))
    (hgadd : ∀ u u' : Fin 2 → O₁, g (u + u') = g u + g u')
    (hgbij : Function.Bijective g)
    (hgsmul : ∀ (c : ℤ_[q]) (u : Fin 2 → O₁), g (c • u) = c • g u)
    (hgj : ∀ (a : 𝓞 D) (u : Fin 2 → O₁), g (j₁ a • u) = j a • g u) :
    ∃ ρ : O₁ →+* O, Function.Injective ρ ∧
      (∀ c : ℤ_[q], ρ (algebraMap ℤ_[q] O₁ c) = algebraMap ℤ_[q] O c) ∧
      (∀ a : 𝓞 D, ρ (j₁ a) = j a) := by
  classical
  have hg0 : g 0 = 0 := by
    have h := hgadd 0 0
    simpa using h.symm
  -- the transported scalar is unique, because `g` is onto and `Fin 2 → O` has a `1`
  have huniq : ∀ z z' : O, (∀ u : Fin 2 → O₁, z • g u = z' • g u) → z = z' := by
    intro z z' h
    obtain ⟨u, hu⟩ := hgbij.2 (1 : Fin 2 → O)
    have h1 := h u
    rw [hu] at h1
    have h2 := congrFun h1 0
    simpa using h2
  -- the `ℤ_q`-submodule of those `b` whose conjugate is again a scalar multiplication
  set S : Submodule ℤ_[q] O₁ :=
    { carrier := {b : O₁ | ∃ z : O, ∀ u : Fin 2 → O₁, g (b • u) = z • g u}
      zero_mem' := ⟨0, fun u => by simpa using hg0⟩
      add_mem' := by
        rintro b b' ⟨z, hz⟩ ⟨z', hz'⟩
        refine ⟨z + z', fun u => ?_⟩
        rw [add_smul, hgadd, hz, hz', add_smul]
      smul_mem' := by
        rintro c b ⟨z, hz⟩
        refine ⟨c • z, fun u => ?_⟩
        rw [smul_assoc, hgsmul, hz, smul_assoc] }
  have hmemS : ∀ b : O₁, ∃ z : O, ∀ u : Fin 2 → O₁, g (b • u) = z • g u := by
    have htop : S = ⊤ := by
      rw [← top_le_iff, ← hspan, Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      exact ⟨j a, hgj a⟩
    intro b
    have hb : b ∈ S := by rw [htop]; exact Submodule.mem_top
    exact hb
  choose f hf using hmemS
  refine ⟨{ toFun := f
            map_one' := huniq _ _ fun u => by rw [← hf 1 u, one_smul, one_smul]
            map_mul' := fun b b' => huniq _ _ fun u => by
              rw [← hf (b * b') u, mul_smul, mul_smul, ← hf b' u, ← hf b (b' • u)]
            map_zero' := huniq _ _ fun u => by
              rw [← hf 0 u, zero_smul, zero_smul, hg0]
            map_add' := fun b b' => huniq _ _ fun u => by
              rw [← hf (b + b') u, add_smul, hgadd, hf b, hf b', add_smul] },
    ?_, ?_, ?_⟩
  · intro b b' hbb
    have hbb' : f b = f b' := hbb
    have hgg : ∀ u : Fin 2 → O₁, g (b • u) = g (b' • u) := fun u => by
      rw [hf b u, hf b' u, hbb']
    have hb1 : b • (1 : Fin 2 → O₁) = b' • (1 : Fin 2 → O₁) := hgbij.1 (hgg 1)
    have h0 := congrFun hb1 0
    simpa using h0
  · intro c
    refine huniq _ _ fun u => ?_
    show f (algebraMap ℤ_[q] O₁ c) • g u = algebraMap ℤ_[q] O c • g u
    rw [← hf (algebraMap ℤ_[q] O₁ c) u, algebraMap_smul, hgsmul, algebraMap_smul]
  · intro a
    refine huniq _ _ fun u => ?_
    show f (j₁ a) • g u = j a • g u
    rw [← hf (j₁ a) u, hgj]

open _root_.NumberField in
/-- **Transport of the coefficient-ring structure along a frame
comparison** (PROVEN 2026-07-27 over the three sub-leaves above — and
REPAIRED the same day: it is FALSE without `[IsDomain O₁]`).

Let `O₁` be a `ℤ_q`-algebra, finite and free over `ℤ_q`, carrying
`j₁ : 𝒪_D →+* O₁` which is `π`-adically dense (`hdense`) and detects the
`I`-adic filtration (`hker`) — i.e. `O₁` is the `I`-adic completion
`𝒪_{D,I}`, pinned exactly as in `exists_adicCoefficientRing`.  Let `O` be
any commutative ring with `j : 𝒪_D →+* O`, and suppose the two squares
are related by an ADDITIVE BIJECTION `g` intertwining the two
`𝒪_D`-actions.  Then `O` is itself a finite free `ℤ_q`-algebra of the
same rank as `O₁`, and `O₁` sits inside it over `𝒪_D`.

THE ARGUMENT.

1. *`O` is `q`-adically complete.*  `g` is additive and bijective, so it
   carries the `q`-adic filtration of `Fin 2 → O₁` onto that of
   `Fin 2 → O`; `O₁` is finite free over `ℤ_q`, hence `q`-adically
   complete and separated, and so therefore is `Fin 2 → O`.  The ring
   `O` is an additive direct summand of `Fin 2 → O`, and completeness
   and separatedness pass to summands.
2. *Hence `Algebra ℤ_[q] O`*, namely `padicIntLiftHom` of the
   `PadicIntLift` section above — this is the same construction that
   gives `𝒪ᵥ` its `ℤ_q`-structure in `padicIntAlgebra`, and it is
   available for exactly this reason.
3. *`g` is `ℤ_q`-linear.*  Every ADDITIVE endomorphism of a finite free
   `ℤ_q`-module is automatically `ℤ_q`-linear: for `c : ℤ_q` and
   integer approximants `cₖ` with `c - cₖ ∈ qᵏℤ_q`, additivity gives
   `f (c • y) - cₖ • f y ∈ qᵏ M` and `c • f y - cₖ • f y ∈ qᵏ M`, so the
   difference lies in `⋂ₖ qᵏ M = 0`.  The same computation applies to
   `g` itself.  Hence `Fin 2 → O` is `ℤ_q`-free of rank
   `2 · rank_{ℤ_q} O₁`, and `O`, as a summand, is free of rank
   `rank_{ℤ_q} O₁`.
4. *`ρ` exists.*  `O` acts faithfully on `Fin 2 → O` by scalars (test on
   `u = 1`), so `O` embeds in the additive endomorphism ring, and `g`
   conjugates "multiplication by `j₁ a`" to "multiplication by `j a`".
   The `ℤ_q`-submodule `M` spanned by `j₁ (𝒪_D)` is ALL of `O₁`
   (`span_range_eq_top_of_adicPin`), so the conjugation carries every
   scalar multiplication by `O₁` to a scalar multiplication by `O`.
   That is `ρ`, injective and satisfying `ρ ∘ j₁ = j` and
   `ρ ∘ algebraMap = algebraMap` by construction.

`hI`, `hqI`, `hπ` and `hπ2` are carried because the `π`-adic bookkeeping
of step 4 is stated relative to them; `hqI` in particular is what makes
`(q)` and `(j₁ π)` cofinal filtrations of `O₁`.

## FALSITY AUDIT (2026-07-27) — the leaf is FALSE without `[IsDomain O₁]`

The instance binder `[IsDomain O₁]` was ADDED on 2026-07-27.  Without
it the statement is refuted by an explicit counterexample, and step 4
of the argument above was wrong in its original form: it asserted that
"`O₁` is a finite `ℤ_q`-algebra, so some power of `(j₁ π)` lies in
`(q)`", which is FALSE for a non-local `O₁`, and with it fell the
Nakayama conclusion `M = O₁`.

THE COUNTEREXAMPLE.  Take `D = ℚ(i)`, `q = 5`, which SPLITS:
`5 = (2+i)(2−i)`.  Put `I = (2+i)` and `I' = (2−i)`, both of residue
degree and ramification index `1`, so `𝒪_{D,I} = 𝒪_{D,I'} = ℤ₅`, with
`σ, σ' : 𝒪_D → ℤ₅` the two completions.  Take `π = 2+i`, so `π ∈ I`,
`π ∉ I²`, and `π ∉ I'` — hence `σ π` is a uniformizer of `ℤ₅` and
`σ' π` is a UNIT.  Now set

    O₁ := ℤ₅ × ℤ₅ × ℤ₅ ,   j₁ a := (σ a, σ' a, σ' a) .

*Every hypothesis holds.*  `O₁` is a finite free `ℤ₅`-algebra of rank
`3`.  `j₁ π = (σ π, unit, unit)`, so
`Ideal.span {j₁ π} ^ n = 5ⁿℤ₅ × ℤ₅ × ℤ₅`: the last two coordinates are
UNCONSTRAINED at every precision.  Hence `hdense` reduces to density of
`𝒪_D` in the first `ℤ₅`, which holds, and `hker` reduces to
`σ a ∈ 5ⁿℤ₅ ↔ a ∈ Iⁿ`, which is `mem_span_uniformizer_pow_iff`.

*But `j₁(𝒪_D)` does not span.*  Its `ℤ₅`-span is
`ℤ₅ × {(t, t)}`, of rank `2 < 3`, because the second and third
coordinates of `j₁ a` are EQUAL by construction.  So the Nakayama step
has no chance: the `(j₁ π)`-adic topology simply does not see the last
two factors.

*And the conclusion fails.*  Take

    O := ℤ₅ × ℤ₅[ε]/(ε²) ,   j a := (σ a, σ' a) ,

again of `ℤ₅`-rank `3`.  As `𝒪_D`-modules both squares are
`(ℤ₅ via σ)² ⊕ (ℤ₅ via σ')⁴` — for `O` because `𝒪_D` acts on
`ℤ₅[ε]/(ε²)` through the SCALAR `σ' a` — so an additive bijection `g`
with `g (j₁ a • u) = j a • g u` exists.  Yet there is NO injective ring
map `ρ : O₁ →+* O` at all: a ring map sends the three orthogonal
idempotents of `ℤ₅³` to three orthogonal idempotents of `O` summing to
`1`, and `O` has only the four idempotents `(0,0), (1,0), (0,1), (1,1)`
because both of its factors are local.  So one of the three must be
`0`, and `ρ` then kills a whole nonzero factor.

WHY `[IsDomain O₁]` IS THE RIGHT REPAIR, and why it is free.  A domain
has no nontrivial idempotents, and — being finite over the complete
local `ℤ_q` — is then LOCAL, which is exactly what makes `(j₁ π)ᴺ`
land inside `(q)` and restores the Nakayama step; this is
`span_range_eq_top_of_adicPin` above.  The only consumer,
`exists_ringEquiv_of_frameComparison` below, already assumes
`[IsDomain O₁]` (it needs `[IsIntegrallyClosed O₁]` too), so the added
binder costs nothing at the call site.  In the real application
`O₁ = 𝒪_{D,I}` is a complete DVR. -/
theorem exists_padicAlgebra_ringHom_of_frameComparison
    {D : Type u} [Field D] [NumberField D]
    (q : ℕ) [Fact q.Prime]
    (I : Ideal (𝓞 D)) (hI : I.IsMaximal) (hqI : (q : 𝓞 D) ∈ I)
    (π : 𝓞 D) (hπ : π ∈ I) (hπ2 : π ∉ I ^ 2)
    (O₁ : Type u) [CommRing O₁] [IsDomain O₁] [Algebra ℤ_[q] O₁] [Module.Finite ℤ_[q] O₁]
    [Module.Free ℤ_[q] O₁]
    (j₁ : 𝓞 D →+* O₁)
    (hdense : ∀ (n : ℕ) (z : O₁), ∃ a : 𝓞 D, z - j₁ a ∈ Ideal.span {j₁ π} ^ n)
    (hker : ∀ (n : ℕ) (a : 𝓞 D), j₁ a ∈ Ideal.span {j₁ π} ^ n ↔ a ∈ I ^ n)
    (O : Type u) [CommRing O] (j : 𝓞 D →+* O)
    (g : (Fin 2 → O₁) → (Fin 2 → O))
    (hgadd : ∀ u u' : Fin 2 → O₁, g (u + u') = g u + g u')
    (hgbij : Function.Bijective g)
    (hgj : ∀ (a : 𝓞 D) (u : Fin 2 → O₁), g (j₁ a • u) = j a • g u) :
    ∃ (_ : Algebra ℤ_[q] O) (_ : Module.Finite ℤ_[q] O) (_ : Module.Free ℤ_[q] O)
      (ρ : O₁ →+* O), Function.Injective ρ ∧
      (∀ c : ℤ_[q], ρ (algebraMap ℤ_[q] O₁ c) = algebraMap ℤ_[q] O c) ∧
      (∀ a : 𝓞 D, ρ (j₁ a) = j a) ∧
      Module.finrank ℤ_[q] O = Module.finrank ℤ_[q] O₁ := by
  obtain ⟨iAlg, iFin, iFree, hrank, hgsmul⟩ :=
    exists_padicAlgebra_of_additiveEquiv_sq q O₁ O g hgadd hgbij
  letI := iAlg; letI := iFin; letI := iFree
  obtain ⟨ρ, hρinj, hρZ, hρj⟩ :=
    exists_ringHom_of_span_range_eq_top q O₁ j₁
      (span_range_eq_top_of_adicPin q I hI hqI π hπ hπ2 O₁ j₁ hdense hker) O j g
      hgadd hgbij hgsmul hgj
  exact ⟨iAlg, iFin, iFree, ρ, hρinj, hρZ, hρj, hrank⟩

/-- **An injection of `ℤ_q`-algebras of equal rank out of an integrally
closed domain is surjective** (PROVEN 2026-07-27 — pure commutative
algebra; Serre, *Local Fields* I, or Neukirch I.2 for the
integral-closure step).

THE ARGUMENT ORIGINALLY RECORDED.  Write `n` for the common rank and
`K` for the fraction field of `O₁`.  Since `O₁` is a domain finite over
`ℤ_q`, the localization `O₁ ⊗_{ℤ_q} ℚ_q` is a field, hence equal to
`K`, of `ℚ_q`-dimension `n`.  Now `ρ` is an injection of finite free
`ℤ_q`-modules of equal rank `n`, so `ρ ⊗ ℚ_q : K → O ⊗_{ℤ_q} ℚ_q` is an
injection of `ℚ_q`-spaces of equal dimension, hence an ISOMORPHISM.
`O` is `ℤ_q`-free, so `O → O ⊗_{ℤ_q} ℚ_q ≅ K` is injective: `O` is a
domain, and a subring of `K` containing `O₁`.  Being finite over `ℤ_q`
it is integral over `O₁`, and `O₁` is integrally closed in `K`, so
`O ⊆ O₁`.  With `O₁ ⊆ O` that is surjectivity.

THE ARGUMENT ACTUALLY EXECUTED, which avoids tensor products entirely
and never constructs the embedding `O ↪ K` as a map.  Fix `x : O`.

* *A denominator exists.*  `ρ` is `ℤ_q`-linear, so its range `N` is a
  `ℤ_q`-submodule of `O` with `finrank N = finrank O₁ = finrank O`;
  `Module.finrank_quotient_add_finrank_le` then forces
  `finrank (O ⧸ N) = 0`, and `Module.finrank_eq_zero_iff` turns that
  into: some `c ≠ 0` in `ℤ_q` has `c • x = ρ a`, `a : O₁`.  This is the
  only place the rank equality is used.
* *The numerator is divisible by the denominator.*  `O` is module-finite
  over `O₁` along `ρ` (`Module.Finite.of_restrictScalars_finite`), so
  `x` is integral: `p` monic over `O₁` with `p(x) = 0`.  Writing
  `cc := algebraMap ℤ_q O₁ c`, `Polynomial.scaleRoots_eval₂_mul` at
  `ρ cc * x = ρ a` gives `ρ ((p.scaleRoots cc).eval a) = 0`, hence
  `(p.scaleRoots cc).eval a = 0` by injectivity.  Read in
  `K = FractionRing O₁`, the SAME identity says `p (ι a / ι cc) = 0`,
  so `ι a / ι cc` is integral over `O₁` and
  `IsIntegrallyClosed.isIntegral_iff` produces `y : O₁` with
  `cc * y = a`.
* *Cancel.*  `ρ (cc * y) = ρ a = c • x` reads `c • ρ y = c • x`, and `O`
  is `ℤ_q`-torsion-free (it is free), so `ρ y = x`.

Note this route never needs `IsDomain O`, and in particular does not
have to prove it first.

WHY EACH HYPOTHESIS IS NEEDED, since each excludes a genuine
counterexample.  Drop `IsIntegrallyClosed O₁` and take `O₁ = ℤ_q[q√d]`
inside `O = ℤ_q[√d]` — equal rank, injective, not surjective.  Drop the
rank equality and take `O₁ = ℤ_q ⊆ O = ℤ_q[√d]`.  Drop `IsDomain O₁`
and the fraction field of the first paragraph does not exist.  Drop
`hρZ` and `ρ` need not be `ℤ_q`-linear, so the rank comparison says
nothing.

Note that `IsDomain O` is NOT a hypothesis, which is the whole point of
the leaf as far as `exists_algebraicClosureEmbedding_of_tateFrame_mult`
is concerned: the audit there rejects `IsDomain O` as an ad-hoc
assumption and requires it to be DERIVED.  The executed proof does not
prove it either — it does not need to.  The consumer gets it for free
from the ring isomorphism `O ≃+* O₁` that this leaf and
`exists_padicAlgebra_ringHom_of_frameComparison` assemble in
`exists_ringEquiv_of_frameComparison`, transporting `IsDomain O₁`. -/
theorem surjective_of_finrank_eq_of_isIntegrallyClosed
    (q : ℕ) [Fact q.Prime]
    (O₁ : Type u) [CommRing O₁] [IsDomain O₁] [IsIntegrallyClosed O₁]
    [Algebra ℤ_[q] O₁] [Module.Finite ℤ_[q] O₁] [Module.Free ℤ_[q] O₁]
    (O : Type u) [CommRing O] [Algebra ℤ_[q] O] [Module.Finite ℤ_[q] O]
    [Module.Free ℤ_[q] O]
    (ρ : O₁ →+* O) (hρinj : Function.Injective ρ)
    (hρZ : ∀ c : ℤ_[q], ρ (algebraMap ℤ_[q] O₁ c) = algebraMap ℤ_[q] O c)
    (hrank : Module.finrank ℤ_[q] O = Module.finrank ℤ_[q] O₁) :
    Function.Surjective ρ := by
  classical
  -- `O` is an `O₁`-algebra through `ρ`, and the two `ℤ_q`-structures agree.
  letI : Algebra O₁ O := ρ.toAlgebra
  haveI : IsScalarTower ℤ_[q] O₁ O :=
    IsScalarTower.of_algebraMap_eq fun c => (hρZ c).symm
  haveI : Module.Finite O₁ O := Module.Finite.of_restrictScalars_finite ℤ_[q] O₁ O
  -- STEP 1.  `O ⧸ ρ(O₁)` has `finrank` zero: every element of `O` has a nonzero
  -- `ℤ_q`-multiple in the image of `ρ`.  This is the only use of `hrank`.
  have hkey : ∀ x : O, ∃ c : ℤ_[q], c ≠ 0 ∧ ∃ a : O₁, ρ a = c • x := by
    have hL : Function.Injective ⇑(IsScalarTower.toAlgHom ℤ_[q] O₁ O).toLinearMap := hρinj
    have hNrank : Module.finrank ℤ_[q]
        (LinearMap.range (IsScalarTower.toAlgHom ℤ_[q] O₁ O).toLinearMap)
        = Module.finrank ℤ_[q] O₁ := LinearMap.finrank_range_of_inj hL
    have hle := Module.finrank_quotient_add_finrank_le (R := ℤ_[q]) (M := O)
      (LinearMap.range (IsScalarTower.toAlgHom ℤ_[q] O₁ O).toLinearMap)
    have hquot0 : Module.finrank ℤ_[q]
        (O ⧸ LinearMap.range (IsScalarTower.toAlgHom ℤ_[q] O₁ O).toLinearMap) = 0 := by
      omega
    intro x
    obtain ⟨c, hc0, hc⟩ :=
      (Module.finrank_eq_zero_iff (R := ℤ_[q])).mp hquot0 (Submodule.Quotient.mk x)
    refine ⟨c, hc0, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hc
    obtain ⟨a, ha⟩ := hc
    exact ⟨a, ha⟩
  -- STEP 2.  Surjectivity, one element at a time.
  intro x
  obtain ⟨c, hc0, a, ha⟩ := hkey x
  set cc : O₁ := algebraMap ℤ_[q] O₁ c with hcc
  have hcc0 : cc ≠ 0 := by
    rw [hcc, Algebra.algebraMap_eq_smul_one]
    intro h
    exact one_ne_zero (smul_right_injective O₁ hc0 (by simpa using h))
  have hrcc : ρ cc = algebraMap ℤ_[q] O c := hρZ c
  have hax : ρ cc * x = ρ a := by rw [hrcc, ← Algebra.smul_def, ha]
  -- `x` is integral over `O₁`, and the scaled polynomial kills the numerator `a`.
  obtain ⟨p, hpm, hpe⟩ : IsIntegral O₁ x := IsIntegral.of_finite O₁ x
  have hscaled : Polynomial.eval₂ ρ (ρ a) (p.scaleRoots cc) = 0 := by
    have hmul := Polynomial.scaleRoots_eval₂_mul (p := p) (f := ρ) (r := x) (s := cc)
    rw [hax] at hmul
    rw [hmul]
    have hzero : Polynomial.eval₂ ρ x p = 0 := hpe
    rw [hzero, mul_zero]
  have hscaled' : Polynomial.eval a (p.scaleRoots cc) = 0 := by
    rw [Polynomial.eval₂_at_apply] at hscaled
    exact hρinj (by simpa using hscaled)
  -- Read in the fraction field: `a / cc` is integral over `O₁`, hence lies in `O₁`.
  set K := FractionRing O₁
  set ι : O₁ →+* K := algebraMap O₁ K with hι
  have hιinj : Function.Injective ι := IsFractionRing.injective O₁ K
  have hιcc : ι cc ≠ 0 := fun h => hcc0 (hιinj (by simpa using h))
  set t : K := ι a / ι cc with ht
  have htmul : ι cc * t = ι a := by
    rw [ht, mul_div_cancel₀]
    exact hιcc
  have hpt : Polynomial.eval₂ ι t p = 0 := by
    have h := Polynomial.scaleRoots_eval₂_mul (p := p) (f := ι) (r := t) (s := cc)
    rw [htmul] at h
    rw [Polynomial.eval₂_at_apply, hscaled', map_zero] at h
    rcases mul_eq_zero.mp h.symm with h' | h'
    · exact absurd h' (pow_ne_zero _ hιcc)
    · exact h'
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp (⟨p, hpm, hpt⟩ : IsIntegral O₁ t)
  have hcy : cc * y = a := by
    apply hιinj
    rw [map_mul, hy, htmul]
  -- Cancel the denominator: `O` is `ℤ_q`-torsion-free because it is free.
  have hfin : c • ρ y = c • x := by
    have hmul : ρ (cc * y) = ρ a := by rw [hcy]
    rw [map_mul, hrcc, ← Algebra.smul_def] at hmul
    rw [hmul, ha]
  exact ⟨y, smul_right_injective O hc0 hfin⟩

open _root_.NumberField in
/-- **An `𝒪_D`-frame comparison identifies the coefficient rings**
(PROVEN 2026-07-27 over the two leaves above).

If two commutative rings `O₁`, `O` carry ring maps from `𝒪_D` and their
squares are related by an additive bijection `g` intertwining the two
`𝒪_D`-actions, and `O₁` is the `I`-adic completion `𝒪_{D,I}` (finite
free over `ℤ_q`, an integrally closed domain, pinned by `hdense` and
`hker`), then `O ≃+* O₁` over `𝒪_D`.

This is the algebraic core of
`exists_algebraicClosureEmbedding_of_tateFrame_mult`, and the reason its
`Function.Injective ι` clause is derivable rather than assumed. -/
theorem exists_ringEquiv_of_frameComparison
    {D : Type u} [Field D] [NumberField D]
    (q : ℕ) [Fact q.Prime]
    (I : Ideal (𝓞 D)) (hI : I.IsMaximal) (hqI : (q : 𝓞 D) ∈ I)
    (π : 𝓞 D) (hπ : π ∈ I) (hπ2 : π ∉ I ^ 2)
    (O₁ : Type u) [CommRing O₁] [IsDomain O₁] [IsIntegrallyClosed O₁]
    [Algebra ℤ_[q] O₁] [Module.Finite ℤ_[q] O₁] [Module.Free ℤ_[q] O₁]
    (j₁ : 𝓞 D →+* O₁)
    (hdense : ∀ (n : ℕ) (z : O₁), ∃ a : 𝓞 D, z - j₁ a ∈ Ideal.span {j₁ π} ^ n)
    (hker : ∀ (n : ℕ) (a : 𝓞 D), j₁ a ∈ Ideal.span {j₁ π} ^ n ↔ a ∈ I ^ n)
    (O : Type u) [CommRing O] (j : 𝓞 D →+* O)
    (g : (Fin 2 → O₁) → (Fin 2 → O))
    (hgadd : ∀ u u' : Fin 2 → O₁, g (u + u') = g u + g u')
    (hgbij : Function.Bijective g)
    (hgj : ∀ (a : 𝓞 D) (u : Fin 2 → O₁), g (j₁ a • u) = j a • g u) :
    ∃ e : O ≃+* O₁, ∀ a : 𝓞 D, e (j a) = j₁ a := by
  obtain ⟨iAlg, iFin, iFree, ρ, hρinj, hρZ, hρj, hrank⟩ :=
    exists_padicAlgebra_ringHom_of_frameComparison q I hI hqI π hπ hπ2 O₁ j₁ hdense hker
      O j g hgadd hgbij hgj
  letI := iAlg; letI := iFin; letI := iFree
  have hsurj : Function.Surjective ρ :=
    surjective_of_finrank_eq_of_isIntegrallyClosed q O₁ O ρ hρinj hρZ hrank
  refine ⟨(RingEquiv.ofBijective ρ ⟨hρinj, hsurj⟩).symm, fun a => ?_⟩
  exact (RingEquiv.ofBijective ρ ⟨hρinj, hsurj⟩).symm_apply_eq.mpr (hρj a).symm

/-- **An injective ring map from a finite `ℤ_ℓ`-algebra domain into
`ℚ̄_ℓ`** (PROVEN).  Factor through `FractionRing O`, which is algebraic
over `ℤ_ℓ` because `O` is finite and torsion-free over it, and lift into
the algebraically closed target with `IsAlgClosed.lift`.

This is a REPRODUCTION of `exists_injective_ringHom_algebraicClosure_of_moduleFinite`
in the DOWNSTREAM `Modularity/KhareWintenberger.lean`, which imports this
module and is therefore unusable from here — the same situation as
`adicArithFrob_rootsOfUnity_pow_absNorm` and
`cyclotomicCharacter_adicArithFrob_absNorm` above, and with the same
intended cleanup: delete the downstream copy, not this one. -/
theorem exists_injective_ringHom_algebraicClosure_of_padicModuleFinite {ℓ : ℕ}
    [Fact ℓ.Prime] (O : Type*) [CommRing O] [IsDomain O] [Algebra ℤ_[ℓ] O]
    [Module.Finite ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O)) :
    ∃ ι : O →+* AlgebraicClosure ℚ_[ℓ], Function.Injective ι := by
  classical
  -- the fraction field of `O`, an algebraic torsion-free `ℤ_ℓ`-algebra
  have hOK : Function.Injective (algebraMap O (FractionRing O)) :=
    IsFractionRing.injective O (FractionRing O)
  haveI : Module.IsTorsionFree ℤ_[ℓ] O :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hZinj
  haveI : IsScalarTower ℤ_[ℓ] O (FractionRing O) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.IsTorsionFree ℤ_[ℓ] (FractionRing O) :=
    Module.isTorsionFree_iff_faithfulSMul.mpr inferInstance
  haveI : Algebra.IsAlgebraic ℤ_[ℓ] (FractionRing O) :=
    (IsFractionRing.isAlgebraic_iff' ℤ_[ℓ] O (FractionRing O)).1 inferInstance
  -- `ℚ̄_ℓ` as a torsion-free `ℤ_ℓ`-algebra through `ℤ_ℓ → ℚ_ℓ → ℚ̄_ℓ`
  letI : Algebra ℤ_[ℓ] (AlgebraicClosure ℚ_[ℓ]) :=
    ((algebraMap ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ])).comp
      (algebraMap ℤ_[ℓ] ℚ_[ℓ])).toAlgebra
  haveI : Module.IsTorsionFree ℤ_[ℓ] (AlgebraicClosure ℚ_[ℓ]) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (fun _ _ hxy => IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ]
        ((algebraMap ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ])).injective hxy))
  -- lift the algebraic extension into the algebraically closed target
  refine ⟨(IsAlgClosed.lift (R := ℤ_[ℓ]) (S := FractionRing O)
    (M := AlgebraicClosure ℚ_[ℓ])).toRingHom.comp
      (algebraMap O (FractionRing O)), fun _ _ hxy => hOK ?_⟩
  exact RingHom.injective _ hxy

open _root_.NumberField in
/-- **The coefficient ring of an `𝒪_D`-frame of the Tate module is
`𝒪_{D,I}`, hence embeds in `ℚ̄_q` compatibly with `D`** (PROVEN
2026-07-27 over `exists_ringEquiv_of_frameComparison` — i.e. over the
two commutative-algebra leaves
`exists_padicAlgebra_ringHom_of_frameComparison` and
`surjective_of_finrank_eq_of_isIntegrallyClosed` — plus the PROVEN
`exists_tateFrame_of_adicCoefficientRing`; the commutative-algebra half
of `exists_weilFrobeniusSystem_of_mult`).

Given a frame `(O, τ, φ)` of `TatePt m x I π` which REMEMBERS THE REAL
MULTIPLICATION — i.e. carries `j : 𝒪_D →+* O` with the intertwining
`hj` — there are a ring map `ψ : D →+* ℚ̄_q`, an INJECTIVE ring map
`ι : O →+* ℚ̄_q`, and the compatibility `ι ∘ j = ψ ∘ (𝒪_D ↪ D)`.

HOW IT IS PROVEN (2026-07-27).  The step that removes the geometry is
the FRAME COMPARISON of the subsection above: the honest frame `φ₁` by
`O₁ := 𝒪_{D,I}` at the same `(q, I, π)` already exists, PROVEN, as
`exists_tateFrame_of_adicCoefficientRing`, so `g := φ⁻¹ ∘ φ₁` is an
additive bijection `(Fin 2 → O₁) → (Fin 2 → O)` intertwining the two
`𝒪_D`-actions.  `exists_ringEquiv_of_frameComparison` then returns
`e : O ≃+* O₁` with `e ∘ j = j₁`, and the two embeddings are read off
`O₁` alone: `ι = ι₁ ∘ e` with `ι₁` from
`exists_injective_ringHom_algebraicClosure_of_padicModuleFinite`, and
`ψ = IsFractionRing.lift (ι₁ ∘ j₁)`, which is legitimate because
`𝒪_D ↪ 𝒪_{D,I} ↪ ℚ̄_q` is injective and `D` is the fraction field of
`𝒪_D`.  The compatibility `ι ∘ j = ψ ∘ (𝒪_D ↪ D)` is then
`IsFractionRing.lift_algebraMap`, and `Function.Injective ι` is a
composite of two injections — DERIVED, exactly as the audit demands.

Note that `hφequiv` and `τ` are indeed never used, as predicted below,
and neither is `hdim` except through `exists_tateFrame_of_adicCoefficientRing`.

THE ARGUMENT the repairer of the sibling left for its prover is recorded
below; it is now discharged by the two leaves above, and steps 1–3 are
what `exists_padicAlgebra_ringHom_of_frameComparison` and
`surjective_of_finrank_eq_of_isIntegrallyClosed` say.  Do NOT look for a
hypothesis that hands you `Function.Injective ι`, and do NOT reintroduce
`IsDomain O`: derive `O = 𝒪_{D,I}` instead.

1. `O` is a `ℤ_q`-algebra, finite and free.  Nothing says so, but `φ`
   forces `O ⊕ O ≅ T ≅ ℤ_q^{2d}` as abelian groups, and every additive
   endomorphism of `ℤ_q^n` is `ℤ_q`-linear (divisibility by `q^n` is
   preserved).  In particular `rank_{ℤ_q} O = d = [𝒪_{D,I} : ℤ_q]`,
   using `hdim` to know `T` has `ℤ_q`-rank `2d`.
2. `j` is injective and `O` contains `𝒪_{D,I}`.  By `hj`, `j a` acts on
   `T` as `m.act a`, so `j` is injective (a nonzero `a ∈ 𝒪_D` acts
   injectively on the `I`-adic Tate module, `T` being `I`-adically
   separated), and the closure of `j(𝒪_D)` inside the `q`-adically
   complete `O` is a copy of the `I`-adic completion `𝒪_{D,I}`.
3. `O = 𝒪_{D,I}`.  `O` is a ring extension of `𝒪_{D,I}` of the same
   `ℤ_q`-rank, hence integral over it and contained in its fraction
   field; `𝒪_{D,I}` is integrally closed, so the inclusion is an
   equality.
4. `𝒪_{D,I}` is a complete discrete valuation ring of characteristic
   zero with residue characteristic `q`, so its fraction field is a
   finite extension of `ℚ_q` and embeds in `ℚ̄_q`; `ψ` is the induced
   place of `D` over `q` and injectivity of `ι` is automatic, a field
   map being injective.

Step 3 is where the two counterexamples of the audit below die:
`ℤ₁₃[ε]` is not integrally closed in the relevant sense (it has a
nonzero nilpotent, so it is not contained in any field) and admits no
`j` at all, and `ℤ₁₃ × ℤ₁₃` admits no `j` because `𝒪_D` acts through the
multiplicity space and is scalar on neither factor.  Neither survives
the pinning, which is the whole content of the repair.

Note `hφequiv` and `τ` are carried but not needed for the argument: the
conclusion is about the RING `O`, and Galois-equivariance of the frame
plays no part in identifying it.  They are kept so that the hypothesis
block is literally the frame produced by
`exists_tateFrame_of_levelStructure`, which is what the consumer has. -/
theorem exists_algebraicClosureEmbedding_of_tateFrame_mult
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (hdim : SmoothOfRelativeDimension (Module.finrank ℚ D) f)
    (q : ℕ) (hq : Fact q.Prime)
    (I : Ideal (NumberField.RingOfIntegers D)) (hI : I.IsMaximal)
    (hqI : (q : NumberField.RingOfIntegers D) ∈ I)
    (π : NumberField.RingOfIntegers D) (hπ : π ∈ I) (hπ2 : π ∉ I ^ 2)
    (O : Type u) (iCR : CommRing O) (iTS : TopologicalSpace O) (iTR : IsTopologicalRing O)
    (τ : GaloisRep F O (Fin 2 → O)) (φ : (Fin 2 → O) → TatePt m x I π)
    (j : NumberField.RingOfIntegers D →+* O)
    (hφadd : ∀ (u u' : Fin 2 → O) (n : ℕ),
      (φ (u + u')).1 n = ab.add ((φ u).1 n) ((φ u').1 n))
    (hφbij : Function.Bijective φ)
    (hφequiv : ∀ (σ : Field.absoluteGaloisGroup F) (u : Fin 2 → O) (n : ℕ),
      (φ (τ σ u)).1 n = ab.galSMul x σ ((φ u).1 n))
    (hj : ∀ (a : NumberField.RingOfIntegers D) (u : Fin 2 → O) (n : ℕ),
      (φ (j a • u)).1 n = m.act a ((φ u).1 n)) :
    ∃ (ψ : D →+* AlgebraicClosure ℚ_[q]) (ι : O →+* AlgebraicClosure ℚ_[q]),
      Function.Injective ι ∧
      ∀ a : NumberField.RingOfIntegers D,
        ι (j a) = ψ (algebraMap (NumberField.RingOfIntegers D) D a) := by
  haveI := hq
  classical
  -- `I` is nonzero: it contains the rational prime `q`.
  have hI0 : I ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot, Nat.cast_eq_zero] at hqI
    exact (Fact.out : q.Prime).ne_zero hqI
  let v : HeightOneSpectrum (𝓞 D) := ⟨I, hI.isPrime, hI0⟩
  -- The HONEST coefficient ring `𝒪_{D,I}` and its `ℤ_q`-structure.
  letI iAlg₁ : Algebra ℤ_[q] (v.adicCompletionIntegers D) := padicIntAlgebra v q hqI
  obtain ⟨iFin₁, iFree₁, iMT₁⟩ := module_finite_free_moduleTopology_padicIntAlgebra v q hqI
  haveI := iFin₁; haveI := iFree₁; haveI := iMT₁
  have hcplt : IsAdicComplete
      (Ideal.span {algebraMap (𝓞 D) (v.adicCompletionIntegers D) π})
      (v.adicCompletionIntegers D) :=
    isAdicComplete_span_uniformizer v π hπ hπ2
  have hdense : ∀ (n : ℕ) (z : v.adicCompletionIntegers D),
      ∃ a : 𝓞 D, z - algebraMap (𝓞 D) (v.adicCompletionIntegers D) a ∈
        Ideal.span {algebraMap (𝓞 D) (v.adicCompletionIntegers D) π} ^ n :=
    fun n z => exists_sub_mem_span_uniformizer_pow v π hπ hπ2 n z
  have hker : ∀ (n : ℕ) (a : 𝓞 D),
      algebraMap (𝓞 D) (v.adicCompletionIntegers D) a ∈
        Ideal.span {algebraMap (𝓞 D) (v.adicCompletionIntegers D) π} ^ n ↔ a ∈ I ^ n :=
    fun n a => mem_span_uniformizer_pow_iff v π hπ hπ2 n a
  -- The HONEST frame at the same `(q, I, π)`.
  obtain ⟨τ₁, φ₁, hφadd₁, hφbij₁, hφequiv₁, hφj₁⟩ :=
    exists_tateFrame_of_adicCoefficientRing m x hdim q I hI hqI π hπ hπ2
      (v.adicCompletionIntegers D) (algebraMap (𝓞 D) (v.adicCompletionIntegers D))
      hcplt hdense hker
  -- The comparison `g = φ⁻¹ ∘ φ₁`, characterized by `φ ∘ g = φ₁`.
  obtain ⟨g, hgdef⟩ :
      ∃ g : (Fin 2 → v.adicCompletionIntegers D) → (Fin 2 → O), ∀ u, φ (g u) = φ₁ u := by
    refine ⟨fun u => (Equiv.ofBijective φ hφbij).symm (φ₁ u), fun u => ?_⟩
    exact (Equiv.ofBijective φ hφbij).apply_symm_apply (φ₁ u)
  have hgadd : ∀ u u' : Fin 2 → v.adicCompletionIntegers D, g (u + u') = g u + g u' := by
    intro u u'
    refine hφbij.1 (Subtype.ext (funext fun n => ?_))
    rw [hgdef, hφadd, hgdef, hgdef, hφadd₁]
  have hgbij : Function.Bijective g := by
    constructor
    · intro u u' huu
      exact hφbij₁.1 (by rw [← hgdef, ← hgdef, huu])
    · intro w
      obtain ⟨u, hu⟩ := hφbij₁.2 (φ w)
      exact ⟨u, hφbij.1 (by rw [hgdef, hu])⟩
  have hgj : ∀ (a : 𝓞 D) (u : Fin 2 → v.adicCompletionIntegers D),
      g (algebraMap (𝓞 D) (v.adicCompletionIntegers D) a • u) = j a • g u := by
    intro a u
    refine hφbij.1 (Subtype.ext (funext fun n => ?_))
    rw [hgdef, hj, hgdef, hφj₁]
  -- The pinning: the frame's coefficient ring IS `𝒪_{D,I}`.
  obtain ⟨e, he⟩ :=
    exists_ringEquiv_of_frameComparison q I hI hqI π hπ hπ2 (v.adicCompletionIntegers D)
      (algebraMap (𝓞 D) (v.adicCompletionIntegers D)) hdense hker O j g hgadd hgbij hgj
  -- `𝒪_{D,I}` embeds into `ℚ̄_q`, injectively.
  have hj₁inj : Function.Injective (algebraMap (𝓞 D) (v.adicCompletionIntegers D)) :=
    FaithfulSMul.algebraMap_injective (𝓞 D) (v.adicCompletionIntegers D)
  have hqne : (q : v.adicCompletionIntegers D) ≠ 0 := by
    intro h0
    refine (Fact.out : q.Prime).ne_zero ?_
    have : ((q : 𝓞 D)) = 0 := hj₁inj (by simpa using h0)
    exact_mod_cast this
  have hZinj : Function.Injective (algebraMap ℤ_[q] (v.adicCompletionIntegers D)) := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    by_contra hcne
    rw [PadicInt.unitCoeff_spec hcne, map_mul, map_pow, map_natCast] at hc
    rcases mul_eq_zero.mp hc with h | h
    · exact ((PadicInt.unitCoeff hcne).isUnit.map
        (algebraMap ℤ_[q] (v.adicCompletionIntegers D))).ne_zero h
    · exact hqne (pow_eq_zero_iff'.mp h).1
  obtain ⟨ι₁, hι₁inj⟩ :=
    exists_injective_ringHom_algebraicClosure_of_padicModuleFinite (ℓ := q)
      (v.adicCompletionIntegers D) hZinj
  -- `ψ` is the place of `D` over `q` determined by `I`: the fraction-field
  -- extension of the injective `𝒪_D → 𝒪_{D,I} → ℚ̄_q`.
  have hgψ : Function.Injective
      (ι₁.comp (algebraMap (𝓞 D) (v.adicCompletionIntegers D))) := hι₁inj.comp hj₁inj
  refine ⟨IsFractionRing.lift (A := 𝓞 D) (K := D) hgψ, ι₁.comp e.toRingHom,
    hι₁inj.comp e.injective, fun a => ?_⟩
  rw [RingHom.comp_apply, show e.toRingHom (j a) = e (j a) from rfl, he a]
  exact (IsFractionRing.lift_algebraMap (K := D) hgψ a).symm

/-! #### The arithmetic half, cut into RATIONALITY and INDEPENDENCE

`exists_intWeilPolynomial_of_mult` below is PROVEN by assembly over the
two leaves that follow this note.  The seam is the one place where the
quantifier order of the target — `a, b` BEFORE `q` and `I` — can be
manufactured out of statements in which they come AFTER, and it is worth
recording why that is not circular.

* `exists_weilCoeffs_of_tateFrame_mult` is the target with `a`, `b` and
  `bad` moved INSIDE the frame quantifiers: *this* frame's Frobenius
  characteristic polynomial has its coefficients in `j(𝒪_D)`.  That is
  pure rationality — Weil, one residue characteristic at a time — and it
  says nothing about `I`-independence.
* `exists_finset_weilCoeffs_eq_of_mult` is exactly the missing content:
  two families obtained that way, from two frames at possibly DIFFERENT
  residue characteristics, agree off a finite set of places.

**BOTH OF THOSE ARE NOW PROVEN TOO** (2026-07-27), by a second cut along
the DETERMINANT/TRACE axis, and the residue is smaller than either of
them.  Three leaves replace them:

* `exists_finset_charFrob_coeff_zero_eq_absNorm_of_tateFrame_mult` — the
  constant coefficient is `N w`.  This is the WEIL PAIRING for a GIVEN
  frame that remembers the real multiplication; the DETERMINANT CLAUSE
  audit of `exists_tateFrame_of_levelStructure` states precisely that
  `j`/`hj` is what makes such a given-frame statement faithful, and this
  leaf has them.  **PROVEN 2026-07-27** over
  `exists_adicPackage_of_tateFrame_mult` and the pre-Chebotarev
  geometric leaf `det_globalFrob_eq_cyclotomicCharacter_of_tateFrame`;
  no new mathematics, and in particular no Weil pairing was proven here
  — the geometry stayed where it was.
* `exists_finset_charFrob_coeff_one_mem_range_of_tateFrame_mult` — the
  linear coefficient lies in `j(𝒪_D)`.  Weil integrality of the trace,
  and nothing else.  **This one is now PROVEN too** (2026-07-27): it is
  a corollary of the frame-free leaf `exists_frobTorsionEndo_of_mult`
  described in the next item, which had to be moved above it for the
  purpose.  So the trace half of rationality and the trace half of
  independence are now the SAME statement, and after the determinant
  leaf was itself closed (over `exists_adicPackage_of_tateFrame_mult`,
  the item above) the cluster has exactly ONE open leaf left here: the
  frame-free `exists_frobTorsionEndo_of_mult`.

  INTEGRATION NOTE (2026-07-27).  A rival closure of this same leaf, on
  another branch of the same batch, relocated its content instead to a
  package-carrying restatement
  `exists_finset_charFrob_coeff_one_mem_range_of_adicTateFrame`.  That
  route was a relocation and not a reduction — it left the sorry count
  unchanged — so the merger kept the reduction above and DELETED the
  restatement, which had no other consumer.
* `exists_finset_weilCoeffs_fst_eq_of_mult` — two frames give the same
  TRACE family off a finite set.  **This one is now PROVEN too**
  (2026-07-27), by a third cut along the FRAME/ARITHMETIC axis: its
  whole content was moved into `exists_frobTorsionEndo_of_mult`, a
  statement about torsion POINTS of the fibre carrying no frame, no
  coefficient ring and no characteristic polynomial, and the rest is
  linear algebra (`weilCoeffs_fst_eq_of_frobTorsionEndo`).  So the
  compatible-system content of the whole chain now sits in ONE leaf that
  never mentions `I`-adic anything, and the comparison of two residue
  characteristics has been replaced by two comparisons against a common
  frame-free value.

Rationality is then the shape of a monic quadratic (proven inline) fed
by the first two; independence is the third plus the observation that
the determinant leaf pins `b w = (N w : 𝒪_D)` in every frame once `j` is
known injective, which `injective_of_tateFrame_mult` supplies from
`exists_algebraicClosureEmbedding_of_tateFrame_mult`.  So the whole
`b`/norm half of the chain is now a corollary of a pairing identity, and
every remaining piece of compatible-system content sits in ONE statement
about traces.  Sorry count went 2 → 3 and the mathematical residue went
down: two of the three are strictly weaker than what they replaced, and
the third is a named classical identity the file already tracks
elsewhere.
* The assembly then needs no reference frame handed to it, and in
  particular no frame-existence leaf.  Split on whether any frame at all
  admits a rational family (`IsTateFrameWeilCoeffs`).  If one does, take
  its `a, b` as the global answer; a given frame's own family agrees with
  them off `bad' ∪ bad''`, both finite, and `bad` is quantified after the
  frame so it may be enlarged freely — which is precisely the slack the
  target's docstring identifies as load-bearing, used here for the first
  time.  If none does, the branch is closed by contradiction rather than
  by vacuity: applying the rationality leaf to the frame just introduced
  produces the witness whose non-existence was assumed.

**CITATION AUDIT — Faltings is NOT what this needs, and saying so is a
correction to the docstring below.**  Independence of `λ` for the
Frobenius characteristic polynomial at a place of GOOD reduction is
classical (Weil): over the residue field the polynomial is the
characteristic polynomial of the Frobenius ENDOMORPHISM, computed from
the degree map `n ↦ deg(n - F)`, which mentions no `λ` at all.  Faltings
is what gives semisimplicity, the Tate conjecture, and independence of
`λ` at the RAMIFIED places — and this statement never claims anything at
a ramified place, because `bad` absorbs them.  So
`exists_finset_weilCoeffs_eq_of_mult` is a Weil-level statement, not a
Faltings-level one, and a prover should not go looking for
*Endlichkeitssätze*.

**ROUTE NOTE, and why the cut is not the endomorphism-algebra one.**
The structurally best proof of both leaves is the one through the
reduction: for `w` of good reduction `Frob_w ∈ End(A_w)` commutes with
`𝒪_D`, so it lies in the centralizer of `𝒪_D` there, which is a
commutative `D`-algebra of degree `≤ 2` (the bound coming from `T_I A_w`
being free of rank two over `𝒪_{D,I}`); `a_w` and `b_w` are then the
coefficients of its characteristic polynomial over `D`, an identity in
the endomorphism algebra in which neither `q` nor `I` occurs, and both
leaves become corollaries of the faithfulness of `T_I`.

That route is NOT available in this tree and building it is a subtree,
not a step.  Checked 2026-07-27: there is no reduction of an abelian
scheme at a finite place anywhere here — no Néron model, no integral
model over `Spec 𝒪_F`, no special fibre, no reduction map on points; the
`GoodReduction` material under `KnownIn1980s/EllipticCurves/` is about
elliptic curves over `ℚ` and does not apply.  Nor is there an
endomorphism ring of an abelian scheme: `AbelianSchemeIsogeny.lean`
supplies only `mulByNat` and its flatness/finiteness/properness, never
`End(A)` as a ring.  And there is no Frobenius ENDOMORPHISM — `Frobᵥ` in
`GaloisRep.charFrob` is the Galois-theoretic Frobenius.  The
endomorphism-algebra cut therefore presupposes: good reduction of an
abelian scheme at a place, the specialization isomorphism
`T_I A_x ≅ T_I A_w`, the Frobenius endomorphism over the residue field,
`End(A) ↪ End(T_I A)`, and the degree map.  It trades Faltings for that
package; it does not remove the deep input.  The cut taken here is
orthogonal to it and survives whichever way that package is eventually
built, since both leaves are stated over frames only. -/

/-- **`a` and `b` are the Weil coefficients read off SOME frame of SOME
`I`-adic Tate module of `(m, x)`** — the auxiliary predicate through
which `exists_intWeilPolynomial_of_mult` is assembled.

This is `exists_weilCoeffs_of_tateFrame_mult`'s conclusion with the
frame data and the exceptional set existentially bound, so that it is a
predicate on the pair of families `(a, b)` ALONE.  That is what makes it
usable as the case split of the assembly: "some frame has a rational
family with these coefficients".

The pinning hypotheses are part of the predicate, `hj` included: a frame
that does not remember the real multiplication must not be allowed to
witness this, or the exotic frame `O = ℤ₁₃ × ℤ₁₃` of Counterexample 2
below would supply coefficients that no honest frame can match. -/
def IsTateFrameWeilCoeffs {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (a b : HeightOneSpectrum (NumberField.RingOfIntegers F) →
      NumberField.RingOfIntegers D) : Prop :=
  ∃ (q : ℕ) (_ : Fact q.Prime)
    (I : Ideal (NumberField.RingOfIntegers D)) (_ : I.IsMaximal)
    (_ : (q : NumberField.RingOfIntegers D) ∈ I)
    (π : NumberField.RingOfIntegers D) (_ : π ∈ I) (_ : π ∉ I ^ 2)
    (O : Type u) (_ : CommRing O) (_ : TopologicalSpace O) (_ : IsTopologicalRing O)
    (τ : GaloisRep F O (Fin 2 → O)) (φ : (Fin 2 → O) → TatePt m x I π)
    (j : NumberField.RingOfIntegers D →+* O),
    (∀ (u u' : Fin 2 → O) (n : ℕ),
      (φ (u + u')).1 n = ab.add ((φ u).1 n) ((φ u').1 n)) ∧
    Function.Bijective φ ∧
    (∀ (σ : Field.absoluteGaloisGroup F) (u : Fin 2 → O) (n : ℕ),
      (φ (τ σ u)).1 n = ab.galSMul x σ ((φ u).1 n)) ∧
    (∀ (c : NumberField.RingOfIntegers D) (u : Fin 2 → O) (n : ℕ),
      (φ (j c • u)).1 n = m.act c ((φ u).1 n)) ∧
    ∃ bad : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)),
      ∀ w ∉ bad,
        τ.charFrob w =
          Polynomial.X ^ 2 - Polynomial.C (j (a w)) * Polynomial.X +
            Polynomial.C (j (b w))

/-- **A frame that remembers the real multiplication has `j`
INJECTIVE** (PROVEN 2026-07-27 over the sibling leaf
`exists_algebraicClosureEmbedding_of_tateFrame_mult`).

That leaf produces `ψ : D →+* ℚ̄_q` and `ι : O →+* ℚ̄_q` with
`ι ∘ j = ψ ∘ (𝒪_D ↪ D)`.  A ring homomorphism out of a FIELD is
injective, and `𝒪_D ↪ D` is injective, so the composite is injective
and therefore so is `j`.  (The injectivity of `ι`, which that leaf also
supplies, is not needed and is discarded.)

This is what lets a coefficient identity in `O` be pulled back to an
identity in `𝒪_D`, and it is the only thing the `b`-half of
`exists_finset_weilCoeffs_eq_of_mult` needs beyond the determinant
clause. -/
theorem injective_of_tateFrame_mult
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (hdim : SmoothOfRelativeDimension (Module.finrank ℚ D) f)
    (q : ℕ) (hq : Fact q.Prime)
    (I : Ideal (NumberField.RingOfIntegers D)) (hI : I.IsMaximal)
    (hqI : (q : NumberField.RingOfIntegers D) ∈ I)
    (π : NumberField.RingOfIntegers D) (hπ : π ∈ I) (hπ2 : π ∉ I ^ 2)
    (O : Type u) (iCR : CommRing O) (iTS : TopologicalSpace O) (iTR : IsTopologicalRing O)
    (τ : GaloisRep F O (Fin 2 → O)) (φ : (Fin 2 → O) → TatePt m x I π)
    (j : NumberField.RingOfIntegers D →+* O)
    (hφadd : ∀ (u u' : Fin 2 → O) (n : ℕ),
      (φ (u + u')).1 n = ab.add ((φ u).1 n) ((φ u').1 n))
    (hφbij : Function.Bijective φ)
    (hφequiv : ∀ (σ : Field.absoluteGaloisGroup F) (u : Fin 2 → O) (n : ℕ),
      (φ (τ σ u)).1 n = ab.galSMul x σ ((φ u).1 n))
    (hj : ∀ (c : NumberField.RingOfIntegers D) (u : Fin 2 → O) (n : ℕ),
      (φ (j c • u)).1 n = m.act c ((φ u).1 n)) :
    Function.Injective j := by
  obtain ⟨ψ, ι, -, hcomp⟩ :=
    exists_algebraicClosureEmbedding_of_tateFrame_mult m x hdim q hq I hI hqI π hπ hπ2 O
      iCR iTS iTR τ φ j hφadd hφbij hφequiv hj
  intro a₁ a₂ hEq
  have hψ : ψ (algebraMap (NumberField.RingOfIntegers D) D a₁)
      = ψ (algebraMap (NumberField.RingOfIntegers D) D a₂) := by
    rw [← hcomp, ← hcomp, hEq]
  exact FaithfulSMul.algebraMap_injective (NumberField.RingOfIntegers D) D (ψ.injective hψ)

/-! ### Upgrading a GIVEN frame to one that carries the adic package

The two leaves of the next subsection are stated over a frame whose
coefficient ring `O` carries nothing but `CommRing`, `TopologicalSpace`
and `IsTopologicalRing`.  Everything the file already proves about
frames — the determinant identity, the geometric Frobenius input —
is stated over a frame carrying the ADIC PACKAGE
(`IsLocalRing O`, `Algebra ℤ_[q] O`, `hcplt`/`hdense`/`hker`).  The
transport below closes that gap once and for all, and both leaves are
then corollaries.

`exists_adicPackage_of_tateFrame_mult` is PROVEN over
`exists_ringEquiv_of_frameComparison` of the subsection above: that
comparison already identifies `O ≃+* 𝒪_{D,I}` over `𝒪_D`, and the whole
package is transported back along the resulting `e` — the `ℤ_q`-algebra
structure as `e.symm ∘ algebraMap`, locality by
`IsLocalRing.of_surjective'`, and `hcplt`/`hdense`/`hker` because `e`
matches the two `π`-adic filtrations (`e (j π) = j₁ π`, so
`y ∈ (j π)ⁿ ↔ e y ∈ (j₁ π)ⁿ` by `Ideal.mem_span_singleton` in both
directions).

WHAT THE PACKAGE CANNOT CONTAIN, AND WHY IT DOES NOT MATTER.  It
deliberately omits `IsModuleTopology ℤ_[q] O`, and that omission is
forced rather than lazy: the frame's `TopologicalSpace O` is a
HYPOTHESIS, so it may be the INDISCRETE topology — `IsTopologicalRing`
holds, `τ` is continuous vacuously, every hypothesis of the two leaves
is satisfied, and `IsModuleTopology ℤ_[q] O` is then FALSE, since
`𝒪_{D,I}` with its module topology is not indiscrete.  No theorem can
produce that instance for a given frame.

The consequence would be fatal for a route through
`det_eq_cyclotomicCharacter_of_tateFrame`, which needs
`IsModuleTopology` for its CHEBOTAREV step
(`det_eq_cyclotomicCharacter_of_globalFrob` uses it twice, for
`t2Space_of_free_isModuleTopology` and for continuity of
`γ ↦ det (τ γ)`).  But the Chebotarev step is not needed here at all:
`GaloisRep.charFrob` is *defined* at the local Frobenius, and
`GaloisRepresentation.GaloisRep.charFrob_eq_charpoly_globalFrob` says —
by `rfl` — that `τ.charFrob w = (τ (globalFrob w)).charpoly`.  So the
determinant leaf only ever asks for the identity AT a Frobenius element,
which is exactly what the geometric leaf
`det_globalFrob_eq_cyclotomicCharacter_of_tateFrame` supplies, and that
leaf's hypotheses are precisely the package minus the topology.
Chebotarev is what propagates the identity from the Frobenius elements
to all of `Γ_F`; a statement about `charFrob` never leaves them. -/

/-- **An ideal of `R`, viewed as a submodule of `R`, is its own
`⊤`-multiple** (PROVEN — `K • ⊤ = K` in `Submodule R R`).

This is the shape in which `IsHausdorff` and `IsPrecomplete` state
membership (`I ^ n • ⊤`), and it is what lets those two conditions be
transported along a ring isomorphism, where only the IDEALS correspond.
Mathlib has `Submodule.set_smul_top_eq_span` and
`Ideal.smul_top_eq_map` but not this specialization. -/
theorem ideal_smul_top_eq_self {R : Type*} [CommRing R] (K : Ideal R) :
    (K • (⊤ : Submodule R R)) = (K : Submodule R R) := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.smul_le]
    intro r hr y _
    exact K.mul_mem_right y hr
  · intro y hy
    have := Submodule.smul_mem_smul hy (Submodule.mem_top (x := (1 : R)))
    simpa using this

open _root_.NumberField in
/-- **A frame that remembers the real multiplication carries the adic
package** (PROVEN 2026-07-27 over `exists_ringEquiv_of_frameComparison`,
i.e. over the two commutative-algebra leaves
`exists_padicAlgebra_ringHom_of_frameComparison` and
`surjective_of_finrank_eq_of_isIntegrallyClosed`).

Given a frame `(O, τ, φ, j)` of `TatePt m x I π` with the pinning `hj`,
the coefficient ring `O` is a local `ℤ_q`-algebra in which `j (𝒪_D)` is
`π`-adically dense and detects the `I`-adic filtration, and `O` is
complete for that filtration.  In other words `O` satisfies every
hypothesis of `det_globalFrob_eq_cyclotomicCharacter_of_tateFrame`.

The proof is the same three moves as the sibling
`exists_algebraicClosureEmbedding_of_tateFrame_mult`: build the honest
frame `φ₁` over `O₁ := 𝒪_{D,I}` at the same `(q, I, π)` by
`exists_tateFrame_of_adicCoefficientRing`, form the additive bijection
`g := φ⁻¹ ∘ φ₁` intertwining the two `𝒪_D`-actions, and feed it to
`exists_ringEquiv_of_frameComparison` to get `e : O ≃+* O₁` with
`e ∘ j = j₁`.  Everything is then transported back along `e`.

`hφequiv` and the topology on `O` are carried but unused — they are
underscore-prefixed so that this is mechanically visible — exactly as in
that sibling: the conclusion is about the RING `O`.  They are kept so
that the hypothesis block is literally the frame a consumer holds.  `τ`
is used only through the type of `φ`.  See the
subsection note above for why `IsModuleTopology ℤ_[q] O` is absent and
why nothing needs it. -/
theorem exists_adicPackage_of_tateFrame_mult
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (hdim : SmoothOfRelativeDimension (Module.finrank ℚ D) f)
    (q : ℕ) (hq : Fact q.Prime)
    (I : Ideal (NumberField.RingOfIntegers D)) (hI : I.IsMaximal)
    (hqI : (q : NumberField.RingOfIntegers D) ∈ I)
    (π : NumberField.RingOfIntegers D) (hπ : π ∈ I) (hπ2 : π ∉ I ^ 2)
    (O : Type u) (iCR : CommRing O) (_iTS : TopologicalSpace O) (_iTR : IsTopologicalRing O)
    (τ : GaloisRep F O (Fin 2 → O)) (φ : (Fin 2 → O) → TatePt m x I π)
    (j : NumberField.RingOfIntegers D →+* O)
    (hφadd : ∀ (u u' : Fin 2 → O) (n : ℕ),
      (φ (u + u')).1 n = ab.add ((φ u).1 n) ((φ u').1 n))
    (hφbij : Function.Bijective φ)
    (_hφequiv : ∀ (σ : Field.absoluteGaloisGroup F) (u : Fin 2 → O) (n : ℕ),
      (φ (τ σ u)).1 n = ab.galSMul x σ ((φ u).1 n))
    (hj : ∀ (a : NumberField.RingOfIntegers D) (u : Fin 2 → O) (n : ℕ),
      (φ (j a • u)).1 n = m.act a ((φ u).1 n)) :
    ∃ _ : Algebra ℤ_[q] O, IsLocalRing O ∧
      IsAdicComplete (Ideal.span {j π}) O ∧
      (∀ (n : ℕ) (z : O), ∃ a : NumberField.RingOfIntegers D,
        z - j a ∈ Ideal.span {j π} ^ n) ∧
      (∀ (n : ℕ) (a : NumberField.RingOfIntegers D),
        j a ∈ Ideal.span {j π} ^ n ↔ a ∈ I ^ n) := by
  haveI := hq
  classical
  -- `I` is nonzero: it contains the rational prime `q`.
  have hI0 : I ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot, Nat.cast_eq_zero] at hqI
    exact (Fact.out : q.Prime).ne_zero hqI
  let v : HeightOneSpectrum (𝓞 D) := ⟨I, hI.isPrime, hI0⟩
  -- The HONEST coefficient ring `𝒪_{D,I}` and its `ℤ_q`-structure.
  letI iAlg₁ : Algebra ℤ_[q] (v.adicCompletionIntegers D) := padicIntAlgebra v q hqI
  obtain ⟨iFin₁, iFree₁, iMT₁⟩ := module_finite_free_moduleTopology_padicIntAlgebra v q hqI
  haveI := iFin₁; haveI := iFree₁; haveI := iMT₁
  have hcplt₁ : IsAdicComplete
      (Ideal.span {algebraMap (𝓞 D) (v.adicCompletionIntegers D) π})
      (v.adicCompletionIntegers D) :=
    isAdicComplete_span_uniformizer v π hπ hπ2
  have hdense₁ : ∀ (n : ℕ) (z : v.adicCompletionIntegers D),
      ∃ a : 𝓞 D, z - algebraMap (𝓞 D) (v.adicCompletionIntegers D) a ∈
        Ideal.span {algebraMap (𝓞 D) (v.adicCompletionIntegers D) π} ^ n :=
    fun n z => exists_sub_mem_span_uniformizer_pow v π hπ hπ2 n z
  have hker₁ : ∀ (n : ℕ) (a : 𝓞 D),
      algebraMap (𝓞 D) (v.adicCompletionIntegers D) a ∈
        Ideal.span {algebraMap (𝓞 D) (v.adicCompletionIntegers D) π} ^ n ↔ a ∈ I ^ n :=
    fun n a => mem_span_uniformizer_pow_iff v π hπ hπ2 n a
  -- The HONEST frame at the same `(q, I, π)`, and the comparison `g = φ⁻¹ ∘ φ₁`.
  obtain ⟨τ₁, φ₁, hφadd₁, hφbij₁, hφequiv₁, hφj₁⟩ :=
    exists_tateFrame_of_adicCoefficientRing m x hdim q I hI hqI π hπ hπ2
      (v.adicCompletionIntegers D) (algebraMap (𝓞 D) (v.adicCompletionIntegers D))
      hcplt₁ hdense₁ hker₁
  obtain ⟨g, hgdef⟩ :
      ∃ g : (Fin 2 → v.adicCompletionIntegers D) → (Fin 2 → O), ∀ u, φ (g u) = φ₁ u := by
    refine ⟨fun u => (Equiv.ofBijective φ hφbij).symm (φ₁ u), fun u => ?_⟩
    exact (Equiv.ofBijective φ hφbij).apply_symm_apply (φ₁ u)
  have hgadd : ∀ u u' : Fin 2 → v.adicCompletionIntegers D, g (u + u') = g u + g u' := by
    intro u u'
    refine hφbij.1 (Subtype.ext (funext fun n => ?_))
    rw [hgdef, hφadd, hgdef, hgdef, hφadd₁]
  have hgbij : Function.Bijective g := by
    constructor
    · intro u u' huu
      exact hφbij₁.1 (by rw [← hgdef, ← hgdef, huu])
    · intro w
      obtain ⟨u, hu⟩ := hφbij₁.2 (φ w)
      exact ⟨u, hφbij.1 (by rw [hgdef, hu])⟩
  have hgj : ∀ (a : 𝓞 D) (u : Fin 2 → v.adicCompletionIntegers D),
      g (algebraMap (𝓞 D) (v.adicCompletionIntegers D) a • u) = j a • g u := by
    intro a u
    refine hφbij.1 (Subtype.ext (funext fun n => ?_))
    rw [hgdef, hj, hgdef, hφj₁]
  -- The pinning: the frame's coefficient ring IS `𝒪_{D,I}`.
  obtain ⟨e, he⟩ :=
    exists_ringEquiv_of_frameComparison q I hI hqI π hπ hπ2 (v.adicCompletionIntegers D)
      (algebraMap (𝓞 D) (v.adicCompletionIntegers D)) hdense₁ hker₁ O j g hgadd hgbij hgj
  -- The `ℤ_q`-structure transported along `e`.
  letI iAlg : Algebra ℤ_[q] O :=
    RingHom.toAlgebra (e.symm.toRingHom.comp (algebraMap ℤ_[q] (v.adicCompletionIntegers D)))
  -- `e` matches the two `π`-adic filtrations.
  have heπ : e.symm (algebraMap (𝓞 D) (v.adicCompletionIntegers D) π) = j π := by
    rw [← he π, e.symm_apply_apply]
  have hmem : ∀ (n : ℕ) (y : O), y ∈ Ideal.span {j π} ^ n ↔
      e y ∈ Ideal.span {algebraMap (𝓞 D) (v.adicCompletionIntegers D) π} ^ n := by
    intro n y
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨e c, by rw [map_mul, map_pow, he]⟩
    · rintro ⟨c, hc⟩
      refine ⟨e.symm c, ?_⟩
      have h2 := congrArg e.symm hc
      rwa [e.symm_apply_apply, map_mul, map_pow, heπ] at h2
  haveI : Nontrivial O := e.toEquiv.nontrivial
  have hloc : IsLocalRing O := IsLocalRing.of_surjective' e.symm.toRingHom e.symm.surjective
  refine ⟨iAlg, hloc, ?_, ?_, ?_⟩
  · -- `IsAdicComplete` transported along `e`, one half at a time.
    haveI hhaus : IsHausdorff (Ideal.span {j π}) O := by
      constructor
      intro y hy
      have hy' : ∀ n : ℕ, e y ∈
          Ideal.span {algebraMap (𝓞 D) (v.adicCompletionIntegers D) π} ^ n := by
        intro n
        rw [← hmem n y]
        have := hy n
        rw [SModEq.sub_mem, sub_zero, ideal_smul_top_eq_self] at this
        exact this
      have hey := hcplt₁.haus (e y) (fun n => by
        rw [SModEq.sub_mem, sub_zero, ideal_smul_top_eq_self]
        exact hy' n)
      -- `simp` is avoided here: the project simp set contains sorried lemmas.
      have h0 := congrArg e.symm hey
      rwa [e.symm_apply_apply, map_zero] at h0
    haveI hprec : IsPrecomplete (Ideal.span {j π}) O := by
      constructor
      intro F0 hF0
      obtain ⟨L, hL⟩ := hcplt₁.prec (f := fun n => e (F0 n)) (by
        intro a b hab
        rw [SModEq.sub_mem, ideal_smul_top_eq_self, ← map_sub, ← hmem]
        have := hF0 hab
        rw [SModEq.sub_mem, ideal_smul_top_eq_self] at this
        exact this)
      refine ⟨e.symm L, fun n => ?_⟩
      rw [SModEq.sub_mem, ideal_smul_top_eq_self, hmem, map_sub, e.apply_symm_apply]
      have := hL n
      rw [SModEq.sub_mem, ideal_smul_top_eq_self] at this
      exact this
    exact ⟨⟩
  · intro n z
    obtain ⟨a, ha⟩ := hdense₁ n (e z)
    refine ⟨a, ?_⟩
    rw [hmem, map_sub, he]
    exact ha
  · intro n a
    rw [hmem, he]
    exact hker₁ n a

/-- **DETERMINANT: the constant coefficient of the Frobenius
characteristic polynomial of a frame is the absolute norm** (PROVEN
2026-07-27 — the WEIL PAIRING for a GIVEN frame that remembers the real
multiplication).

For all but finitely many `w`,

    (τ.charFrob w).coeff 0 = (N w : O).

`charFrob` is the characteristic polynomial of an endomorphism of a
free module of rank `2`, so its constant coefficient is `(-1)² · det`,
i.e. the determinant itself; the statement is therefore
`det (τ ∘ Frob_w) = N w`, written in the form both consumers actually
use so that no `LinearMap.det`-to-`charpoly` bridge is needed.

WHY THIS IS FAITHFUL, AND WHY IT IS NOT THE CLAUSE ALREADY DISCHARGED.
The DETERMINANT CLAUSE of `exists_tateFrame_of_levelStructure` (see its
docstring) proves exactly this identity, but only for the frame that
leaf CHOOSES — one carrying the full adic package
(`IsLocalRing O`, `Algebra ℤ_[q] O`, `IsModuleTopology ℤ_[q] O`,
`hcplt`/`hdense`/`hker`), through
`det_eq_cyclotomicCharacter_of_tateFrame` and
`cyclotomicCharacter_adicArithFrob_absNorm`.  Here the frame is GIVEN
and carries none of that package.  The audit in that docstring is
explicit about the dividing line: over a given frame the identity is
FALSE without the real-multiplication tie (the commutant can be larger
than `𝒪_{D,I}`, and the determinant becomes `χ₁ · ψ⁻¹(χ₂)` instead of
`χ₁ · χ₂ = N w`), and "over a frame the prover chooses, it needs
nothing".  This leaf has the tie — `j` and `hj` — so it sits on the
true side of that line.

HOW IT IS PROVEN (2026-07-27), in three moves and no new mathematics.

1. `exists_adicPackage_of_tateFrame_mult` above recognises the given
   frame's `O` as `𝒪_{D,I}` and hands back the adic package for `j`.
2. `det_globalFrob_eq_cyclotomicCharacter_of_tateFrame` — the geometric
   leaf, whose hypothesis block is exactly that package — gives
   `det (τ (globalFrob w)) = χ_cyc(globalFrob w)` off a finite `Sbad`,
   and `cyclotomicCharacter_adicArithFrob_absNorm` evaluates the right
   side as `N w` off the (finite, by
   `exists_finset_forall_natCast_notMem`) set of places over `q`.
3. `charFrob` is the charpoly at `globalFrob w`
   (`GaloisRepresentation.GaloisRep.charFrob_eq_charpoly_globalFrob`, a
   `rfl`), and `LinearMap.det_eq_sign_charpoly_coeff` at
   `finrank O (Fin 2 → O) = 2` turns `coeff 0` into `det` with sign
   `(-1)² = 1`.

WHY NO CHEBOTAREV, WHICH IS WHAT MAKES THIS PROVABLE AT ALL.  The
obvious route is through `det_eq_cyclotomicCharacter_of_tateFrame`, the
identity on the whole of `Γ_F`.  That route is CLOSED for a given
frame: its Chebotarev step needs `IsModuleTopology ℤ_[q] O`, and a
given frame's topology is a hypothesis that may be the indiscrete one,
under which every hypothesis of this leaf holds and that instance is
false.  The escape is that `charFrob` never leaves the Frobenius
elements, so the pre-Chebotarev leaf suffices — see the subsection note
above `exists_adicPackage_of_tateFrame_mult` for the full argument.

The exceptional set is the union of the (finite) set of places over `q`
with the geometric leaf's own `Sbad`; the places of bad reduction do NOT
have to be excluded, since `det τ = χ_cyc` is an identity of characters
and is insensitive to ramification of `τ`. -/
theorem exists_finset_charFrob_coeff_zero_eq_absNorm_of_tateFrame_mult
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (hdim : SmoothOfRelativeDimension (Module.finrank ℚ D) f)
    (q : ℕ) (hq : Fact q.Prime)
    (I : Ideal (NumberField.RingOfIntegers D)) (hI : I.IsMaximal)
    (hqI : (q : NumberField.RingOfIntegers D) ∈ I)
    (π : NumberField.RingOfIntegers D) (hπ : π ∈ I) (hπ2 : π ∉ I ^ 2)
    (O : Type u) (iCR : CommRing O) (iTS : TopologicalSpace O) (iTR : IsTopologicalRing O)
    (τ : GaloisRep F O (Fin 2 → O)) (φ : (Fin 2 → O) → TatePt m x I π)
    (j : NumberField.RingOfIntegers D →+* O)
    (hφadd : ∀ (u u' : Fin 2 → O) (n : ℕ),
      (φ (u + u')).1 n = ab.add ((φ u).1 n) ((φ u').1 n))
    (hφbij : Function.Bijective φ)
    (hφequiv : ∀ (σ : Field.absoluteGaloisGroup F) (u : Fin 2 → O) (n : ℕ),
      (φ (τ σ u)).1 n = ab.galSMul x σ ((φ u).1 n))
    (hj : ∀ (c : NumberField.RingOfIntegers D) (u : Fin 2 → O) (n : ℕ),
      (φ (j c • u)).1 n = m.act c ((φ u).1 n)) :
    ∃ bad : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)),
      ∀ w ∉ bad, (τ.charFrob w).coeff 0 = (Ideal.absNorm w.asIdeal : O) := by
  haveI := hq
  classical
  -- 1. the given frame carries the adic package
  obtain ⟨iAlg, hloc, hcplt, hdense, hker⟩ :=
    exists_adicPackage_of_tateFrame_mult m x hdim q hq I hI hqI π hπ hπ2 O iCR iTS iTR τ φ j
      hφadd hφbij hφequiv hj
  letI := iAlg
  haveI := hloc
  -- 2. the two finite exceptional sets
  obtain ⟨bad0, hbad0⟩ :=
    exists_finset_forall_natCast_notMem (F := F) q (Fact.out : q.Prime).ne_zero
  obtain ⟨Sbad, hSbad⟩ :=
    det_globalFrob_eq_cyclotomicCharacter_of_tateFrame m x hdim q I hI hqI π hπ hπ2 O j
      hcplt hdense hker τ φ hφadd hφbij hφequiv hj
  refine ⟨bad0 ∪ Sbad, fun w hw => ?_⟩
  have hw0 : w ∉ bad0 := fun h => hw (Finset.mem_union_left _ h)
  have hwS : w ∉ Sbad := fun h => hw (Finset.mem_union_right _ h)
  -- the cyclotomic character at the global Frobenius is the absolute norm
  have hchi : ((cyclotomicCharacter (AlgebraicClosure ℚ) q
      ((Field.absoluteGaloisGroup.map (algebraMap ℚ F)
        (GaloisRepresentation.globalFrob w)).toRingEquiv) : ℤ_[q]ˣ) : ℤ_[q])
      = (Ideal.absNorm w.asIdeal : ℤ_[q]) :=
    cyclotomicCharacter_adicArithFrob_absNorm F w (hbad0 w hw0)
  -- 3. `charFrob` is the charpoly at `globalFrob`, whose `coeff 0` is the determinant
  have hcp : τ.charFrob w = (τ (GaloisRepresentation.globalFrob w)).charpoly :=
    _root_.GaloisRepresentation.GaloisRep.charFrob_eq_charpoly_globalFrob τ w
  -- `simp` is deliberately avoided in this closing step: the project simp set
  -- contains sorried lemmas, and a `simpa` here would import `sorryAx`.
  have hdet : (τ (GaloisRepresentation.globalFrob w)).charpoly.coeff 0 =
      LinearMap.det (τ (GaloisRepresentation.globalFrob w)) := by
    rw [LinearMap.det_eq_sign_charpoly_coeff, Module.finrank_fin_fun, neg_one_sq, one_mul]
  rw [hcp, hdet, hSbad w hwS, hchi, map_natCast]

/-! #### The frame-free Weil leaf, cut along the SPECIALIZATION SEAM

`exists_frobTorsionEndo_of_mult` below is **PROVEN** (2026-07-27) by
assembly over the two leaves stated in this subsection.  The ROUTE NOTE
above says the structurally right proof goes through the reduction, and
that the package it needs — good reduction of an abelian scheme at a
finite place, the specialization isomorphism, the Frobenius
ENDOMORPHISM of the reduction — exists nowhere in this tree, in
`~/cs/FLT` or in the pin.  That is still true, and it is re-confirmed
below.  What has changed is that the package no longer has to be
*proven* in order to cut: it has to be *stated*, and the two halves it
separates are genuinely different theorems.

**WHAT MOVED, precisely.**  The seam is the reduction map at `w`.  It
sends every statement about `Γ_F` and about places of `F` into the first
leaf, and every statement about the characteristic equation into the
second, where the base field is FINITE:

* `exists_finset_frobSpecialization_of_mult` keeps *all* of the
  arithmetic of `F`: the exceptional set `bad`, the arithmetic Frobenius
  `Frob_w ∈ Γ_F`, the residue field `κ(w)` and its cardinality `N w`,
  the exclusion `q ∉ w`, and the whole `∀ I, ∀ n` prime-to-`w` torsion
  bookkeeping.  It asserts a REDUCTION MAP: an additive,
  `𝒪_D`-equivariant `e` from the geometric points of the fibre to the
  geometric points of an abelian scheme over `κ(w)` of the same relative
  dimension, INJECTIVE on prime-to-`w` torsion and intertwining `Frob_w`
  there with the `N w`-power Frobenius of `κ(w)`.  Nothing about a
  characteristic equation occurs in it.
* `exists_frobEndoCharEq_of_mult_finiteBase` keeps *all* of the Weil
  content, over a FINITE base field: `∃ t, F² + N = t·F` on the geometric
  points.  It mentions no number field `F`, no place, no `bad`, no ideal
  `I`, no `n` and no torsion — because over `κ(w)` the relation is an
  identity of ENDOMORPHISMS, so it holds at every geometric point at
  once.  That is exactly why the `∃ t, ∀ I` quantifier order of the
  target is not the residue of this cut but a CONSEQUENCE of it: one `t`
  serves every `I` because one endomorphism identity serves every point.

**WHY THIS IS NOT EITHER OF THE TWO CUTS THAT WERE REJECTED.**

* It is not an interface-only `GoodReductionFrobenius` datum whose glue
  is trivial.  The datum here carries NO characteristic equation; the
  equation is proved over the finite field, in a statement whose base
  field is a different kind of object from `F`.  The glue is the
  transport of that equation back through `e`, which needs the Galois
  stability of `A[Iⁿ]`, the injectivity of `e` on it, and the closure of
  `A[Iⁿ]` under `ab.add` and `m.act` — none of which is `rfl`.
* It is not the `∀ I`-pointwise / independence split, which was rejected
  because the `t` for a fixed `I` is already unique and so the whole
  compatible-system content survives into the second half.  Here the `I`
  quantifier does not appear in the second leaf AT ALL: it is discharged
  by the first leaf, which is a statement about a single map `e`, and
  the independence is produced by the finite-field leaf for free.

**FAITHFULNESS OF THE FIRST LEAF.**  It is an EXISTENCE statement, so a
junk witness cannot falsify it; the risk is the opposite one, that it is
too weak to glue.  It is not: the assembly below uses exactly its seven
clauses and nothing else.  It is TRUE for the honest witness — the
Néron model of the fibre at `w`, whose special fibre is an abelian
variety over `κ(w)` of the same dimension with the same real
multiplication, together with the reduction map, which is defined on all
of `A(F̄)` by the valuative criterion (`ab.proper`), is a group
homomorphism, commutes with `m.act`, and is injective on prime-to-`w`
torsion.  The intertwining is stated ONLY on prime-to-`w` torsion, which
is where it holds: on the full point set `Frob_w` is defined only up to
inertia, and inertia acts trivially exactly on the prime-to-`w` torsion.

**FAITHFULNESS OF THE SECOND LEAF.**  Here the data is universally
quantified, so junk witnesses matter.  Three hypotheses are load-bearing
and none can be dropped:

* `hfin`/`hN` — `k` is finite of cardinality `N`.  Over an infinite `k`,
  `Nat.card k = 0` and `hσ` would read `σ z = 1`, which no field
  automorphism satisfies; the leaf would be vacuous rather than false,
  and the constant term `N` would be meaningless.
* `hσ` — `σ` really is the `N`-power map.  This is what identifies the
  Galois action with the Frobenius ENDOMORPHISM of the abelian scheme;
  for any other `σ` the conclusion is false (take `σ = 1`, where it would
  assert `y + N·y = t·y` for all `y`, i.e. that `1 + N - t` kills the
  whole group).
* `hdim'` — the relative dimension is `[D:ℚ]`.  This is the
  Hilbert–Blumenthal condition; it is what makes `T_I` free of rank TWO
  over `𝒪_{D,I}`, hence the degree of `σ` over `D` at most two, hence a
  QUADRATIC relation.  Without it `σ` satisfies only its
  `2·dim/[D:ℚ]`-degree characteristic polynomial over `𝒪_D`.

The normalisation is the one the rest of this section uses: the constant
coefficient is `N` and not `N²`, matching
`exists_finset_charFrob_coeff_zero_eq_absNorm_of_tateFrame_mult` and the
Shimura/Taylor Hilbert–Blumenthal convention.  Consistency check on the
degree: `deg σ = N^g` for `g = dim`, and
`Nm_{D/ℚ}(N) = N^{[D:ℚ]} = N^g`, so `det_{𝒪_D} σ = N` is the right
element of `𝒪_D`.

**WHAT IS STILL MISSING, re-checked 2026-07-27 by re-running the check
rather than trusting this note.**  `grep -rl 'Neron\|NéronModel' Fermat/`
finds only `FreyCurve/MazurTorsion.lean`, `ModularCurve/X0.lean` and
`EllipticCurve/MordellWeil.lean`, all about elliptic curves over `ℚ`;
`~/cs/FLT` has no abelian-scheme material; the pin has no `NeronModel`
and no `AbelianVariety`.  So BOTH leaves below are gated on machinery
that must be built.  The cut does not remove that; it splits it into two
disjoint subtrees that can be owned independently — Néron models and
specialization on one side (Bosch–Lütkebohmert–Raynaud, Mumford §6), the
characteristic equation of the Frobenius endomorphism of an abelian
variety over a finite field on the other (Weil; Mumford *Abelian
Varieties* §19, Milne *Abelian Varieties* §§V–VI, Tate's 1966 theorem for
the `𝒪_D`-rationality of the coefficients).

**UPDATE 2026-07-27 — THE FIRST OF THE TWO LEAVES IS NOW PROVEN, over a
strictly smaller geometric one.**  `exists_finset_frobSpecialization_of_mult`
below is no longer a `sorry`: it is assembled from four statements, three
of which are PROVEN outright and only one of which is open.

* `finite_residueField_heightOneSpectrum` and
  `natCard_residueField_heightOneSpectrum` (PROVEN) discharge the two
  clauses `Finite κ(w)` and `Nat.card κ(w) = N w`.  These are pure
  algebraic number theory — `𝒪_F/w` is finite for `w` maximal and
  `Ideal.absNorm` is by definition `Nat.card (𝒪_F ⧸ w)` — and they have
  nothing to do with abelian schemes.
* `exists_absoluteGaloisGroup_pow_natCard_of_finite` (PROVEN) discharges
  the existence of `σ` and the clause `hσ`: over a finite field the
  `#k`-power map really is a `k`-algebra automorphism of `k̄`.  This is
  mathlib's `FiniteField.frobeniusAlgEquivOfAlgebraic`.
* `exists_finset_reductionMap_of_mult` (OPEN) keeps everything geometric:
  the finite set `bad`, the reduced abelian scheme with its real
  multiplication, and the reduction map `e`.

Two clauses were also made MORE PRIMITIVE in the passage, and the algebra
that converts them back is what the assembly proves:

* injectivity on `A[Iⁿ]` became **"the kernel of reduction contains no
  nonzero prime-to-`w` torsion"**, which is the classical statement (the
  kernel of reduction is a formal group, hence pro-`p` for `p` the
  residue characteristic).  The assembly recovers `Set.InjOn` from it by
  the difference trick, using that `A[Iⁿ]` is closed under `ab.add` and
  `ab.neg`, that `e` is additive hence sends `0` to `0` and `neg` to
  `neg`, and that `(q : 𝒪_D)ⁿ ∈ Iⁿ` whenever `q ∈ I`;
* the Frobenius intertwining is likewise stated on points killed by
  `(q : 𝒪_D)ⁿ` rather than on `A[Iⁿ]`, and the assembly specialises it
  through the same `Ideal.pow_mem_pow` step.

So the ideal `I` and its maximality, which are bookkeeping rather than
geometry, no longer appear in the open leaf at all: it quantifies only
over a prime `q` prime to `w` and an exponent `n`.  What remains open is
exactly the Néron-model content, and nothing else. -/

/-- **THE RESIDUE FIELD AT A FINITE PLACE OF A NUMBER FIELD IS FINITE**
(PROVEN).  `w.asIdeal` is a nonzero prime of the Dedekind domain `𝒪_F`,
hence maximal, and `𝒪_F ⧸ w.asIdeal` is finite; `Ideal.ResidueField` of a
maximal ideal is the fraction field of that finite domain, i.e. the
quotient itself.  Stated separately because the pin carries no `Finite`
instance for `Ideal.ResidueField` at a height-one prime, and
`exists_finset_frobSpecialization_of_mult` has to produce one. -/
theorem finite_residueField_heightOneSpectrum {F : Type u} [Field F] [NumberField F]
    (w : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    Finite w.asIdeal.ResidueField := by
  haveI : w.asIdeal.IsMaximal := w.isPrime.isMaximal w.ne_bot
  infer_instance

/-- **THE RESIDUE FIELD AT `w` HAS `N w` ELEMENTS** (PROVEN).
`Ideal.absNorm` is by definition `Submodule.cardQuot`, i.e.
`Nat.card (𝒪_F ⧸ w)`, and for `w` maximal the algebra map
`𝒪_F ⧸ w → w.asIdeal.ResidueField` is bijective
(`Ideal.bijective_algebraMap_quotient_residueField`). -/
theorem natCard_residueField_heightOneSpectrum {F : Type u} [Field F] [NumberField F]
    (w : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    Nat.card w.asIdeal.ResidueField = Ideal.absNorm w.asIdeal := by
  haveI : w.asIdeal.IsMaximal := w.isPrime.isMaximal w.ne_bot
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact (Nat.card_eq_of_bijective _
    (w.asIdeal.bijective_algebraMap_quotient_residueField)).symm

/-- **THE FROBENIUS ELEMENT OF THE ABSOLUTE GALOIS GROUP OF A FINITE
FIELD** (PROVEN).  For `k` finite with `#k = N` the `N`-power map is a
`k`-algebra automorphism of `k̄`: it is a ring homomorphism because the
characteristic divides `N`, it fixes `k` pointwise by `x^{#k} = x`, and
it is bijective because `k̄` is perfect.  This is mathlib's
`FiniteField.frobeniusAlgEquivOfAlgebraic`, read into
`Field.absoluteGaloisGroup k`.

This is the clause `hσ` of `exists_finset_frobSpecialization_of_mult`,
and it is the reason that leaf does not have to *assume* a Frobenius: the
element is unique with this property, so producing it costs nothing and
asserting it would have been a hypothesis in disguise. -/
theorem exists_absoluteGaloisGroup_pow_natCard_of_finite {k : Type u} [Field k]
    (hfin : Finite k) :
    ∃ σ : Field.absoluteGaloisGroup k, ∀ z : AlgebraicClosure k,
      (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) z = z ^ Nat.card k := by
  haveI := hfin
  haveI : Fintype k := Fintype.ofFinite k
  refine ⟨FiniteField.frobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k), fun z => ?_⟩
  rw [Nat.card_eq_fintype_card]
  rfl

/-- **THE REDUCTION MAP AT A PLACE OF GOOD REDUCTION, IN ITS PRIMITIVE
FORM** (sorry leaf — Néron models and the specialization isomorphism;
Bosch–Lütkebohmert–Raynaud *Néron Models*, Mumford *Abelian Varieties*
§6).

This is the whole geometric content of
`exists_finset_frobSpecialization_of_mult`, and nothing else: the number
theory of `κ(w)` and the existence of the Frobenius `σ` have been peeled
off into the three proven statements above, and `σ` enters here only as a
HYPOTHESIS pinned by its defining property `z ↦ z^{N w}` (which
determines it uniquely, so nothing is assumed by taking it as input).

Outside a finite set of places `w` of `F` the fibre `A_x` reduces at `w`:
there is an abelian scheme `f' : A' ⟶ Spec κ(w)` of the same relative
dimension `[D:ℚ]` carrying the same real multiplication `m'`, and a
REDUCTION MAP `e` on geometric points which

* is additive (`hadd`) and `𝒪_D`-equivariant (`hact`) on ALL geometric
  points — the reduction of an `F̄`-point is defined unconditionally by
  the valuative criterion of properness, since `ab.proper` holds and the
  Néron model is proper at a place of good reduction;
* has a KERNEL CONTAINING NO NONZERO PRIME-TO-`w` TORSION: if `y` is
  killed by `(q : 𝒪_D)ⁿ` for a prime `q` with `q ∉ w`, and `e y = e 0`,
  then `y = 0`.  Classically the kernel of reduction is the group of
  points of a formal group over the maximal ideal, hence pro-`p` for `p`
  the residue characteristic of `w`, so it meets the prime-to-`p`
  torsion trivially;
* intertwines `Frob_w` with `σ` on that same prime-to-`w` torsion.

WHY BOTH TORSION CLAUSES ARE RESTRICTED THE SAME WAY, and why that is
where they are TRUE rather than merely convenient.  On the full geometric
point set `Frob_w` is only defined modulo the inertia group at `w`, and
inertia acts trivially precisely on the prime-to-`w` torsion; on
`q`-power torsion at `w ∣ q` the reduction map is not injective either.
The two clauses are stated together, under the same quantifiers, for
exactly that reason.

WHAT IS DELIBERATELY ABSENT.  No characteristic equation, no coefficient
ring, no frame, no representation — those live on the other side of the
seam, in `exists_frobEndoCharEq_of_mult_finiteBase`, over a finite base
field.  Also no ideal `I` and no `I.IsMaximal`: the passage from
`(q : 𝒪_D)ⁿ`-torsion to `A[Iⁿ]` is `Ideal.pow_mem_pow` and is carried out
in the consumer, not here.

`κ(w)` is written as `w.asIdeal.ResidueField`, i.e. the residue field of
the local ring at `w`. -/
theorem exists_finset_reductionMap_of_mult
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (hdim : SmoothOfRelativeDimension (Module.finrank ℚ D) f) :
    ∃ bad : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)),
      ∀ w ∉ bad,
        ∀ σ : Field.absoluteGaloisGroup w.asIdeal.ResidueField,
          (∀ z : AlgebraicClosure w.asIdeal.ResidueField,
            (σ : AlgebraicClosure w.asIdeal.ResidueField ≃ₐ[w.asIdeal.ResidueField]
                AlgebraicClosure w.asIdeal.ResidueField) z = z ^ Ideal.absNorm w.asIdeal) →
        ∃ (A' : Scheme.{u}) (f' : A' ⟶ Spec (CommRingCat.of w.asIdeal.ResidueField))
          (ab' : AbelianSchemeStruct f')
          (m' : Mult ab' (NumberField.RingOfIntegers D))
          (e : GeomFibrePt f x →
            GeomFibrePt f' (𝟙 (Spec (CommRingCat.of w.asIdeal.ResidueField)))),
          SmoothOfRelativeDimension (Module.finrank ℚ D) f' ∧
          (∀ y y' : GeomFibrePt f x, e (ab.add y y') = ab'.add (e y) (e y')) ∧
          (∀ (c : NumberField.RingOfIntegers D) (y : GeomFibrePt f x),
            e (m.act c y) = m'.act c (e y)) ∧
          (∀ q n : ℕ, q.Prime → (q : NumberField.RingOfIntegers F) ∉ w.asIdeal →
            ∀ y : GeomFibrePt f x,
              m.act ((q : NumberField.RingOfIntegers D) ^ n) y
                  = ab.zero (specAlgClos F ≫ x) →
                e y = e (ab.zero (specAlgClos F ≫ x)) →
                y = ab.zero (specAlgClos F ≫ x)) ∧
          (∀ q n : ℕ, q.Prime → (q : NumberField.RingOfIntegers F) ∉ w.asIdeal →
            ∀ y : GeomFibrePt f x,
              m.act ((q : NumberField.RingOfIntegers D) ^ n) y
                  = ab.zero (specAlgClos F ≫ x) →
                e (ab.galSMul x
                    (Field.absoluteGaloisGroup.map (algebraMap F (w.adicCompletion F))
                      (Field.AbsoluteGaloisGroup.adicArithFrob w)) y)
                  = ab'.galSMul _ σ (e y)) :=
  sorry

/-- **THE REDUCTION MAP AT A PLACE OF GOOD REDUCTION** (**PROVEN
2026-07-27** over `exists_finset_reductionMap_of_mult` and the three
proven statements immediately above; see the subsection note above for
why this is one of the two halves of the frame-free Weil leaf and for the
faithfulness audit).

Outside a finite set of places `w` of `F` the fibre `A_x` reduces at `w`:
there is an abelian scheme `f' : A' ⟶ Spec κ(w)` over the residue field,
of the same relative dimension `[D:ℚ]` and carrying the same real
multiplication `m'` by `𝒪_D`, an element `σ` of `Γ_{κ(w)}` acting as the
`N w`-power map on `κ(w)ᵃˡᵍ`, and a REDUCTION MAP `e` on geometric points
which

* is additive (`hadd`) and `𝒪_D`-equivariant (`hact`) on ALL geometric
  points — the reduction of an `F̄`-point is defined unconditionally by
  the valuative criterion of properness, since `ab.proper` holds and the
  Néron model is proper at a place of good reduction;
* is INJECTIVE on `A[Iⁿ]` and intertwines `Frob_w` with `σ` there,
  whenever the residue characteristic `q` of `I` is not the residue
  characteristic of `w`.

The restriction of the last clause to prime-to-`w` torsion is not a
weakening for convenience: it is where the statement is TRUE.  On the
full geometric point set `Frob_w` is only defined modulo the inertia
group at `w`, and inertia acts trivially precisely on the prime-to-`w`
torsion; on `q`-power torsion at `w ∣ q` the reduction map is not
injective either.  The two clauses are stated together, under the same
quantifiers, for exactly that reason.

`κ(w)` is written as `w.asIdeal.ResidueField`, i.e. the residue field of
the local ring at `w`; `Finite` and `Nat.card = N w` are part of the
conclusion because the pin carries no `Finite` instance for it, and they
are discharged here by `finite_residueField_heightOneSpectrum` and
`natCard_residueField_heightOneSpectrum`. -/
theorem exists_finset_frobSpecialization_of_mult
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (hdim : SmoothOfRelativeDimension (Module.finrank ℚ D) f) :
    ∃ bad : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)),
      ∀ w ∉ bad,
        ∃ (A' : Scheme.{u}) (f' : A' ⟶ Spec (CommRingCat.of w.asIdeal.ResidueField))
          (ab' : AbelianSchemeStruct f')
          (m' : Mult ab' (NumberField.RingOfIntegers D))
          (σ : Field.absoluteGaloisGroup w.asIdeal.ResidueField)
          (e : GeomFibrePt f x →
            GeomFibrePt f' (𝟙 (Spec (CommRingCat.of w.asIdeal.ResidueField)))),
          Finite w.asIdeal.ResidueField ∧
          Nat.card w.asIdeal.ResidueField = Ideal.absNorm w.asIdeal ∧
          SmoothOfRelativeDimension (Module.finrank ℚ D) f' ∧
          (∀ z : AlgebraicClosure w.asIdeal.ResidueField,
            (σ : AlgebraicClosure w.asIdeal.ResidueField ≃ₐ[w.asIdeal.ResidueField]
                AlgebraicClosure w.asIdeal.ResidueField) z = z ^ Ideal.absNorm w.asIdeal) ∧
          (∀ y y' : GeomFibrePt f x, e (ab.add y y') = ab'.add (e y) (e y')) ∧
          (∀ (c : NumberField.RingOfIntegers D) (y : GeomFibrePt f x),
            e (m.act c y) = m'.act c (e y)) ∧
          (∀ q : ℕ, q.Prime → (q : NumberField.RingOfIntegers F) ∉ w.asIdeal →
            ∀ I : Ideal (NumberField.RingOfIntegers D), I.IsMaximal →
              (q : NumberField.RingOfIntegers D) ∈ I → ∀ n : ℕ,
                Set.InjOn e (m.torsion x (I ^ n)).1 ∧
                ∀ y ∈ (m.torsion x (I ^ n)).1,
                  e (ab.galSMul x
                      (Field.absoluteGaloisGroup.map (algebraMap F (w.adicCompletion F))
                        (Field.AbsoluteGaloisGroup.adicArithFrob w)) y)
                    = ab'.galSMul _ σ (e y)) := by
  classical
  obtain ⟨bad, hbad⟩ := exists_finset_reductionMap_of_mult m x hdim
  refine ⟨bad, fun w hw => ?_⟩
  have hfin : Finite w.asIdeal.ResidueField := finite_residueField_heightOneSpectrum w
  have hcard : Nat.card w.asIdeal.ResidueField = Ideal.absNorm w.asIdeal :=
    natCard_residueField_heightOneSpectrum w
  obtain ⟨σ, hσ0⟩ := exists_absoluteGaloisGroup_pow_natCard_of_finite hfin
  rw [hcard] at hσ0
  obtain ⟨A', f', ab', m', e, hdim', hadd, hact, hker, hint⟩ := hbad w hw σ hσ0
  refine ⟨A', f', ab', m', σ, e, hfin, hcard, hdim', hσ0, hadd, hact, ?_⟩
  -- `A[J]` is closed under the group law and under negation: both are
  -- `mem_torsion_iff` plus one axiom of `Mult`.
  have hTadd : ∀ (J : Ideal (NumberField.RingOfIntegers D)) (u v : GeomFibrePt f x),
      u ∈ (m.torsion x J).1 → v ∈ (m.torsion x J).1 → ab.add u v ∈ (m.torsion x J).1 := by
    intro J u v hu hv
    rw [mem_torsion_iff] at hu hv ⊢
    intro a ha
    rw [m.act_addPt a u v, hu a ha, hv a ha]
    exact ab.zero_add _
  have hTneg : ∀ (J : Ideal (NumberField.RingOfIntegers D)) (u : GeomFibrePt f x),
      u ∈ (m.torsion x J).1 → ab.neg u ∈ (m.torsion x J).1 := by
    intro J u hu
    rw [mem_torsion_iff] at hu ⊢
    intro a ha
    letI : AddCommGroup (GeomFibrePt f x) := ab.addCommGroup (specAlgClos F ≫ x)
    letI : Module (NumberField.RingOfIntegers D) (GeomFibrePt f x) :=
      m.module (specAlgClos F ≫ x)
    have hu' : (a : NumberField.RingOfIntegers D) • u = (0 : GeomFibrePt f x) := hu a ha
    show (a : NumberField.RingOfIntegers D) • (-u) = (0 : GeomFibrePt f x)
    rw [smul_neg, hu', neg_zero]
  -- an additive map kills the zero point and commutes with negation
  have hzero : e (ab.zero (specAlgClos F ≫ x))
      = ab'.zero (specAlgClos w.asIdeal.ResidueField ≫
          𝟙 (Spec (CommRingCat.of w.asIdeal.ResidueField))) := by
    letI : AddCommGroup (GeomFibrePt f' (𝟙 (Spec (CommRingCat.of w.asIdeal.ResidueField)))) :=
      ab'.addCommGroup (specAlgClos w.asIdeal.ResidueField ≫ 𝟙 _)
    have h := hadd (ab.zero (specAlgClos F ≫ x)) (ab.zero (specAlgClos F ≫ x))
    rw [ab.zero_add] at h
    show e (ab.zero (specAlgClos F ≫ x)) = 0
    have h' : (0 : GeomFibrePt f' (𝟙 (Spec (CommRingCat.of w.asIdeal.ResidueField))))
        + e (ab.zero (specAlgClos F ≫ x))
        = e (ab.zero (specAlgClos F ≫ x)) + e (ab.zero (specAlgClos F ≫ x)) :=
      (zero_add _).trans h
    exact (add_right_cancel h').symm
  have hneg : ∀ u : GeomFibrePt f x, e (ab.neg u) = ab'.neg (e u) := by
    intro u
    letI : AddCommGroup (GeomFibrePt f' (𝟙 (Spec (CommRingCat.of w.asIdeal.ResidueField)))) :=
      ab'.addCommGroup (specAlgClos w.asIdeal.ResidueField ≫ 𝟙 _)
    have h := hadd (ab.neg u) u
    rw [ab.neg_add, hzero] at h
    show e (ab.neg u) = -(e u)
    have h' : e (ab.neg u) + e u
        = (0 : GeomFibrePt f' (𝟙 (Spec (CommRingCat.of w.asIdeal.ResidueField)))) := h.symm
    exact eq_neg_of_add_eq_zero_left h'
  intro q hq hqw I hI hqI n
  -- `A[Iⁿ]` is killed by `(q : 𝒪_D)ⁿ`, which is what the leaf's two
  -- torsion clauses are stated over
  have hpow : ∀ y : GeomFibrePt f x, y ∈ (m.torsion x (I ^ n)).1 →
      m.act ((q : NumberField.RingOfIntegers D) ^ n) y = ab.zero (specAlgClos F ≫ x) := by
    intro y hy
    exact (mem_torsion_iff m x _ y).mp hy _ (Ideal.pow_mem_pow hqI n)
  refine ⟨?_, fun y hy => hint q n hq hqw y (hpow y hy)⟩
  intro y hy y' hy' hee
  letI : AddCommGroup (GeomFibrePt f x) := ab.addCommGroup (specAlgClos F ≫ x)
  letI : AddCommGroup (GeomFibrePt f' (𝟙 (Spec (CommRingCat.of w.asIdeal.ResidueField)))) :=
    ab'.addCommGroup (specAlgClos w.asIdeal.ResidueField ≫ 𝟙 _)
  have hzmem : ab.add y (ab.neg y') ∈ (m.torsion x (I ^ n)).1 :=
    hTadd _ _ _ hy (hTneg _ _ hy')
  have hez : e (ab.add y (ab.neg y')) = e (ab.zero (specAlgClos F ≫ x)) := by
    rw [hadd, hneg, hee, hzero]
    exact (ab'.add_comm (e y') (ab'.neg (e y'))).trans (ab'.neg_add _)
  have hz := hker q n hq hqw _ (hpow _ hzmem) hez
  have hz' : y + -y' = (0 : GeomFibrePt f x) := hz
  exact add_neg_eq_zero.mp hz'

/-! #### The finite-field half, cut along the ENDOMORPHISM seam

`exists_frobEndoCharEq_of_mult_finiteBase` below is **PROVEN
(2026-07-27)** by assembly over the three leaves stated in this
subsection.  Its own docstring records what it is and why its
hypotheses are load-bearing; this note records only the cut.

**WHY A CUT WAS POSSIBLE AT ALL.**  The target is a relation between
maps on the geometric point set `A'(k̄)`, and *as maps on that set* the
relation has no purchase: `y ↦ σ · y` is invertible there (it is a group
ACTION, with inverse `σ⁻¹ · –`), so every factorisation one might hope to
extract from it is free and carries nothing.  Concretely, a
"Verschiebung" defined only on points — `V y := N · (σ⁻¹ · y)` — satisfies
`V ∘ F = F ∘ V = [N]` by `Mult.galSMul_act` alone, so a cut into "V
exists" plus "the trace is rational" would be a cut into a triviality
plus the whole theorem.  That is the trap this cut avoids.

What has content is that the Galois action is ALGEBRAIC: that it is
induced by a MORPHISM of schemes.  So the seam here is the passage from
`Γ_k` to `End_k(A')`, and it separates three genuinely different
theorems:

* `exists_frobEndomorphism_of_finiteBase` — the `N`-power Frobenius is an
  ENDOMORPHISM of `A'` over `Spec k`, inducing the action of `σ` on
  geometric points.  Pure characteristic-`p` geometry: no `D`, no real
  multiplication, no relative dimension.  It is where `hfin`, `hN` and
  `hσ` are really consumed — `z ^ N = z` on `k` is what makes the
  absolute Frobenius a `k`-morphism.
* `exists_verschiebung_of_frobEndomorphism_finiteBase` — `[N]` factors
  through that endomorphism, on both sides, BY A MORPHISM.  This is the
  Verschiebung: for `N = p ^ a`, `F` is the `a`-th power of the
  `p`-Frobenius, so `ker F` is infinitesimal and sits inside `A'[N]`,
  and `[N]` therefore factors through `F`.  Again
  no `D` and no dimension hypothesis.  Stated at the level of morphisms
  and not of points, which is exactly what makes it a theorem rather
  than the triviality described above.
* `exists_frobTraceAct_of_mult_finiteBase` — `F + V ∈ 𝒪_D`.  This is the
  Weil content proper, and it is where `hdim'` and the real
  multiplication are consumed: `T_I A'` is free of rank TWO over
  `𝒪_{D,I}` exactly because the relative dimension is `[D:ℚ]`, so the
  commutative algebra `D[F]` has degree at most two over `D`, so `F`
  satisfies a monic quadratic, whose linear coefficient is `F + V` and
  whose constant coefficient is `F ∘ V = N`.

**THE ASSEMBLY**, which is where the constant coefficient `N` of the
target comes from and is not `rfl`: with `t` the trace,

    F²(y) + N · y = F²(y) + F(V y) = F(F y + V y) = F(t · y) = t · F(y),

using only that `F` is additive on geometric points (`pre_add`, the
naturality axiom) and commutes with the real multiplication
(`Mult.galSMul_act`).  Both are already proven in
`Modularity/AbelianScheme.lean`; nothing else is needed.

**WHAT REMAINS MISSING**, re-checked 2026-07-27 in this worktree rather
than quoted: `grep -rli frobenius .lake/packages/mathlib/Mathlib/AlgebraicGeometry/`
is EMPTY — the pin has no absolute or relative Frobenius morphism of
schemes at all — and `~/cs/FLT` has no abelian-variety material.  So the
first leaf is gated on writing the Frobenius morphism, the second on
`ker F ⊆ ker[N]` plus factorisation of isogenies, and the third on the
Tate module of an abelian variety over a finite field.  The three are
disjoint and can be owned independently, which is the whole gain: the
first two are characteristic-`p` geometry (Mumford *AV* §15, Milne *AV*
§I.5), the third is Weil (Mumford *AV* §19, Milne *AV* §V, Tate 1966). -/

/-- **THE FROBENIUS ENDOMORPHISM OF AN ABELIAN SCHEME OVER A FINITE
FIELD** (sorry leaf — the `N`-power Frobenius morphism; see the
subsection note above for the cut).

For `k` finite with `N` elements there is a morphism `Fr : A' ⟶ A'` over
`Spec k` whose action on geometric points is the action of the
arithmetic Frobenius `σ ∈ Γ_k`.

Classically `Fr` is the ABSOLUTE `N`-power Frobenius of `A'`: the
identity on the underlying space, `a ↦ a ^ N` on the structure sheaf.
It is a morphism OVER `Spec k` — which is the clause `Fr ≫ f' = f'` —
precisely because every element of a field with `N` elements satisfies
`z ^ N = z`, so the `N`-power Frobenius of `Spec k` is the identity;
this is the only place `hfin` and `hN` are used, and without them the
statement is false (over an infinite `k` the `N`-power map does not fix
the base, and `Fr` is not a `k`-morphism).

The pointwise clause is an equation of morphisms `Spec k̄ ⟶ A'`, and it
is the standard identification "arithmetic Frobenius = Frobenius
endomorphism": a geometric point is a ring map `y : 𝒪 → k̄`, the left
side is `σ ∘ y` and the right side is `y ∘ (·)^N`, and these agree
because `y (a ^ N) = y a ^ N = σ (y a)` by `hσ`.  Note that it FORCES
`Fr`: `A'` is smooth over `k`, hence reduced, so a morphism is
determined by its effect on `k̄`-points.  There is therefore no junk
witness, and the leaf below that consumes `Fr` is not weakened by
receiving it existentially.

NOT ASSERTED: that `Fr` is a group endomorphism or commutes with the
real multiplication.  Both are FREE on geometric points from the
pointwise clause, since the Galois action is already known to be
additive (`AbelianSchemeStruct.pre_add`) and `𝒪_D`-linear
(`Mult.galSMul_act`); stating them here would duplicate proven
material. -/
theorem exists_frobEndomorphism_of_finiteBase
    {k : Type u} [Field k] (hfin : Finite k) (N : ℕ) (hN : Nat.card k = N)
    {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of k)}
    (ab' : AbelianSchemeStruct f')
    (σ : Field.absoluteGaloisGroup k)
    (hσ : ∀ z : AlgebraicClosure k,
      (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) z = z ^ N) :
    ∃ Fr : A' ⟶ A', Fr ≫ f' = f' ∧
      ∀ y : GeomFibrePt f' (𝟙 (Spec (CommRingCat.of k))),
        (ab'.galSMul (𝟙 (Spec (CommRingCat.of k))) σ y).1 = y.1 ≫ Fr :=
  sorry

/-- **THE VERSCHIEBUNG: `[N]` FACTORS THROUGH THE FROBENIUS
ENDOMORPHISM** (sorry leaf — Mumford *AV* §15, Milne *AV* §I.5; see the
subsection note above for the cut).

Given the Frobenius endomorphism `Fr` of the previous leaf there is a
morphism `V : A' ⟶ A'` over `Spec k` with

    Fr ≫ V = [N]  and  V ≫ Fr = [N]

as morphisms `A' ⟶ A'`, where `[N] = ab'.mulByNat N` is multiplication by
`N` (`Modularity/AbelianSchemeIsogeny.lean`).

Classically: `Fr` is purely inseparable of degree `N ^ dim`, and for
`N = p ^ a` it is the `a`-th power of the `p`-Frobenius, so `ker Fr` is
infinitesimal and killed by `N`; hence `ker Fr ⊆ ker [N]` and `[N]`
factors as `V ∘ Fr` for a unique isogeny `V`, the Verschiebung.  The
second identity follows from the first: `[N]` is central in `End(A')`, so
`Fr ≫ (V ≫ Fr) = [N] ≫ Fr = Fr ≫ [N]`, and `Fr` — an isogeny, hence
faithfully flat — is right-cancellable.

**WHY THIS IS STATED FOR MORPHISMS AND NOT FOR POINTS.**  On the
geometric point set `A'(k̄)` this statement is a TRIVIALITY and carries
none of the content above: `y ↦ σ · y` is a bijection there, with
inverse `y ↦ σ⁻¹ · y`, so `V y := N · (σ⁻¹ · y)` satisfies both
identities by `Mult.galSMul_act` and nothing has been proved.  What is
true only for a morphism — and what the Weil leaf needs — is that `V` is
ALGEBRAIC.  Stating it here at the level of `A' ⟶ A'` is the whole
reason this cut is a cut; see the subsection note.

`hFrpt` is what pins `Fr` as the Frobenius: without it `Fr` could be any
endomorphism, and `[N]` does not factor through an arbitrary one (take
`Fr = 0` with `dim ≥ 1`).  `hfin`, `hN` and `hσ` are carried because they
are what make `hFrpt` say "Frobenius" rather than merely "some
endomorphism inducing `σ`". -/
theorem exists_verschiebung_of_frobEndomorphism_finiteBase
    {k : Type u} [Field k] (hfin : Finite k) (N : ℕ) (hN : Nat.card k = N)
    {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of k)}
    (ab' : AbelianSchemeStruct f')
    (σ : Field.absoluteGaloisGroup k)
    (hσ : ∀ z : AlgebraicClosure k,
      (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) z = z ^ N)
    (Fr : A' ⟶ A') (hFrf : Fr ≫ f' = f')
    (hFrpt : ∀ y : GeomFibrePt f' (𝟙 (Spec (CommRingCat.of k))),
      (ab'.galSMul (𝟙 (Spec (CommRingCat.of k))) σ y).1 = y.1 ≫ Fr) :
    ∃ V : A' ⟶ A', V ≫ f' = f' ∧
      Fr ≫ V = ab'.mulByNat N ∧ V ≫ Fr = ab'.mulByNat N :=
  sorry

/-! #### The Weil half, cut along the LEVEL / RATIONALITY / DENSITY axes

`exists_frobTraceAct_of_mult_finiteBase` below is **PROVEN
(2026-07-27)** by assembly over the four leaves stated in this
subsection.  The subsection note above describes the three-way
endomorphism cut of `exists_frobEndoCharEq_of_mult_finiteBase` and says
that its third member — this one — is "gated on the Tate module of an
abelian variety over a finite field".  That is still exactly right; what
follows is that gate opened into its four independent pieces.

**WHY A CUT IS POSSIBLE, AND WHERE THE ONLY REAL SUBTLETY IS.**  Write
`F` for `ab'.galSMul σ` and `W` for `Vpt`.  Two observations do all the
structural work and are proved inline below, not assumed:

* `F` is INJECTIVE on geometric points — it is the action of a group
  element, and `specGal` turns the group law into composition.  Hence
  `F + W = t` is EQUIVALENT to `F² + N = t·F` pointwise, because
  `F (F y + W y) = F²y + N·y` (the second summand by `hVFr` read on
  points) and `F (t·y) = t·F y` (`Mult.galSMul_act`).  So the target may
  be attacked in its characteristic-equation form and transported back,
  and no cancellation of `N` — which would be illegitimate on
  `N`-torsion — is ever performed.
* The Galois action carries `A'[Iⁿ]` into itself (`Mult.torsion`) and is
  `𝒪_D`-linear there, so in a level frame it is given by a MATRIX over
  `𝒪_D/Iⁿ`.  That is `exists_frobLevelMatrix_of_levelTateFrame` below,
  and it is pure algebra: no geometry, no finiteness of `k`.

Given those, the characteristic equation at one level is 2×2
Cayley–Hamilton, `mulVec_add_det_mul_eq_trace_mul_fin_two`, and the
remaining content splits into four disjoint theorems:

* `exists_levelTateFrame_finiteBase` — `A'[Iⁿ]` is FREE OF RANK TWO over
  `𝒪_D/Iⁿ` for `I` of residue characteristic prime to `#k`.  This is
  where `hdim'` is consumed, and it is the ONLY leaf that uses it.  It is
  the finite-base analogue of `exists_levelTateFrame`, which cannot be
  reused: that one is stated over a NUMBER FIELD and its proof runs
  through `card_torsion_of_isMaximal` and the Betti frame, i.e. through
  characteristic zero.  The prime-to-`p` restriction is not decoration —
  at the residue characteristic of `k` the statement is FALSE
  (`A'[pⁿ](k̄)` has `p`-rank at most `g`, and is `0` in the supersingular
  case), which is why the hypothesis `¬ q ∣ N` appears.
* `det_frobLevelMatrix_eq_natCast_finiteBase` — the DETERMINANT of that
  matrix is `N`.  This is the Weil pairing over a finite field, in the
  Hilbert–Blumenthal normalisation the rest of this section uses
  (`det_{𝒪_D} F = N`, not `N²`; consistency check: `deg F = N^g` and
  `Nm_{D/ℚ}(N) = N^{[D:ℚ]} = N^g`).  It is the finite-base counterpart of
  `exists_finset_charFrob_coeff_zero_eq_absNorm_of_tateFrame_mult`.
* `exists_frobLevelTrace_of_mult_finiteBase` — the TRACE is a single
  global integer of `D`, the SAME one at every level.  Note what the
  content is and is not: a trace in `𝒪_D/Iⁿ` always lifts to `𝒪_D`,
  since `Ideal.Quotient.mk` is surjective, so nothing is asserted by
  "rationality at one level".  The whole statement is the UNIFORMITY —
  one `t` serving every maximal `I` and every `n` at once — which is
  precisely the compatible-system content, i.e. Weil (Mumford *AV* §19,
  Milne *AV* §V, Tate 1966), and the `∃ t` standing outside the `∀ I, ∀ n`
  is where it lives.
* `frobTraceAct_of_torsion_of_mult_finiteBase` — an identity verified on
  all PRIME-TO-`p` torsion holds at EVERY geometric point.  This is the
  one place where the algebraicity of the maps is unavoidable, and it is
  worth saying why, because it is the trap of this cluster.  `A'(k̄)` is a
  torsion group, but it is the direct sum of its primary parts and a
  homomorphism of abstract groups killing all the prime-to-`p` parts is
  in general NOT zero on the `p`-part.  What rules that out is that
  `F + W - t` comes from a MORPHISM of schemes and `⋃ₙ A'[ℓⁿ]` is
  Zariski dense — equivalently `End(A') ↪ End(T_ℓ A')`.  That is why this
  leaf carries `Fr`, `V`, `hFrf`, `hVf`, `hFrV` and `hVpt` although the
  assembly itself needs only `hVFr`: they are the data that makes the
  operator algebraic, and a prover of this leaf must use them.  It needs
  neither `hdim'` nor the rank-two theory.

**FAITHFULNESS OF THE TWO FRAME-QUANTIFIED LEAVES.**  Both are stated
`∀ c, IsLevelTateFrame … c → ∀ Φ, (∀ u, F (c u) = c (Φ *ᵥ u)) → …`.  A
different frame changes `Φ` by conjugation, and `det`/`trace` are
conjugation invariants, so neither statement depends on the choice — and
`Φ` is UNIQUE for a given `c`, since `c` is injective and a matrix is
determined by its action on the standard basis.  There is therefore no
junk witness on either side.  The exotic-frame counterexample that
forces `j`/`hj` on every frame-level statement elsewhere in this file
cannot touch these two: the coefficient ring is not abstract here, it is
`𝒪_D/Iⁿ` itself, and the real multiplication enters through `m'.act`
directly via the last clause of `IsLevelTateFrame`.

**WHAT IS STILL MISSING**, re-checked rather than quoted: the pin has no
abelian varieties and no Frobenius morphism of schemes
(`grep -rli frobenius .lake/packages/mathlib/Mathlib/AlgebraicGeometry/`
is empty), `~/cs/FLT` has no abelian-variety material, and this tree has
no `End(A)` as a ring and no Weil pairing over a finite field.  So all
four leaves are gated on machinery that must be built; the gain is that
the four subtrees are disjoint — `ℓ`-adic torsion of an abelian variety
in characteristic `p` (Mumford *AV* §6, Milne *AV* §I.7), the Weil
pairing (Mumford *AV* §16, §20), Weil's rationality of the
characteristic polynomial (Mumford *AV* §19, Tate 1966), and Zariski
density of torsion / faithfulness of the Tate module (Mumford *AV* §19,
Milne *AV* §V.1) — and can be owned independently. -/

/-- **CAYLEY–HAMILTON IN DIMENSION TWO, COORDINATEWISE** (PROVEN).  For a
`2 × 2` matrix `Φ` over any commutative ring, `Φ² + det Φ = tr Φ · Φ`,
read on a vector and one coordinate at a time.

Stated in this shape rather than as a matrix identity because that is how
the assembly of `exists_frobTraceAct_of_mult_finiteBase` consumes it: the
level frame there transports `Matrix.mulVec` and scalar multiplication
coordinatewise, and going through `Matrix.charpoly` would buy nothing at
`n = 2`. -/
theorem mulVec_add_det_mul_eq_trace_mul_fin_two {R : Type*} [CommRing R]
    (Φ : Matrix (Fin 2) (Fin 2) R) (u : Fin 2 → R) (i : Fin 2) :
    (Φ.mulVec (Φ.mulVec u)) i + Φ.det * u i = Φ.trace * (Φ.mulVec u) i := by
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two,
      Matrix.trace_fin_two] <;> ring

open _root_.NumberField in
/-- **THE GALOIS ACTION, READ IN A LEVEL FRAME, IS A MATRIX** (PROVEN).

If `c` is a level-`J` frame of the geometric fibre — an additive,
`𝒪_D`-semilinear bijection `(𝒪_D/J)² ≃ A'[J]` — then for every
`σ ∈ Γ_k` there is a matrix `Φ` over `𝒪_D/J` with
`σ · c u = c (Φ *ᵥ u)`.

Three inputs, all already proven, and no geometry:
`Mult.torsion` carries the Galois-stability of `A[J]`, so `σ · c u` is
again in the image of `c`; `AbelianSchemeStruct.pre_add` makes the
transported map additive; and `Mult.galSMul_act` makes it
`𝒪_D`-linear, hence `𝒪_D/J`-linear because `Ideal.Quotient.mk` is
surjective.  A linear endomorphism of a free module of rank two is a
matrix.

`Φ` is UNIQUE, since `c` is injective and `Φ *ᵥ ·` is determined on the
standard basis; that is what makes the two frame-quantified leaves below
faithful. -/
theorem exists_frobLevelMatrix_of_levelTateFrame
    {k : Type u} [Field k]
    {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of k)}
    (ab' : AbelianSchemeStruct f')
    {D : Type u} [Field D] [NumberField D]
    (m' : Mult ab' (NumberField.RingOfIntegers D))
    (σ : Field.absoluteGaloisGroup k)
    (J : Ideal (NumberField.RingOfIntegers D))
    (c : (Fin 2 → NumberField.RingOfIntegers D ⧸ J) →
      GeomFibrePt f' (𝟙 (Spec (CommRingCat.of k))))
    (hc : IsLevelTateFrame m' (𝟙 (Spec (CommRingCat.of k))) J c) :
    ∃ Φ : Matrix (Fin 2) (Fin 2) (NumberField.RingOfIntegers D ⧸ J),
      ∀ u, ab'.galSMul (𝟙 (Spec (CommRingCat.of k))) σ (c u) = c (Φ.mulVec u) := by
  classical
  obtain ⟨hmem, hadd, hinj, hsurj, hsmul⟩ := hc
  have hgal_add : ∀ u v : GeomFibrePt f' (𝟙 (Spec (CommRingCat.of k))),
      ab'.galSMul (𝟙 (Spec (CommRingCat.of k))) σ (ab'.add u v)
        = ab'.add (ab'.galSMul (𝟙 (Spec (CommRingCat.of k))) σ u)
            (ab'.galSMul (𝟙 (Spec (CommRingCat.of k))) σ v) :=
    fun u v => ab'.pre_add (specGal σ) (specGal_comp_base _ σ) u v
  have hex : ∀ u, ∃ v, c v = ab'.galSMul (𝟙 (Spec (CommRingCat.of k))) σ (c u) := by
    intro u
    exact hsurj _ ((m'.torsion (𝟙 (Spec (CommRingCat.of k))) J).2 σ (c u) (hmem u))
  choose g hg using hex
  have hgadd : ∀ u v, g (u + v) = g u + g v := by
    intro u v
    apply hinj
    rw [hg, hadd, hgal_add, ← hg, ← hg, ← hadd]
  have hgsmul : ∀ (r : NumberField.RingOfIntegers D ⧸ J) (u),
      g (fun i => r * u i) = fun i => r * g u i := by
    intro r u
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    apply hinj
    rw [hg, hsmul, m'.galSMul_act, ← hg, hsmul]
  refine ⟨LinearMap.toMatrix'
    { toFun := g, map_add' := hgadd, map_smul' := fun r u => hgsmul r u }, fun u => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  exact (hg u).symm

open _root_.NumberField in
/-- **THE PRIME-TO-`p` TORSION OF AN ABELIAN SCHEME WITH REAL
MULTIPLICATION OVER A FINITE FIELD IS FREE OF RANK TWO** (sorry leaf —
Mumford *Abelian Varieties* §6, Milne *Abelian Varieties* §I.7; see the
subsection note above for the cut).

For `k` finite with `N` elements, `I` a maximal ideal of `𝒪_D` whose
residue characteristic `q` does not divide `N`, and any `n`, the
`Iⁿ`-torsion of the geometric fibre admits a level frame: an additive,
injective, `𝒪_D`-semilinear map `(𝒪_D/Iⁿ)² → A'(k̄)` with image exactly
`A'[Iⁿ]`.

Classically `A'[qⁿ](k̄) ≅ (ℤ/qⁿ)^{2g}` for `q` different from the
characteristic — this is where the separability of `[qⁿ]` is used, and it
is exactly what fails at `q = p` — and `hdim'` says `g = [D:ℚ]`, so the
`𝒪_D/Iⁿ`-module `A'[Iⁿ]` has the cardinality of `(𝒪_D/Iⁿ)²` and is free
of rank two by the same counting argument that
`card_torsion_of_isMaximal` runs in characteristic zero.

**THIS IS NOT `exists_levelTateFrame`, AND THAT ONE CANNOT BE REUSED.**
The existing frame theorem is stated over a base that is a NUMBER FIELD
and is proved through the Betti frame (`exists_bettiFrame`,
`card_torsion_of_isMaximal`), i.e. through singular homology of the
complex points.  Over a finite field there is no such input and the
statement is genuinely different — in particular it is FALSE without
`¬ q ∣ N`: at the residue characteristic of `k` the group `A'[pⁿ](k̄)` has
order `p^{rn}` with `r ≤ g` the `p`-rank, and is trivial in the
supersingular case, so no rank-two frame can exist.

`hfin` and `hN` are used only to give the prime-to-characteristic
condition its meaning (`N = #k = p^a`, so `¬ q ∣ N` says `q ≠ p`); `σ`
and `hσ` do not occur, because this statement is about the torsion
subgroup alone and not about the Frobenius. -/
theorem exists_levelTateFrame_finiteBase
    {k : Type u} [Field k] (hfin : Finite k) (N : ℕ) (hN : Nat.card k = N)
    {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of k)}
    (ab' : AbelianSchemeStruct f')
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m' : Mult ab' (NumberField.RingOfIntegers D))
    (hdim' : SmoothOfRelativeDimension (Module.finrank ℚ D) f')
    (q : ℕ) (hq : q.Prime) (hqN : ¬ q ∣ N)
    (I : Ideal (NumberField.RingOfIntegers D)) (hI : I.IsMaximal)
    (hqI : (q : NumberField.RingOfIntegers D) ∈ I) (n : ℕ) :
    ∃ c : (Fin 2 → NumberField.RingOfIntegers D ⧸ I ^ n) →
        GeomFibrePt f' (𝟙 (Spec (CommRingCat.of k))),
      IsLevelTateFrame m' (𝟙 (Spec (CommRingCat.of k))) (I ^ n) c :=
  sorry

open _root_.NumberField in
/-- **THE DETERMINANT OF FROBENIUS AT A PRIME-TO-`p` LEVEL IS `N`**
(sorry leaf — the Weil pairing over a finite field; Mumford *Abelian
Varieties* §16 and §20, Milne *Abelian Varieties* §I.13; see the
subsection note above for the cut).

In any level frame of `A'[Iⁿ]`, the matrix `Φ` of the `N`-power Frobenius
has `det Φ = N` in `𝒪_D/Iⁿ`.

Classically: the `𝒪_D`-linear Weil pairing identifies `⋀²_{𝒪_D} T_I A'`
with the `I`-adic Tate module of `μ`, on which the arithmetic Frobenius
of `k` acts by the absolute norm `N`.  This is the finite-base
counterpart of `exists_finset_charFrob_coeff_zero_eq_absNorm_of_tateFrame_mult`,
and the NORMALISATION is the same one used throughout this section — the
constant coefficient over `𝒪_D` is `N`, not `N²`, which is the
Hilbert–Blumenthal convention of Shimura / Taylor 2002 §1.  Consistency
check on degrees: `deg F = N^g` for `g = dim A'`, and
`Nm_{D/ℚ}(N) = N^{[D:ℚ]} = N^g`, so `N ∈ 𝒪_D` is the right determinant.

FAITHFULNESS.  `hσ` is load-bearing and cannot be dropped: it is what
makes `σ` the `N`-power Frobenius rather than an arbitrary element of
`Γ_k`, and for `σ = 1` the determinant is `1`.  The quantification over
the frame is harmless — a change of frame conjugates `Φ`, and `det` is a
conjugation invariant — and `Φ` is pinned by `hΦ` because `c` is
injective, so there is no junk witness.  `hdim'` is deliberately ABSENT:
the existence of the frame `c` already forces the relative dimension, and
this statement is about a frame that is handed to it. -/
theorem det_frobLevelMatrix_eq_natCast_finiteBase
    {k : Type u} [Field k] (hfin : Finite k) (N : ℕ) (hN : Nat.card k = N)
    {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of k)}
    (ab' : AbelianSchemeStruct f')
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m' : Mult ab' (NumberField.RingOfIntegers D))
    (σ : Field.absoluteGaloisGroup k)
    (hσ : ∀ z : AlgebraicClosure k,
      (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) z = z ^ N)
    (q : ℕ) (hq : q.Prime) (hqN : ¬ q ∣ N)
    (I : Ideal (NumberField.RingOfIntegers D)) (hI : I.IsMaximal)
    (hqI : (q : NumberField.RingOfIntegers D) ∈ I) (n : ℕ)
    (c : (Fin 2 → NumberField.RingOfIntegers D ⧸ I ^ n) →
      GeomFibrePt f' (𝟙 (Spec (CommRingCat.of k))))
    (hc : IsLevelTateFrame m' (𝟙 (Spec (CommRingCat.of k))) (I ^ n) c)
    (Φ : Matrix (Fin 2) (Fin 2) (NumberField.RingOfIntegers D ⧸ I ^ n))
    (hΦ : ∀ u, ab'.galSMul (𝟙 (Spec (CommRingCat.of k))) σ (c u) = c (Φ.mulVec u)) :
    Φ.det = Ideal.Quotient.mk (I ^ n) (N : NumberField.RingOfIntegers D) :=
  sorry

open _root_.NumberField in
/-- **THE TRACE OF FROBENIUS IS ONE GLOBAL INTEGER OF `D`, THE SAME AT
EVERY LEVEL** (sorry leaf — Weil; Mumford *Abelian Varieties* §19, Milne
*Abelian Varieties* §V, Tate 1966.  See the subsection note above for the
cut).

There is a single `t ∈ 𝒪_D` such that for EVERY maximal `I` of residue
characteristic prime to `#k`, every `n`, every level frame of `A'[Iⁿ]`
and the matrix `Φ` of the Frobenius in it, `tr Φ = t mod Iⁿ`.

**WHERE THE CONTENT IS, AND WHAT IS NOT ASSERTED.**  Nothing at all is
asserted by "the trace at one level is rational": `tr Φ` lives in
`𝒪_D/Iⁿ` and `Ideal.Quotient.mk` is surjective, so a lift to `𝒪_D`
exists for free.  The entire statement is the UNIFORMITY — the `∃ t`
stands OUTSIDE the `∀ I, ∀ n`, so one global integer serves every maximal
ideal and every level at once.  That is exactly the compatible-system
content, i.e. Weil's theorem that the characteristic polynomial of the
Frobenius endomorphism has coefficients in `𝒪_D` independent of `I`, and
it is the reason the consumer's `∃ t, ∀ I` quantifier order costs
nothing further downstream.

Classically: `F` commutes with the real multiplication, so `D[F]` is a
commutative `D`-subalgebra of `End⁰(A')` acting `D_I`-linearly on
`V_I A' ≅ D_I²`; a commutative subalgebra of `M₂` containing the scalars
has degree at most two, so `F` satisfies a monic quadratic over `D` whose
linear coefficient is `tr Φ` for every `I` at once, and the coefficients
are integral because `F` preserves the lattice `T_I` and `𝒪_D` is
integrally closed.

FAITHFULNESS.  `hσ` is load-bearing (for `σ = 1` the trace is `2`, and
the statement is then true but about a different operator; for a general
`σ` no such `t` need exist).  `hdim'` is deliberately ABSENT: this leaf
is quantified over frames that are handed to it, and the existence of a
rank-two frame already forces the relative dimension — the leaf is
vacuously true for a fibre that admits none.  Frame-independence is
automatic, since a change of frame conjugates `Φ` and `trace` is a
conjugation invariant. -/
theorem exists_frobLevelTrace_of_mult_finiteBase
    {k : Type u} [Field k] (hfin : Finite k) (N : ℕ) (hN : Nat.card k = N)
    {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of k)}
    (ab' : AbelianSchemeStruct f')
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m' : Mult ab' (NumberField.RingOfIntegers D))
    (σ : Field.absoluteGaloisGroup k)
    (hσ : ∀ z : AlgebraicClosure k,
      (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) z = z ^ N) :
    ∃ t : NumberField.RingOfIntegers D,
      ∀ q : ℕ, q.Prime → ¬ q ∣ N →
        ∀ I : Ideal (NumberField.RingOfIntegers D), I.IsMaximal →
          (q : NumberField.RingOfIntegers D) ∈ I → ∀ n : ℕ,
          ∀ c : (Fin 2 → NumberField.RingOfIntegers D ⧸ I ^ n) →
              GeomFibrePt f' (𝟙 (Spec (CommRingCat.of k))),
            IsLevelTateFrame m' (𝟙 (Spec (CommRingCat.of k))) (I ^ n) c →
            ∀ Φ : Matrix (Fin 2) (Fin 2) (NumberField.RingOfIntegers D ⧸ I ^ n),
              (∀ u, ab'.galSMul (𝟙 (Spec (CommRingCat.of k))) σ (c u) = c (Φ.mulVec u)) →
              Φ.trace = Ideal.Quotient.mk (I ^ n) t :=
  sorry

open _root_.NumberField in
/-- **AN IDENTITY VERIFIED ON ALL PRIME-TO-`p` TORSION HOLDS AT EVERY
GEOMETRIC POINT** (sorry leaf — Zariski density of the prime-to-`p`
torsion, equivalently the faithfulness of the Tate module; Mumford
*Abelian Varieties* §19, Milne *Abelian Varieties* §V.1.  See the
subsection note above for the cut).

If `F y + V y = t · y` for every `y` killed by `Iⁿ`, for every maximal
`I` of residue characteristic prime to `#k` and every `n`, then it holds
for EVERY geometric point of the fibre.

**WHY THIS IS NOT FREE, WHICH IS THE TRAP OF THIS CLUSTER.**  `A'(k̄)` is
a torsion group — every geometric point is defined over a finite subfield
— so one is tempted to conclude that a homomorphism killing all the
prime-to-`p` torsion kills everything.  That is FALSE: a torsion abelian
group is the direct sum of its primary components, and an endomorphism of
abstract groups may be arbitrary on the `p`-component while vanishing on
all the others.  What excludes it here is that `F + V - t` is ALGEBRAIC:
it is induced by a morphism of schemes, and `⋃ₙ A'[ℓⁿ]` is Zariski dense
in `A'` for any `ℓ` different from the characteristic, so a morphism
vanishing on it vanishes.  Equivalently `End(A') → End(T_ℓ A')` is
injective.

That is why the leaf carries the whole morphism package `Fr`, `V`,
`hFrf`, `hVf`, `hFrpt`, `hFrV`, `hVpt` even though the assembly of the
consumer uses only `hVFr` among them: they are what makes the operator
algebraic, and any proof of this leaf must use them.  The one piece of
the arithmetic package it does NOT need is `hdim'` — density is
independent of the relative dimension — and the rank-two theory does not
enter.

FAITHFULNESS.  The conclusion is universally quantified over `t`, so a
junk `t` would falsify the leaf if the hypothesis admitted one; it does
not, because the prime-to-`p` torsion already pins `t` (it is determined
modulo `Iⁿ` for every prime-to-`p` `I` and every `n`, hence determined).
`hσ` is load-bearing for the same reason as in the sibling leaves: it is
what identifies the Galois action with the Frobenius endomorphism. -/
theorem frobTraceAct_of_torsion_of_mult_finiteBase
    {k : Type u} [Field k] (hfin : Finite k) (N : ℕ) (hN : Nat.card k = N)
    {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of k)}
    (ab' : AbelianSchemeStruct f')
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m' : Mult ab' (NumberField.RingOfIntegers D))
    (σ : Field.absoluteGaloisGroup k)
    (hσ : ∀ z : AlgebraicClosure k,
      (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) z = z ^ N)
    (Fr V : A' ⟶ A') (hFrf : Fr ≫ f' = f') (hVf : V ≫ f' = f')
    (hFrpt : ∀ y : GeomFibrePt f' (𝟙 (Spec (CommRingCat.of k))),
      (ab'.galSMul (𝟙 (Spec (CommRingCat.of k))) σ y).1 = y.1 ≫ Fr)
    (hFrV : Fr ≫ V = ab'.mulByNat N) (hVFr : V ≫ Fr = ab'.mulByNat N)
    (Vpt : GeomFibrePt f' (𝟙 (Spec (CommRingCat.of k))) →
      GeomFibrePt f' (𝟙 (Spec (CommRingCat.of k))))
    (hVpt : ∀ y : GeomFibrePt f' (𝟙 (Spec (CommRingCat.of k))), (Vpt y).1 = y.1 ≫ V)
    (t : NumberField.RingOfIntegers D)
    (htors : ∀ q : ℕ, q.Prime → ¬ q ∣ N →
      ∀ I : Ideal (NumberField.RingOfIntegers D), I.IsMaximal →
        (q : NumberField.RingOfIntegers D) ∈ I → ∀ n : ℕ,
        ∀ y ∈ (m'.torsion (𝟙 (Spec (CommRingCat.of k))) (I ^ n)).1,
          ab'.add (ab'.galSMul (𝟙 (Spec (CommRingCat.of k))) σ y) (Vpt y) = m'.act t y) :
    ∀ y : GeomFibrePt f' (𝟙 (Spec (CommRingCat.of k))),
      ab'.add (ab'.galSMul (𝟙 (Spec (CommRingCat.of k))) σ y) (Vpt y) = m'.act t y :=
  sorry

/-- **THE TRACE OF FROBENIUS IS A GLOBAL INTEGER OF `D`** (**PROVEN
2026-07-27** by assembly over the four leaves in the subsection note
immediately above — Weil; this is the deep half of the finite-field
cut, see also the subsection note further above).

With `Fr` the Frobenius endomorphism and `V` its Verschiebung, there is a
single `t ∈ 𝒪_D` with

    Fr(y) + V(y) = t · y

for EVERY geometric point `y`.  Together with `Fr ∘ V = [N]` this is the
characteristic equation `F² - t F + N = 0`, which is what the consumer
`exists_frobEndoCharEq_of_mult_finiteBase` assembles.

WHERE THE CONTENT IS.  `hdim'` says the relative dimension is `[D:ℚ]`,
which is the Hilbert–Blumenthal condition; it makes `T_I A'` free of rank
TWO over `𝒪_{D,I}` for every maximal `I` of residue characteristic
different from that of `k`.  `Fr` is central in `End(A')` (Frobenius
commutes with every `k`-endomorphism, in particular with the real
multiplication), so `D[Fr]` is a COMMUTATIVE `D`-subalgebra of
`End⁰(A')`, acting faithfully and `D_I`-linearly on `V_I A' ≅ D_I²`; a
commutative subalgebra of `M₂` containing the scalars has degree at most
two, so `[D[Fr] : D] ≤ 2` and `Fr` satisfies a monic quadratic over `D`.
Its coefficients are integral because `Fr` preserves the lattice `T_I`,
so they lie in `𝒪_D`, and its linear coefficient is `Fr + V`.

WHY `V` IS A HYPOTHESIS AND NOT AN EXISTENTIAL.  The pair
`(hFrV, hVFr)` PINS `V`: on geometric points `Fr` is bijective (it is the
action of a group element), so `V` is determined by `Fr ≫ V = [N]`
alone, and `A'` is reduced, so the morphism is determined by its effect
on points.  There is therefore no junk `V` for which this statement could
be false — which is what makes it safe to universally quantify over `V`
here while producing it existentially in the previous leaf.

NOT ASSERTED: the archimedean bound `|t| ≤ 2√N` (the Riemann-hypothesis
half of Weil, needed by no consumer in this tree), and nothing about the
`I`-adic representations — no ideal `I`, no `n` and no torsion occurs
anywhere in this statement, which is the point of pushing the whole
cluster down to the residue field.

THE ROUTE OF THE PROOF BELOW, which is the paragraph above split four
ways; see the subsection note immediately above for the audit of each
piece.  Two facts are proved INLINE and are the reason the cut works.
First, `Fr` acts INJECTIVELY on geometric points, being the action of a
group element, so the target `F + V = t` is equivalent to the
characteristic equation `F² + N = t·F` — and the transport back is by
injectivity rather than by cancelling `N`, which would be illegitimate on
`N`-torsion.  Second, the Galois action preserves `A'[Iⁿ]` and is
`𝒪_D`-linear there, so in a level frame it is a `2 × 2` MATRIX
(`exists_frobLevelMatrix_of_levelTateFrame`, proven).  The equation at one
level is then Cayley–Hamilton
(`mulVec_add_det_mul_eq_trace_mul_fin_two`, proven) fed by
`det_frobLevelMatrix_eq_natCast_finiteBase` (the determinant is `N`) and
`exists_frobLevelTrace_of_mult_finiteBase` (one global trace for all
levels), over the frame supplied by `exists_levelTateFrame_finiteBase`;
and `frobTraceAct_of_torsion_of_mult_finiteBase` passes from the
prime-to-`p` torsion to every geometric point.

WHERE THE HYPOTHESES GO, since the split relocates them.  `hdim'` is
consumed by `exists_levelTateFrame_finiteBase` and by nothing else — it
is what makes the frame have rank TWO.  `hσ` goes to the determinant, the
trace and the density leaves, being what identifies the Galois action
with the Frobenius endomorphism.  `Fr`, `hFrf`, `hVf`, `hFrV` and `hVpt`
go to the density leaf, where the algebraicity of `F + V - t` is what
must be used; the assembly itself needs only `hVFr` and `hFrpt`, through
which it reads `F ∘ V = [N]` on points. -/
theorem exists_frobTraceAct_of_mult_finiteBase
    {k : Type u} [Field k] (hfin : Finite k) (N : ℕ) (hN : Nat.card k = N)
    {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of k)}
    (ab' : AbelianSchemeStruct f')
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m' : Mult ab' (NumberField.RingOfIntegers D))
    (hdim' : SmoothOfRelativeDimension (Module.finrank ℚ D) f')
    (σ : Field.absoluteGaloisGroup k)
    (hσ : ∀ z : AlgebraicClosure k,
      (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) z = z ^ N)
    (Fr V : A' ⟶ A') (hFrf : Fr ≫ f' = f') (hVf : V ≫ f' = f')
    (hFrpt : ∀ y : GeomFibrePt f' (𝟙 (Spec (CommRingCat.of k))),
      (ab'.galSMul (𝟙 (Spec (CommRingCat.of k))) σ y).1 = y.1 ≫ Fr)
    (hFrV : Fr ≫ V = ab'.mulByNat N) (hVFr : V ≫ Fr = ab'.mulByNat N)
    (Vpt : GeomFibrePt f' (𝟙 (Spec (CommRingCat.of k))) →
      GeomFibrePt f' (𝟙 (Spec (CommRingCat.of k))))
    (hVpt : ∀ y : GeomFibrePt f' (𝟙 (Spec (CommRingCat.of k))), (Vpt y).1 = y.1 ≫ V) :
    ∃ t : NumberField.RingOfIntegers D,
      ∀ y : GeomFibrePt f' (𝟙 (Spec (CommRingCat.of k))),
        ab'.add (ab'.galSMul (𝟙 (Spec (CommRingCat.of k))) σ y) (Vpt y) = m'.act t y := by
  classical
  -- `N · y` is postcomposition with the morphism `[N]`.
  have hNact : ∀ y : GeomFibrePt f' (𝟙 (Spec (CommRingCat.of k))),
      (m'.act (N : NumberField.RingOfIntegers D) y).1 = y.1 ≫ ab'.mulByNat N := by
    intro y
    letI : AddCommGroup (GeomFibrePt f' (𝟙 (Spec (CommRingCat.of k)))) :=
      ab'.addCommGroup (specAlgClos k ≫ 𝟙 (Spec (CommRingCat.of k)))
    letI : Module (NumberField.RingOfIntegers D)
        (GeomFibrePt f' (𝟙 (Spec (CommRingCat.of k)))) :=
      m'.module (specAlgClos k ≫ 𝟙 (Spec (CommRingCat.of k)))
    have h1 : m'.act (N : NumberField.RingOfIntegers D) y
        = (N : NumberField.RingOfIntegers D) • y := rfl
    rw [h1, Nat.cast_smul_eq_nsmul]
    exact ab'.nsmul_val N y
  -- `F ∘ V = [N]` read on geometric points, off the morphism identity `V ≫ Fr = [N]`.
  have hFVpt : ∀ y : GeomFibrePt f' (𝟙 (Spec (CommRingCat.of k))),
      ab'.galSMul (𝟙 (Spec (CommRingCat.of k))) σ (Vpt y)
        = m'.act (N : NumberField.RingOfIntegers D) y := by
    intro y
    apply Subtype.ext
    rw [hFrpt (Vpt y), hVpt y, hNact y, Category.assoc, hVFr]
  -- the Galois action is additive (`pre_add`) and injective (it is a group action).
  have hgal_add : ∀ u v : GeomFibrePt f' (𝟙 (Spec (CommRingCat.of k))),
      ab'.galSMul (𝟙 (Spec (CommRingCat.of k))) σ (ab'.add u v)
        = ab'.add (ab'.galSMul (𝟙 (Spec (CommRingCat.of k))) σ u)
            (ab'.galSMul (𝟙 (Spec (CommRingCat.of k))) σ v) :=
    fun u v => ab'.pre_add (specGal σ) (specGal_comp_base _ σ) u v
  have hFinj : Function.Injective (ab'.galSMul (𝟙 (Spec (CommRingCat.of k))) σ) := by
    letI : AddCommGroup (GeomFibrePt f' (𝟙 (Spec (CommRingCat.of k)))) :=
      ab'.addCommGroup (specAlgClos k ≫ 𝟙 (Spec (CommRingCat.of k)))
    letI : DistribMulAction (Field.absoluteGaloisGroup k)
        (GeomFibrePt f' (𝟙 (Spec (CommRingCat.of k)))) :=
      ab'.geomFibreAction (𝟙 (Spec (CommRingCat.of k)))
    exact MulAction.injective σ
  obtain ⟨t, ht⟩ :=
    exists_frobLevelTrace_of_mult_finiteBase hfin N hN ab' m' σ hσ
  refine ⟨t, ?_⟩
  refine frobTraceAct_of_torsion_of_mult_finiteBase hfin N hN ab' m' σ hσ Fr V hFrf hVf
    hFrpt hFrV hVFr Vpt hVpt t ?_
  intro q hq hqN I hI hqI n y hy
  obtain ⟨c, hc⟩ :=
    exists_levelTateFrame_finiteBase hfin N hN ab' m' hdim' q hq hqN I hI hqI n
  obtain ⟨Φ, hΦ⟩ := exists_frobLevelMatrix_of_levelTateFrame ab' m' σ (I ^ n) c hc
  have hdet := det_frobLevelMatrix_eq_natCast_finiteBase hfin N hN ab' m' σ hσ q hq hqN
    I hI hqI n c hc Φ hΦ
  have htr := ht q hq hqN I hI hqI n c hc Φ hΦ
  obtain ⟨-, hadd, -, hsurj, hsmul⟩ := hc
  obtain ⟨u, rfl⟩ := hsurj y hy
  -- the characteristic equation `F² + N = t·F` at level `Iⁿ`, by Cayley–Hamilton
  have key : ab'.add (ab'.galSMul (𝟙 (Spec (CommRingCat.of k))) σ
        (ab'.galSMul (𝟙 (Spec (CommRingCat.of k))) σ (c u)))
      (m'.act (N : NumberField.RingOfIntegers D) (c u))
      = m'.act t (ab'.galSMul (𝟙 (Spec (CommRingCat.of k))) σ (c u)) := by
    rw [hΦ u, hΦ (Φ.mulVec u), ← hsmul (N : NumberField.RingOfIntegers D) u, ← hdet,
      ← hadd, ← hsmul t (Φ.mulVec u), ← htr]
    exact congrArg c (funext fun i => mulVec_add_det_mul_eq_trace_mul_fin_two Φ u i)
  -- `F` is injective, so `F + V = t` follows from `F² + N = t·F`
  apply hFinj
  rw [hgal_add, hFVpt, key, m'.galSMul_act]

/-- **WEIL'S CHARACTERISTIC EQUATION FOR THE FROBENIUS ENDOMORPHISM OVER
A FINITE FIELD** (**PROVEN 2026-07-27** over the three leaves in the
subsection note immediately above — the Frobenius endomorphism, its
Verschiebung, and the `𝒪_D`-rationality of the trace.  It was previously
a leaf; the faithfulness audit of its three load-bearing hypotheses in
the subsection note further above still applies verbatim, and every one
of them is passed on to the leaf that consumes it).

Let `k` be a finite field with `N` elements, `f' : A' ⟶ Spec k` an
abelian scheme of relative dimension `[D:ℚ]` with real multiplication by
`𝒪_D`, and `σ ∈ Γ_k` the `N`-power Frobenius.  Then there is a single
`t ∈ 𝒪_D` with

    σ²(y) + N · y = t · σ(y)

for EVERY geometric point `y` — not merely for torsion points, and with
no ideal `I` anywhere in sight.  That is the whole point of pushing the
statement down to the residue field: over `k` the arithmetic Frobenius
of `Γ_k` IS the `N`-power Frobenius ENDOMORPHISM of `A'`, so the relation
is an identity in `End(A')` and holds at every point at once.  The
`I`-independence that the frame-free leaf below needs is therefore not
proved here — it never arises.

Classically: `σ` lies in the centre of `End(A')`, hence in the
centralizer of `𝒪_D`, which is a commutative `D`-algebra of degree at
most two because `T_I A'` is free of rank two over `𝒪_{D,I}` (this is
where `hdim'` is consumed); `t` and `N` are the coefficients of its
characteristic polynomial over `D`, integral by Weil, and the constant
one is `N` in the Hilbert–Blumenthal normalisation (`deg σ = N^g` and
`Nm_{D/ℚ}(N) = N^g`).

That paragraph is now the ROUTE of the proof below, split three ways:
"the arithmetic Frobenius IS an endomorphism" is
`exists_frobEndomorphism_of_finiteBase`, "`[N]` factors through it" is
`exists_verschiebung_of_frobEndomorphism_finiteBase`, and "the linear
coefficient lies in `𝒪_D`" is `exists_frobTraceAct_of_mult_finiteBase`.
Only the last needs `hdim'`; the assembly itself needs neither, and uses
just the additivity of the Galois action and its commutation with the
real multiplication, both already proven in
`Modularity/AbelianScheme.lean`.

NOT ASSERTED: the archimedean bound `|t| ≤ 2√N`, which is the Riemann
hypothesis half and which no consumer in this tree needs. -/
theorem exists_frobEndoCharEq_of_mult_finiteBase
    {k : Type u} [Field k] (hfin : Finite k) (N : ℕ) (hN : Nat.card k = N)
    {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of k)}
    (ab' : AbelianSchemeStruct f')
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m' : Mult ab' (NumberField.RingOfIntegers D))
    (hdim' : SmoothOfRelativeDimension (Module.finrank ℚ D) f')
    (σ : Field.absoluteGaloisGroup k)
    (hσ : ∀ z : AlgebraicClosure k,
      (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) z = z ^ N) :
    ∃ t : NumberField.RingOfIntegers D,
      ∀ y : GeomFibrePt f' (𝟙 (Spec (CommRingCat.of k))),
        ab'.add (ab'.galSMul _ σ (ab'.galSMul _ σ y))
            (m'.act (N : NumberField.RingOfIntegers D) y)
          = m'.act t (ab'.galSMul _ σ y) := by
  classical
  obtain ⟨Fr, hFrf, hFrpt⟩ := exists_frobEndomorphism_of_finiteBase hfin N hN ab' σ hσ
  obtain ⟨V, hVf, hFrV, hVFr⟩ :=
    exists_verschiebung_of_frobEndomorphism_finiteBase hfin N hN ab' σ hσ Fr hFrf hFrpt
  -- `V` read on geometric points: postcomposing with `V` preserves the base point,
  -- because `V` is a morphism over `Spec k`.
  have hVbase : ∀ y : GeomFibrePt f' (𝟙 (Spec (CommRingCat.of k))),
      (y.1 ≫ V) ≫ f' = specAlgClos k ≫ 𝟙 (Spec (CommRingCat.of k)) := by
    intro y
    rw [Category.assoc, hVf]
    exact y.2
  obtain ⟨t, ht⟩ :=
    exists_frobTraceAct_of_mult_finiteBase hfin N hN ab' m' hdim' σ hσ Fr V hFrf hVf hFrpt
      hFrV hVFr (fun y => ⟨y.1 ≫ V, hVbase y⟩) (fun _ => rfl)
  -- `N · y` is postcomposition with the morphism `[N]`: the real multiplication acts
  -- on a rational integer through the underlying `ℕ`-action, which is `mulByNat`.
  have hNact : ∀ y : GeomFibrePt f' (𝟙 (Spec (CommRingCat.of k))),
      (m'.act (N : NumberField.RingOfIntegers D) y).1 = y.1 ≫ ab'.mulByNat N := by
    intro y
    letI : AddCommGroup (GeomFibrePt f' (𝟙 (Spec (CommRingCat.of k)))) :=
      ab'.addCommGroup (specAlgClos k ≫ 𝟙 (Spec (CommRingCat.of k)))
    letI : Module (NumberField.RingOfIntegers D)
        (GeomFibrePt f' (𝟙 (Spec (CommRingCat.of k)))) :=
      m'.module (specAlgClos k ≫ 𝟙 (Spec (CommRingCat.of k)))
    have h1 : m'.act (N : NumberField.RingOfIntegers D) y
        = (N : NumberField.RingOfIntegers D) • y := rfl
    rw [h1, Nat.cast_smul_eq_nsmul]
    exact ab'.nsmul_val N y
  -- `Frob ∘ V = [N]` on geometric points, read off the morphism identity `V ≫ Fr = [N]`.
  have hFVpt : ∀ y : GeomFibrePt f' (𝟙 (Spec (CommRingCat.of k))),
      ab'.galSMul (𝟙 (Spec (CommRingCat.of k))) σ
          (⟨y.1 ≫ V, hVbase y⟩ : GeomFibrePt f' (𝟙 (Spec (CommRingCat.of k))))
        = m'.act (N : NumberField.RingOfIntegers D) y := by
    intro y
    apply Subtype.ext
    rw [hFrpt ⟨y.1 ≫ V, hVbase y⟩, hNact y, Category.assoc, hVFr]
  -- the Galois action is additive: this is the naturality axiom `pre_add`.
  have hgal_add : ∀ u v : GeomFibrePt f' (𝟙 (Spec (CommRingCat.of k))),
      ab'.galSMul (𝟙 (Spec (CommRingCat.of k))) σ (ab'.add u v)
        = ab'.add (ab'.galSMul (𝟙 (Spec (CommRingCat.of k))) σ u)
            (ab'.galSMul (𝟙 (Spec (CommRingCat.of k))) σ v) :=
    fun u v => ab'.pre_add (specGal σ) (specGal_comp_base _ σ) u v
  refine ⟨t, fun y => ?_⟩
  -- `F² + N = F ∘ (F + V) = F ∘ [t] = [t] ∘ F`.
  calc ab'.add (ab'.galSMul (𝟙 (Spec (CommRingCat.of k))) σ
          (ab'.galSMul (𝟙 (Spec (CommRingCat.of k))) σ y))
        (m'.act (N : NumberField.RingOfIntegers D) y)
      = ab'.add (ab'.galSMul (𝟙 (Spec (CommRingCat.of k))) σ
            (ab'.galSMul (𝟙 (Spec (CommRingCat.of k))) σ y))
          (ab'.galSMul (𝟙 (Spec (CommRingCat.of k))) σ
            (⟨y.1 ≫ V, hVbase y⟩ : GeomFibrePt f' (𝟙 (Spec (CommRingCat.of k))))) := by
        rw [hFVpt y]
    _ = ab'.galSMul (𝟙 (Spec (CommRingCat.of k))) σ
          (ab'.add (ab'.galSMul (𝟙 (Spec (CommRingCat.of k))) σ y)
            (⟨y.1 ≫ V, hVbase y⟩ : GeomFibrePt f' (𝟙 (Spec (CommRingCat.of k))))) :=
        (hgal_add _ _).symm
    _ = ab'.galSMul (𝟙 (Spec (CommRingCat.of k))) σ (m'.act t y) := by rw [ht y]
    _ = m'.act t (ab'.galSMul (𝟙 (Spec (CommRingCat.of k))) σ y) :=
        m'.galSMul_act (𝟙 (Spec (CommRingCat.of k))) σ t y

/-- **FROBENIUS SATISFIES ITS CHARACTERISTIC EQUATION ON THE TORSION OF
THE FIBRE** (**PROVEN 2026-07-27** over the two leaves immediately above,
by the specialization cut described in the subsection note there — Weil.
It was previously the only remaining compatible-system input of the whole
chain; that content now sits in
`exists_frobEndoCharEq_of_mult_finiteBase`, over a FINITE field, where it
is an identity of endomorphisms and no longer mentions `I` at all).

There is a family `t : w ↦ 𝒪_D` and a finite set of places such that
outside it, writing `Frob_w` for the arithmetic Frobenius at `w` read in
`Γ_F` (the element `absoluteGaloisGroup.map (algebraMap F F_w)
(adicArithFrob w)` whose characteristic polynomial `charFrob` is), one
has

    Frob_w²(y) + (N w) · y = t w · Frob_w(y)

for EVERY geometric point `y` of the fibre killed by `Iⁿ`, for every
maximal `I` whose residue characteristic `q` is not the residue
characteristic of `w`, and every `n`.

WHAT THIS IS CLASSICALLY, AND WHY IT IS THE RIGHT PLACE TO CUT.  At a
place `w` of good reduction the prime-to-`p` torsion of `A` injects
Galois-equivariantly into the torsion of the reduction `A_w`, on which
`Frob_w` acts as the `q_w`-power Frobenius ENDOMORPHISM; that
endomorphism satisfies its own characteristic equation
`F² - a_w F + N w = 0` in `End(A_w)`, whose coefficients are global
integers of `D` because the real multiplication makes `T_I A_w` free of
rank two over `𝒪_{D,I}`.  So this is exactly the classical input — Weil,
not Faltings, and the CITATION AUDIT in the section note above applies
verbatim — with every trace of the `I`-adic bookkeeping removed: there
is no frame here, no coefficient ring `O`, no representation `τ` and no
characteristic polynomial.  The independence-of-`λ` content is carried
by the single quantifier order `∃ t, ∀ I`: ONE `t w` serves every `I`
at once, which is what it means for the `I`-adic Tate modules to be
members of one compatible system.

Everything else in the chain is now algebra:
`weilCoeffs_fst_eq_of_frobTorsionEndo` below transports this relation
through an arbitrary frame and shows the frame's own `a w` equals
`t w`, and `exists_finset_weilCoeffs_fst_eq_of_mult` then compares two
frames through that common value.

FAITHFULNESS — THE THREE PINS, AND WHY EACH IS LOAD-BEARING.

* **`I.IsMaximal` cannot be dropped.**  With `I = ⊥` the ideal `Iⁿ` is
  `⊥`, `Submodule.torsionBySet` over the zero ideal is the WHOLE module,
  and the relation would be asserted for every geometric point of the
  fibre, torsion or not.  That is FALSE: `Frob_w` is a field
  automorphism, not an endomorphism of `A`, and the characteristic
  equation holds only where the reduction map is defined, i.e. on
  torsion.  Maximality is what forces `Iⁿ` to have finite index and
  hence `torsion (Iⁿ) ⊆ A[qⁿ]`.
* **`(q : 𝒪_F) ∉ w.asIdeal` cannot be dropped.**  At `w` above `q` the
  `q`-power torsion is ramified at `w`, so the action of a Frobenius
  LIFT is not even well defined independently of the lift, and no
  relation with `𝒪_D`-coefficients can hold.  This is exactly the
  exclusion the frames' own `bad` sets make (they contain the places
  over their residue characteristic), and it is why it appears here as a
  hypothesis rather than being absorbed into `bad`: `bad` is quantified
  before `I`, so it cannot depend on `q`.
* **`N w` is the ABSOLUTE norm**, matching the determinant leaf
  `exists_finset_charFrob_coeff_zero_eq_absNorm_of_tateFrame_mult`; this
  is the Hilbert–Blumenthal normalization of Shimura / Taylor 2002 §1,
  in which the constant coefficient over `𝒪_D` is `N w` and not `N w²`.

WHERE THE `j`/`hj` PINNING WENT, since this leaf carries neither.  Every
frame-level statement in this section must pin the real multiplication
with `j` and `hj`, because Counterexample 2 below — the exotic frame
`O = ℤ₁₃ × ℤ₁₃` acting by the two projections on the CM example — is a
rank-two frame satisfying every other hypothesis whose `charFrob` is a
SQUARE, refuting the charpoly equation outright.  That counterexample
cannot touch this leaf, because there is no frame here to be exotic:
`t w` acts through `m.act`, the real-multiplication datum of the abelian
scheme ITSELF.  `hj` exists only to transport `m.act` into an abstract
coefficient ring, so stating the relation over `m.act` directly is the
same pinning in its primitive form, and strictly stronger — the exotic
frame is excluded because it never enters.  Consistency check on that
same example: `A = E × E` with `E : y² = x³ − x`, the Frobenius of the
reduction is `F_E × F_E` and satisfies `F² − a_w F + N w = 0` with
`a_w ∈ ℤ ⊆ 𝒪_D`, so this leaf holds there while the exotic frame's own
coefficients are correctly refused by `IsTateFrameWeilCoeffs`.

Both statements below that DO quantify over a frame —
`weilCoeffs_fst_eq_of_frobTorsionEndo` and
`exists_finset_weilCoeffs_fst_eq_of_mult` — carry `j` and `hj` verbatim
through `IsTateFrameWeilCoeffs`, which is unchanged.

WHAT IS NOT ASSERTED.  Nothing about `|t w| ≤ 2√(N w)` — the
archimedean Riemann-hypothesis half is true and is needed by no consumer
in this tree.  Nothing at a place of bad reduction, which `bad`
absorbs.  Nothing about `I` dividing the residue characteristic of `w`.

AUDIT — A POINTWISE-IN-`w` VERSION OF THE OLD CUT IS FALSE, which is
why the deep content had to be moved to the torsion and not merely
re-quantified.  The tempting reformulation "∃ bad, ∀ w ∉ bad, ∀ frames,
`τ.charFrob w = X² - C (j (a w)) X + C (j (b w))`" is REFUTED: fix any
`w`, and take the frame at a residue characteristic `q` with `w ∣ q`.
That frame constrains nothing at `w` — `w` lies in its own exceptional
set — and the identity genuinely fails there, since the `q`-adic
representation is ramified at `w`.  No choice of a `w`-set repairs this,
because the offending `q` varies with the frame and the frame is
quantified after `bad`.  The leaf above escapes the refutation precisely
because the exclusion is stated as a hypothesis relating `I` to `w`.

MACHINERY THIS STILL NEEDS, unchanged from the ROUTE NOTE above: good
reduction of an abelian scheme at a finite place, the specialization
isomorphism on prime-to-`p` torsion, and the Frobenius endomorphism of
the reduction.  None of the three exists in this tree — re-checked
2026-07-27, see the subsection note above for the command.  **That is
still true and this statement is nonetheless PROVEN**, because the three
had only to be STATED for the cut, not proved: they are now the two
leaves above, `exists_finset_frobSpecialization_of_mult` (good reduction,
the reduction map, and the specialization injectivity) and
`exists_frobEndoCharEq_of_mult_finiteBase` (the Frobenius endomorphism's
characteristic equation, over a finite field).  So the obligation moved
rather than vanishing, and it moved into two subtrees with disjoint
literature — which is the whole gain.

UPDATE 2026-07-27: `exists_finset_frobSpecialization_of_mult` has since
been PROVEN in its turn, over `exists_finset_reductionMap_of_mult` plus
three proven statements of algebraic number theory and finite-field
theory; the Néron-model obligation now sits there, with the residue-field
arithmetic and the ideal bookkeeping stripped out of it.  The chain from
this theorem down to open leaves is therefore
`exists_finset_reductionMap_of_mult` and
`exists_frobEndoCharEq_of_mult_finiteBase`, and nothing else.

SUBSUMPTION — DONE 2026-07-27, and it is why this leaf now sits HERE.
This leaf subsumes what used to be the independent sibling trace leaf
`exists_finset_charFrob_coeff_one_mem_range_of_tateFrame_mult`, which is
now PROVEN over it (see that docstring for the argument, and for the one
extra input — the injective embedding `ι : O →+* ℚ̄_q` — that the
frame-ful sibling `weilCoeffs_fst_eq_of_frobTorsionEndo` does not need).
The declaration was moved above the trace leaf for exactly that reason;
nothing else about it changed.  Closing this statement therefore closed
TWO leaves, and the given-frame Weil cluster now has exactly ONE open
leaf left, the determinant leaf
`exists_finset_charFrob_coeff_zero_eq_absNorm_of_tateFrame_mult` —
plus, as of this cut, the two new frame-free ones above.

ROUTE STATUS, re-checked 2026-07-27 against the whole tree and STILL
CURRENT: the three missing inputs named above are still missing, and the
check is cheap to repeat — `grep -rl 'Neron\|NéronModel' Fermat/` finds
only `FreyCurve/MazurTorsion.lean`, `ModularCurve/X0.lean` and
`EllipticCurve/MordellWeil.lean`, all of them about elliptic curves over
`ℚ` rather than abelian schemes, and `~/cs/FLT` has no Néron model, no
abelian variety and no Frobenius endomorphism either.

**The correction this proof makes to the previous version of this
paragraph** is its last sentence, which read "no reformulation of the
statement shortens it".  That is right about the STATEMENT and wrong as
a conclusion about the CUT: the statement really cannot be weakened —
every remaining quantifier (`∃ t` before `∀ I`, `I.IsMaximal`, `q ∉ w`)
is shown load-bearing above — but it can be *decomposed*, because the
missing machinery only had to be written down, not proved.  The seam is
the reduction map at `w`, and the two halves it produces are stated in
the subsection note above together with the audit of what each carries. -/
theorem exists_frobTorsionEndo_of_mult
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (hdim : SmoothOfRelativeDimension (Module.finrank ℚ D) f) :
    ∃ (t : HeightOneSpectrum (NumberField.RingOfIntegers F) →
        NumberField.RingOfIntegers D)
      (bad : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F))),
      ∀ w ∉ bad, ∀ q : ℕ, q.Prime →
        ∀ I : Ideal (NumberField.RingOfIntegers D), I.IsMaximal →
          (q : NumberField.RingOfIntegers D) ∈ I →
          (q : NumberField.RingOfIntegers F) ∉ w.asIdeal →
          ∀ (n : ℕ) (y : GeomFibrePt f x), y ∈ (m.torsion x (I ^ n)).1 →
            ab.add
              (ab.galSMul x
                (Field.absoluteGaloisGroup.map (algebraMap F (w.adicCompletion F))
                  (Field.AbsoluteGaloisGroup.adicArithFrob w))
                (ab.galSMul x
                  (Field.absoluteGaloisGroup.map (algebraMap F (w.adicCompletion F))
                    (Field.AbsoluteGaloisGroup.adicArithFrob w)) y))
              (m.act ((Ideal.absNorm w.asIdeal : ℕ) : NumberField.RingOfIntegers D) y)
              = m.act (t w)
                  (ab.galSMul x
                    (Field.absoluteGaloisGroup.map (algebraMap F (w.adicCompletion F))
                      (Field.AbsoluteGaloisGroup.adicArithFrob w)) y) := by
  classical
  -- `A[J]` is closed under the group law and under the real
  -- multiplication: both are `mem_torsion_iff` plus one axiom of `Mult`.
  have hTadd : ∀ (J : Ideal (NumberField.RingOfIntegers D)) (u v : GeomFibrePt f x),
      u ∈ (m.torsion x J).1 → v ∈ (m.torsion x J).1 → ab.add u v ∈ (m.torsion x J).1 := by
    intro J u v hu hv
    rw [mem_torsion_iff] at hu hv ⊢
    intro a ha
    rw [m.act_addPt a u v, hu a ha, hv a ha]
    exact ab.zero_add _
  have hTact : ∀ (J : Ideal (NumberField.RingOfIntegers D))
      (c : NumberField.RingOfIntegers D) (u : GeomFibrePt f x),
      u ∈ (m.torsion x J).1 → m.act c u ∈ (m.torsion x J).1 := by
    intro J c u hu
    rw [mem_torsion_iff] at hu ⊢
    intro a ha
    rw [← m.act_mul a c u, mul_comm, m.act_mul c a u, hu a ha]
    letI : AddCommGroup (GeomFibrePt f x) := ab.addCommGroup (specAlgClos F ≫ x)
    letI : Module (NumberField.RingOfIntegers D) (GeomFibrePt f x) :=
      m.module (specAlgClos F ≫ x)
    exact smul_zero c
  obtain ⟨bad, hbad⟩ := exists_finset_frobSpecialization_of_mult m x hdim
  -- At a place of good reduction, transport the finite-field identity
  -- back along the reduction map.
  have key : ∀ w ∉ bad, ∃ t : NumberField.RingOfIntegers D,
      ∀ q : ℕ, q.Prime →
        ∀ I : Ideal (NumberField.RingOfIntegers D), I.IsMaximal →
          (q : NumberField.RingOfIntegers D) ∈ I →
          (q : NumberField.RingOfIntegers F) ∉ w.asIdeal →
          ∀ (n : ℕ) (y : GeomFibrePt f x), y ∈ (m.torsion x (I ^ n)).1 →
            ab.add
              (ab.galSMul x
                (Field.absoluteGaloisGroup.map (algebraMap F (w.adicCompletion F))
                  (Field.AbsoluteGaloisGroup.adicArithFrob w))
                (ab.galSMul x
                  (Field.absoluteGaloisGroup.map (algebraMap F (w.adicCompletion F))
                    (Field.AbsoluteGaloisGroup.adicArithFrob w)) y))
              (m.act ((Ideal.absNorm w.asIdeal : ℕ) : NumberField.RingOfIntegers D) y)
              = m.act t
                  (ab.galSMul x
                    (Field.absoluteGaloisGroup.map (algebraMap F (w.adicCompletion F))
                      (Field.AbsoluteGaloisGroup.adicArithFrob w)) y) := by
    intro w hw
    obtain ⟨A', f', ab', m', σ, e, hfin, hcard, hdim', hσ, hadd, hact, htors⟩ := hbad w hw
    obtain ⟨t, ht⟩ :=
      exists_frobEndoCharEq_of_mult_finiteBase hfin _ hcard ab' m' hdim' σ hσ
    refine ⟨t, ?_⟩
    intro q hq I hI hqI hqw n y hy
    obtain ⟨hinj, hint⟩ := htors q hq hqw I hI hqI n
    set Frob := Field.absoluteGaloisGroup.map (algebraMap F (w.adicCompletion F))
      (Field.AbsoluteGaloisGroup.adicArithFrob w) with hFrob
    have hy1 : ab.galSMul x Frob y ∈ (m.torsion x (I ^ n)).1 := (m.torsion x (I ^ n)).2 _ _ hy
    have hy2 : ab.galSMul x Frob (ab.galSMul x Frob y) ∈ (m.torsion x (I ^ n)).1 :=
      (m.torsion x (I ^ n)).2 _ _ hy1
    refine hinj (hTadd _ _ _ hy2 (hTact _ _ _ hy)) (hTact _ _ _ hy1) ?_
    calc e (ab.add (ab.galSMul x Frob (ab.galSMul x Frob y))
            (m.act ((Ideal.absNorm w.asIdeal : ℕ) : NumberField.RingOfIntegers D) y))
        = ab'.add (e (ab.galSMul x Frob (ab.galSMul x Frob y)))
            (e (m.act ((Ideal.absNorm w.asIdeal : ℕ) : NumberField.RingOfIntegers D) y)) :=
          hadd _ _
      _ = ab'.add (ab'.galSMul _ σ (ab'.galSMul _ σ (e y)))
            (m'.act ((Ideal.absNorm w.asIdeal : ℕ) : NumberField.RingOfIntegers D) (e y)) := by
          rw [hint _ hy1, hint _ hy, hact]
      _ = m'.act t (ab'.galSMul _ σ (e y)) := ht (e y)
      _ = m'.act t (e (ab.galSMul x Frob y)) := by rw [hint _ hy]
      _ = e (m.act t (ab.galSMul x Frob y)) := (hact _ _).symm
  refine ⟨fun w => if hw : w ∈ bad then 0 else (key w hw).choose, bad, ?_⟩
  intro w hw q hq I hI hqI hqw n y hy
  simpa only [dif_neg hw] using (key w hw).choose_spec q hq I hI hqI hqw n y hy

/-- **TRACE: the linear coefficient of the Frobenius characteristic
polynomial of a frame lies in `j(𝒪_D)`** (PROVEN 2026-07-27 over the
frame-free leaf `exists_frobTorsionEndo_of_mult` just above, the
determinant leaf, and `exists_algebraicClosureEmbedding_of_tateFrame_mult`
— it was previously an independent sorry leaf, and its arithmetic content
has now been ABSORBED by the frame-free one).

For all but finitely many `w`,

    (τ.charFrob w).coeff 1 ∈ Set.range j,

i.e. `- a_w`, the trace of Frobenius, is a GLOBAL algebraic integer of
`D` and not merely an `I`-adic one.  Classically `a_w` is the trace of
the Frobenius endomorphism of the reduction `A_w`, and its integrality
is Weil's.

HOW THE COLLAPSE WORKS, and why it needs one input the sibling
`weilCoeffs_fst_eq_of_frobTorsionEndo` does not.  The frame-free leaf,
transported through `(hφadd, hφbij, hφequiv, hj)` exactly as in that
sibling's step 1, gives the operator identity

    τ(σ_w)² + j(N w) = j(t w) · τ(σ_w)                                (∗)

on `Fin 2 → O`, WITHOUT assuming anything about `τ.charFrob w`.  Since
`τ.charFrob w` is monic of degree `2` it equals
`X² + C c₁ X + C c₀`, and Cayley–Hamilton (`LinearMap.aeval_self_charpoly`)
gives `τ(σ_w)² + c₁ τ(σ_w) + c₀ = 0`; the determinant leaf pins
`c₀ = (N w : O) = j (N w)`, so subtracting (∗) leaves
`(c₁ + j (t w)) · τ(σ_w) = 0`.  Feeding `τ(σ_w) v` back in and using (∗)
once more turns that into `(c₁ + j (t w)) · j(N w) = 0`.

Here the product CANNOT be pushed back along `j` first — `c₁` is not yet
known to be in the image of `j`; that is precisely what is being proven —
so the zero-divisor step has to happen in `O` itself, and it needs `O` to
embed in a field.  That is what
`exists_algebraicClosureEmbedding_of_tateFrame_mult` supplies: an
INJECTIVE `ι : O →+* ℚ̄_q` with `ι ∘ j = ψ ∘ (𝒪_D ↪ D)`, so
`ι (j (N w)) = ψ (N w) ≠ 0` and hence `c₁ = - j (t w) = j (- t w)`.
(The sibling avoids this input because there the difference is already
of the form `j (a w - t w)`; the asymmetry is real and is the reason
that leaf's docstring says no `IsDomain O` is needed while this one does
consume the embedding.)

Note what is NOT asserted: `b_w = N w` is the separate determinant leaf
above, and the archimedean bound `|a_w| ≤ 2√(N w)` — the Riemann
hypothesis half — is true but is needed by no consumer in this tree and
is deliberately not stated.

`hdim` is what makes the rank two rather than `2d`; `hπ`, `hπ2` pin `π`
as a uniformizer so that `TatePt` is the `I`-adic Tate module; `hj` is
what makes the coefficient `𝒪_D`-rational at all — without it the
frame's coefficient ring need not even contain a copy of `𝒪_D`. -/
theorem exists_finset_charFrob_coeff_one_mem_range_of_tateFrame_mult
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (hdim : SmoothOfRelativeDimension (Module.finrank ℚ D) f)
    (q : ℕ) (hq : Fact q.Prime)
    (I : Ideal (NumberField.RingOfIntegers D)) (hI : I.IsMaximal)
    (hqI : (q : NumberField.RingOfIntegers D) ∈ I)
    (π : NumberField.RingOfIntegers D) (hπ : π ∈ I) (hπ2 : π ∉ I ^ 2)
    (O : Type u) (iCR : CommRing O) (iTS : TopologicalSpace O) (iTR : IsTopologicalRing O)
    (τ : GaloisRep F O (Fin 2 → O)) (φ : (Fin 2 → O) → TatePt m x I π)
    (j : NumberField.RingOfIntegers D →+* O)
    (hφadd : ∀ (u u' : Fin 2 → O) (n : ℕ),
      (φ (u + u')).1 n = ab.add ((φ u).1 n) ((φ u').1 n))
    (hφbij : Function.Bijective φ)
    (hφequiv : ∀ (σ : Field.absoluteGaloisGroup F) (u : Fin 2 → O) (n : ℕ),
      (φ (τ σ u)).1 n = ab.galSMul x σ ((φ u).1 n))
    (hj : ∀ (c : NumberField.RingOfIntegers D) (u : Fin 2 → O) (n : ℕ),
      (φ (j c • u)).1 n = m.act c ((φ u).1 n)) :
    ∃ bad : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)),
      ∀ w ∉ bad, (τ.charFrob w).coeff 1 ∈ Set.range j := by
  classical
  -- The trivial coefficient ring is degenerate (`natDegree` is `0`, not `2`) and is
  -- discharged directly: `Set.range j` is everything there.
  rcases subsingleton_or_nontrivial O with hO | hO
  · exact ⟨∅, fun w _ => ⟨0, Subsingleton.elim _ _⟩⟩
  obtain ⟨t, badt, ht⟩ := exists_frobTorsionEndo_of_mult m x hdim
  obtain ⟨badd, hbadd⟩ :=
    exists_finset_charFrob_coeff_zero_eq_absNorm_of_tateFrame_mult m x hdim q hq I hI hqI
      π hπ hπ2 O iCR iTS iTR τ φ j hφadd hφbij hφequiv hj
  obtain ⟨ψ, ι, hιinj, hcomp⟩ :=
    exists_algebraicClosureEmbedding_of_tateFrame_mult m x hdim q hq I hI hqI π hπ hπ2 O
      iCR iTS iTR τ φ j hφadd hφbij hφequiv hj
  obtain ⟨badq, hbadq⟩ := exists_finset_forall_natCast_notMem (F := F) q hq.out.ne_zero
  refine ⟨badt ∪ badd ∪ badq, fun w hw => ?_⟩
  have hwt : w ∉ badt := fun hc => hw (by simp [hc])
  have hwd : w ∉ badd := fun hc => hw (by simp [hc])
  have hwq : w ∉ badq := fun hc => hw (by simp [hc])
  set σw : Field.absoluteGaloisGroup F :=
    Field.absoluteGaloisGroup.map (algebraMap F (w.adicCompletion F))
      (Field.AbsoluteGaloisGroup.adicArithFrob w)
  set Nw : NumberField.RingOfIntegers D :=
    ((Ideal.absNorm w.asIdeal : ℕ) : NumberField.RingOfIntegers D) with hNwdef
  -- Step 1: transport the frame-free torsion relation through the frame.
  have hstar : ∀ u : Fin 2 → O,
      τ σw (τ σw u) + (j Nw) • u = (j (t w)) • (τ σw u) := by
    intro u
    refine hφbij.injective (Subtype.ext (funext fun n => ?_))
    rw [hφadd, hj, hj, hφequiv, hφequiv]
    exact ht w hwt q hq.out I hI hqI (hbadq w hwq) n _ ((φ u).2.1 n)
  -- Step 2: a monic quadratic is determined by its two lower coefficients, and
  -- Cayley–Hamilton turns that shape into a relation on `Fin 2 → O`.
  have hshape : ∀ P : Polynomial O, P.Monic → P.natDegree = 2 →
      P = Polynomial.X ^ 2 + Polynomial.C (P.coeff 1) * Polynomial.X
        + Polynomial.C (P.coeff 0) := by
    intro P hm hd
    refine Polynomial.ext fun n => ?_
    match n with
    | 0 => simp
    | 1 => simp
    | 2 =>
      have h2 : P.coeff 2 = 1 := by rw [← hd]; exact hm.coeff_natDegree
      simp [h2]
    | (k + 3) =>
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      simp
  have hmonic : (τ.charFrob w).Monic := by
    show ((τ.toLocal w (Field.AbsoluteGaloisGroup.adicArithFrob w)).charpoly).Monic
    exact LinearMap.charpoly_monic _
  have hdeg : (τ.charFrob w).natDegree = 2 := by
    show ((τ.toLocal w (Field.AbsoluteGaloisGroup.adicArithFrob w)).charpoly).natDegree = 2
    rw [LinearMap.charpoly_natDegree]
    exact Module.finrank_fin_fun O
  have hc0 : (τ.charFrob w).coeff 0 = j Nw := by
    rw [hbadd w hwd, hNwdef, map_natCast]
  obtain ⟨c1, hc1⟩ : ∃ c1 : O, (τ.charFrob w).coeff 1 = c1 := ⟨_, rfl⟩
  have hchar : τ.charFrob w
      = Polynomial.X ^ 2 + Polynomial.C c1 * Polynomial.X + Polynomial.C (j Nw) := by
    rw [← hc1, ← hc0]
    exact hshape _ hmonic hdeg
  set M := τ.toLocal w (Field.AbsoluteGaloisGroup.adicArithFrob w)
  have hMσ : ∀ u, M u = τ σw u := fun _ => rfl
  have hCH : (Polynomial.aeval M) (τ.charFrob w) = 0 :=
    LinearMap.aeval_self_charpoly M
  rw [hchar] at hCH
  have hCHu : ∀ u : Fin 2 → O,
      τ σw (τ σw u) + c1 • (τ σw u) + (j Nw) • u = 0 := by
    intro u
    have := congrArg (fun e : Module.End O (Fin 2 → O) => e u) hCH
    simpa [Module.End.mul_apply, pow_two, Module.algebraMap_end_apply, hMσ] using this
  -- Step 3: the two quadratic relations differ only in their linear term.
  have hc : ∀ u : Fin 2 → O, (c1 + j (t w)) • (τ σw u) = 0 := by
    intro u
    have h2 := hCHu u
    have hsq : τ σw (τ σw u) = (j (t w)) • (τ σw u) - (j Nw) • u := by
      rw [← hstar u]; abel
    rw [hsq] at h2
    rw [add_smul]
    linear_combination (norm := abel) h2
  -- Step 4: feed `τ(σ_w) v` back in to push the difference onto `N w`.
  have hkey : ∀ v : Fin 2 → O, ((c1 + j (t w)) * j Nw) • v = 0 := by
    intro v
    have h3 := hc (τ σw v)
    have h5 : τ σw (τ σw v) = (j (t w)) • (τ σw v) - (j Nw) • v := by
      rw [← hstar v]; abel
    rw [h5, smul_sub, smul_comm (c1 + j (t w)) (j (t w)), hc, smul_zero, zero_sub,
      neg_eq_zero, ← mul_smul] at h3
    exact h3
  have hzero : (c1 + j (t w)) * j Nw = 0 := by
    have := congrFun (hkey (fun _ : Fin 2 => (1 : O))) 0
    simpa using this
  -- Step 5: `N w ≠ 0` and `O` embeds in a field, so the difference vanishes.
  have hNne : Nw ≠ 0 := by
    rw [hNwdef, Ne, Nat.cast_eq_zero]
    exact fun hc0' => w.ne_bot (Ideal.absNorm_eq_zero_iff.mp hc0')
  have hjNne : ι (j Nw) ≠ 0 := by
    rw [hcomp]
    have h1 : algebraMap (NumberField.RingOfIntegers D) D Nw ≠ 0 := fun hcon =>
      hNne (FaithfulSMul.algebraMap_injective (NumberField.RingOfIntegers D) D
        (by rw [hcon, map_zero]))
    exact fun hcon => h1 (ψ.injective (by rw [hcon, map_zero]))
  have hczero : c1 + j (t w) = 0 := by
    refine hιinj ?_
    rw [map_zero]
    have h6 := congrArg ι hzero
    rw [map_mul, map_zero] at h6
    exact (mul_eq_zero.mp h6).resolve_right hjNne
  refine ⟨-(t w), ?_⟩
  rw [hc1, map_neg]
  linear_combination -hczero

set_option backward.isDefEq.respectTransparency false in
/-- **RATIONALITY: the Frobenius characteristic polynomial of ONE frame
has its coefficients in `j(𝒪_D)`** (PROVEN 2026-07-27 over the
determinant and trace leaves just above, plus the polynomial-shape glue
proven inline — Weil's integrality for abelian varieties over finite
fields, in the Hilbert–Blumenthal normalization of Shimura /
Taylor 2002 §1).

Fix a frame `(O, τ, φ, j)` of `TatePt m x I π` which remembers the real
multiplication.  Then for all but finitely many places `w` of `F`,

    τ.charFrob w = X² - C (j (a w)) · X + C (j (b w))

for some `a, b : w ↦ 𝒪_D`.  This is the target statement with `a`, `b`
and `bad` moved INSIDE the frame quantifiers, so it carries no
independence-of-`I` content whatever; that is
`exists_finset_weilCoeffs_eq_of_mult`'s job.

HOW IT IS PROVEN, AND WHAT IS LEFT.  Three things are needed and they
are now separated:

* *Shape.*  `τ.charFrob w` is the characteristic polynomial of an
  endomorphism of `O²`, hence MONIC of degree `2` whatever the frame, so
  it equals `X² + C (coeff 1) · X + C (coeff 0)`.  That is pure
  polynomial algebra and is proven inline below (`hshape`, `hmonic`,
  `hdeg`), on top of `LinearMap.charpoly_monic`,
  `LinearMap.charpoly_natDegree` and `Module.finrank_fin_fun`.  The
  degenerate case `O` trivial is discharged first, by
  `Subsingleton.elim` on coefficients — `natDegree` is `0`, not `2`,
  there, and every polynomial equation holds anyway.
* *The constant coefficient* is `N w`, hence `j` of a global integer:
  the determinant leaf
  `exists_finset_charFrob_coeff_zero_eq_absNorm_of_tateFrame_mult`.
* *The linear coefficient* lies in `j(𝒪_D)`: the trace leaf
  `exists_finset_charFrob_coeff_one_mem_range_of_tateFrame_mult`.

`a w` and `b w` are then read off by `choose`, with the junk value `0`
inside the union of the two exceptional sets, where nothing is claimed.
Only the trace leaf carries arithmetic that this tree does not already
have in some form; `b w` comes out as `N w` on the nose, which is what
makes the `b`-half of the sibling independence leaf free.

Classically `a w` is the trace and `b w` the norm of the Frobenius
endomorphism of the reduction `A_w`, and integrality is Weil's; the
archimedean bound `|a w| ≤ 2√N(w)` is true but is NOT needed by any
consumer in this tree and is deliberately not asserted, so no prover
here need carry the Riemann-hypothesis half.

`hdim` is what makes the rank two rather than `2d`; `hπ`, `hπ2` pin `π`
as a uniformizer so that `TatePt` is the `I`-adic Tate module; `hj` is
what makes the coefficients `𝒪_D`-rational at all — without it the
frame's coefficient ring need not even contain a copy of `𝒪_D`. -/
theorem exists_weilCoeffs_of_tateFrame_mult
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (hdim : SmoothOfRelativeDimension (Module.finrank ℚ D) f)
    (q : ℕ) (hq : Fact q.Prime)
    (I : Ideal (NumberField.RingOfIntegers D)) (hI : I.IsMaximal)
    (hqI : (q : NumberField.RingOfIntegers D) ∈ I)
    (π : NumberField.RingOfIntegers D) (hπ : π ∈ I) (hπ2 : π ∉ I ^ 2)
    (O : Type u) (iCR : CommRing O) (iTS : TopologicalSpace O) (iTR : IsTopologicalRing O)
    (τ : GaloisRep F O (Fin 2 → O)) (φ : (Fin 2 → O) → TatePt m x I π)
    (j : NumberField.RingOfIntegers D →+* O)
    (hφadd : ∀ (u u' : Fin 2 → O) (n : ℕ),
      (φ (u + u')).1 n = ab.add ((φ u).1 n) ((φ u').1 n))
    (hφbij : Function.Bijective φ)
    (hφequiv : ∀ (σ : Field.absoluteGaloisGroup F) (u : Fin 2 → O) (n : ℕ),
      (φ (τ σ u)).1 n = ab.galSMul x σ ((φ u).1 n))
    (hj : ∀ (c : NumberField.RingOfIntegers D) (u : Fin 2 → O) (n : ℕ),
      (φ (j c • u)).1 n = m.act c ((φ u).1 n)) :
    ∃ (a b : HeightOneSpectrum (NumberField.RingOfIntegers F) →
        NumberField.RingOfIntegers D)
      (bad : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F))),
      ∀ w ∉ bad,
        τ.charFrob w =
          Polynomial.X ^ 2 - Polynomial.C (j (a w)) * Polynomial.X +
            Polynomial.C (j (b w)) := by
  classical
  -- The trivial coefficient ring is degenerate (`natDegree` is `0`, not `2`) and
  -- is discharged directly: every polynomial equation over it holds.
  rcases subsingleton_or_nontrivial O with hO | hO
  · exact ⟨0, 0, ∅, fun w _ => Polynomial.ext fun n => Subsingleton.elim _ _⟩
  obtain ⟨bad₀, hbad₀⟩ :=
    exists_finset_charFrob_coeff_zero_eq_absNorm_of_tateFrame_mult m x hdim q hq I hI hqI
      π hπ hπ2 O iCR iTS iTR τ φ j hφadd hφbij hφequiv hj
  obtain ⟨bad₁, hbad₁⟩ :=
    exists_finset_charFrob_coeff_one_mem_range_of_tateFrame_mult m x hdim q hq I hI hqI
      π hπ hπ2 O iCR iTS iTR τ φ j hφadd hφbij hφequiv hj
  -- A monic quadratic is determined by its two lower coefficients.
  have hshape : ∀ P : Polynomial O, P.Monic → P.natDegree = 2 →
      P = Polynomial.X ^ 2 + Polynomial.C (P.coeff 1) * Polynomial.X
        + Polynomial.C (P.coeff 0) := by
    intro P hm hd
    refine Polynomial.ext fun n => ?_
    match n with
    | 0 => simp
    | 1 => simp
    | 2 =>
      have h2 : P.coeff 2 = 1 := by rw [← hd]; exact hm.coeff_natDegree
      simp [h2]
    | (k + 3) =>
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      simp
  have hmonic : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      (τ.charFrob w).Monic := by
    intro w
    show ((τ.toLocal w (Field.AbsoluteGaloisGroup.adicArithFrob w)).charpoly).Monic
    exact LinearMap.charpoly_monic _
  have hdeg : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      (τ.charFrob w).natDegree = 2 := by
    intro w
    show ((τ.toLocal w (Field.AbsoluteGaloisGroup.adicArithFrob w)).charpoly).natDegree = 2
    rw [LinearMap.charpoly_natDegree]
    exact Module.finrank_fin_fun O
  -- Read off `(a w, b w)` place by place; junk inside the exceptional set.
  have key : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      ∃ ab' : NumberField.RingOfIntegers D × NumberField.RingOfIntegers D,
        w ∉ bad₀ ∪ bad₁ →
          τ.charFrob w = Polynomial.X ^ 2 - Polynomial.C (j ab'.1) * Polynomial.X
            + Polynomial.C (j ab'.2) := by
    intro w
    by_cases hw : w ∈ bad₀ ∪ bad₁
    · exact ⟨(0, 0), fun h => absurd hw h⟩
    have hw₀ : w ∉ bad₀ := fun h => hw (Finset.mem_union_left _ h)
    have hw₁ : w ∉ bad₁ := fun h => hw (Finset.mem_union_right _ h)
    obtain ⟨α, hα⟩ := hbad₁ w hw₁
    refine ⟨(-α, ((Ideal.absNorm w.asIdeal : ℕ) : NumberField.RingOfIntegers D)),
      fun _ => ?_⟩
    have h0 : j ((Ideal.absNorm w.asIdeal : ℕ) : NumberField.RingOfIntegers D)
        = (τ.charFrob w).coeff 0 := by
      rw [map_natCast, hbad₀ w hw₀]
    have h1 : j (-α) = -(τ.charFrob w).coeff 1 := by rw [map_neg, hα]
    refine (hshape (τ.charFrob w) (hmonic w) (hdeg w)).trans ?_
    simp only [h0, h1, Polynomial.C_neg]
    ring
  choose ab' hab' using key
  exact ⟨fun w => (ab' w).1, fun w => (ab' w).2, bad₀ ∪ bad₁, fun w hw => hab' w hw⟩

/-- **A FRAME'S TRACE IS THE FRAME-FREE ONE** (PROVEN 2026-07-27 over
`exists_frobTorsionEndo_of_mult`, the determinant leaf and
`injective_of_tateFrame_mult`): if `(a, b)` are the Weil coefficients of
SOME frame, then `a w = t w` off a finite set, where `t` is the family
supplied by the frame-free Cayley–Hamilton relation.

This is the whole algebraic half of independence, and it contains no
arithmetic at all — every arithmetic input is a hypothesis.  Five steps:

1. *Transport.*  The frame `(O, τ, φ, j)` satisfies `hφadd`, `hφequiv`
   and `hj`, so applying the torsion relation at `y = (φ u).1 n` for
   every `n` and using injectivity of `φ` turns it into an identity in
   `Fin 2 → O`:

       τ(σ_w)²(u) + j(N w) · u = j(t w) · τ(σ_w)(u).

   Note this is where `hj` earns its keep: without it there is no map
   `𝒪_D → O` along which the relation can be read, and the statement of
   the leaf would not typecheck, let alone be true.
2. *Cayley–Hamilton.*  `τ.charFrob w` is by definition the characteristic
   polynomial of `τ(σ_w)`, so `LinearMap.aeval_self_charpoly` gives
   `τ(σ_w)²(u) - j(a w) · τ(σ_w)(u) + j(b w) · u = 0` once the frame's
   own polynomial identity has been substituted.
3. *The determinant leaf* pins `b w = (N w : 𝒪_D)` — via
   `injective_of_tateFrame_mult`, exactly as in
   `exists_finset_weilCoeffs_eq_of_mult` below.
4. Subtracting 2 from 1 kills the quadratic and the constant terms
   together, leaving `j (a w - t w) · τ(σ_w)(u) = 0` for every `u`.
5. Feeding `τ(σ_w)(v)` back in for `u` and using 2 once more turns that
   into `j ((a w - t w) * N w) = 0`; `j` is injective, `𝒪_D` is a
   domain, and `N w ≠ 0`, so `a w = t w`.

Step 5 is why no `IsDomain O` hypothesis is needed and why the sibling
`exists_algebraicClosureEmbedding_of_tateFrame_mult` is not consumed
here: the product is pushed back into `𝒪_D` along `j` BEFORE it is
factored, so the zero-divisor argument happens in a ring already known
to be a domain.  The exceptional set is the union of the frame's own,
the determinant leaf's, the torsion relation's, and the (finite, by
`exists_finset_forall_natCast_notMem`) set of places above the frame's
residue characteristic `q`. -/
theorem weilCoeffs_fst_eq_of_frobTorsionEndo
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (hdim : SmoothOfRelativeDimension (Module.finrank ℚ D) f)
    (t : HeightOneSpectrum (NumberField.RingOfIntegers F) →
      NumberField.RingOfIntegers D)
    (badt : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (ht : ∀ w ∉ badt, ∀ q : ℕ, q.Prime →
        ∀ I : Ideal (NumberField.RingOfIntegers D), I.IsMaximal →
          (q : NumberField.RingOfIntegers D) ∈ I →
          (q : NumberField.RingOfIntegers F) ∉ w.asIdeal →
          ∀ (n : ℕ) (y : GeomFibrePt f x), y ∈ (m.torsion x (I ^ n)).1 →
            ab.add
              (ab.galSMul x
                (Field.absoluteGaloisGroup.map (algebraMap F (w.adicCompletion F))
                  (Field.AbsoluteGaloisGroup.adicArithFrob w))
                (ab.galSMul x
                  (Field.absoluteGaloisGroup.map (algebraMap F (w.adicCompletion F))
                    (Field.AbsoluteGaloisGroup.adicArithFrob w)) y))
              (m.act ((Ideal.absNorm w.asIdeal : ℕ) : NumberField.RingOfIntegers D) y)
              = m.act (t w)
                  (ab.galSMul x
                    (Field.absoluteGaloisGroup.map (algebraMap F (w.adicCompletion F))
                      (Field.AbsoluteGaloisGroup.adicArithFrob w)) y))
    (a b : HeightOneSpectrum (NumberField.RingOfIntegers F) →
      NumberField.RingOfIntegers D)
    (h : IsTateFrameWeilCoeffs m x a b) :
    ∃ bad : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)),
      ∀ w ∉ bad, a w = t w := by
  classical
  obtain ⟨q, hq, I, hI, hqI, π, hπ, hπ2, O, iCR, iTS, iTR, τ, φ, j,
    hφadd, hφbij, hφequiv, hj, badf, hbadf⟩ := id h
  have hjinj := injective_of_tateFrame_mult m x hdim q hq I hI hqI π hπ hπ2 O iCR iTS iTR
    τ φ j hφadd hφbij hφequiv hj
  obtain ⟨badd, hbadd⟩ :=
    exists_finset_charFrob_coeff_zero_eq_absNorm_of_tateFrame_mult m x hdim q hq I hI hqI
      π hπ hπ2 O iCR iTS iTR τ φ j hφadd hφbij hφequiv hj
  obtain ⟨badq, hbadq⟩ := exists_finset_forall_natCast_notMem (F := F) q hq.out.ne_zero
  refine ⟨badt ∪ badf ∪ badd ∪ badq, fun w hw => ?_⟩
  have hwt : w ∉ badt := fun hc => hw (by simp [hc])
  have hwf : w ∉ badf := fun hc => hw (by simp [hc])
  have hwd : w ∉ badd := fun hc => hw (by simp [hc])
  have hwq : w ∉ badq := fun hc => hw (by simp [hc])
  set σw : Field.absoluteGaloisGroup F :=
    Field.absoluteGaloisGroup.map (algebraMap F (w.adicCompletion F))
      (Field.AbsoluteGaloisGroup.adicArithFrob w)
  set Nw : NumberField.RingOfIntegers D :=
    ((Ideal.absNorm w.asIdeal : ℕ) : NumberField.RingOfIntegers D) with hNwdef
  -- Step 1: transport the torsion relation through the frame.
  have hstar : ∀ u : Fin 2 → O,
      τ σw (τ σw u) + (j Nw) • u = (j (t w)) • (τ σw u) := by
    intro u
    refine hφbij.injective (Subtype.ext (funext fun n => ?_))
    rw [hφadd, hj, hj, hφequiv, hφequiv]
    exact ht w hwt q hq.out I hI hqI (hbadq w hwq) n _ ((φ u).2.1 n)
  -- Step 2: Cayley–Hamilton for the frame's own characteristic polynomial.
  have hchar := hbadf w hwf
  set M := τ.toLocal w (Field.AbsoluteGaloisGroup.adicArithFrob w)
  have hMσ : ∀ u, M u = τ σw u := fun _ => rfl
  have hCH : (Polynomial.aeval M) (τ.charFrob w) = 0 :=
    LinearMap.aeval_self_charpoly M
  rw [hchar] at hCH
  have hCHu : ∀ u : Fin 2 → O,
      τ σw (τ σw u) - (j (a w)) • (τ σw u) + (j (b w)) • u = 0 := by
    intro u
    have := congrArg (fun e : Module.End O (Fin 2 → O) => e u) hCH
    simpa [Module.End.mul_apply, pow_two, Module.algebraMap_end_apply, hMσ] using this
  -- Step 3: the determinant leaf pins `b w = N w`.
  have e0 : (τ.charFrob w).coeff 0 = j (b w) := by rw [hchar]; simp
  have hbw : b w = Nw := hjinj (by rw [hNwdef, map_natCast, ← e0, hbadd w hwd])
  -- Step 4: subtracting the two relations kills both ends.
  have hc : ∀ u : Fin 2 → O, (j (a w - t w)) • (τ σw u) = 0 := by
    intro u
    have h1 := hstar u
    have h2 := hCHu u
    rw [hbw] at h2
    rw [map_sub]
    have hsq : τ σw (τ σw u) = (j (t w)) • (τ σw u) - (j Nw) • u := by
      rw [← h1]; abel
    rw [hsq] at h2
    rw [sub_smul]
    linear_combination (norm := abel) -h2
  -- Step 5: push the product back into `𝒪_D` along `j` and factor there.
  have hkey : ∀ v : Fin 2 → O, (j (a w - t w) * j Nw) • v = 0 := by
    intro v
    have h3 := hc (τ σw v)
    have h4 := hCHu v
    rw [hbw] at h4
    have h5 : τ σw (τ σw v) = (j (a w)) • (τ σw v) - (j Nw) • v := by
      rw [← sub_eq_zero, ← h4]; abel
    rw [h5, smul_sub, smul_comm (j (a w - t w)) (j (a w)), hc, smul_zero, zero_sub,
      neg_eq_zero, ← mul_smul] at h3
    exact h3
  have hzero : j (a w - t w) * j Nw = 0 := by
    have := congrFun (hkey (fun _ : Fin 2 => (1 : O))) 0
    simpa using this
  have hmul : (a w - t w) * Nw = 0 := hjinj (by rw [map_mul, hzero, map_zero])
  have hNne : Nw ≠ 0 := by
    rw [hNwdef, Ne, Nat.cast_eq_zero]
    exact fun hc0 => w.ne_bot (Ideal.absNorm_eq_zero_iff.mp hc0)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hNne)

/-- **INDEPENDENCE OF THE TRACE: two frames give the same `a` at all
but finitely many places** (PROVEN 2026-07-27 over the frame-free
Cayley–Hamilton leaf `exists_frobTorsionEndo_of_mult` and the algebraic
glue `weilCoeffs_fst_eq_of_frobTorsionEndo`; it was previously the last
sorried place in the chain where two residue characteristics are
compared — after the determinant leaf
`exists_finset_charFrob_coeff_zero_eq_absNorm_of_tateFrame_mult` this is
ALL that is left of the compatible-system content of
`exists_intWeilPolynomial_of_mult`).

The `b`-half of the sibling `exists_finset_weilCoeffs_eq_of_mult` is no
longer open: the determinant leaf pins `j (b w) = (N w : O)` in EVERY
frame, and `injective_of_tateFrame_mult` pulls that back to
`b w = (N w : 𝒪_D)`, a value with no frame in it.  The trace admits no
such shortcut — there is no character whose value it is — so it is
exactly the surviving compatible-system statement.

The exceptional set is existential and that is deliberate: `a` and `a'`
are constrained by their frames only outside those frames' own bad sets
(which contain, in particular, the places over `q` and over `q'`, and
those cannot be bounded uniformly in the residue characteristic), and on
those sets they are arbitrary.  So no pointwise-in-`w` version of this
statement is true, and none is needed — the assembly unions finite sets.

HOW IT IS PROVEN, AND WHERE THE DEEP INPUT WENT.  The ROUTE NOTE above
identified the structurally right argument — both sides compute the
trace of the Frobenius ENDOMORPHISM of `A_w`, an identity in which no
residue characteristic occurs — and recorded that it was unavailable
because this tree has no reduction of an abelian scheme.  The cut taken
here keeps that argument and moves ONLY its irreducible half into a
statement that mentions no frame at all:

* `exists_frobTorsionEndo_of_mult` (the surviving deep leaf) says that
  outside a finite set of places there is ONE `t w ∈ 𝒪_D` with
  `Frob_w² y + (N w) y = t w · Frob_w y` for every `Iⁿ`-torsion point `y`
  of the fibre, for every maximal `I` of residue characteristic
  different from `w`'s.  The `∃ t, ∀ I` order IS the
  independence-of-`λ` content; the statement is Weil's characteristic
  equation for the Frobenius endomorphism, read on torsion points.
* `weilCoeffs_fst_eq_of_frobTorsionEndo` (proven) transports that
  relation through an ARBITRARY frame and shows the frame's own `a w`
  equals `t w`.  Everything there is linear algebra over `O` plus the
  determinant leaf and injectivity of `j`.

The two frames of this statement then agree because each separately
agrees with the same frame-free `t`, and the exceptional set is the
union of the two.  So the comparison of two residue characteristics is
no longer performed anywhere: it has been replaced by two independent
comparisons against a common value, which is what a compatible system
is.

Note in particular that no reduction machinery was needed for the
GLUE — only for `exists_frobTorsionEndo_of_mult` itself, where the
survey in the ROUTE NOTE above still applies verbatim. -/
theorem exists_finset_weilCoeffs_fst_eq_of_mult
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (hdim : SmoothOfRelativeDimension (Module.finrank ℚ D) f)
    (a b a' b' : HeightOneSpectrum (NumberField.RingOfIntegers F) →
      NumberField.RingOfIntegers D)
    (h : IsTateFrameWeilCoeffs m x a b) (h' : IsTateFrameWeilCoeffs m x a' b') :
    ∃ bad : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)),
      ∀ w ∉ bad, a w = a' w := by
  classical
  obtain ⟨t, badt, ht⟩ := exists_frobTorsionEndo_of_mult m x hdim
  obtain ⟨bad1, h1⟩ := weilCoeffs_fst_eq_of_frobTorsionEndo m x hdim t badt ht a b h
  obtain ⟨bad2, h2⟩ := weilCoeffs_fst_eq_of_frobTorsionEndo m x hdim t badt ht a' b' h'
  exact ⟨bad1 ∪ bad2, fun w hw =>
    (h1 w fun hc => hw (Finset.mem_union_left _ hc)).trans
      (h2 w fun hc => hw (Finset.mem_union_right _ hc)).symm⟩

/-- **INDEPENDENCE: two frames give the SAME `𝒪_D`-coefficients at all
but finitely many places** (PROVEN 2026-07-27 by splitting off the `b`
half — its compatible-system content now lives entirely in the sibling
`exists_finset_weilCoeffs_fst_eq_of_mult` just above, which is the trace
half).

If `(a, b)` are the Weil coefficients of some frame and `(a', b')` those
of some other frame — the two frames unrelated, at possibly DIFFERENT
rational primes `q`, `q'` and different maximal ideals `I`, `I'` — then
`a w = a' w` and `b w = b' w` for all but finitely many `w`.

Why this is the right way to say it, and why it is not the target again.
The two characteristic polynomials live over two DIFFERENT coefficient
rings `O = 𝒪_{D,I}` and `O' = 𝒪_{D,I'}` and cannot be compared as
polynomials at all; the comparison is possible only after each has been
recognised as coming from a family of GLOBAL integers of `D`, which is
what `IsTateFrameWeilCoeffs` records.  So this leaf is exactly the
assertion that the `I`-adic and `I'`-adic Tate modules are two members of
ONE compatible system, with nothing else attached.

The exceptional set is existential and that is deliberate: `a` and `b`
are constrained by their frames only outside those frames' own bad sets,
and on those sets they are arbitrary, so no pointwise statement is
available and none is needed — the assembly unions finite sets.

HOW IT IS PROVEN, AND WHAT MOVED.  The two halves are no longer
symmetric:

* The `b` half is now CLOSED here.  `IsTateFrameWeilCoeffs` hands over
  each frame in full, so the determinant leaf
  `exists_finset_charFrob_coeff_zero_eq_absNorm_of_tateFrame_mult`
  applies to each of them and gives `j (b w) = (N w : O)` and
  `j' (b' w) = (N w : O')` off finite sets; `injective_of_tateFrame_mult`
  — itself proven over the sibling
  `exists_algebraicClosureEmbedding_of_tateFrame_mult` — turns each of
  those into `b w = (N w : 𝒪_D) = b' w`, a value in which no frame
  appears.  That is the Weil pairing doing the work, exactly as it does
  in the DETERMINANT CLAUSE of `exists_tateFrame_of_levelStructure`.
* The `a` half is `exists_finset_weilCoeffs_fst_eq_of_mult` above and
  is the surviving deep leaf.

So the compatible-system content of the chain is now localized in ONE
statement about traces, and the norm half is a corollary of a pairing
identity rather than of independence of `λ`. -/
theorem exists_finset_weilCoeffs_eq_of_mult
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (hdim : SmoothOfRelativeDimension (Module.finrank ℚ D) f)
    (a b a' b' : HeightOneSpectrum (NumberField.RingOfIntegers F) →
      NumberField.RingOfIntegers D)
    (h : IsTateFrameWeilCoeffs m x a b) (h' : IsTateFrameWeilCoeffs m x a' b') :
    ∃ bad : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)),
      ∀ w ∉ bad, a w = a' w ∧ b w = b' w := by
  classical
  obtain ⟨bada, hbada⟩ := exists_finset_weilCoeffs_fst_eq_of_mult m x hdim a b a' b' h h'
  obtain ⟨badb, hbadb⟩ :
      ∃ bad : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)),
        ∀ w ∉ bad, b w = b' w := by
    obtain ⟨q, hq, I, hI, hqI, π, hπ, hπ2, O, iCR, iTS, iTR, τ, φ, jj,
      hφadd, hφbij, hφequiv, hj, bad1, hbad1⟩ := id h
    obtain ⟨q', hq', I', hI', hqI', π', hπ', hπ2', O', iCR', iTS', iTR', τ', φ', jj',
      hφadd', hφbij', hφequiv', hj', bad2, hbad2⟩ := id h'
    obtain ⟨badd, hbadd⟩ :=
      exists_finset_charFrob_coeff_zero_eq_absNorm_of_tateFrame_mult m x hdim q hq I hI hqI
        π hπ hπ2 O iCR iTS iTR τ φ jj hφadd hφbij hφequiv hj
    obtain ⟨badd', hbadd'⟩ :=
      exists_finset_charFrob_coeff_zero_eq_absNorm_of_tateFrame_mult m x hdim q' hq' I' hI'
        hqI' π' hπ' hπ2' O' iCR' iTS' iTR' τ' φ' jj' hφadd' hφbij' hφequiv' hj'
    have hinj := injective_of_tateFrame_mult m x hdim q hq I hI hqI π hπ hπ2 O iCR iTS iTR
      τ φ jj hφadd hφbij hφequiv hj
    have hinj' := injective_of_tateFrame_mult m x hdim q' hq' I' hI' hqI' π' hπ' hπ2' O'
      iCR' iTS' iTR' τ' φ' jj' hφadd' hφbij' hφequiv' hj'
    refine ⟨bad1 ∪ bad2 ∪ badd ∪ badd', fun w hw => ?_⟩
    have hw1 : w ∉ bad1 := fun hc => hw (by simp [hc])
    have hw2 : w ∉ bad2 := fun hc => hw (by simp [hc])
    have hwd : w ∉ badd := fun hc => hw (by simp [hc])
    have hwd' : w ∉ badd' := fun hc => hw (by simp [hc])
    have e0 : (τ.charFrob w).coeff 0 = jj (b w) := by rw [hbad1 w hw1]; simp
    have e0' : (τ'.charFrob w).coeff 0 = jj' (b' w) := by rw [hbad2 w hw2]; simp
    have eb : b w = ((Ideal.absNorm w.asIdeal : ℕ) : NumberField.RingOfIntegers D) :=
      hinj (by rw [map_natCast, ← e0, hbadd w hwd])
    have eb' : b' w = ((Ideal.absNorm w.asIdeal : ℕ) : NumberField.RingOfIntegers D) :=
      hinj' (by rw [map_natCast, ← e0', hbadd' w hwd'])
    rw [eb, eb']
  exact ⟨bada ∪ badb, fun w hw => ⟨hbada w (fun hc => hw (Finset.mem_union_left _ hc)),
    hbadb w (fun hc => hw (Finset.mem_union_right _ hc))⟩⟩

/-- **The Frobenius characteristic polynomials of the `𝒪_D`-Tate modules
are `X² - a_w X + b_w` with `a_w, b_w ∈ 𝒪_D` independent of `I`**
(PROVEN 2026-07-27 by assembly over `exists_weilCoeffs_of_tateFrame_mult`
and `exists_finset_weilCoeffs_eq_of_mult`; see the section note above for
why that is the seam, and for the correction to the citation — the
arithmetic half of `exists_weilFrobeniusSystem_of_mult`, and the deepest
statement in the chain: Weil's Riemann hypothesis for abelian varieties
over finite fields, in the Hilbert–Blumenthal normalization of Shimura /
Taylor 2002 §1–2.  Faltings, *Endlichkeitssätze für abelsche Varietäten
über Zahlkörpern*, Invent. Math. 73 (1983), was cited here and is NOT
needed: independence of `λ` at a place of GOOD reduction is classical,
and `bad` absorbs every ramified place).

For an abelian scheme with real multiplication by `𝒪_D` and an
`F`-point `x` there are two families `a, b : w ↦ 𝒪_D` such that for
EVERY maximal ideal `I` of `𝒪_D`, every `π`, and every frame `φ` of
`TatePt m x I π` by a rank-two representation `τ` over a coefficient
ring `O` WHICH REMEMBERS THE REAL MULTIPLICATION (`j`, `hj`), one has

    τ.charFrob w = X² - j(a_w)·X + j(b_w)

for all but finitely many `w`.  Classically `a_w` is the trace and `b_w`
the determinant of `Frob_w` on the `𝒪_D`-Tate module of the reduction;
both are algebraic integers of `D`, and they do not depend on `I` —
that independence IS Faltings' theorem, and it is what makes the
`λ`-adic and `𝔭`-adic Tate modules of one abelian variety two members of
ONE compatible system.

What is load-bearing in the way this is stated.

* `a` and `b` are quantified BEFORE `q` and `I`; the frame data and
  `bad` after.  That ordering is the independence-of-`λ` statement, and
  reversing it would make the leaf either false or vacuous.
* The coefficients live in `𝒪_D` ITSELF and are transported into `O`
  along `j`, not along some embedding chosen per `I`.  This is what
  makes the statement `D`-rational without any mention of `ℚ̄_q`, and it
  is why the compatible-system content is now visible on the face of the
  statement rather than hidden inside an existential over embeddings.
* `bad` is quantified AFTER `q` and this is not slack — it must contain
  the places of `F` above `q`, where the `I`-adic representation is
  ramified and its Frobenius characteristic polynomial is not the Weil
  polynomial at all; since `q` ranges over every rational prime, no
  single finite set can contain the places above all of them.  Only the
  places of bad reduction of `A_x` are independent of `q`.
* `j` and `hj` may NOT be dropped.  Without them `O`, `τ` and `φ` range
  over frames that do not remember the real multiplication, and the
  conclusion is FALSE by Counterexample 2 of the audit below — the
  exotic frame `O = ℤ₁₃ × ℤ₁₃` has `τ.charFrob w = (X - c_w)²`, a
  square, while the honest frame has `X² - a_w X + N(w)`, and these
  disagree at infinitely many `w` by Chebotarev.  The monicity of the
  displayed polynomial is not an extra assumption: `τ.charFrob` is a
  characteristic polynomial of an endomorphism of a free rank-two
  module, so it is monic of degree two whatever the frame. -/
theorem exists_intWeilPolynomial_of_mult
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (hdim : SmoothOfRelativeDimension (Module.finrank ℚ D) f) :
    ∃ a b : HeightOneSpectrum (NumberField.RingOfIntegers F) →
        NumberField.RingOfIntegers D,
      ∀ (q : ℕ) (_ : Fact q.Prime)
        (I : Ideal (NumberField.RingOfIntegers D)) (_ : I.IsMaximal)
        (_ : (q : NumberField.RingOfIntegers D) ∈ I)
        (π : NumberField.RingOfIntegers D) (_ : π ∈ I) (_ : π ∉ I ^ 2)
        (O : Type u) (_ : CommRing O) (_ : TopologicalSpace O) (_ : IsTopologicalRing O)
        (τ : GaloisRep F O (Fin 2 → O)) (φ : (Fin 2 → O) → TatePt m x I π)
        (j : NumberField.RingOfIntegers D →+* O),
        (∀ (u u' : Fin 2 → O) (n : ℕ),
          (φ (u + u')).1 n = ab.add ((φ u).1 n) ((φ u').1 n)) →
        Function.Bijective φ →
        (∀ (σ : Field.absoluteGaloisGroup F) (u : Fin 2 → O) (n : ℕ),
          (φ (τ σ u)).1 n = ab.galSMul x σ ((φ u).1 n)) →
        (∀ (c : NumberField.RingOfIntegers D) (u : Fin 2 → O) (n : ℕ),
          (φ (j c • u)).1 n = m.act c ((φ u).1 n)) →
        ∃ bad : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)),
          ∀ w ∉ bad,
            τ.charFrob w =
              Polynomial.X ^ 2 - Polynomial.C (j (a w)) * Polynomial.X +
                Polynomial.C (j (b w)) := by
  classical
  -- Does ANY frame admit a rational family?  If so its coefficients are the answer.
  by_cases hex : ∃ a b : HeightOneSpectrum (NumberField.RingOfIntegers F) →
      NumberField.RingOfIntegers D, IsTateFrameWeilCoeffs m x a b
  · obtain ⟨a, b, href⟩ := hex
    refine ⟨a, b, ?_⟩
    intro q hq I hI hqI π hπ hπ2 O iCR iTS iTR τ φ j hφadd hφbij hφequiv hj
    -- The given frame has its own rational family, a priori unrelated to `a`, `b`.
    obtain ⟨a', b', bad', hbad'⟩ :=
      exists_weilCoeffs_of_tateFrame_mult m x hdim q hq I hI hqI π hπ hπ2 O iCR iTS iTR
        τ φ j hφadd hφbij hφequiv hj
    -- Independence identifies the two families off a finite set.
    obtain ⟨bad'', hbad''⟩ :=
      exists_finset_weilCoeffs_eq_of_mult m x hdim a' b' a b
        ⟨q, hq, I, hI, hqI, π, hπ, hπ2, O, iCR, iTS, iTR, τ, φ, j,
          hφadd, hφbij, hφequiv, hj, bad', hbad'⟩ href
    -- `bad` is quantified after the frame, so it may absorb both finite sets.
    refine ⟨bad' ∪ bad'', fun w hw => ?_⟩
    have hw' : w ∉ bad' := fun h => hw (Finset.mem_union_left _ h)
    have hw'' : w ∉ bad'' := fun h => hw (Finset.mem_union_right _ h)
    rw [hbad' w hw', (hbad'' w hw'').1, (hbad'' w hw'').2]
  · -- No frame admits one; but the frame just introduced does, by rationality.
    refine ⟨0, 0, ?_⟩
    intro q hq I hI hqI π hπ hπ2 O iCR iTS iTR τ φ j hφadd hφbij hφequiv hj
    obtain ⟨a', b', bad', hbad'⟩ :=
      exists_weilCoeffs_of_tateFrame_mult m x hdim q hq I hI hqI π hπ hπ2 O iCR iTS iTR
        τ φ j hφadd hφbij hφequiv hj
    exact absurd
      ⟨a', b', q, hq, I, hI, hqI, π, hπ, hπ2, O, iCR, iTS, iTR, τ, φ, j,
        hφadd, hφbij, hφequiv, hj, bad', hbad'⟩ hex

/-- **The Frobenius characteristic polynomials of the Tate modules form
one `D`-rational compatible system** (PROVEN 2026-07-26 by assembly over
the two leaves just above, `exists_algebraicClosureEmbedding_of_tateFrame_mult`
and `exists_intWeilPolynomial_of_mult`; see the section note there for
why that is the seam — item 9 of the
Tate-module construction, and the deepest statement in the chain: Weil's
Riemann hypothesis for abelian varieties over finite fields together
with Faltings' theorem that the system is independent of the residue
characteristic; see Faltings, *Endlichkeitssätze für abelsche
Varietäten über Zahlkörpern*, Invent. Math. 73 (1983), and Taylor 2002
§2 for the Hilbert–Blumenthal normalization used here).

For an abelian scheme with real multiplication by `𝒪_D` and an
`F`-point `x` there is a family `P : w ↦ P_w ∈ D[T]` of polynomials with
coefficients in `D` ITSELF, such that for EVERY maximal ideal `I` of
`𝒪_D`, every `π` and every frame `φ` of `TatePt m x I π` by a rank-two
representation `τ` over a coefficient ring `O`, the characteristic
polynomial of Frobenius at `w` on `τ` agrees with `P_w` inside an
algebraic closure of `ℚ_q`, for all but finitely many `w`.

Four points are load-bearing in the way this is stated.

* The system `P` is quantified BEFORE `I`: one family of polynomials
  serves every residue characteristic. That is exactly the
  independence-of-`λ` statement, and it is what makes the `λ`-adic and
  `𝔭`-adic Tate modules of a single abelian variety two members of ONE
  compatible system — the fields `matchℓ` and `matchp` of
  `HilbertBlumenthalPoint`.
* The exceptional set `bad` is quantified AFTER `q`, and this is not
  slack — the statement would be FALSE the other way round. `bad` must
  contain the places of `F` above `q`, where the `I`-adic representation
  is ramified and its Frobenius characteristic polynomial is not the
  Weil polynomial at all; and since `q` ranges over every rational
  prime, no single finite set can contain the places above all of them.
  Only the places of bad reduction of `A_x` are independent of `q`. The
  consumer needs no more: it applies this leaf at exactly two ideals and
  takes the union of the two exceptional sets, which is finite.
* `τ` is not quantified freely: it must FRAME the Tate module
  `TatePt m x I π`. Without that hypothesis the statement would be false,
  since nothing would tie `τ` to `A` — a residual condition constrains a
  representation only modulo `I`. The frame is transported along a
  bijection, and characteristic polynomials are invariant under
  conjugation, so — the original claim continued — no compatibility
  beyond additivity and Galois equivariance is required of `φ`. **That
  last clause was FALSE and has been repaired**: the frame must also
  remember the real multiplication, which is the hypothesis pair
  `j` / `hj` below. See the audit.
* The embeddings `ψ` of `D` and `ι` of `O` into `ℚ̄_q` are likewise
  produced per `I` (they are the place of `D` over `q` determined by
  `I`, and the structural embedding of the completion), whereas `P` is
  not; `ι` is required injective, which is the statement that `O` is a
  domain of characteristic zero — the Carayol normalization of the
  coefficients. That `O` is such a domain is NOT a consequence of the
  frame axioms alone — it is a consequence of `j`/`hj`, which force
  `O = 𝒪_{D,I}`; see the audit.

## FAITHFULNESS AUDIT (2026-07-26) — THE LEAF WAS FALSE AS STATED, AND IS REPAIRED HERE

Two independent explicit counterexamples to the PREVIOUS statement are
given below; they are retained because they are what pins the two
hypotheses `j` and `hj` down, and because any future weakening of those
hypotheses reinstates them.

**The repair is now MADE, in the three coordinated edits described at the
end** (2026-07-26, later the same day). When the counterexamples were
first written the repair could only be REPORTED: the frame is produced by
the sibling `exists_tateFrame_of_levelStructure` (a different owner,
working concurrently) and consumed by the PROVEN assembly
`nonempty_hilbertBlumenthalPoint_of_isTwistedHilbertBlumenthalModuli`
(`Modularity/KhareWintenberger.lean`), so changing this statement in
isolation would have turned a false leaf into a hard build error, which
is worse. The sibling now PRODUCES `j` and `hj`, so all three edits land
together and the seam typechecks.

Everything below describing the defect refers to the statement WITHOUT
`j`/`hj`. With them, the leaf is open but faithful.

**The quantifier repair recorded in the second bullet DID hold up.**
`bad`, `ψ` and `ι` are all produced after `q`, `I`, `π` and the frame;
`P` alone is produced before `q`; every remaining binder (`D`, `m`, `x`,
`hdim`) is genuinely independent of `q`. No sibling quantifier has the
same defect. The falsity found here is a different one.

### The defect

`O`, `τ` and `φ` range over ALL frames of `TatePt m x I π` that are
merely additive, bijective and `Γ_F`-equivariant. Nothing requires the
frame to REMEMBER THE REAL MULTIPLICATION — that the `O`-module
structure transported to `T` along `φ` is the one induced by `𝒪_D`
through `m.act`. Additivity plus `Γ_F`-equivariance determine `τ`
uniquely as `φ⁻¹ ∘ galSMul σ ∘ φ`, but they leave `O` free: any
commutative subring `O ⊆ End_{Γ_F}(T)` that is `ℤ_q`-free of rank
`[𝒪_{D,I} : ℤ_q]` and over which `T` is free of rank `2` is a legal
frame. When `A_x` has endomorphisms beyond `𝒪_D`, such rings exist and
are NOT `𝒪_{D,I}`.

(`O` is automatically a `ℤ_q`-algebra even though nothing says so: `φ`
forces `O ⊕ O ≅ T ≅ ℤ_q^{2d}` as abelian groups, and every additive
endomorphism of `ℤ_q^n` is `ℤ_q`-linear, since divisibility by `q^n` is
preserved. So the exotic frames below really are the general shape.)

### Counterexample 1 — `Function.Injective ι` fails, and it survives
### EVERY clause the sibling leaf produces

`D = ℚ(√5)` (totally real, `finrank ℚ D = 2`), `F` any number field,
`E/F` any elliptic curve, `A = E × E` over `S = Spec F`, `x = 𝟙`. Then
`f : A ⟶ S` is proper, smooth, with geometrically connected fibres, of
relative dimension `2 = finrank ℚ D`, and `𝒪_D = ℤ[(1+√5)/2]` acts by
the companion matrix `[[0,1],[1,1]] ∈ M₂(ℤ) ⊆ End(E × E)` of `X² − X − 1`
(verified: `charpoly [0,1;1,1] = x² − x − 1`). Every hypothesis holds.

Take `q = 13`, which is INERT in `ℚ(√5)` (`kronecker(5,13) = −1`), so
`I = 13·𝒪_D` is maximal, `13 ∈ I`, `π = 13 ∉ I²`, and
`T := TatePt m x I π = T₁₃(E × E) = W ⊗_{ℤ₁₃} T₁₃E` with `W = ℤ₁₃²` the
"multiplicity space" on which `M₂(ℤ₁₃)` acts and `Γ_F` acts trivially.

Now put `O := ℤ₁₃[N] ≅ ℤ₁₃[ε]/(ε²)`, `N = [[0,1],[0,0]] ∈ End(W)`. It is
a commutative topological ring; `W` is free of rank `1` over it
(`W = O·e₂`), so `T ≅ O ⊗_{ℤ₁₃} T₁₃E ≅ O²`; and `Γ_F`, acting only on
the `T₁₃E` factor, is `O`-linear. So `(O, τ, φ)` is a legal frame. But
`O` has a nonzero nilpotent, so **there is no injective ring
homomorphism `O →+* AlgebraicClosure ℚ₁₃` at all**, and the conclusion
fails outright.

This frame satisfies **every** clause of the sibling leaf's conclusion,
which is what makes it decisive: `O` is LOCAL, an `ℤ₁₃`-algebra, finite
free over `ℤ₁₃`, carries its module topology — and it even meets the
residual clause. Indeed `τ.charFrob w = X² − a_w X + N(w) ∈ ℤ₁₃[X]`
(`a_w` the trace of `Frob_w` on `T₁₃E`), while `A[I] = A[13]` is
`𝔽₁₆₉ ⊗_{𝔽₁₃} E[13]` with `ρ'.charFrob w = X² − ā_w X + N̄(w)` over
`k' = 𝔽₁₆₉`; so `ι₀ : ℤ₁₃[ε] →+* 𝔽₁₆₉`, `ε ↦ 0`, discharges
`(τ.charFrob w).map ι₀ = ρ'.charFrob w` at every `w`. **Hence adding to
this leaf every hypothesis the consumer could actually supply from the
sibling still leaves it false.** That is why the repair has to reach the
real multiplication rather than the shape of `O`.

### Counterexample 2 — the charpoly equation itself fails

Its role is different from Counterexample 1's, and the difference
matters when choosing a repair. This frame is NOT local and does NOT
satisfy the sibling's residual clause, so it is not a counterexample to
the strengthened statements — but it refutes the CHARPOLY EQUATION
itself, not merely the injectivity of `ι`. **So "just delete
`Function.Injective ι`" is not a repair either**: what is broken is the
identification of `τ.charFrob` with a member of the system, and the
injectivity failure of Counterexample 1 is a symptom of the same cause.

Same `D = ℚ(√5)` and `q = 13`, but take `F = ℚ(i)` and `E : y² = x³ − x`
(conductor `32`), which has CM by `ℤ[i] ⊆ F`; `A = E × E` as before.
`13 ≡ 1 mod 4`, so `13` SPLITS in `ℚ(i)`, whence
`T₁₃E = T_𝔭 ⊕ T_𝔭̄` with `Γ_F` acting by two distinct characters
`χ, χ̄ : Γ_F → ℤ₁₃^×`. Hence `T = U₁ ⊕ U₂` with `U_i ≅ ℤ₁₃²` and `Γ_F`
acting on `U₁`, `U₂` by the SCALARS `χ(σ)`, `χ̄(σ)`.

Frame: `O := ℤ₁₃ × ℤ₁₃` acting by the two projections. `T` is free of
rank `2` over it (`e_iT ≅ ℤ₁₃²`), `Γ_F` is `O`-linear, and in the basis
`t_i = u_i + v_i` one has `τ(σ) = (χ(σ), χ̄(σ))·id`, so

    τ.charFrob w = (X − c_w)²  with  c_w = (χ(w), χ̄(w)) ∈ O.

A ring hom out of a product into a field kills one of the two orthogonal
idempotents, so EVERY `ι : O →+* ℚ̄₁₃` factors through a projection and
`(τ.charFrob w).map ι` is a SQUARE `(X − ι(c_w))²` — whatever embedding
of `ℤ₁₃` it uses (this is why possibly-discontinuous embeddings do not
rescue the statement).

Meanwhile the STANDARD frame at the same `(q, I, π)` — namely
`O = 𝒪_{D,I} = ℤ₁₃[α]`, the unramified quadratic extension of `ℤ₁₃`,
`α` the companion matrix acting on `W`, with `T ≅ 𝒪_{D,I} ⊗_{ℤ₁₃} T₁₃E`
— has `τ.charFrob w = X² − a_w X + N(w)`, where `a_w ∈ ℤ` is the trace
of `Frob_w` on `T₁₃E` and `N(w)` its norm; since `ψ` is a field
embedding, hence injective, this
FORCES `P w = X² − a_w X + N(w) ∈ ℚ[X] ⊆ D[X]`, and `ψ` fixes it. So the
exotic frame demands that `X² − a_w X + N(w)` be a square, i.e.
`a_w² = 4N(w)`, i.e. `χ(w) = χ̄(w)`, for all `w` outside a finite set.
But `χ ≠ χ̄` (for `w` over a split `p`,
`{χ(w), χ̄(w)}` is the pair of conjugate Hecke values, e.g. `{9, 2}` in
`ℤ₁₃` at `w | 5`, since `a₅(E) = −2` and `π₅ = −1 + 2i`, `i ↦ 5`), so by
Chebotarev they differ at infinitely many `w`. Contradiction.

(Consistency check that the exotic frame is real rather than an
arithmetic slip: the `ℤ₁₃`-characteristic polynomial of `Frob_w` on `T`
must be the norm of the `O`-one, and indeed
`(X−χ)²(X−χ̄)² = N_{O/ℤ₁₃}((X−c_w)²)` agrees with the value computed
from the standard frame.)

### What does NOT repair it

Three cheaper patches suggest themselves; all three fail, and the reason
each fails is worth recording so that nobody spends a cycle on it.

* *Add the sibling's `O`-conditions* (`Algebra ℤ_[q] O`, `IsLocalRing O`,
  `Module.Finite`/`Module.Free ℤ_[q] O`, `IsModuleTopology ℤ_[q] O`) —
  the only strengthening the consumer could actually supply, since the
  sibling produces exactly these. It excludes Counterexample 2 (that `O`
  is not local) but NOT Counterexample 1, which satisfies all of them.
* *Delete `Function.Injective ι`.* Counterexample 2 refutes the charpoly
  equation on its own, so the statement stays false; and the consumer
  needs the injectivity anyway — it is the `HilbertBlumenthalPoint`
  fields `ιO₀_injective`/`ιC_injective`, used again downstream at
  `KhareWintenberger.lean:3309`. Deleting it breaks the assembly without
  buying truth.
* *Add `IsDomain O`.* This does kill Counterexample 1, but it is an
  ad-hoc symptom patch — it asserts the conclusion one wanted about `O`
  instead of deriving it — and the consumer cannot supply it: the
  sibling's `O` is only known to be LOCAL, and `ℤ₁₃[ε]` is a local ring
  that is not a domain. So it is neither structural nor available.

Corroboration that `IsDomain` is precisely what is missing: the tree's
own PROVEN helper for producing such an embedding,
`exists_injective_ringHom_algebraicClosure_of_moduleFinite`
(`Modularity/KhareWintenberger.lean`), takes `[IsDomain O]`,
`[Algebra ℤ_[ℓ] O]`, `[Module.Finite ℤ_[ℓ] O]` and injectivity of
`algebraMap ℤ_[ℓ] O` as hypotheses — it factors through
`FractionRing O` and `IsAlgClosed.lift`, and there is no such
factorization without the domain hypothesis. This leaf ASSERTS the
existence of that embedding for an `O` about which it hypothesises
strictly less, which is how the clause got in.

### The repair (MADE — this is what `j` and `hj` are)

Pin the frame to the real multiplication. Concretely, THIS leaf now takes
a ring homomorphism together with the intertwining it must satisfy,

    (j : NumberField.RingOfIntegers D →+* O)
    (hj : ∀ (a : NumberField.RingOfIntegers D) (u : Fin 2 → O) (n : ℕ),
            (φ (j a • u)).1 n = m.act a ((φ u).1 n))

as further hypotheses of the innermost `∀` (`j` sits after `φ` in the
binder chain, `hj` after the equivariance arrow). This is exactly the
statement that `φ` is a frame of the Tate module AS AN `𝒪_D`-MODULE,
and it repairs both counterexamples at once: `j` forces `O` to contain
the image of `𝒪_D ⊗ ℤ_q` acting on `T`, which is `𝒪_{D,I}`, and the
rank count `rank_{ℤ_q} O = [𝒪_{D,I} : ℤ_q]` together with `𝒪_{D,I}`
being integrally closed then forces `O = 𝒪_{D,I}`. In particular `O` is
a domain of characteristic `0`, so `Function.Injective ι` becomes
automatic rather than an assumption smuggled into the conclusion, and
`τ.charFrob` becomes the reduced (rank-two over `𝒪_{D,I}`) Frobenius
polynomial, which is what Weil and Faltings are about.

Neither counterexample survives: `ℤ₁₃[ε] = ℤ₁₃[N]` admits no `j`,
because `j((1+√5)/2)` would have to act on `W` as the companion matrix
`α`, which generates the unramified quadratic `ℤ₁₃[α] ≠ ℤ₁₃[N]`; and
`ℤ₁₃ × ℤ₁₃` admits none either, because `𝒪_D` acts through the
`W`-factor and is therefore not scalar on either `e_iT`.

The seam needed three coordinated edits, none of which was this
declaration's owner's to make alone. **All three are now in place:**

1. `exists_tateFrame_of_levelStructure` additionally PRODUCES `j` and
   `hj`. This was free for its author: it constructs `O = 𝒪_{D,I}` and
   `φ` from the `I`-adic Tate module, so `j` is the structural map of
   `exists_adicCoefficientRing` and `hj` is `hφj`, which is how the
   action was built in `exists_tateFrame_of_adicCoefficientRing`.
2. This leaf takes `j`, `hj` as hypotheses (as displayed above).
3. `nonempty_hilbertBlumenthalPoint_of_isTwistedHilbertBlumenthalModuli`
   threads them through its two `obtain`s — the bindings that were
   parked there as `_jD₀`/`_hjD₀` and `_jDp`/`_hjDp` precisely against
   this day are now consumed, and the `HilbertBlumenthalPoint` fields
   `ιO₀_injective` / `ιC_injective` and `matchℓ` / `matchp` are supplied
   from the repaired leaf rather than from the refuted one.

**Consequence for the eventual prover of this leaf**: `Function.Injective ι`
is no longer an assumption smuggled into the conclusion. Discharge it by
first proving `O = 𝒪_{D,I}` from `j`, `hj`, the `ℤ_q`-rank count and
integral closedness — do NOT look for a hypothesis that hands it to you,
and do NOT reintroduce `IsDomain O` as a hypothesis (that is the ad-hoc
patch the audit rejects: it kills counterexample 1 and leaves
counterexample 2 standing).

The sibling `exists_tateFrame_of_levelStructure` was NOT itself false —
the honest `I`-adic Tate module does frame it — it was merely too weak,
and that weakness is what this leaf inherited.

### THE PROOF (2026-07-26): the repaired leaf is an ASSEMBLY

With `j`/`hj` in place the statement is no longer atomic, and it is
discharged here over the two leaves above.  `P` is the explicit
polynomial `X² - a_w X + b_w` read in `D`, with `a`, `b` the
`𝒪_D`-integral families of `exists_intWeilPolynomial_of_mult`; the
embeddings `ψ` and `ι` and the injectivity of `ι` come from
`exists_algebraicClosureEmbedding_of_tateFrame_mult`; and the matching
of the two sides is the compatibility `ι ∘ j = ψ ∘ (𝒪_D ↪ D)` applied
coefficient by coefficient through `Polynomial.map`.

Note what this does to the refuted clause.  `Function.Injective ι` is no
longer asserted here at all — it is IMPORTED from a statement that
mentions no Frobenius and whose proof obligation is exactly "the frame's
coefficient ring is `𝒪_{D,I}`".  That is the repair carried through to
its conclusion: the clause is now owed where it can be discharged,
rather than smuggled into a conclusion about characteristic polynomials.
The counterexamples above are retained because they are what pins the
repair down, and because any future weakening of `j`/`hj` — in this
declaration or in either leaf — reinstates them verbatim. -/
theorem exists_weilFrobeniusSystem_of_mult
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (hdim : SmoothOfRelativeDimension (Module.finrank ℚ D) f) :
    ∃ P : HeightOneSpectrum (NumberField.RingOfIntegers F) → Polynomial D,
      ∀ (q : ℕ) (_ : Fact q.Prime)
        (I : Ideal (NumberField.RingOfIntegers D)) (_ : I.IsMaximal)
        (_ : (q : NumberField.RingOfIntegers D) ∈ I)
        (π : NumberField.RingOfIntegers D) (_ : π ∈ I) (_ : π ∉ I ^ 2)
        (O : Type u) (_ : CommRing O) (_ : TopologicalSpace O) (_ : IsTopologicalRing O)
        (τ : GaloisRep F O (Fin 2 → O)) (φ : (Fin 2 → O) → TatePt m x I π)
        (j : NumberField.RingOfIntegers D →+* O),
        (∀ (u u' : Fin 2 → O) (n : ℕ),
          (φ (u + u')).1 n = ab.add ((φ u).1 n) ((φ u').1 n)) →
        Function.Bijective φ →
        (∀ (σ : Field.absoluteGaloisGroup F) (u : Fin 2 → O) (n : ℕ),
          (φ (τ σ u)).1 n = ab.galSMul x σ ((φ u).1 n)) →
        (∀ (a : NumberField.RingOfIntegers D) (u : Fin 2 → O) (n : ℕ),
          (φ (j a • u)).1 n = m.act a ((φ u).1 n)) →
        ∃ (bad : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
          (ψ : D →+* AlgebraicClosure ℚ_[q]) (ι : O →+* AlgebraicClosure ℚ_[q]),
          Function.Injective ι ∧
          ∀ w ∉ bad, (τ.charFrob w).map ι = (P w).map ψ := by
  -- The `𝒪_D`-integral compatible system: one pair of families for every `q` and `I`.
  obtain ⟨a, b, hab⟩ := exists_intWeilPolynomial_of_mult m x hdim
  -- `P` is that system read in `D`.
  refine ⟨fun w => Polynomial.X ^ 2 -
      Polynomial.C (algebraMap (NumberField.RingOfIntegers D) D (a w)) * Polynomial.X +
      Polynomial.C (algebraMap (NumberField.RingOfIntegers D) D (b w)), ?_⟩
  intro q hq I hI hqI π hπ hπ2 O iCR iTS iTR τ φ j hφadd hφbij hφequiv hj
  obtain ⟨bad, hbad⟩ :=
    hab q hq I hI hqI π hπ hπ2 O iCR iTS iTR τ φ j hφadd hφbij hφequiv hj
  -- The frame remembers `m.act`, so its coefficient ring is `𝒪_{D,I}`: that is what
  -- supplies `ψ`, `ι`, the injectivity, and the compatibility `ι ∘ j = ψ ∘ (𝒪_D ↪ D)`.
  obtain ⟨ψ, ι, hιinj, hcompat⟩ :=
    exists_algebraicClosureEmbedding_of_tateFrame_mult m x hdim q hq I hI hqI π hπ hπ2 O
      iCR iTS iTR τ φ j hφadd hφbij hφequiv hj
  refine ⟨bad, ψ, ι, hιinj, fun w hw => ?_⟩
  -- Both sides are `X² - (…)·X + (…)`, and the two constant terms agree by `hcompat`.
  rw [hbad w hw]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C, hcompat]

end Fermat
