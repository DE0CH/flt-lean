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
  that mathlib does not have.  Its one residual leaf is
  `module_finite_free_moduleTopology_padicIntAlgebra`.

`exists_weilFrobeniusSystem_of_mult` remains a single sorried leaf; it
is stated about the geometric objects of `AbelianScheme.lean` and about
nothing else.
-/
module

public import Fermat.FLT.Modularity.AbelianScheme
public import Fermat.FLT.Deformations.RepresentationTheory.GaloisRep
-- `IsDedekindDomain.HeightOneSpectrum.natCard_under_maximalIdeal`: the residue
-- cardinality at `w` in the Frobenius specification of
-- `adicArithFrob_rootsOfUnity_pow_absNorm`
public import Fermat.FLT.Deformations.RepresentationTheory.CompletionTransport
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Dimension.Constructions
-- `IsAdicComplete`: the completeness half of the pin that identifies the
-- coefficient ring of `exists_adicCoefficientRing` with `𝒪_{D,I}`
public import Mathlib.RingTheory.AdicCompletion.Basic
-- `IsAdic.isAdicComplete_iff`: `IsAdicComplete` from completeness and
-- Hausdorffness of the adic topology, used to discharge that pin for
-- `v.adicCompletionIntegers D`
public import Mathlib.RingTheory.AdicCompletion.Topology
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
-- `NumberField.IsTotallyReal`: the real-multiplication field of a
-- Hilbert–Blumenthal family is totally real, in both leaf STATEMENTS
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

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

/-- **`𝒪_v` is finite and free over `ℤ_q`, with the module topology**
(sorry node — commutative algebra; Serre *Local Fields* II, Neukirch
II.4).

For `v` a height-one point of `𝒪_D` lying over the rational prime `q`,
the completion `𝒪_v` is finite and free over `ℤ_q` of rank `e·f`, and
its valuation topology is the `ℤ_q`-module topology.  The `ℤ_q`-algebra
structure is not part of the burden — it is `padicIntAlgebra` above,
PROVEN; and neither are the three pin conjuncts of
`exists_adicCoefficientRing`.  This is all that leaf still needs.

WHAT IS MISSING UPSTREAM, precisely.  Mathlib has `𝒪_v` with its ring,
topology, locality and discrete-valuation structure, and (in
`Mathlib/NumberTheory/NumberField/Completion/FinitePlace.lean`) even
`Module.Finite Kᵥ L_w` for completions of a finite extension — but that
instance takes `Algebra Kᵥ L_w` as a HYPOTHESIS.  There is no
functoriality of adic completions along a finite extension in mathlib:
no `Algebra (v.adicCompletion K) (w.adicCompletion L)`, hence no
`Module.Finite` / `Module.Free` / `IsModuleTopology` for the integers
either.

THE VENDORING TARGET.  `~/cs/FLT/FLT/DedekindDomain/Completion/BaseChange.lean`
has all of it: `adicValued.continuous_algebraMap` and
`adicCompletionSemialgHom` build the map `Kᵥ → L_w`,
`adicCompletionSemialgHom_image_adicCompletionIntegers` restricts it to
the integers, and `integerBaseChangeLinearEquiv : B ⊗[A] 𝒪ᵥ ≃ ∏_{w∣v} 𝒪_w`
together with the `Module.Finite` / `Module.Free` / `IsModuleTopology`
instances there is the rest.  `ℤ_q` is identified with `𝒪_{ℚ,(q)}` by
mathlib's `PadicInt.adicCompletionIntegersEquiv`.  That file's mathlib
pin is `81a5d2` against ours `a3364fa`, so every name and signature
lifted needs re-checking.

ROUTES THAT AVOID THE BASE CHANGE.  `Module.Free` should be automatic
from `Module.Finite`: `ℤ_q` is a principal ideal domain and `𝒪_v` is a
domain into which it injects (a nonzero ring map from a DVR whose
target has characteristic zero), so `𝒪_v` is torsion-free and
`Module.free_of_finite_type_torsion_free'` applies.  For `Module.Finite`
the classical argument is complete Nakayama: `𝒪_v` is `q`-adically
complete (`isAdicComplete_span_natCast`) and `𝒪_v / q𝒪_v ≅ 𝒪_D / Iᵉ` is
FINITE — the isomorphism being exactly what
`exists_sub_mem_span_uniformizer_pow` (surjectivity) and
`mem_span_uniformizer_pow_iff` (kernel) above supply.  For
`IsModuleTopology`, `isAdic_span_uniformizer` says the topology of `𝒪_v`
has `{(π)ⁿ}` as a basis of neighbourhoods of `0`, and `(π)ᵉ = (q)`, so
once a `ℤ_q`-basis is in hand the topology is the product one. -/
theorem module_finite_free_moduleTopology_padicIntAlgebra
    (q : ℕ) [Fact q.Prime] (hqv : (q : 𝓞 D) ∈ v.asIdeal) :
    letI := padicIntAlgebra v q hqv
    Module.Finite ℤ_[q] (v.adicCompletionIntegers D) ∧
      Module.Free ℤ_[q] (v.adicCompletionIntegers D) ∧
      IsModuleTopology ℤ_[q] (v.adicCompletionIntegers D) :=
  sorry

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
  2026-07-26** in the subsection above, over the one residual leaf
  `module_finite_free_moduleTopology_padicIntAlgebra`.
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
`padicIntLiftHom`).  The residual burden is the single leaf
`module_finite_free_moduleTopology_padicIntAlgebra`: `Module.Finite`,
`Module.Free` and `IsModuleTopology` over `ℤ_q`, which mathlib does not
have because it has no functoriality of adic completions along a finite
extension.  Its docstring records the vendoring target in `~/cs/FLT`.

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
  of the resulting representation.
* `exists_galoisRep_of_isOpen_congruence` — TOPOLOGY. A homomorphism
  into `End_O(O²)` all of whose congruence subgroups mod `Pⁿ` are open
  is continuous for the module topology. This is where the `ℤ_q`-module
  topology of `O` is compared with the `π`-adic one.

Everything else — the identification `𝒪_D/Iⁿ ≅ O/(π)ⁿ`, the inverse
limit, bijectivity of the frame, `O`-linearity of the Galois action and
the `j`-compatibility clause — is PROVEN in
`exists_tateFrame_of_adicCoefficientRing` from those three. -/

/-! #### The three sub-leaves of `exists_levelwiseTateFrame`

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

Since 2026-07-26 the lifting step is itself PROVEN, over
`exists_mem_torsion_act_uniformizer_eq` (also PROVEN) and hence over the
single geometric fact `exists_nsmul_eq_geomFibrePt` — divisibility of an
abelian variety. So the geometry that is still open beneath the levelwise
frame is exactly two statements: the RANK COUNT (`exists_levelTateFrame`)
and DIVISIBILITY (`exists_nsmul_eq_geomFibrePt`). Everything between them
is commutative algebra proven here. -/

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

/-- **The `Iⁿ`-torsion is free of rank two over `𝒪_D/Iⁿ`, at each single
level `n`** (sorry node — abelian varieties; Mumford *Abelian Varieties*
§18, Silverman *AEC* III.7, Taylor 2002 §2).

**This is where the rank count lives, and it is the only genuinely
geometric input of the levelwise frame.** No compatibility in `n` is
asserted: the frames at different levels are chosen independently, and
tying them together is the business of `exists_levelTateFrame_succ` and
of the recursion in `exists_levelwiseTateFrame`.

The argument. `A_x` is an abelian variety of dimension `g = [D:ℚ]` over
an algebraically closed field of characteristic zero — that is `hdim`
together with the properness, smoothness and connectedness carried by
`ab` — so `H₁(A_x, ℚ)` has `ℚ`-dimension `2g`. The real multiplication
makes it a module over the FIELD `D`, hence free, of `D`-dimension
`2g/[D:ℚ] = 2`; **this is exactly where `hdim` enters, and it is why the
rank is two over the coefficient ring rather than over `ℤ_q`.** Tensoring
with `ℚ_q` and projecting to the factor of `D ⊗ ℚ_q = ∏_{I ∣ q} D_I` cut
out by `I` gives a two-dimensional `D_I`-space; `A[Iⁿ]` is its
`𝒪_{D,I}`-lattice modulo `Iⁿ`, and `𝒪_{D,I}/Iⁿ = 𝒪_D/Iⁿ`.

At `n = 0` the statement is trivial on both sides: `I⁰ = ⊤`, the
quotient ring is trivial (so the source is a singleton), and `A[⊤] = 0`
because `1 ∈ ⊤` acts as the identity. -/
theorem exists_levelTateFrame
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (hdim : SmoothOfRelativeDimension (Module.finrank ℚ D) f)
    (I : Ideal (NumberField.RingOfIntegers D)) (hI : I.IsMaximal) (n : ℕ) :
    ∃ c : (Fin 2 → NumberField.RingOfIntegers D ⧸ I ^ n) → GeomFibrePt f x,
      IsLevelTateFrame m x (I ^ n) c :=
  sorry

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
geometric points of a fibre** (sorry node — abelian varieties; Mumford
*Abelian Varieties* §6 (Application 2 of the theorem of the cube),
Silverman *AEC* III.4.2 and III.6.4).

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
divisibility by a nonzero element of `𝒪_D` through the absolute norm. -/
theorem exists_nsmul_eq_geomFibrePt
    {A S : Scheme.{u}} {f : A ⟶ S} (ab : AbelianSchemeStruct f)
    {F : Type u} [Field F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (N : ℕ) (hN : N ≠ 0) (y : GeomFibrePt f x) :
    ∃ w : GeomFibrePt f x,
      letI := ab.addCommGroup (specAlgClos F ≫ x)
      N • w = y :=
  sorry

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
`A[I] ≠ 0` on any abelian variety. -/
theorem exists_mem_torsion_act_uniformizer_eq
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
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

/-- **The pointwise stabilizer of the `J`-torsion is open in `Γ_F`**
(sorry node — arithmetic of abelian varieties; Silverman *AEC* III.7,
Mumford §18).

For a nonzero ideal `J` of `𝒪_D` the `J`-torsion of the geometric fibre
is a FINITE set — it is contained in `A[N]` for `N` any nonzero rational
integer in `J`, and `A[N] ≅ (ℤ/N)^{2g}` — and every one of its points is
defined over a finite extension of `F`, because the `N`-division scheme
is finite over the base. Hence the subgroup of `Γ_F` fixing `A[J]`
pointwise contains the open subgroup `Γ_{F'}` for `F'` a finite
extension of `F` splitting the finitely many points, and a subgroup of a
topological group containing an open subgroup is open.

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
      ∀ y ∈ (m.torsion x J).1, ab.galSMul x σ y = y} :=
  sorry

/-- **A homomorphism with open congruence subgroups is a continuous
representation** (sorry node — topology and commutative algebra).

`O` is finite over `ℤ_q` and carries the `ℤ_q`-module topology, so its
topology is the `q`-adic one; and `P` is a proper ideal containing `q`,
so the `P`-adic and `q`-adic filtrations of `O` are cofinal in each
other — one inclusion is `q ∈ P`, the other is nilpotence of the maximal
ideal of the artinian local ring `O/qO`, which contains the image of
`P`. Hence `{Pⁿ}` is a neighbourhood basis of `0` in `O`, `{Pⁿ·End}` one
of `0` in `End_O(O²)` for the module topology, and openness of every
congruence subgroup is exactly continuity of `t` at `1`.

**Both hypotheses on `P` are load-bearing.** Without `hPq` the `P`-adic
topology can be coarser than the `q`-adic one (take `P = 0`, all of
whose congruence subgroups are trivially open while `t` is arbitrary);
without `hPtop` it can be finer (`P = ⊤` makes every congruence subgroup
the whole group). -/
theorem exists_galoisRep_of_isOpen_congruence
    {F : Type u} [Field F] [NumberField F] (q : ℕ) [Fact q.Prime]
    {O : Type u} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [Algebra ℤ_[q] O] [IsLocalRing O] [Module.Finite ℤ_[q] O] [Module.Free ℤ_[q] O]
    [IsModuleTopology ℤ_[q] O]
    (P : Ideal O) (hPq : (q : O) ∈ P) (hPtop : P ≠ ⊤)
    (t : Field.absoluteGaloisGroup F →* Module.End O (Fin 2 → O))
    (hloc : ∀ n : ℕ, IsOpen {σ : Field.absoluteGaloisGroup F |
      ∀ (u : Fin 2 → O) (i : Fin 2), (t σ u - u) i ∈ P ^ n}) :
    ∃ τ : GaloisRep F O (Fin 2 → O), ∀ σ, τ σ = t σ :=
  sorry

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

* `exists_tatePt_val_one_eq` — the reduction `T ↠ A[I]` is SURJECTIVE
  (divisibility of the group of geometric points of an abelian variety
  over an algebraically closed field of characteristic zero).
* `exists_tatePt_act_eq_of_val_one_eq_zero` — its KERNEL is `π · T`
  (a shift of the inverse system, plus `I ^ n = (π ^ n) + I ^ (n+1)`,
  which holds because `π` generates the one-dimensional `𝒪_D/I`-vector
  space `I / I ^ 2`). **PROVEN** — it needed no new input beyond the
  hypotheses it was cut with.
* `exists_residualEmbedding_of_residualComparison` — the Noether–Skolem
  step, over an abstract comparison map.

Together the first two say `T / π T ≅ A[I]` as `Γ_F`-modules, which
composed with the level structure `e` is exactly the hypothesis of the
third. -/

/-- **Every `I`-torsion point of the geometric fibre lifts to the Tate
module** (sorry node — abelian varieties: divisibility of `A(F̄)`;
Mumford *Abelian Varieties* §6, Silverman *AEC* III.4/III.7).

Multiplication by a nonzero `π ∈ 𝒪_D` is an isogeny of the geometric
fibre `A_x`, hence surjective on `F̄`-points (`F̄` is algebraically closed
of characteristic zero), so the inverse system

  `⋯ --·π--> A[I³] --·π--> A[I²] --·π--> A[I]`

has surjective transition maps and its limit `TatePt m x I π` surjects
onto its first stage `A[I]`. This is the ONLY place where surjectivity
of the reduction is used; the hypotheses `hI`, `hπ`, `hπ2` are what make
`π` a genuine uniformizer at `I` (with `π = 0` the limit is zero and the
statement is false), and `hπ2` is what makes the `n`-th stage of the
lifting stay inside `A[I ^ n]`.

Note the indexing convention of `TatePt`: `t.1 0 = 0` and `t.1 1 ∈ A[I]`,
so `t.1 1` is the reduction. -/
theorem exists_tatePt_val_one_eq
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (I : Ideal (NumberField.RingOfIntegers D)) (hI : I.IsMaximal)
    (π : NumberField.RingOfIntegers D) (hπ : π ∈ I) (hπ2 : π ∉ I ^ 2)
    (y : GeomFibrePt f x) (hy : y ∈ (m.torsion x I).1) :
    ∃ t : TatePt m x I π, t.1 1 = y :=
  sorry

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

/-- **Two rank-two structures on one irreducible residual representation
differ by a ring map** (sorry node — representation theory: Schur,
Wedderburn and Noether–Skolem; this is the leaf carrying `hirr`).

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
`Ō` is a field is proving something weaker than the statement. -/
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
        ρ' σ = E.conj (Matrix.toLin' ((LinearMap.toMatrix' (τ σ)).map ι₀)) :=
  sorry

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
sorried `have`. It is cut here into three statements, of which exactly
ONE is open and it is the only deep one:

* `det_eq_cyclotomicCharacter_of_tateFrame` (SORRY NODE — the WEIL
  PAIRING; the only new leaf): the determinant of the frame
  representation IS the `q`-adic cyclotomic character, as a character
  of the whole of `Γ_F`. No exceptional set and nothing local appears:
  the bad places enter only at the second step.
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

/-- **The determinant of a Tate frame is the cyclotomic character**
(sorry node — the WEIL PAIRING; Silverman *AEC* III.8 for the elliptic
case, Mumford *Abelian Varieties* §16/§20 for the polarized case in
general, Taylor 2002 §2 and Carayol for the Hilbert–Blumenthal
normalization used here).

For a frame `φ` of the Tate module `TatePt m x I π` by
`τ : Γ_F → GL₂(O)` over the completion `O = 𝒪_{D,I}` — additive,
bijective, `Γ_F`-equivariant, and compatible with the real
multiplication through `j` — the determinant of `τ` is the `q`-adic
cyclotomic character:

  `det (τ σ) = χ_cyc(σ)` for EVERY `σ ∈ Γ_F`.

The argument. A polarization of the abelian variety `A_x` gives the
`𝒪_D`-linear Weil pairing on `T_I A`, an alternating perfect pairing

  `T_I A × T_I A → 𝔡_D⁻¹ ⊗_{𝒪_D} 𝒪_{D,I}(1)`

which is `Γ_F`-equivariant with the Galois action on the target through
the cyclotomic character alone (`Γ_F` acts trivially on the inverse
different, which is a module of the base ring). Since `T_I A` is free
of rank two over `O`, the pairing identifies `∧²_O T_I A` with a free
rank-one `O`-module on which `Γ_F` acts by `χ_cyc`, and the determinant
of an endomorphism of a rank-two free module is its action on the
second exterior power. Hence `det ∘ τ = χ_cyc`.

FAITHFULNESS. This is stated for a GIVEN frame, which the docstring of
`exists_tateFrame_of_levelStructure` warns is FALSE without the
real-multiplication tie: for a merely additive and `Γ_F`-equivariant
frame the `O`-structure transported to `T` is an arbitrary embedding
`O ↪ End_{ℤ_q[Γ_F]}(T)`, and when that commutant is larger than
`𝒪_{D,I}` — `T ⊗ ℚ_q = χ₁ ⊕ χ₂` with `𝒪_{D,I}/ℤ_q` carrying a
nontrivial automorphism `ψ`, so that `a ∗ (u₁, u₂) := (a u₁, ψ(a) u₂)`
is a second free rank-two structure — the determinant becomes
`χ₁ · ψ⁻¹(χ₂)` instead of `χ₁ · χ₂ = χ_cyc`. That is why the whole of
`j`, `hφj`, `hcplt`, `hdense` and `hker` are hypotheses here and not
just decoration: together they say that `j` is injective with `𝒪_D`
`I`-adically dense in `O`, and that the `O`-action on `T` extends
`m.act` — which forces `O = 𝒪_{D,I}` acting canonically, and kills the
exotic frames. Do not weaken them.

No exceptional set appears: this is an identity of characters on the
whole of `Γ_F`, ramified places included. The finite bad set of the
consumer comes only from evaluating `χ_cyc` at a Frobenius, which is
possible exactly away from `q`
(`cyclotomicCharacter_adicArithFrob_absNorm`). -/
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
    ∀ σ : Field.absoluteGaloisGroup F,
      LinearMap.det (τ σ) =
        algebraMap ℤ_[q] O
          ((cyclotomicCharacter (AlgebraicClosure ℚ) q
            ((Field.absoluteGaloisGroup.map (algebraMap ℚ F) σ).toRingEquiv) :
              ℤ_[q]ˣ) : ℤ_[q]) :=
  sorry

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

/-- **The Frobenius characteristic polynomials of the Tate modules form
one `D`-rational compatible system** (sorry node — item 9 of the
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
  last clause is exactly the falsity refuted below.**
* The embeddings `ψ` of `D` and `ι` of `O` into `ℚ̄_q` are likewise
  produced per `I` (they are the place of `D` over `q` determined by
  `I`, and the structural embedding of the completion), whereas `P` is
  not; `ι` is required injective, which is the statement that `O` is a
  domain of characteristic zero — the Carayol normalization of the
  coefficients. **`O` being a domain is not a consequence of any
  hypothesis here**; see the audit.

## FAITHFULNESS AUDIT (2026-07-26) — THIS LEAF IS FALSE AS STATED

Two independent explicit counterexamples are given below. **Do not
dispatch a prover at this statement**: it cannot be proven, and anything
derived from it is worthless. The repair is a CUT-LEVEL change spanning
three declarations with three different owners and is described at the
end; it is REPORTED, not made here, because the frame is produced by the
sibling `exists_tateFrame_of_levelStructure` (another owner, working
concurrently) and consumed by the PROVEN assembly
`nonempty_hilbertBlumenthalPoint_of_isTwistedHilbertBlumenthalModuli`
(`Modularity/KhareWintenberger.lean`), whose `HilbertBlumenthalPoint`
fields `ιO₀_injective` / `ιC_injective` and `matchℓ` / `matchp` are
exactly the two clauses refuted. Changing this statement in isolation
turns a false leaf into a hard build error, which is worse.

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

### Counterexample 1 — `Function.Injective ι` fails

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
the `T₁₃E` factor, is `O`-linear. So `(O, τ, φ)` is a legal frame — and
note it even satisfies everything the sibling leaf produces (`O` is
LOCAL, finite free over `ℤ₁₃`, with its module topology). But `O` has a
nonzero nilpotent, so **there is no injective ring homomorphism
`O →+* AlgebraicClosure ℚ₁₃` at all**, and the conclusion fails outright.

### Counterexample 2 — the charpoly equation itself fails

This one is the serious one: it survives any strengthening of `O` short
of tying the frame to `𝒪_D`, and it shows the defect is not about `ι`.

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

### The repair (REPORTED, not made here)

Pin the frame to the real multiplication. Concretely, add to THIS leaf a
ring homomorphism together with the intertwining it must satisfy,

    (j : NumberField.RingOfIntegers D →+* O)
    (hj : ∀ (a : NumberField.RingOfIntegers D) (u : Fin 2 → O) (n : ℕ),
            (φ (j a • u)).1 n = m.act a ((φ u).1 n))

as further hypotheses of the innermost `∀`. This is exactly the
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

The seam therefore needs three coordinated edits, none of which is this
declaration's owner's to make alone:

1. `exists_tateFrame_of_levelStructure` must additionally PRODUCE `j`
   and `hj`. This is free for its author: it constructs
   `O = 𝒪_{D,I}` and `φ` from the `I`-adic Tate module, so `j` is the
   structural map.
2. This leaf takes `j`, `hj` as hypotheses (as displayed above).
3. `nonempty_hilbertBlumenthalPoint_of_isTwistedHilbertBlumenthalModuli`
   threads them through its two `obtain`s.

Until (1) lands, adding (2) alone would break (3), so the statement is
left untouched and the falsity is recorded here instead. The sibling
`exists_tateFrame_of_levelStructure` is NOT itself false — the honest
`I`-adic Tate module does frame it — it is merely too weak, and that
weakness is what this leaf inherited. -/
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
        (τ : GaloisRep F O (Fin 2 → O)) (φ : (Fin 2 → O) → TatePt m x I π),
        (∀ (u u' : Fin 2 → O) (n : ℕ),
          (φ (u + u')).1 n = ab.add ((φ u).1 n) ((φ u').1 n)) →
        Function.Bijective φ →
        (∀ (σ : Field.absoluteGaloisGroup F) (u : Fin 2 → O) (n : ℕ),
          (φ (τ σ u)).1 n = ab.galSMul x σ ((φ u).1 n)) →
        ∃ (bad : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
          (ψ : D →+* AlgebraicClosure ℚ_[q]) (ι : O →+* AlgebraicClosure ℚ_[q]),
          Function.Injective ι ∧
          ∀ w ∉ bad, (τ.charFrob w).map ι = (P w).map ψ :=
  sorry

end Fermat
