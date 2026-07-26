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

Two lemmas and one assembly.

* `isIrreducible_map_of_restrictionSurjective`: irreducibility of a
  Galois representation descends along a restriction that preserves the
  image. It is what lets the consumer supply the irreducibility
  hypothesis that the frame leaf needs at `λ` (see the FAITHFULNESS
  AUDIT there — the leaf was FALSE without it).
* `exists_mem_notMem_sq_of_isMaximal`: a nonzero maximal ideal of a
  Dedekind domain contains an element outside its square — the
  uniformizer `π` that `TatePt` is indexed by.
* `exists_tateFrame_of_levelStructure` itself is PROVEN (2026-07-26),
  by assembly over three independent leaves, one per theory:
  `exists_adicCoefficientRing` (commutative algebra: the completion
  `𝒪_{D,I}` as a topological `ℤ_q`-algebra),
  `exists_tateFrame_of_adicCoefficientRing` (abelian varieties: `T_I A`
  is free of rank two over it, equivariantly) and
  `exists_residualEmbedding_of_tateFrame` (representation theory: the
  reduction matches the level structure up to `Aut(k')` — the ONLY
  place `hirr` is used, and the step whose unconditional form was
  refuted).
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
  normalization of Taylor 2002 §2.
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

/-- **The Tate module is free of rank two over the completion**, with a
continuous Galois action extending the real multiplication (sorry node —
abelian varieties; Mumford *Abelian Varieties* §18, Silverman *AEC*
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
docstring there. -/
theorem exists_tateFrame_of_adicCoefficientRing
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (hdim : SmoothOfRelativeDimension (Module.finrank ℚ D) f)
    (I : Ideal (NumberField.RingOfIntegers D)) (hI : I.IsMaximal)
    (π : NumberField.RingOfIntegers D) (hπ : π ∈ I) (hπ2 : π ∉ I ^ 2)
    (O : Type u) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [IsLocalRing O]
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
        (φ (j a • u)).1 n = m.act a ((φ u).1 n) :=
  sorry

/-- **The reduction of a Tate frame matches the level structure, up to an
automorphism of the residue field** (sorry node — representation theory;
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
must establish simplicity of the commutant FIRST. -/
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
        (τ.charFrob w).map ι₀ = ρ'.charFrob w :=
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
`HilbertBlumenthalPoint.detσ`. -/
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
    exists_tateFrame_of_adicCoefficientRing m x hdim I hI π hπ hπ2 O j hcplt hdense hker
  obtain ⟨ι₀, hι₀⟩ :=
    exists_residualEmbedding_of_tateFrame m x I hI π hπ hπ2 O j hker τ φ hφadd hφbij hφequiv
      hφj hV ρ' hirr e headd heinj heequiv heimg
  -- The determinant (Weil-pairing) clause, added 2026-07-26 by another owner
  -- and merged onto this assembly: the `𝒪_D`-linear Weil pairing makes
  -- `∧²_{𝒪_{D,I}} T_I A` the inverse different twisted by `χ_cyc`, so
  -- `det τ = χ_cyc` and `χ_cyc(Frob_w) = Nw` away from the bad places.  It is
  -- a statement about the pairing, which none of the three leaves above sees,
  -- so it is the ONE clause of this conclusion still open.
  have hdet : ∃ bad : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)),
      ∀ w ∉ bad,
        LinearMap.det (τ.toLocal w (Field.AbsoluteGaloisGroup.adicArithFrob w)) =
          (Ideal.absNorm w.asIdeal : O) := sorry
  obtain ⟨bad, hbad⟩ := hdet
  exact ⟨π, hπ, hπ2, O, iCR, iTS, iTR, iAlg, iLoc, iFin, iFree, iMT, τ, φ, ι₀, j, bad,
    hφadd, hφbij, hφequiv, hι₀, hφj, hbad⟩

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
