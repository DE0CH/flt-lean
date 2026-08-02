/-
NumberField/MixedSpaceThetaTransport.lean — own work for the Fermat project.

# The lattice theta law on the Euclidean mixed space of a number field

This file carries the `ZLattice` Poisson/theta transformation law
(`zlattice_theta_transform`, PROVEN in `ZLatticePoisson.lean` and passed around as the
hypothesis `hθ`) from the universe `Type`, where it is stated, to the Euclidean mixed
space `NumberField.mixedEmbedding.euclidean.mixedSpace K`, where the consumer
`heckeIdealTheta_functionalEquation_of_traceForm` needs it; and it then feeds it the
trace-form bridge of `MixedSpaceTraceForm.lean` to obtain the theta functional equation
relating the ideal lattice of a fractional ideal `I` to that of its trace-dual
`dualIdeal K I = (I·𝔡_K)⁻¹`.

## Why the transport is needed at all

`hθ` quantifies over `E : Type` — universe `0` — because that is the generality in which
the Poisson law was proved.  `euclidean.mixedSpace K` lives in `K`'s universe, so `hθ`
**cannot be applied to it directly**; that obstruction is recorded in the docstring of
the consumer and was, until this file, the reason the geometric route could not even be
started.  `thetaLaw_univLift` removes it once and for all: the law is invariant under a
linear ISOMETRY, and `(stdOrthonormalBasis ℝ E).repr` is one from any finite-dimensional
real inner product space to `EuclideanSpace ℝ (Fin (finrank ℝ E))`, which IS in `Type`.

Three things have to travel along that isometry and each is a lemma here:

* the two theta sums — `tsum_comap_norm`, because an isometry preserves norms;
* the covolume — `ZLattice.covolume_comap`, since a linear isometry equivalence between
  finite-dimensional inner product spaces is measure preserving;
* the `ℤ`-DUAL — `dualSubmodule_comap`.  This is the only one with any content, and it is
  three lines: `⟪e x, y⟫ = ⟪x, e.symm y⟫`, so `x` pairs integrally with the pullback
  lattice exactly when `e x` pairs integrally with the original.

## What comes out

`traceLattice_theta`: for every unit fractional ideal `I` and every `t > 0`,

`Σ_{v ∈ Λ_I} exp(-π t⁻¹‖v‖²) = covol(Λ_I)⁻¹ · t^{n/2} · Σ_{v ∈ Λ_{I∨}} exp(-π t‖v‖²)`

with `Λ_I = traceLattice K I`, `I∨ = dualIdeal K I` and `n = [K:ℚ]`.  This is step 4 of
the route recorded on the consumer ("the anisotropic law"), and it is where sub-leaf (B)
is spent: `TraceFormBridge.2` says the `ℤ`-dual of `Λ_I` is `mixedConj (Λ_{I∨})`, and
`mixedConj` is an ISOMETRY, so `tsum_map_isometry` erases it from the theta sum.  No
analysis of any kind appears in this file.

## What is deliberately NOT here

The covolume is left as `ZLattice.covolume (traceLattice K I)`.  Its value is
`|N(I)|·√|d_K|` — `mixedEmbedding.covolume_idealLattice` gives `N(I)·2^{-r₂}·√|d_K|` for
the unrescaled lattice and the `√2` on the `r₂` complex coordinates contributes
`(√2)^{2r₂} = 2^{r₂}` — and, with `covol(Λ_{I∨}) = 1/(|N(I)|·√|d_K|)` being its exact
reciprocal, that is the source of the functional-equation constant `1`.  Making it
explicit needs a `ZLattice.covolume` analogue of `covolume_comap` for a linear equivalence
that is NOT measure preserving (a `covolume_map` scaling by `|det|`), which the pin does
not have; it is pure measure theory with no arithmetic in it and is queued separately.
-/
module

public import Fermat.FLT.NumberField.MixedSpaceTraceForm
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section

open NumberField NumberField.mixedEmbedding Module MeasureTheory

namespace Fermat.MixedSpaceTrace

/-- The `ZLattice` theta transformation law, in exactly the shape in which
`heckeIdealTheta_functionalEquation_of_traceForm` receives it as the hypothesis `hθ`, and
in which `zlattice_theta_transform` proves it: quantified over `E : Type`. -/
abbrev ThetaLaw : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
      (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
      (t : ℝ), 0 < t →
      ∑' v : L, Real.exp (-Real.pi * t⁻¹ * ‖(v : E)‖ ^ 2) =
        (ZLattice.covolume L)⁻¹ * t ^ ((Module.finrank ℝ E : ℝ) / 2) *
          ∑' w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L,
            Real.exp (-Real.pi * t * ‖(w : E)‖ ^ 2)

/-! ### Transport along a linear isometry -/

section Transport

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The `ℤ`-dual of a lattice pulls back along a linear isometry equivalence.  This is the
only clause of the theta law with content: `⟪e x, y⟫ = ⟪x, e.symm y⟫`. -/
theorem dualSubmodule_comap (e : F ≃ₗᵢ[ℝ] E) (L : Submodule ℤ E) :
    LinearMap.BilinForm.dualSubmodule (innerₗ F)
        (ZLattice.comap ℝ L e.toContinuousLinearEquiv.toLinearMap)
      = ZLattice.comap ℝ (LinearMap.BilinForm.dualSubmodule (innerₗ E) L)
          e.toContinuousLinearEquiv.toLinearMap := by
  have key : ∀ (x : F) (y : E), (innerₗ E) (e x) y = (innerₗ F) x (e.symm y) := by
    intro x y
    have h := e.inner_map_map x (e.symm y)
    rw [LinearIsometryEquiv.apply_symm_apply] at h
    exact h
  ext x
  simp only [ZLattice.comap, Submodule.mem_comap, LinearMap.BilinForm.mem_dualSubmodule,
    LinearMap.restrictScalars_apply]
  refine ⟨fun h y hy => ?_, fun h y hy => ?_⟩
  · show (innerₗ E) (e x) y ∈ (1 : Submodule ℤ ℝ)
    rw [key]
    exact h (e.symm y) (by show e (e.symm y) ∈ L; simpa using hy)
  · have h2 : (innerₗ E) (e x) (e y) ∈ (1 : Submodule ℤ ℝ) := h (e y) (by exact hy)
    rw [key, LinearIsometryEquiv.symm_apply_apply] at h2
    exact h2

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- A tsum of a function of the norm over a lattice is unchanged by pulling the lattice
back along a linear isometry equivalence. -/
theorem tsum_comap_norm (e : F ≃ₗᵢ[ℝ] E) (M : Submodule ℤ E) (g : ℝ → ℝ) :
    ∑' v : ZLattice.comap ℝ M e.toContinuousLinearEquiv.toLinearMap, g ‖(v : F)‖
      = ∑' v : M, g ‖(v : E)‖ := by
  refine (Equiv.tsum_eq
    (ZLattice.comap_equiv ℝ M e.toContinuousLinearEquiv.toLinearEquiv).toEquiv
    (fun v => g ‖(v : F)‖)).symm.trans ?_
  refine tsum_congr fun v => ?_
  congr 1
  show ‖e.symm (v : E)‖ = ‖(v : E)‖
  exact e.symm.norm_map _

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- A tsum of a function of the norm is unchanged by pushing the lattice forward along a
linear isometry of the ambient space.  This is what makes the conjugation `mixedConj` of
`MixedSpaceTraceForm.lean` invisible to a theta sum. -/
theorem tsum_map_isometry (f : E ≃ₗᵢ[ℝ] E) (M : Submodule ℤ E) (g : ℝ → ℝ) :
    ∑' v : Submodule.map (f.toLinearEquiv.restrictScalars ℤ : E →ₗ[ℤ] E) M, g ‖(v : E)‖
      = ∑' v : M, g ‖(v : E)‖ := by
  refine (Equiv.tsum_eq (Submodule.equivMapOfInjective
      ((f.toLinearEquiv.restrictScalars ℤ : E →ₗ[ℤ] E)) f.injective M).toEquiv
      (fun v => g ‖(v : E)‖)).symm.trans ?_
  refine tsum_congr fun v => ?_
  congr 1
  show ‖f (v : E)‖ = ‖(v : E)‖
  exact f.norm_map _

variable [MeasurableSpace E] [BorelSpace E]

/-- **The universe transport, and the end of the obstruction recorded on
`heckeIdealTheta_functionalEquation_of_traceForm`.**  `hθ` is stated for `E : Type`, but
`euclidean.mixedSpace K` lives in `K`'s universe; this moves the law to an ARBITRARY
finite-dimensional real inner product space, by transporting along
`(stdOrthonormalBasis ℝ E).repr`. -/
theorem thetaLaw_univLift (hθ : ThetaLaw)
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (t : ℝ) (ht : 0 < t) :
    ∑' v : L, Real.exp (-Real.pi * t⁻¹ * ‖(v : E)‖ ^ 2) =
      (ZLattice.covolume L)⁻¹ * t ^ ((Module.finrank ℝ E : ℝ) / 2) *
        ∑' w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L,
          Real.exp (-Real.pi * t * ‖(w : E)‖ ^ 2) := by
  set n := Module.finrank ℝ E with hn
  let e : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] E := (stdOrthonormalBasis ℝ E).repr.symm
  have hcov : ZLattice.covolume
      (ZLattice.comap ℝ L e.toContinuousLinearEquiv.toLinearMap) = ZLattice.covolume L :=
    ZLattice.covolume_comap L volume volume (e := e.toContinuousLinearEquiv) e.measurePreserving
  have hrk : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  have key := hθ (EuclideanSpace ℝ (Fin n))
    (ZLattice.comap ℝ L e.toContinuousLinearEquiv.toLinearMap) t ht
  rw [hcov, hrk, dualSubmodule_comap e L,
    tsum_comap_norm e L (fun s => Real.exp (-Real.pi * t⁻¹ * s ^ 2)),
    tsum_comap_norm e (LinearMap.BilinForm.dualSubmodule (innerₗ E) L)
      (fun s => Real.exp (-Real.pi * t * s ^ 2))] at key
  exact key

end Transport

/-! ### The theta functional equation for the trace ideal lattices -/

section IdealLattice

open scoped nonZeroDivisors Classical

variable (K : Type*) [Field K] [NumberField K]

instance instDiscreteTopologyTraceLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    DiscreteTopology (traceLattice K I) :=
  show DiscreteTopology (Submodule.span ℤ (Set.range (traceLatticeBasis K I))) from inferInstance

instance instIsZLatticeTraceLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    IsZLattice ℝ (traceLattice K I) :=
  show IsZLattice ℝ (Submodule.span ℤ (Set.range (traceLatticeBasis K I))) from inferInstance

/-- **The theta functional equation for the trace ideal lattice of a fractional ideal**, and
the place where sub-leaf (B) of `heckeIdealTheta_functionalEquation_of_traceForm` is spent.

`htrace.2` identifies the `ℤ`-dual of `traceLattice K I` — in exactly the
`LinearMap.BilinForm.dualSubmodule (innerₗ _)` sense in which the Poisson law is stated —
with `traceLattice K (dualIdeal K I)` moved by the conjugation isometry `mixedConj`, and
`tsum_map_isometry` erases that isometry from the theta sum.  The universe obstruction is
handled by `thetaLaw_univLift`.

This is step 4 of the route ("the anisotropic law").  On classes it does the right thing:
`dualIdeal K I = (I·𝔡_K)⁻¹` has class `[I]⁻¹·[𝔡_K]⁻¹`, so the class `C = [I]⁻¹` of ideals
being summed over on the left is carried to `[I]·[𝔡_K] = [𝔡_K]·C⁻¹`, which is exactly
`dedekindDualClass K C`. -/
theorem traceLattice_theta (hθ : ThetaLaw) (htrace : TraceFormBridge K)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) (ht : 0 < t) :
    ∑' v : traceLattice K I, Real.exp (-Real.pi * t⁻¹ * ‖(v : euclidean.mixedSpace K)‖ ^ 2) =
      (ZLattice.covolume (traceLattice K I))⁻¹ * t ^ ((Module.finrank ℚ K : ℝ) / 2) *
        ∑' v : traceLattice K (dualIdeal K I),
          Real.exp (-Real.pi * t * ‖(v : euclidean.mixedSpace K)‖ ^ 2) := by
  have key := thetaLaw_univLift hθ (traceLattice K I) t ht
  rw [euclidean.finrank, htrace.2 I,
    tsum_map_isometry (mixedConj K) (traceLattice K (dualIdeal K I))
      (fun s => Real.exp (-Real.pi * t * s ^ 2))] at key
  exact key

/-- **The theta functional equation for the trace ideal lattices, packaged as a `Prop`** so
that a consumer can take it as a hypothesis without having to `open scoped Classical`
itself — exactly as `TraceFormBridge` is packaged, and for the same reason (the `Inner`
instance on `euclidean.mixedSpace K` goes through `Fintype {w // IsReal w}`, which needs a
`DecidablePred`).  It is PROVEN: see `idealLatticeTheta`. -/
def IdealLatticeTheta : Prop :=
  ∀ (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ), 0 < t →
    ∑' v : traceLattice K I, Real.exp (-Real.pi * t⁻¹ * ‖(v : euclidean.mixedSpace K)‖ ^ 2) =
      (ZLattice.covolume (traceLattice K I))⁻¹ * t ^ ((Module.finrank ℚ K : ℝ) / 2) *
        ∑' v : traceLattice K (dualIdeal K I),
          Real.exp (-Real.pi * t * ‖(v : euclidean.mixedSpace K)‖ ^ 2)

/-- **Steps 3 and 4 of Hecke's route are closed.**  The Poisson law `hθ` together with the
metric bridge `htrace` (sub-leaf (B), PROVEN as `traceFormBridge`) give the theta
functional equation for every trace ideal lattice. -/
theorem idealLatticeTheta (hθ : ThetaLaw) (htrace : TraceFormBridge K) :
    IdealLatticeTheta K :=
  fun I t ht => traceLattice_theta K hθ htrace I t ht

end IdealLattice

end Fermat.MixedSpaceTrace
