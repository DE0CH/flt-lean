/-
Mathlib/AlgebraicGeometry/ReducedClosedSubscheme.lean — own work for the Fermat
project (not vendored from the FLT project).

# Factoring a morphism through a REDUCED closed subscheme

The pin carries the whole ideal-sheaf apparatus a closed subscheme needs —
`AlgebraicGeometry.Scheme.IdealSheafData`, its `support`/`vanishingIdeal`
Galois connection, `Scheme.Hom.ker`, `Scheme.Hom.support_ker` and
`AlgebraicGeometry.IsClosedImmersion.lift` — and it does NOT carry the one
statement every consumer of them wants:

> a morphism out of a REDUCED scheme whose image lands in a REDUCED closed
> subscheme factors through that subscheme,

i.e. that for reduced schemes the scheme-theoretic containment `ι.ker ≤ g.ker`
which `IsClosedImmersion.lift` demands is implied by the purely TOPOLOGICAL
containment `Set.range g.base ⊆ Set.range ι.base`.  That is
`exists_lift_of_range_subset` below, and it is what this module exists for.

The route is the standard one and needs exactly one fact that the pin does not
state: the kernel of a quasi-compact morphism out of a reduced scheme is a
RADICAL ideal sheaf (`Scheme.Hom.radical_ker`).  Given that, the Galois
connection does the rest, since `vanishingIdeal I.support = I.radical`.

## Where this was wanted before

`ModularCurve/X0.lean`'s "ROUTE AUDIT, 2026-07-27" on leaf (iii-b) of
`exists_addHom_factor_zmulPts` describes this argument in prose, correctly and
in detail — *"Both kernels are radical because their sources are reduced, so by
`Scheme.Hom.support_ker` and `Scheme.IdealSheafData.vanishingIdeal` (antitone)
the target follows from `Set.range … ⊆ closure (Set.range d)`"* — as its
"Route 2", and never writes it down; the leaf was ultimately closed by a
different, pointwise route, and the audit is marked SUPERSEDED.  So this is the
first time the route is a theorem rather than a paragraph.  A successor working
in that file, or on any other "the image lies in the subscheme, so the morphism
does" obligation, should cite `exists_lift_of_range_subset` rather than
re-deriving it.

## What is deliberately NOT here

No REDUCED-INDUCED-STRUCTURE constructor.  `Scheme.IdealSheafData.vanishingIdeal
Z` together with `IdealSheafData.subscheme` already IS that construction in the
pin, and `range_subschemeι`/`ker_subschemeι` are its API; a wrapper would add
nothing.  What was missing is only the universal property against reduced test
objects, which is what is proved here.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {X Y B : Scheme.{u}}

/-- **The kernel of a ring map into a REDUCED ring is radical.**  The
scheme-level `Scheme.Hom.radical_ker` is this, component by component. -/
theorem RingHom.radical_ker_eq_of_isReduced (R S : Type*) [CommRing R] [CommRing S]
    [_root_.IsReduced S] (φ : R →+* S) :
    (RingHom.ker φ).radical = RingHom.ker φ := by
  refine le_antisymm ?_ Ideal.le_radical
  intro x hx
  obtain ⟨n, hn⟩ := hx
  simp only [RingHom.mem_ker] at hn ⊢
  rw [map_pow] at hn
  exact _root_.IsReduced.eq_zero _ ⟨n, hn⟩

/-- **The kernel of a quasi-compact morphism out of a REDUCED scheme is a
RADICAL ideal sheaf.**

Quasi-compactness is what makes `Scheme.Hom.ker_apply` available, i.e. what
makes `f.ker` component-wise the honest ring-theoretic kernel; without it
`Hom.ker` is only the largest quasi-coherent ideal sheaf below those kernels
and the statement is not expected to hold. -/
theorem Scheme.Hom.radical_ker (f : X ⟶ Y) [QuasiCompact f] [IsReduced X] :
    f.ker.radical = f.ker := by
  ext U : 2
  rw [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
  haveI : _root_.IsReduced Γ(X, f ⁻¹ᵁ U.1) := IsReduced.component_reduced _
  exact RingHom.radical_ker_eq_of_isReduced _ _ (f.app U.1).hom

/-- **A morphism out of a REDUCED scheme whose image lies inside a REDUCED
closed subscheme factors through it** — the universal property of the reduced
induced structure, in the form a consumer actually meets it.

The hypothesis is TOPOLOGICAL (`Set.range g.base ⊆ Set.range ι.base`) where
`IsClosedImmersion.lift` asks for the scheme-theoretic `ι.ker ≤ g.ker`; the two
agree because both kernels are radical (`Scheme.Hom.radical_ker`, using that
both sources are reduced) and `vanishingIdeal` is antitone with
`vanishingIdeal I.support = I.radical`.

Both reducedness hypotheses are load-bearing and neither can be dropped:

* drop `IsReduced Y` and take `Y = Spec k[ε]/(ε²) ⟶ X = 𝔸¹_k` the tangent
  vector at the origin, `ι` the origin: the range is the origin, contained in
  `Set.range ι.base`, and the morphism does not factor through `Spec k`;
* drop `IsReduced B` and take `X = 𝔸¹_k`, `B = Spec k[ε]/(ε²)` the origin with
  its doubled structure, `Y = X`, `g = 𝟙`: the ranges are not comparable, so
  the honest witness is `Y = Spec k` the origin and `ι` the SAME doubled
  origin — `g` factors, but through a DIFFERENT scheme; what fails in general
  is that `ι.ker` is then not radical, so a `g` whose kernel is the radical of
  `ι.ker` has `ι.ker ≰ g.ker`. Concretely `X = 𝔸¹`, `B = Spec k[x]/(x²)`,
  `Y = Spec k[x]/(x)`: `Set.range g.base = Set.range ι.base = {0}` and there is
  no `Y ⟶ B` over `X` unless one composes the other way.

`QuasiCompact g` is not a restriction in practice: it is automatic whenever `Y`
is quasi-compact and `X` is quasi-separated
(`AlgebraicGeometry.quasiCompact_of_compactSpace`), which covers every source
of finite type over a field. -/
theorem exists_lift_of_range_subset (ι : B ⟶ X) (g : Y ⟶ X)
    [IsClosedImmersion ι] [IsReduced B] [QuasiCompact g] [IsReduced Y]
    (h : Set.range g.base ⊆ Set.range ι.base) :
    ∃ l : Y ⟶ B, l ≫ ι = g := by
  have hker : ι.ker ≤ g.ker := by
    have h1' : (g.ker.support : Set X) ⊆ (ι.ker.support : Set X) := by
      rw [Scheme.Hom.support_ker, Scheme.Hom.support_ker]
      exact closure_mono h
    have h1 : g.ker.support ≤ ι.ker.support := h1'
    have h2 := Scheme.IdealSheafData.vanishingIdeal_antimono h1
    rwa [Scheme.IdealSheafData.vanishingIdeal_support,
      Scheme.IdealSheafData.vanishingIdeal_support, Scheme.Hom.radical_ker,
      Scheme.Hom.radical_ker] at h2
  exact ⟨IsClosedImmersion.lift ι g hker, IsClosedImmersion.lift_fac ι g hker⟩

-- The lift is UNIQUE, a closed immersion being a monomorphism, but that needs no
-- declaration here: it is `(cancel_mono ι).1` verbatim, and a named wrapper for
-- it would be free-floating code.

end AlgebraicGeometry
