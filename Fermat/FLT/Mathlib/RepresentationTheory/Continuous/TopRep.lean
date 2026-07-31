/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie, Claude
-/
module

public import Mathlib.RepresentationTheory.Continuous.TopRep
public import Fermat.FLT.Mathlib.RepresentationTheory.Continuous.Basic

/-!
# The internal hom of topological representations

Vendored VERBATIM from `~/cs/FLT`, file
`FLT/Mathlib/RepresentationTheory/Continuous/TopRep.lean` (author Edison Xie); absent from our
mathlib pin `a3364fa` (re-checked 2026-07-31).

Material destined for `Mathlib.RepresentationTheory.Continuous.TopRep`.
-/

@[expose] public section

universe u v

open ContinuousLinearMap.CompactOpen

namespace TopRep

variable {k : Type u} {G : Type v} [CommRing k] [TopologicalSpace k] [Group G]

/-- The internal hom of two topological representations: the topological representation on the
space of continuous linear maps `A →L[k] B`, with `G` acting by conjugation. -/
abbrev iHom (A B : TopRep k G) : TopRep k G := TopRep.of (ContRepresentation.linHom A.ρ B.ρ)

end TopRep
