/-
Copyright (c) 2026 Duxing Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Duxing Yang
-/
module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-!
# Definitions for Dickson's classification in `PGL₂`

VENDORING CHANGE (2026-07-16, Fermat project): upstream keeps these
definitions together with sorry-d statements in `Defs.lean` and proves
copies in `Proofs.lean`. Here the definitions are split into this
`Basic.lean` (imported by the `Slop` development) so that the statements
in `Defs.lean` can carry their proofs directly without an import cycle.
-/

@[expose] public section

namespace Dickson

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- An algebraic closure `K p` of the finite field `𝔽_p = ZMod p`. -/
noncomputable abbrev K : Type := AlgebraicClosure (ZMod p)

/-- The projective general linear group `PGL₂(K p)`, i.e. `GL₂(K p)` modulo its centre. -/
abbrev PGL : Type := Matrix.ProjGenLinGroup (Fin 2) (K p)

/-- The projective special linear group `PSL₂(K p)`. -/
abbrev PSL : Type := Matrix.ProjectiveSpecialLinearGroup (Fin 2) (K p)

end Dickson
