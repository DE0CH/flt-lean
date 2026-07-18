/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Kevin Buzzard
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Group.Action.Hom

/-!
# Algebra structures on equivariant homs
-/

@[expose] public section





instance {R S T G : Type*} [CommSemiring R] [Semiring S] [Semiring T] [Algebra R S] [Algebra R T]
    [Monoid G] [MulSemiringAction G T] [SMulCommClass G R T] : MulAction G (S →ₐ[R] T) where
  smul g := (MulSemiringAction.toAlgHom _ _ g).comp
  one_smul f := by ext x; exact one_smul G (f x)
  mul_smul g g' f := by ext x; exact mul_smul g g' (f x)



