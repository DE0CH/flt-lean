/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Continuous actions on discrete modules

The typeclass `ContinuousSMulDiscrete G M`, expressing that a `G`-action on
a (potentially untopologized) `M` is *discretely continuous*: every stabiliser
is open. Equivalent to `ContinuousSMul` once `M` is given the discrete topology.

Material destined for Mathlib.
-/

@[expose] public section

variable {G M : Type*} [TopologicalSpace G] [SMul G M]

/--
`ContinuousSMulDiscrete G M` means that the action `G × M → M` is continuous
when `M` is given the discrete topology (See `continuousSMulDiscrete_iff`).

This class is especially useful when `M` already has another topology and we cannot easily put the
discrete topology on it.
-/
class ContinuousSMulDiscrete (G M : Type*) [TopologicalSpace G] [SMul G M] : Prop where
  isOpen_smul_eq (G) (x y : M) : IsOpen { g : G | g • x = y }

lemma continuousSMulDiscrete_iff [TopologicalSpace M] [DiscreteTopology M] :
    ContinuousSMulDiscrete G M ↔ ContinuousSMul G M := by
  refine ⟨fun H ↦ ⟨continuous_discrete_rng.mpr fun y ↦ ?_⟩, fun H ↦ ⟨fun x y ↦ ?_⟩⟩
  · convert_to IsOpen (⋃ x, { g : G | g • x = y } ×ˢ {x})
    · ext; simp
    · exact isOpen_iUnion fun _ ↦
        .prod (ContinuousSMulDiscrete.isOpen_smul_eq _ _ _) (isOpen_discrete _)
  · exact ((isOpen_discrete {y}).preimage continuous_smul).preimage (Continuous.prodMk_left x)

instance (priority := low) [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMulDiscrete G M] : ContinuousSMul G M := by
  rwa [← continuousSMulDiscrete_iff]



