/-
Copyright (c) 2025 Bryan Wang Peng Jun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang Peng Jun
-/
module

public import Fermat.FLT.Mathlib.MeasureTheory.Constructions.BorelSpace.InfinitePlace
public import Fermat.FLT.Mathlib.MeasureTheory.Constructions.BorelSpace.FiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.AdeleRing
import Fermat.FLT.Mathlib.NumberTheory.NumberField.InfiniteAdeleRing

/-!
# Adele Ring

Material destined for Mathlib.
-/

@[expose] public section

variable (K : Type*) [Field K] [NumberField K]

open NumberField

instance : MeasurableSpace (AdeleRing (𝓞 K) K) := inferInstanceAs (MeasurableSpace (_ × _))

instance : BorelSpace (AdeleRing (𝓞 K) K) := inferInstanceAs (BorelSpace (_ × _))
