/-
Copyright (c) 2026 Duxing Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Duxing Yang
-/
module

public import Fermat.FLT.Slop.PGL2.FiniteSubgroups.TameClassification
public import Fermat.FLT.Slop.PGL2.FiniteSubgroups.WildClassification

/-!
# Dickson's classification of the finite subgroups of `PGL₂(𝔽̄_p)`

The main theorem `Dickson.dickson_classification`: for `p` an odd prime, every finite
subgroup of `PGL₂(𝔽̄_p)` is one of:

* cyclic;
* dihedral of order `2n`, `n ≥ 2`;
* isomorphic to `A₄`, `S₄` or `A₅`;
* a semidirect product of an elementary abelian `p`-group by a cyclic group of order
  prime to `p`;
* isomorphic to `PSL₂(𝔽_{p^m})` or `PGL₂(𝔽_{p^m})` for some `m ≥ 1`.

This is the combination of the tame case (`Dickson.classification_tame_slop`, order
coprime to `p`) and the wild case (`Dickson.classification_wild_slop`, order divisible
by `p`).

This classification (due to Dickson, 1901) is used in the proof of Fermat's Last
Theorem to analyse the image of the mod-`p` Galois representations attached to the
Frey curve.
-/

/- The code in this file was ported from Duxing Yang's `DicksonClassification` project
and does not yet follow the mathlib style conventions enforced by the linters below. -/
set_option linter.style.longLine false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.style.show false
set_option linter.style.openClassical false
set_option linter.style.cdot false
set_option linter.style.multiGoal false
set_option linter.style.refine false
set_option linter.style.induction false
set_option linter.unusedFintypeInType false

@[expose] public section

open scoped Classical

namespace Dickson

variable (p : ℕ) [Fact (Nat.Prime p)] [h_odd : Fact (p > 2)]

end Dickson
