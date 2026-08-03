## A DOCSTRING'S "MISSING PIECE" LIST IS ABOUT ABSENCE — GREP THE IMPORT CONE BEFORE BELIEVING IT

(2026-07-31, `flt-lean-109`.) `isMultiplicativeType_corner_of_connected_of_inertiaLevelOneFlag`'s
docstring named exactly one obstruction and told the next owner what to do about it: *"The missing
formal piece is the 'precomposition with a surjective bialgebra map is a monoid hom on points'
lemma; `AlgHom.comp_convMul_distrib` is the POST-composition analogue and is the model to copy.
Whoever writes it should state it as its own named leaf."* Precise, actionable, and **wrong in both
directions**:

* mathlib already has the precomposition lemma — `AlgHom.convMul_comp_bialgHom_distrib`, sitting
  four lines above the postcomposition one the docstring cites as the model;
* and this project had ALREADY wrapped it for its own bare-hom convolution monoid five days
  earlier, as `algHom_convMul_comp_bialgHom` / `algHom_convOne_comp_bialgHom` in
  `Deformations/RepresentationTheory/FlatPointsGroup.lean` — reachable from the file in question
  through its own `public import` of `Modularity/Interface.lean`.

This is the same failure the memory `flt-inventory-audits-understate-what-exists` records, one
level up: an audit is reliable about *what the argument needs* and unreliable about *what exists*.
The docstring writer searched for the shape they expected to write and did not search the tree.

The check is two greps and it is worth running against EVERY "missing"/"unwritten"/"needs a new
lemma" claim before you write a line:

    grep -rn '<the mathlib-ish name>' .lake/packages/mathlib/Mathlib/ | head
    grep -rn '<the concept, 2-3 spellings>' --include=*.lean Fermat/ | head

and when the docstring names a "model to copy", **read the model's file** — the analogue you want
is usually its neighbour.

Second half of the same lesson, and it cuts the other way: the docstring ALSO described the
remaining step as bookkeeping (*"intersecting the ambient flag with the image gives an
inertia-stable chain"*). That one was harder than advertised — `AddSubmonoid.comap` of a one-step
extension is not a one-step extension on the nose, and the proof needs the primality of `p` (via
`ZMod p` being a field) or else a maximal-order choice of generator. It came to ~120 lines against
the ~25 of the bijective transport beside it. **So a docstring's difficulty estimates are
hypotheses in both directions: the "missing" piece was already written, and the "bookkeeping" piece
was the real work.** Cost of not checking: one leaf re-proven, one leaf under-budgeted.

