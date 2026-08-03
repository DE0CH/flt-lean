## A CIRCULARITY GUARD MAKES A GREP-FOUND DECLARATION UNCITEABLE — and then COPYING IS the right answer
(Same task.)  The standing advice on an "X is not in the tree" obligation is to grep
before writing anything, because it usually already exists under another name.  It did:
the task's named obligation — the `ℓ`-adic cyclotomic character as a CONTINUOUS
character — is `cycUnitChar` / `continuous_cycUnitChar` in
`HardlyRamified/Family.lean`, four declarations, exactly the wanted content.
**And it could not be used.**  `Deformation.lean`'s import header carries an explicit
`CIRCULARITY GUARD: no import from Family.lean`, because `Family.lean` imports
`Modularity/Interface.lean`.  So the grep SUCCEEDED and the answer was still "write it".
Two things follow, and the first is the one that saves the time:
* **After the grep hits, check the import DIRECTION and the target's own import
  header for a guard, before deciding what the hit means.**  A hit has three possible
  readings — usable, usable-after-an-import, and unciteable-by-policy — and only the
  third obliges you to write anything.  Reading the header is one `sed`; the guard in
  this development is always stated in prose at the top of the module, never inferable
  from the import list alone (the forbidden import is by construction absent).
* **When it is the third, copy DELIBERATELY and say so**, with three facts in the
  docstring: that it is a copy, which declaration it copies, and **which of the two
  should be deleted if the guard is ever lifted** (here: this one, `cycUnitChar` being
  older and having more consumers).  A copy without that sentence is indistinguishable
  from a duplicate cut to `dupstmt.py` and to the next reader, and the deletion
  decision — which is an author's — gets rediscovered instead of inherited.
Corollary worth separating: the obligation's SECOND half here (`Continuous (algebraMap
ℤ_[ℓ] R)` for the adic topology) existed too, but as **twenty lines inside the body of
`isModuleTopology_of_isAdic_maximalIdeal`**, 9 000 lines below and unciteable for that
reason as well.  Hoisting it out with `ℓ ∈ 𝔪` as a hypothesis — rather than re-deriving
that step, which is long there because it has no residue map to use — cost nothing and
is the "a fact proven inside a body that exports something else" shape this file already
records.  **Grep the BODIES, not only the statements, and expect the hoisted version to
want a hypothesis the original derived inline.**
