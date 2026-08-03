## A "WHAT MUST BE BUILT" LIST IS THREE PRICES, NOT ONE — PRICE EACH ITEM AND DISCHARGE THE CHEAP ONE
(2026-07-31, `flt-lean-18`, `exists_fontaineCoordinates_of_not_primeFieldValued` in
`HardlyRamified/ModThree.lean`.)  A mature leaf whose route ends *"WHAT MUST BE BUILT: X,
Y and Z"* reads as one indivisible price, and the reflex — correct, as far as it goes — is
to report the leaf as a chapter and move on.  Three prior passes did exactly that.  **Price
the items SEPARATELY.**  Here item 1 of 3 (*"`W(κ) ⊆ 𝒪_E` as an `𝒪₃ᵥ`-algebra"*) is **60
lines**, and discharging it is a clean `1 → 1` RECUT: the leaf keeps its statement, becomes
two-line glue, and the new leaf differs only by RECEIVING the object item 1 asked for.  The
expensive items are untouched and the next owner is not sent to build a coefficient ring.
**The general shape to look for: an item on such a list that is a CONSTRUCTION rather than
a THEORY.**  A construction can be handed in as a hypothesis; a theory cannot.  Handing it
in costs one recut and no mathematics, and it is worth doing even when the residue stays a
chapter — which it did here.
### The construction: `exists_teichmullerSection`, and why "adjoin everything" is the cheap form
For `R` local, `𝔪`-adically complete, with FINITE residue field `k`, the residue map has a
section by roots of `X ^ q − X` (`q = #k`): `τ : k → R` with `residue (τ y) = y` and
`τ y ^ q = τ y`.  Then `Algebra.adjoin 𝒪 (Set.range τ)` IS the unramified coefficient ring
`W(k) ⊆ R` — finite over the base (finite range of integral elements), surjecting onto `k`.
Two choices make it ~60 lines rather than a fight, and both are copied from this file's own
`Patching.lean` note:
* **`X ^ q − X`, not `X ^ (q−1) − 1`.**  Its derivative reduces to `−1` on the nose
  (`FiniteField.cast_card_eq_zero`), so Hensel's simple-root hypothesis needs no case split
  on whether the point is zero;
* **lift EVERY element, not a multiplicative generator.**  A generator forces
  `Submonoid.powers` / `Subgroup.zpowers` membership bookkeeping — which is recorded there
  as having TIMED OUT in the ambient context of a big file — whereas `choose` over all of
  `k` is one line and `k` being finite is all that is needed.
`HenselianRing R (maximalIdeal R)` comes free from `IsAdicComplete` (instance), and
`HenselianRing.is_henselian` is the form to call: `HenselianLocalRing` is a different class
and mathlib has no instance from the first to the second.
### THE BASE CHANGE GOES ON THE ALGEBRA, NOT ON THE COEFFICIENT RING — and that deletes an obligation
The recorded route said to base-change `A` to `A ⊗ W(κ)` and *also* implied producing a map
`W(κ) → A ⧸ J`.  The second is unnecessary and it was the expensive half: **the tensor
product carries the `W(κ)`-algebra structure by construction**, so the local factor and its
idempotent are produced INSIDE the `W(κ)`-indexed step, never before it.  Nothing has to be
Hensel-lifted into `A`.
What licenses the base change at all is worth stating as a check, because it is the same
one every "change the coefficient ring" route needs: **an unramified base extension does not
move the Hom-sets.**  `𝒲` unramified over `𝒪` makes an `𝒪`-algebra map `𝒲 → 𝒪_E/𝔪^k` over a
fixed residue map UNIQUE, so restriction along `A → A ⊗ 𝒲` is a bijection from `𝒲`-algebra
maps over `ū` to `𝒪`-algebra maps over `ū`.  Every clause of a conclusion phrased in those
Hom-sets then transports verbatim — and here the conclusion's `F` and `p` are arbitrary
FUNCTIONS on `𝒪_E`-tuples rather than power series over the base, which is exactly why the
statement needs no change when the coefficient ring does.  **If a leaf's conclusion mentions
the base ring only through the Hom-sets, a base change is free at the level of the
STATEMENT and costs only the machinery.**
### The obstruction test that says a base change is FORCED
Before costing any of this, confirm the base really must move, and it is one line:
**a surjection `α : R ↠ B` out of a LOCAL ring makes `B` local with residue field a QUOTIENT
of `R`'s.**  `MvPowerSeries (Fin h) 𝒪` is local with residue field `κ(𝒪)`, so presenting `B`
over `𝒪` forces `κ(B) = κ(𝒪)`.  And the obvious dodge fails for a reason worth writing down:
an extra VARIABLE cannot supply the missing residue generator, because a variable is sent
into the maximal ideal while a lift of a generator of `κ(B)` is a UNIT.  What is left is
`W(κ)[[X]] ≅ 𝒪[[X]][Y]/(g)` — `h` variables and `h + 1` equations — which is not the shape a
"`h` equations in `h` variables" presentation records.  So the base change is forced, and
saying so precisely is what stops the next agent looking for a trick.
### Report a `1 → 1` recut as a recut
The direct-sorry count does not move and nothing became provable that was not before.  Say
so in the commit and in the docstring — a `−1 +1` warning-set delta is indistinguishable
from one closure plus one unrelated disclosure — and say which of the route's items is now
discharged, with the others left standing and re-priced.
