## A NAME YOU ADD UPSTREAM CAN BREAK A DOWNSTREAM MODULE THAT `open`s YOUR NAMESPACE — AND YOUR OWN BUILD IS GREEN
(2026-07-31, `flt-lean-175`, caught one command before committing.) The standing
duplicate-declaration checks are about a name declared TWICE. There is a cheaper defect that
none of them sees and that a green build of your own module cannot: **you add a new name to an
upstream module, and a downstream module that `open`s your namespace already has that name.**
Nothing is declared twice, nothing collides in your file, and the failure appears only when the
DOWNSTREAM module is elaborated — as an ambiguity at ITS call sites, in code neither you nor its
author touched.
Concretely: `BinaryQuadraticForm.lean` gained a `formPoint`/`coe_formPoint` dictionary for the
class equation. `FreyCurve/MazurTorsion.lean` — which `public import`s it and whose
`FormPointDictionary` section opens `Fermat.BinaryQuadraticForm.Heegner` — has had a `formPoint`
and a `coe_formPoint` of its own since it cut the CM-`j`-invariant cluster. Every unqualified
`formPoint f hf` in those 300 lines would have become an overload.
**So the check before you commit a new declaration is not "is this name declared elsewhere in
my file" but a tree-wide grep for the BARE name:**
    grep -rn "^\(theorem\|lemma\|noncomputable def\|def\) <name>\b" Fermat/ --include=*.lean
A hit in a module that imports yours is a collision even though the qualified names differ.
The cheap repair is to RENAME YOURS (`posDefPoint` here) — renaming theirs edits a live
cluster's call sites for your convenience, which is the wrong direction.
**And read the hit before renaming, because it is usually telling you something bigger.** Two
things fell out of that one grep:
* the downstream twin was the RICHER one (uniqueness in `ℍ`, injectivity at fixed discriminant,
  `SL₂(ℤ)`-equivariance) and could not be cited, being downstream — the standing
  "missing machinery may be DOWNSTREAM" situation. The disposition that costs nothing now is to
  **align the two bodies so a later consolidation is mechanical** (here `formPoint f hf` and
  `posDefPoint f` differ by `dif_pos hf` after unfolding), say so in the docstring, and queue
  the hoist rather than doing it inside a 26 000-line file with a live owner;
* the same cluster's OPEN LEAF `exists_smul_eq_of_jInvariant_eq` (`j` separates `SL₂(ℤ)`-orbits)
  was exactly the input I had just costed, in my own leaf's docstring, as "absent from the pin,
  needs the valence formula". It is absent from the PIN and present in the PROJECT as a named
  leaf. **A costing paragraph that greps mathlib and stops is half the search** — and the half
  it skips is the half that changes the verdict, because a leaf another cluster already owes is
  shared, not new.
