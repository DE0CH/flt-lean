## A "WHAT REMAINS GENUINELY MISSING" PARAGRAPH CAN BE FALSE ABOUT ITS OWN FILE — AND THE THEOREM MAY BE 35 000 LINES BELOW
(2026-08-01, `flt-lean-133`, on `exists_isotypicQuotient_of_isIsotypicHom` in
`ModularCurve/X0.lean`.)  This file already records that an absence audit is a
search result and that missing machinery may be DOWNSTREAM (in a module that
imports yours) or UPSTREAM (in a module you already import).  There is a third
place, it is the one nobody greps, and it produces the most confident wrong
answer of the three: **the same file, tens of thousands of lines further down.**
That leaf's docstring said, in bold, that "there is no image factorisation for
homomorphisms of abelian schemes in this project, none in mathlib at this pin,
and none in `~/cs/FLT`", and prescribed building one.  `X0.lean` PROVES it
TWICE — `exists_surjectiveAbelianImage_of_isAdditiveOn` and
`exists_addSurjectiveAbelianImage_of_isAdditiveOn_aux`, the second stating
exactly the extra additivity clauses the consumer needed — and the single clause
neither exports (`ψ` preserves the image, hence restricts to it) is **twelve
lines** over `exists_factor_of_ker_le`, `ker_comp_of_isSchemeTheoreticallyDominant`
and `IdealSheafData.map_mono`, all of which are also already in the file.  The
node was never mathematics.  It was Lean's declaration order.
**The grep that finds this costs one command and is NOT a grep for a
declaration name** — the theorem you want is named in somebody else's
vocabulary, for somebody else's consumer.  Grep for the CONCEPT across the file
you are already editing, before believing any absence claim in it:
    grep -n '<concept>\|<the mathlib primitive it would be built on>' <your own file>
Here `grep -n 'toImage\|Hom.image\|abelianImage' X0.lean` returns the whole
development in one screen, including a subsection header that says in prose
"the image of a homomorphism of abelian varieties is an abelian subvariety, one
theorem".
### MEASURE BOTH RELOCATION DIRECTIONS BEFORE CHOOSING ONE — the numbers decide it, and they are two scripts
Once a leaf is known to be declaration-order, the repair is a move, and there
are exactly two candidates.  Both are computable from a comment-stripped scan
that attributes every token to its enclosing declaration (walk backwards to the
nearest declaration header — never forwards):
* **the CONSUMER CLOSURE** of the leaf, intersected with the declarations above
  the machinery: that is what a *move down* costs.  Here 47 declarations, of
  which **12** sit above the machinery and would have to travel 35 000 lines;
* **the PRODUCER CONE** of the machinery, intersected with the declarations
  below the leaf: that is what a *hoist* costs.  Here **54** declarations — and,
  decisively, they turned out to be essentially CONTIGUOUS (a single ~2 100-line
  band), and nothing in the band depends on anything between the leaf and the
  band, which is exactly the hoist's legality condition.
So the two numbers were 12 scattered over 35 000 lines against 54 in one band,
and the band wins.  **Neither number is guessable** — this file's own docstrings
had priced the same move twice, in prose, without either.  Compute them; the
scan is thirty lines of Python and runs in under a minute if you index
`token -> enclosing declaration` ONCE rather than re-scanning per name (the
naive quadratic version does not finish).
**And there is usually a third option that beats both: extract the machinery
into its own module.**  The producer cone's dependencies that lie ABOVE the leaf
are the real cost of an extraction, and here that was 20 declarations
(`SpecQ`, `RelPoint.post`, `IsAdditiveOn` and neighbours) out of 74.  A hoist
relieves the ordering constraint once; a module removes it permanently, and a
new module cannot conflict with anything.
### DO NOT LAND A PROVEN TWIN OF A DECLARATION-ORDER LEAF
The tempting move, once you know the leaf is provable further down, is to prove
it there under another name so the file "contains the proof".  That declaration
has no consumer — the leaf's consumers are all above it — so it is FREE-FLOATING
CODE, which this project forbids, and a statement-level duplicate scan will
flag it against the leaf.  **Put the verified proof text in the leaf's
docstring instead**, say where it was checked and against what, and queue the
relocation.  A machine-checked proof recorded in a docstring is a handoff; the
same proof landed as an unconsumed declaration is a defect.
### `fun n p q => …` DOES NOT AUTO-BIND IMPLICITS AFTER AN EXPLICIT ONE
Two of the three errors in the first draft of that assembly were this, and the
message names the wrong thing.  Against an expected type
`∀ (n : ℕ) {T : Scheme} {g : T ⟶ S} (p q : RelPoint bf g), …`, the term
`fun n p q => w.S_add n p q` binds `p` to the IMPLICIT `T`, and the error reads
    Application type mismatch: the argument p has type Scheme of sort `Type 1`
    but is expected to have type RelPoint w.bstr ?m of sort `Type`
which looks like a unification failure in `S_add`.  Write the `have` in tactic
mode and `intro` every binder including the implicits.  Same shape bit again on
a five-binder naturality `have`.  Whenever a `have` whose type interleaves
explicit and implicit binders is proven by a bare `fun`, use `by intro …` instead.
