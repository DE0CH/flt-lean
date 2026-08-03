## A FILE THAT NAMES ITS OWN FOLLOW-UP HAS ALREADY DONE THE CUT — grep for the SPELLING, then check whether its precondition has landed
(2026-08-01, `flt-lean-180`, on `exists_isotypicHom_of_isWeightTwoEigenformOn_gamma1`.)
The `Γ₁` Eichler–Shimura non-vanishing leaf was dispatched as "decompose it, and share
machinery with the `Γ₀` side rather than mirroring it". The decomposition was already
written down — **as a sentence, with the successor declaration's exact name in it**, in a
DIFFERENT leaf's docstring 1200 lines below:
> The tidy follow-up, once that branch is on `main`, is to split
> `exists_isotypicQuotientFamily_finiteKer_gamma1` along the same seam
> (`exists_universalIsotypicQuotient_gamma1` plus a shared joint-kernel statement) and
> reuse the structure.
Its precondition ("once that branch is on `main`") had been satisfied in the meantime, and
nothing re-reads a blocked-follow-up note when the thing it waits on lands. So the run
reduced to: confirm the precondition (`git show main:X0.lean | grep IsUniversalIsotypicQuotient`),
take the predicted name, and write the bridge.
**So add to the first ten minutes of any decomposition task: grep the WHOLE file for a name
that does not exist yet.** A `grep -o '[a-z][A-Za-z_]*_gamma1' <file> | sort -u` against the
declared names finds every such promise at once. The phrases that carry them here are "the
tidy follow-up", "once that branch is on `main`", "is deliberately NOT done in the edit
that lands", "a further refactor and is not done here" — all of which read as *closed* and
are in fact *queued with an expiry date nobody watches*. Same family as
[[flt-expired-prohibition-is-a-magnet]], with the note pointing forward instead of back.
### The finding underneath it: TWO RIVAL CUTS OF ONE NODE, BOTH OPEN, BOTH CONSUMED, IN ONE FILE
`X0.lean` carries `exists_isotypicHom_of_isWeightTwoEigenform` (58209) **and**
`exists_universalIsotypicQuotient` (58398). Same hypotheses; the second's conclusion implies
the first's modulo a shape-free bridge. Both are `sorry`, and — this is why no scan sees it —
**both have live consumers**, so neither is an orphan and the frontier honestly counts two.
`dupstmt.py` cannot pair them (different conclusions), `xdup.py` cannot (different names).
The tell was that two sibling assemblies 190 lines apart reach the same
`IsIsotypicQuotient` by different routes; the check is to read the two PROOF BODIES.
**When you find such a pair, keep the one whose conclusion is STRONGER and bridge down** —
that is CLAUDE.md's standing rule ("keep the arrangement whose root leaf is IMPLIED by the
rival's root") applied to a pair that is not textually duplicated at all.
**And check the arity quantifier before calling the stronger form a harder obligation.** Here
`IsIsotypicHom.equivariant` is at EVERY arity while the Hecke pin constrains only the arities
coprime to `N`, and the file's own analysis says the isotypic image must therefore be chosen
MAXIMAL. So every producer of the weaker statement builds the stronger object anyway: the
recut is free, and a "this restatement is accidentally stronger" objection does not apply.
Say that in the commit, because the objection is the right reflex and a reader will have it.
### `pre_zero` NATURALITY TURNS "THIS MORPHISM IS NONZERO" INTO "THIS POINT IS NONZERO"
The one field with content in that bridge, and the technique generalises to any
functor-of-points abelian scheme in this development. To get *the homomorphism `u : J ⟶ A`
is nonzero as a `J`-point of `A`* from *`A` is nontrivial* (its TAUTOLOGICAL point is
nonzero), use that `u` **is** the pullback of the tautological point along `u` itself —
`RelPoint.pre u u_comp ⟨𝟙 A, _⟩ = ⟨u, _⟩` by `Category.comp_id` — plus
`AbelianSchemeStruct.pre_zero`, which says `pre` carries zero to zero. Both sides are then
in the image of `RelPoint.pre u u_comp`, so it suffices that this map be INJECTIVE, and
since `RelPoint` is the subtype `{x : T ⟶ A // x ≫ f = g}` and `pre` is precomposition,
that is exactly `Epi u`. For a surjective homomorphism of abelian schemes over `ℚ` that is
free: `flat_of_surjective_of_isAdditiveOn` (PROVEN, `X0.lean:89901`) plus mathlib's
`Flat.epi_of_flat_of_surjective`. Ten lines, no scheme-theoretic image, no reducedness
argument, no "a surjective section is an isomorphism".
**The trap the technique avoids is worth naming**: the obvious route unfolds `zero` as a
section and argues that a surjective section of a separated smooth morphism is an
isomorphism. `AbelianSchemeStruct.zero` is an ABSTRACT FIELD, not `zeroOfMor`, so that
unfolding is not available at all — and the naturality axiom beside it is. **When a
structure axiomatises an object, reach for its naturality clauses before reaching for a
construction of it.**
### Where the bridge had to live, and why that is a real constraint rather than a preference
`flat_of_surjective_of_isAdditiveOn` sits at `X0.lean:89901`, **31 000 lines BELOW** the
`IsIsotypicHom` cluster it would serve. So the bridge is provable in `X1.lean` (which
imports all of `X0.lean`) and NOT at the `Γ₀` leaf's own position. The `Γ₀` side therefore
keeps its rival cut until someone hoists that block — measured with `flt-hoistcheck.py`
as 24 lines with 3 transitive dependencies, all inside `X0.lean`. **A shape-free lemma is
shareable only DOWNSTREAM of everything it consumes; "put it in the shared file" is not a
placement decision you get to make freely.** Measure before promising a successor that a
bridge can be reused upstream.
