## A DEAD CONJUNCT INSIDE A LIVE LEAF — the duplication no scan compares
(2026-08-02, `flt-lean-392`, `redX_base_ne_and_card_compl_range_le_of_jNeronDatum`
in `FreyCurve/MazurTorsion.lean`.)  This file already catalogues the orphaned
LEAF (nothing consumes it) and the duplicate CUT (two declarations, one
statement).  Here is a third shape, and it is invisible to the checks written
for both.
A leaf whose conclusion is a **conjunction** can have one conjunct alive and one
DEAD, where the dead one duplicates a *separate* leaf elsewhere in the file.
* the consumerless-leaf check PASSES — the theorem has a live consumer, which
  projects the other conjunct;
* `dupstmt.py` and `xdup.py` are silent — the duplication is between a CONJUNCT
  and a whole declaration, and no scan compares those;
* the frontier count is one honest open leaf, and the build's
  `declaration uses 'sorry'` warning is truthful.
Concretely: that leaf's first conjunct was the live route to
`redX_base_ne_of_isCusp` when it was cut on 2026-07-30.  The next day the
separation half was re-cut through a new structure — `IsX0JNeronCuspModel`,
with `nonempty_isX0JNeronCuspModel` as its leaf — and `redX_base_ne_of_isCusp`
was reproven over that, four hundred lines ABOVE.  From that moment the
conjunct was simultaneously provable in place and still citing Deligne–Rapoport
for a fact the tree was independently citing them for elsewhere.  Nothing said
so for three days.
**THE CHECK, and it costs one grep per leaf: when a leaf's conclusion is a
conjunction, list its consumers and record WHICH PROJECTION each one uses.**
    grep -rn '<leafName>' --include=*.lean Fermat/     # comment-stripped
    # then read each hit: `.1`, `.2`, `.left`, `.right`, or a destructuring
    # `obtain ⟨h1, h2⟩` -- and note which components are actually bound
A conjunct no consumer projects is dead.  In a tree that re-cuts as aggressively
as this one, it is usually dead *because it was independently re-proven*, so the
next move is to grep the file for a declaration whose statement IS that conjunct
— and if there is one above you, the conjunct is free.
**THE REPAIR IS A RECUT THAT KEEPS THE STATEMENT.**  Prove the composite
outright (dead conjunct from the sibling route, live conjunct from a new leaf
that is the live conjunct copied CHARACTER FOR CHARACTER), and leave the
signature and the call site untouched.  Copying the conjunct verbatim is what
makes the inherited falsity audit transfer rather than have to be re-run — say
so in the new leaf's docstring, since an audit labelled "inherited" with no
argument is a failure mode this file records elsewhere.
**REPORT IT AS `1 -> 1`, WITH THE RECEIPT.**  The warning-set delta is `-1 +1`
and is indistinguishable from "nothing happened"; the honest statement is that
the count did not move and a duplicated CITATION was removed.  Two cheap
receipts, both worth quoting in the commit:
    git diff -- <file> | grep -E '^[+-] *sorry *$'      # exactly one + and one -
    # comment-stripped `sorry` token count before and after, against the
    # build's `declaration uses 'sorry'` count -- equal all three ways rules
    # out an anonymous inner sorry having been swapped in
**AND SAY WHY THE SURVIVING CONJUNCT DID NOT ALSO FALL**, on the leaf.  Here the
two halves look like "one fact read twice" — the leaf's own docstring said so,
correctly — and they are still not equally reachable: the separation half is
about SECTIONS, which are `RelPoint`s, which is what every field of the datum
speaks about; the counting half is about CARDINALITIES OF UNDERLYING POINT SETS,
and the datum carries its fibre comparisons only as functorial `RelPoint`
equivalences.  **A structure that settles one conjunct of a "one fact read
twice" pair need not settle the other, and the discriminator is which LANGUAGE
each conjunct is stated in** — points, sections, or sheaves.  Check that before
assuming a new structure closes both.
### Rider: `dupstmt.py` IS BLIND TO A TWO-SPELLING TWIN, AND A CLEAN RUN IS NOT EVIDENCE
(2026-08-02, `flt-lean-40`, arrived at the section above independently and one day
later — see the decline note below, which is the more useful half.)
The rule above says to match an orphan closure against the open leaves **on the
statement, never on the name**. It is worth saying why no tool does that for you.
`tools/merge/dupstmt.py` normalises binder grouping, the leading `_` and — in its
weakest key — alpha-renaming of top-level and inner binders. A two-spelling twin
defeats all three, because the two statements are not alpha-variants: they are
DIFFERENT TERMS that happen to be definitionally equal
(`HilbertInertiaTrivialAt w N`, a bounded quantifier over `Γ F_w`, against
`∀ σ : ↥(localInertiaGroup w), hilbertInertiaToGlobalHom F w σ ∈ N`, the same map
over the subtype). Run on the whole tree over sorried declarations at release 33
it reports **0 groups**, on a tree containing exactly this pair. So: a clean
`dupstmt` run rules out copy-paste duplicates and says nothing whatever about the
class the section above is about. The only instrument for that is reading the two
statements.
**And the cheapest tell that a module HAS a two-spelling pair is free: the same
translation one level up is already written down.** Here
`finite_hilbertInertiaOutsideSubgroups`'s docstring explains, in prose, that its
own inertia clause and `HilbertInertiaTrivialAt`'s "are the same statement
(`hilbertInertiaToGlobalHom` is `hilbertDecompHom` composed with
`Subgroup.subtype`)". That paragraph is a general fact about the module, not a
remark about one proof — so when you find one, grep for every other leaf written
in the losing spelling.
**INDEPENDENT CONFIRMATION OF THE BRIDGE, since it is worth what a second
computation is worth.** Dispatched at the same leaf a day later, with no sight of
`flt-lean-71`, I re-derived the identical four-line proof — the same
`Set.Finite.subset`, the same `fun w hw σ hσ => hinert w hw ⟨σ, hσ⟩`, differing
only in one binder name — the same relocation direction, and the same accounting
(module 14 → 13 sorried declarations; comment-stripped sorry TOKEN count 14 → 13
in step, which is what rules out an anonymous inner sorry having been swapped in).
Verified green: `lake build` of the module plus its farthest downstream consumer
`Fermat.FLT.Modularity.KhareWintenberger`, `EXIT=0`,
`Build completed successfully (5643 jobs)`, zero errors. My Lean payload was then
DECLINED in favour of `flt-lean-71`'s, which is a strict superset (same bridge,
plus the deletion of the orphaned subgroup route). Two agents converging on one
four-line proof is reassuring about the mathematics and is still one worker-cycle
spent; the release-window check the prompt mandates (`git show merger:<file>`) was
run and correctly reported the leaf OPEN, because the rival lives on an unmerged
sibling branch that neither `main` nor `merger` can see. **`git branch --contains`
on a commit named in a QUEUE ENTRY is the check that would have caught it**, and
it costs one command — queue text is written by agents who have just done the
work, so it names branches no ownership record does.
