## A FILE'S ONE CROSSING FROM THE FUNCTOR OF POINTS INTO A RING IS A SHARED BRIDGE — never cut a specialised twin of it

(2026-07-31, `flt-lean-101`, closing `mem_intSpan_of_isCMByRamifiedMaximalOrder` in
`FreyCurve/MazurTorsion.lean` with NO new leaf.)

This development states its geometry in the functor of points (`RelPoint`, `ab.add`,
naturality in the test object) and its arithmetic in rings (`WeierstrassCurve.End`,
`Subring.closure`, `ℤ`-bases). Every leaf that needs both has to CROSS, and the crossing
is the expensive part — so a file accumulates exactly one bridge, cut once, for whichever
consumer needed it first. Here that is `exists_end_of_relPointEndo`: given a Weierstrass
model over `ℚ̄`, the `ℚ̄`-points ARE `W.Point` as a group and every ADDITIVE NATURAL
endomorphism of the functor of points is realised in `WeierstrassCurve.End W`.

**A branch cut a second, specialised copy of it, and that is the failure worth naming.**
`flt-lean-106` needed the same transport at `IsCMByRamifiedMaximalOrder` and at this one
`p`, and opened `exists_endTransport_of_isCMByRamifiedMaximalOrder` for it. The bridge had
been cut the day before, is quantified over an arbitrary level and an arbitrary additive
natural `u`, is strictly more general, and already had two consumers. Applying it took four
lines. The specialised twin was never owed.

**The check, and it is a grep for the CROSSING rather than for your leaf's vocabulary.**
Before cutting any leaf whose statement mentions BOTH a functor-of-points object and a ring
element, grep the file for the place it already crosses:

    grep -n 'WeierstrassCurve.End\|AddMonoid.End\|≃+' <the file> | head -40

and read the docstring of the first hit that is a bridge. A bridge's author quantifies it
generously ON PURPOSE and says so — this one's docstring opens "**The level `N` is
irrelevant** and is not constrained" and "the same map applied to an ARBITRARY additive
natural `u`". A twin cut against that sentence is a duplicate the frontier counts as
ordinary work, and neither `own.py` nor any duplicate scan can see it, because the two
statements share no identifier.

**And the sub-subsection note that predicted the work can be stale about who does it.**
The note above these two leaves says the spanning half "needs to know what `End(d.E)` IS,
and that is where the transport is unavoidable", and that "a successor who builds the
TRANSPORT gets both at once". Both sentences are true about the MATHEMATICS and wrong about
the WORK: the transport was built for a different consumer, 1400 lines up, before the note
was written. **A route note names what is needed; it is silent about what has since been
supplied for somebody else.** Grep the file for the thing, not for the leaf that would have
produced it.

### The Lean trap: `rw [ab.pre_add]` does NOT fire on a goal that displays `pre (x + y)`

`AbelianSchemeStruct.pre_add` is stated about the STRUCTURE FIELD, `RelPoint.pre h hg
(ab.add x y) = …`, while `ab.addCommGroup` is `@[reducible]` so a goal written with the
instance presents the same term as `RelPoint.pre h hg (x + y)`. The two are defeq and NOT
syntactically equal, so

    rw [d.ab.pre_add k hg]
    -- Did not find an occurrence of the pattern  RelPoint.pre k hg (d.ab.add ?x ?y)
    -- in the target expression
    --   … = RelPoint.pre k hg (a • x + b • h.phi x)

fails on a goal that visibly contains it. **The cure is to bundle and re-state**: build the
`AddMonoidHom` inline and state the `have` in the spelling the goal uses, so the defeq check
happens once at `exact` instead of inside `rw`'s matcher —

    have hadd : ∀ y z : RelPoint d.f g,
        RelPoint.pre k hg (y + z) = RelPoint.pre k hg y + RelPoint.pre k hg z := fun y z =>
      map_add (AddMonoidHom.mk' (fun w : RelPoint d.f g => RelPoint.pre k hg w)
        (fun w v => d.ab.pre_add k hg w v)) y z

and the same shape with `map_zsmul` for `pre (n • y) = n • pre y`, which is what a naturality
obligation for a family `fun U g x => a • x + b • φ x` needs and which has no lemma of its
own. (`ab.preAddHom` in `AbelianSchemeIsogeny.lean` is this bundling, but it is a `def`, so
under `@[expose] public section` a consumer reaching it through a non-public import cannot
unfold it; inlining costs two lines and cannot go wrong.)

This is the standing "printed pattern equals printed target ⟹ switch to a defeq-checking
tactic" rule with a new and very common cause: **a structure-field operation versus its
`@[reducible]`-instance spelling.** Expect it at every `ab.add`/`ab.zero`/`ab.neg` lemma in
this development the moment the goal has been written with `+`, `0`, `-`.
