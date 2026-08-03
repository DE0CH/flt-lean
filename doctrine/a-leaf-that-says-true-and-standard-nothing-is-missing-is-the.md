## A LEAF THAT SAYS "TRUE AND STANDARD, NOTHING IS MISSING" IS THE ONE NOBODY GREPPED

(2026-08-02, `isIntegral_curveBaseChange_specQ` in `ModularCurve/X0.lean`, closed in five
lines.)  Every rule above is about an ABSENCE claim going stale.  This is the opposite
shape, it is commoner, and it is cheaper to miss — because a leaf in this shape looks
*finished*.

That leaf's docstring opened *"TRUE and standard, in three steps, none of which needs
anything not at this pin"* and then listed the three steps correctly: smooth over a field
⟹ regular stalks ⟹ reduced; connected plus locally irreducible ⟹ irreducible; irreducible
plus reduced is `IsIntegral`.  Every word of it was right.
`Modularity/AbelianSchemeIsogeny.lean`'s `isIntegral_of_smooth_geometricallyConnected` had
been **PROVEN along exactly those three steps since 2026-07-27 — four days before the leaf
was cut** — and `X0.lean` `public import`s that module.  All that was left was one base
change, which is two instance lookups.

**Why nothing catches it.**  A leaf that claims something is MISSING attracts a
re-grep, because this file tells you to re-grep absence claims.  A leaf that claims
nothing is missing attracts neither: it is not blocked, so it does not read as a theory
build worth attacking; and it asserts no absence, so there is nothing anybody is
instructed to check.  It just sits, looking assessed.

**The tell is the docstring's own confidence, and the cure is to read the step list as a
SEARCH QUERY rather than as a plan.**  "TRUE and standard", "in three steps", "routine",
"none of which needs anything not at this pin" all say that somebody has already worked
the composite out — and in a tree this size, a composite somebody has worked out is a
composite somebody may have written down.  So, before writing step one, grep for the
CONCLUSION of the last step, over the WHOLE tree:

    grep -rn 'IsIntegral' --include=*.lean Fermat/ | grep -i 'connected\|smooth'

That found it in one command.  Note the two things that make a name-based search fail
here and a conclusion-based one succeed: the proven theorem is 89 000 lines away in
another module, and its name (`isIntegral_of_smooth_geometricallyConnected`) shares no
component with the leaf's (`isIntegral_curveBaseChange_specQ`) — the leaf is named for
the OBJECT it is about and the theorem for the HYPOTHESES it consumes.

Corollary for whoever CUTS such a leaf: if you are confident enough to write the three
steps down, you are one grep from knowing whether they are already a theorem.  Run it and
put the answer in the docstring — "grepped `<query>` on `<date>`, nothing" — so that the
next reader inherits a search instead of a plan.

Two mechanical facts banked while closing it, both worth knowing before pricing any
base-change obligation over a field: **`Smooth` and `GeometricallyConnected` each carry a
DIRECT `instance … : P (pullback.snd f g)` at this pin** (`Morphisms/Smooth.lean`,
`Geometrically/Connected.lean`), so base-changing them is `inferInstance` and not a
`MorphismProperty.pullback_snd` call needing an `IsStableUnderBaseChange` argument — unlike
`SmoothOfRelativeDimension`, whose stability is a `lemma`.  And
**`GeometricallyConnected` DOES forbid the empty scheme**: it is
`geometrically (ConnectedSpace ·)`, `ConnectedSpace` extends `Nonempty`, and over a
one-point base `GeometricallyConnected.connectedSpace_of_subsingleton` delivers
`ConnectedSpace X` outright.  So a leaf with that hypothesis and an `IsIntegral`
conclusion carries nonemptiness on BOTH sides and needs no extra clause — the empty-curve
worry that several docstrings in this file raise is resolved, in the safe direction.

