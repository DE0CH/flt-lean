## A PROVEN COMPOSITE CAN PRODUCE EVERY OBJECT YOUR LEAF NAMES AND STILL NOT PROVE IT — ASK WHAT IT **PINS**, NOT WHAT IT PRODUCES
(2026-07-31, `flt-lean-128`, `exists_gamma0Datum_specQ_isBaseChangeOf_of_j_special`
in `ModularCurve/X0.lean`.)  The task prompt was emphatic and, on its face, right:
*"THIS IS A TRANSLATION TASK, NOT A TWIST THEORY … the CM descent already exists
~13 000 lines above, at general `N`, and is PROVEN … apply the bridge, run the
`j = 1728` or `j = 0` theorem, then package the result back into a `Gamma0Datum p
SpecQ`."*  Every clause of that is TRUE.  The composite is even shorter than
advertised — `exists_stableCyclic_j_of_gamma0Datum_algClos` already runs the bridge
AND the twist at every `j`, and `exists_weierstrassModel_gamma0Datum_liesIn` already
does the packaging, both PROVEN.  **And the composite cannot prove the leaf**, because
the leaf's conclusion is `IsBaseChangeOf (specAlgClos ℚ) d d₀` — *`d` IS a base change
of `d₀`* — and every statement in the chain is EXISTENTIAL in the curve and records
nothing relating its output to `d`.
**The general test, and it costs one read of the producer's conclusion: does the
producer PIN the object your conclusion pins, or merely produce one of the same
shape?**  A chain of `∃ E, ∃ g, P E g` theorems composes beautifully and pins nothing.
The tell is a docstring sentence the producers here state outright and nobody reads as
a warning — *"it does not relate `E` to `d` — no isomorphism, no equality of `j`"*.
Read that as: **this theorem is unusable for any conclusion that mentions `d`.**  Same
family as [[flt-two-leaves-may-be-one]] read in reverse: there two differently-worded
statements were the same theorem; here two identically-worded chains ("produce a curve
over `ℚ` with a stable subgroup") are different theorems, and only the pinned one is
yours.
**THE MISSING COMPARISON IS USUALLY BUILT AND THEN DISCARDED — grep the producer's
PROOF for it before pricing the repair.**  Here the `ℚ̄`-isomorphism carrying `⟨g⟩` to
`⟨g'⟩` is constructed in three lines at `QuarticTwist.lean:992–998` and again at
`SexticTwist.lean:259–265` (`hψ : ⟨δ,0,0,0⟩ • (E'⁄Ω) = (E⁄Ω)`, `ψ := (equivOfEq
hψ.symm).trans (equivVariableChange …)`, and the returned witness is literally `ψ g`)
— and then thrown away by an existential conclusion that does not mention it.  So the
repair is a STRENGTHENING IN PLACE that costs those proofs nothing, not a new theory.
That is the same shape as the `j`-conjunct repair this file already records on
`exists_stableCyclic_j_of_gamma0Datum_algClos` ("`j` is preserved at every single step
and was recorded at none, which is why this is a BOOKKEEPING leaf"), and the same
closed-call-graph argument applies.
**Why it was still right NOT to do it in one run, and this is the judgement to copy.**
The strengthening is an interface change across three files with five call sites, in a
119 000-line module that elaborates in ~35 minutes and has many concurrent editors —
the class-7 interface split, by the book.  What was done instead: the target was PROVEN
over a single new leaf that is the exact `j`-special MIRROR of its `j`-generic sibling
(same conclusion shape, `(E, Cv)` moved from hypothesis to output because at `j ∈ {0,
1728}` `ofJ j₀` is the wrong curve), the rigidity/packaging step was discharged with
the PROVEN `nonempty_isBaseChangeOf_of_isWeierstrassModel_common`, and the two
three-line discard sites plus the exact conjunct to add were written into the new
leaf's docstring and queued.  **Count `1 → 1`, and say so** — no mathematics closed.
What changed is that the residue is stated in the same shape as its sibling, so the two
share a successor and share the two inputs they both owe, and that the route the
consumer's docstring prescribed has been corrected IN PLACE where it was wrong rather
than left to send the next agent down it.
Rider, because it is the cheapest half of the check: **a docstring's "the last step is
the mirror of what the generic leaf does" is a claim about the generic leaf.**  Open it.
Here the generic sibling's "last step" is its own open leaf plus two further inputs it
names as its own further cut — so "mirror" meant "inherit its whole difficulty", which
is the opposite of what the sentence conveys.
