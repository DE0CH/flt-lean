## A HOIST INVERTS EVERY "QUOTING IT WOULD BE CIRCULAR" NOTE — and the leaf the note protected is then a DEAD DOWNSTREAM DUPLICATE closable in three lines
(2026-08-02, `flt-lean-77`, on `exists_inj_point_x0Model_of_relPointEquiv` in
`FreyCurve/MazurTorsion.lean`.)  This file already records that a docstring's
ABSENCE claims decay, and that an import-CYCLE verdict expires when the leaves
under it close.  There is a third and sharper decay, it is caused by an ordinary
successful refactor, and it silently converts a closable leaf into one nobody may
touch.
That leaf carried, in bold, a traced circularity:
> `card_le_of_rankZeroJacobian` wants `HasRankZeroJacobian`, and at these levels
> the only producer is `hasRankZeroJacobian` → `finite_jacobian` →
> `isTorsion_jacobian` → `finite_relPoint_x0` → `exists_x0Model` → **THIS leaf**.
> (Traced 2026-07-31 against the tree.)
and its sibling's docstring said the same thing from the other end — *"the same
statement without `ab` is `exists_x0Model` (below, PROVEN — but proven FROM the
assembly that consumes this leaf, so the two are not interchangeable and
**quoting it here would be circular**)"*.  Both were accurate when written.
**Both were false by the time they were read, and the single word that gives it
away is `below`.**  `exists_x0Model` had since been HOISTED out of
`MazurTorsion.lean` into `ModularCurve/X0.lean`, which `MazurTorsion.lean`
`public import`s — so it is not below, it is UPSTREAM, its body names only
`exists_x0Compactification_relPoint_inj_x0Model` and
`nonempty_relPointEquiv_of_isX0Compactification_rat`, and **Lean would forbid the
asserted cycle outright.**  The leaf closed in three lines
(`obtain ⟨g, hg⟩ := exists_x0Model N hN h; exact ⟨g ∘ t.symm, hg.comp t.symm.injective⟩`),
verified in a scratch in **9 seconds**.
**The mechanism, and it is general: a hoist moves a declaration ACROSS a module
boundary, and a circularity note is a claim about POSITION.**  Every such note
therefore flips from true to false at the moment the hoist lands — and unlike a
broken proof, nothing reports it: both files compile, the leaf still emits its
`declaration uses 'sorry'`, every ownership check passes, and the note reads as a
careful, dated, traced warning.  It is the most persuasive possible reason not to
try the one thing that works.
**The check is two commands and it beats re-tracing the chain:**
    grep -rn 'theorem <the cited name>' --include=*.lean Fermat/   # WHICH FILE is it in now?
    grep -n 'public import .*<that file>' <your file>              # is that file UPSTREAM of you?
If the cited declaration is upstream, the cycle cannot exist, whatever the note
says — so read its PROOF BODY next, not the chain the note describes.  **Treat
the words "below", "above" and "further down" in any docstring as position
assertions with an expiry date**; this file already says that for hoists you
perform, and the case that bites is the hoist somebody else performed.
**AND THE LEAF THAT SUCH A NOTE PROTECTS IS TYPICALLY DEAD, WHICH IS WHY IT
SURVIVES.**  Here the sole consumer,
`exists_relPoint_inj_x0Model_of_abelianSchemeStruct`, has exactly ONE
comment-stripped occurrence tree-wide — its own declaration.  The pair is a
DOWNSTREAM RIVAL CUT of the upstream `exists_x0Compactification_relPoint_inj_x0Model`
→ `exists_x0Model` chain, i.e. [[flt-downstream-rival-cut-is-consumerless-by-construction]],
and a downstream rival of an upstream theorem is consumerless by construction.
That memory's recorded repair was *"hoist it, do not re-derive it"*; **for this
leaf no hoist was needed at all**, because the upstream theorem already has the
same conclusion under strictly FEWER hypotheses.  So add one step before pricing
any hoist of a downstream rival: **diff the rival's statement against the
upstream one and check for subsumption.**  Identical conclusion plus a superset
of hypotheses means the downstream leaf is not a rival cut to be relocated but a
weaker corollary to be discharged, and the discharge is one `exact`.
**REPORT THE ACCOUNTING HONESTLY, because it flatters and should not.**  This is
`−1` on the direct-sorry count and `0` on the mathematics: the modular
identification is still owed, once, upstream, exactly where it was.  What was
removed is a SECOND copy of that obligation which every frontier instrument was
counting as independent work and which had already drawn at least two dispatches.
Say that in the commit, or the delta reads as a theory gap closing.
* **Closing by delegation beat deleting the dead pair, and the reason is
  ownership.** Deleting also strands the PROVEN ~130-line
  `exists_weierstrassPointEquiv_of_abelianSchemeStruct` above it, whose only
  consumer is the consumer of this leaf.  Choosing what happens to another
  agent's proven work is an author's call; closing the leaf costs two lines,
  strands nothing, and leaves the deletion decidable later.  **Prefer the repair
  that keeps every option open when the file has other owners.**
* **Correct the stale note IN PLACE and quote what it used to say.**  The
  reasoning that produced it is still worth reading, and a note that is silently
  deleted gets re-derived — its author had traced a real chain, and only the
  positions moved.
