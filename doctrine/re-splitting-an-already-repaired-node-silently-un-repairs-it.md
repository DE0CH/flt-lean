## RE-SPLITTING AN ALREADY-REPAIRED NODE SILENTLY UN-REPAIRS IT — the repair's hypothesis looks unused in the half you are writing
(2026-08-01, `flt-lean-199`, `ModThree.lean`.) This file already records that a leaf
restated a second time VOIDS its earlier audit, and that a decomposition can leave a
hypothesis on only one half. Here is the composite, and it is the worst-behaved member
of the family because **the refuted statement comes back under a NEW NAME while the
corrected one is left standing, unconsumed, three lines away.**
Sequence, all of it by different agents, none of them careless:
1. 2026-07-30. `exists_minimalIdempotentPresentation` is REFUTED — a presentation
   `𝒪₃ᵥ[[X₁…X_h]] ↠ B` forces `B`'s residue field to be `𝔽₃`, and nothing said so. The
   audit is written into the docstring with a complete witness, and the repair lands as
   a new hypothesis `hū3` on a corrected step-2 leaf,
   `exists_minimalPresentation_of_isLocalRing_quotient`.
2. 2026-07-31. A re-split of the same parent into step 1 + step 2 creates a SECOND
   step-2 leaf, `exists_minimalPresentation_of_idempotentLocalQuotient` — the same
   statement **with `hū3` dropped** — and re-points the parent at it, dropping `hū3`
   from the parent too.
Net: the statement the file itself refutes yesterday is back today, and the corrected
leaf has NO CONSUMER anywhere in the tree.
**Why nothing catches it.** The re-split conflicts with nothing (it is an addition and a
one-line body change). The build stays green. The sorry count goes UP by one, which reads
as ordinary decomposition. `own.py`/`leafstat.py` correctly report both leaves open and
unowned. `dupstmt.py` does not pair them — they differ by a genuine binder. And a task
prompt generated from the new leaf's docstring describes a perfectly sensible piece of
commutative algebra.
**THE TELL, and it is one `grep`: the parent's docstring names a different step-2 leaf
from the one its proof body calls.** Nobody rewrote the parent's prose during the
re-split, so it still said *"PROVEN 2026-07-30 from
`exists_minimalPresentation_of_isLocalRing_quotient` above"* while the body called the
new name. That is the same docstring-versus-body signal recorded elsewhere in this file
for duplicate cuts; here it is the signal for an un-repair.
**Two checks, both cheap, and run them in this order when you are handed a freshly-cut
leaf:**
* **grep the file for a FALSITY AUDIT naming your leaf's PARENT**, not your leaf. Your
  leaf is a day old and has no audit; the statement it was cut from may have been
  refuted last week, and the audit sits under the parent's name. `grep -n "FALSITY
  AUDIT"` on the enclosing file and read every one whose subject is upstream of you.
* **diff your leaf's binder list against the parent's.** A cut copies binders by hand,
  so a binder the parent has and the child lacks is a transcription loss, never a design
  decision — and a hypothesis added by a repair is exactly the one that looks decorative
  to whoever is writing the other half. Here the only difference between the two step-2
  leaves was `hū3`.
**And the third tell is free if you are already running it: a PROVEN-correct leaf that
suddenly has no consumer.** A re-split orphans the leaf it duplicates. So the standing
"grep each open leaf for a CODE consumer" check finds this from the other end — the
corrected leaf, not the false one, is the one that goes quiet.
**The repair is normally free, because the dropped hypothesis is still in the caller's
hand.** `exists_fontainePresentation` held `hū3` and was discarding it, so restoring it
through two signatures changed no call site and no statement above them. Delete the
false duplicate rather than adding `hū3` to it: with the hypothesis restored it is
character-for-character the leaf it duplicated, and two names for one open obligation is
strictly worse than one.
Corollary for whoever DOES a re-split: the audit that repaired the node is part of the
node. Carry it — or at minimum carry its hypothesis — into every child, and re-point the
parent's docstring in the same commit as its body.
