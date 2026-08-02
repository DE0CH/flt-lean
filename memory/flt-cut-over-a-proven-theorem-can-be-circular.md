---
name: flt-cut-over-a-proven-theorem-can-be-circular
description: A cut resting on a PROVEN theorem can still be circular — check that theorem's CALL GRAPH for other open leaves in the file, because "proven" is not "independent".
metadata:
  type: feedback
---

Cutting a leaf over a theorem that is PROVEN feels safe, and the check every
cutter runs — *is my input available?* — passes. It is not enough. If that
proven theorem's call graph reaches a DIFFERENT open leaf in the same file,
the cut has re-derived its own root and the file now owes the same citation
twice.

Measured 2026-08-02, `ModularCurve/X1.lean`: the 2026-07-31 ATLAS cut of
`exists_isFineGamma1Moduli` rested on the PROVEN `exists_gamma1AffineModel`,
whose call graph is

    exists_gamma1AffineModel -> exists_gamma1GITPresentation
      -> exists_gamma1Rigidification -> exists_gamma1RigidifiedModuli
      -> isAffine_of_gamma1RigidifiedModuliScheme
      -> exists_isAffine_gamma1RigidifiedModuliScheme
      -> exists_isAffine_gamma1ModuliScheme        <- a LEAF, 6600 lines up

so the cut spent a second leaf re-deriving Katz–Mazur 4.7.1 from 4.7.1.

**Why:** this is [[flt-both-rival-cuts-landed]] with no merge in it — one
agent, one branch — so none of the merge-damage scans apply. Both leaves
emitted an honest `declaration uses` warning, both passed the three-part
ownership test, and the two statements share no identifier, so
`dupstmt.py` and `xdup.py` are silent too. The only artefact that shows it
is the call graph, and nothing computes it.

**How to apply:** before writing a cut, take the theorems your new proof
will consume and ask, for each, whether its transitive callees include any
open leaf in the file. Twenty lines of Python over comment-stripped source
(declare/use, attribute each use to its enclosing declaration, BFS). If a
leaf comes back, the cut is a cycle — a proven input that bottoms out in
your sibling is your sibling.

**Resolving one you find:** keep the arrangement whose root is IMPLIED by
the rival's root; that leaves the file owing strictly less. Here
`exists_isAffine_gamma1ModuliScheme` implies the atlas route's conclusion in
eleven lines, while the atlas route implies nothing without an atlas it can
only get from that leaf — so route B was deleted, −1 leaf, no mathematics.
Two riders: check the loser's *unique* hypotheses before deleting (the
deleted route needed `∀ Z, Subsingleton (Z ⟶ S)`, which the survivor's
over-`S` `∃!` makes free — that is what made the deletion free), and record
the cycle plus `git show <sha>^` in the survivor's docstring, or it will be
cut again. See also [[flt-consumer-scan-must-be-a-fixpoint]].
