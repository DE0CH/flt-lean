---
name: flt-route-says-return-discarded-datum
description: A leaf cut to "return the datum theorem X discards" may already be receiving it — the tell is a comment at the discard site, not in the leaf
metadata:
  type: project
---

A leaf whose route note says *"theorem `X` produces this and throws it away —
return it"* is very often already receiving it, because the repair landed between
the leaf being cut and the leaf being dispatched.

Measured 2026-07-31 (`flt-lean-56`, `exists_x0CurveModel_of_base_moduli` in
`ModularCurve/X0.lean`, cut 2026-07-31 and closed the next day in 15 lines). Its
three-step route asked for two strengthenings that had ALREADY landed in release 32,
plus a bridge (`IsX0CurveModel.classify_genericOpen`) that was already PROVEN and
written for exactly that crossing. Residue: keep a conjunct the consumer drops.

**Why:** In this development a leaf is cut, and then its route note is never
revisited. But whoever performs the upstream repair works at the DISCARD SITE and
leaves a comment there — often naming the leaf. So the freshest statement about a
leaf is usually not in the leaf.

**How to apply:** Before costing such a route, three cheap checks —
1. read the CONCLUSION of the theorem said to discard the datum: already a
   conjunction, or already returning a strengthened structure? then step 1 is done;
2. read the CONSUMER's `obtain` pattern and body — `⟨…, hι⟩` followed by `hι.1`
   means the datum is flowing and being dropped, i.e. the leaf is a REPACKAGING;
3. `grep` the leaf's own name across the file, not just its declaration.

Same family as [[flt-leaf-cost-estimates-are-hypotheses]] and
[[flt-audit-scoped-to-declaration-it-read]], with the stale reference one
declaration away rather than one file or one pin away. See also
[[flt-both-docstrings-name-the-loser]] for the case where the prose lies in both
directions and only the proof body is honest.
