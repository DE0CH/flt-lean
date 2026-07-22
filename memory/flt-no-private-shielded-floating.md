---
name: flt-no-private-shielded-floating
description: "Deyao 2026-07-18: never use `private` (or any other mechanism) to shield bottom-up work from the free-floating check — resolve strictly top-down"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 407dda52-29da-420e-82fd-64073bb43c54
---

In the FLT project, do not build material bottom-up and mark it `private` so
that the free-floating detector (`fermat/free-floating.py`, enforced by the
Stop hook) does not flag it. The privateness exemption exists for genuine
implementation details of consumed proofs, not as a loophole.

**Why:** Deyao (2026-07-18, verbatim intent): "you must not continue working
on a floating piece in any way that works around the mechanical checks done by
the stop hook." The no-floating rule *is* the top-down policy: every new piece
of work must already be inside the dependency cone of `fermat_last_theorem`
through a real consumer at the moment it is written. Private-shielding
produces exactly the unconsumed islands the rule forbids, while making them
invisible to the checker — worse than visible floating.

**How to apply:** to work on a deep gap, first open its *consumer* sorry with
a proof skeleton that uses the new material; state the needed sub-lemmas
(sorried, with `set_option warn.sorry false in`) at their point of use, so the
compiler sees the dependency edge immediately; only then resolve them, layer
by layer, downward. If a lemma would have no consumer edge after the current
iteration, do not write it yet. Related: [[flt-continuous-loop-directives]].
