---
name: flt-differing-duplicate-three-outcomes
description: A cross-file duplicate whose two copies DIFFER has three outcomes, and "downstream is proven" does not mean deleting it loses a proof
metadata:
  type: project
---

`xdup.py` finds duplicate declarations across an import cone; `dedup_cross.py`
deletes only the pairs whose bodies AGREE and leaves the rest for a decision.
Release 34 had 62 pairs, 3 of which differed, and the three needed three
DIFFERENT answers — so "the downstream copy is proven, therefore deleting it
reverts a proof" is not a rule.

Classify each differing pair by sorry-status AND by what the downstream proof
actually rests on:

1. **downstream SORRIED, upstream PROVEN** — delete downstream. Pure win.
2. **downstream PROVEN, upstream SORRIED, and the downstream proof DELEGATES to
   the upstream chain** — delete downstream, nothing is lost. Check by walking
   the upstream call graph: if the upstream theorem the proof cites transitively
   CONSUMES the upstream copy of the leaf, the leaf cannot be proven that way
   upstream (circular) and the downstream copy is a delegation that bottoms out
   in the upstream sorry. It is the "downstream rival cut, consumerless by
   construction" shape.
3. **downstream PROVEN, upstream SORRIED, and the downstream "proof" is a RECUT
   over another sorry** — this is real design work (a smaller residual leaf) and
   deleting it loses it. TRANSPLANT the whole recut upstream — the helper leaf
   and the proof over it — then delete downstream as an identical pair. Count
   neutral, residual leaf strictly smaller.

**Why:** deleting on sorry-status alone gets (2) and (3) backwards in opposite
directions — (2) looks like a loss and is not, (3) looks like a duplicate and is
a recut.

**How to apply:** for each DIFF `dedup_cross.py` reports, grep the downstream
proof's cited names; if they are all upstream and proven, it is case 1 or 2 —
decide by whether the cited theorem consumes your leaf. If any cited name is
itself a `sorry`, it is case 3: transplant. See [[flt-cut-times-hoist-orphans-downstream]].
