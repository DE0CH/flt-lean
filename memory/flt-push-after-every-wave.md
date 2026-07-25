---
name: flt-push-after-every-wave
description: Deyao 2026-07-24 — push after every integration wave; do not hold pushes hostage to composition gates
metadata: 
  node_type: memory
  type: feedback
  originSessionId: bb651553-75cd-46f7-939d-740c91e7f702
  modified: 2026-07-24T19:42:31.933Z
---

Deyao (2026-07-24): "you are forgetting to push, i've pushed some for you."

**Why:** The orchestrator was holding `git push` until full serial gate
passes over every changed file, leaving main many merges ahead of
origin for long stretches. Deyao wants origin current; he pushed
manually to catch up.

**How to apply:** `git push` at the END of every integration wave
(after the merge + duplicate-scan + slot-free + queue steps), not
after the gate chain. Gates still run and still matter — a red gate
gets fixed in a follow-up commit and pushed again. Per-branch work is
already agent-verified before merge, so the composition risk on origin
is small and short-lived. Related: [[kill-recovery-just-resume]],
[[flt-fleet-13-worktree-protocol]].
