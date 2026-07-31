---
name: flt-frozen-main-rots-the-queue
description: When a release is HELD, main does not move, so queue1 stays "AUDITED" and dispatchable while its tasks silently go stale against merger — audit against merger, not main
metadata:
  type: project
---

Release 32 (2026-07-31) measured it: **48 of 265 `queue1` tasks — 18% — named a
leaf `merger` had already PROVEN**, and 10 more named no open leaf at all.  Five
consecutive held releases had frozen `main`, and because `main` does not move the
loop's `audit_current` guard keeps passing and dispatch keeps running off a task
list last re-audited at the previous PUBLISHED release.

The fix is one filter and no build: `tools/merge/frontier.py --root .` on the
merger tree, then keep a task iff it names a short name still in that frontier.
Keep the `AUDITED:` stamp equal to `main` — `flt_loop_rows.py`'s `r15_guard`
refuses to dispatch otherwise — and re-read both queues immediately before an
`os.replace` write, because the loop pops every ten seconds.

Tokenise with "isalnum or `_` or `'`", never a regex character class; match on
the last dotted component with a trailing dot stripped; and expect exactly one
residual uncovered "leaf", the `sorry` inside a string literal in
`Fermat/SorryGate.lean`'s `elab`.

Related: [[flt-release-deletes-nonleaf-tasks]], [[flt-preflight-finds-unowned-leaves]].
