---
name: flt-merger-check-is-per-declaration
description: Run the merger release-window check on every leaf you decide to attack, not only on the TARGET you were dispatched at
metadata:
  type: feedback
---

(2026-07-31, `flt-lean-38`.) I ran `git show merger:<file> | grep -n <name>` for my assigned
TARGET — correctly; it was still `sorry` there — and did not re-run it for the SIBLING leaf
I chose to close forty minutes later. `merger` already proved that one, by a strictly
stronger route (no Galois hypothesis), so a complete, green, axiom-clean proof had to be
thrown away.

**Why:** the release-window rule is keyed on the DECLARATION being written, not on the task
that was dispatched. Any leaf attacked mid-run — a sibling, a helper noticed open, a residue
of your own cut — is a fresh dispatch as far as that check is concerned.

**How to apply:** `git show merger:<file> | grep -n '^theorem <name>'` before the first line
of ANY leaf, and read the declaration rather than matching the name. Second, cheaper net:
`grep -c '<declName>' ~/.flt-loop/queue2` — a queued task *about* the leaf (here: one asking
to GENERALISE it) only makes sense if it is already proven. When it fires, decline your own
payload and revert the region byte-identically to your base so the merge is a no-op;
`git merge-tree --write-tree --name-only HEAD merger` reporting *Auto-merging* rather than
*CONFLICT* is the receipt. See [[flt-ramification-leaf-is-subgroup-trivial]].
