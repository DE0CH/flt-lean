---
name: orchestrator-never-commits-to-main
description: "Deyao 2026-07-26: the orchestrator branches like any agent; committing tooling straight to main is a hack and is effectively irreversible"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 0dcd9de4-e92b-4213-94e8-e5bca672954a
  modified: 2026-07-26T14:38:47.952Z
---

The orchestrator must NEVER author a commit on `main` — not even for
orchestrator-only files (`.claude/*`, `flt-*.py`, non-Lean tooling). It commits
to its own branch and puts that branch in `~/.flt-merge-batch`, exactly like an
agent's work. Deyao's words on catching it: *"this is hacky … is the correct
thing to make another branch instead?"* — yes.

**Why:** the merge worker's release step is `git branch -f main <the sha it
built>`. A commit authored directly on `main` is not in the merger's history, so
that force-move silently discards it. Repairing that requires sending the merger
a one-off "merge `main` first" instruction — and an instruction that exists only
to undo a self-inflicted divergence is the hack itself. The branch route needs
no instruction.

**And it cannot be walked back.** Worktrees fast-forward to `main` at every
dispatch, so within minutes a dozen worktrees sit ON the bad commit; rewinding
`main` then makes their branches non-ancestors of `main`, which the dispatch
hook hard-crashes on by design. Committing to `main` is effectively
irreversible — the only safe move afterwards is to leave it and not repeat it.

**How to apply:** before any orchestrator-side `git commit`, branch first. See
[[flt-minimal-orchestration]] (the orchestrator only advances the pointer and
writes prompts) and [[flt-orchestrator-role]].
