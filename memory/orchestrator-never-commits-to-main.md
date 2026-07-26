---
name: orchestrator-never-commits-to-main
description: "Deyao 2026-07-26: the merge batch is for Lean edits that could turn a green build red; orchestrator tooling goes straight to main"
metadata:
  node_type: memory
  type: feedback
  originSessionId: 0dcd9de4-e92b-4213-94e8-e5bca672954a
  modified: 2026-07-26T15:17:01.547Z
---

**The merge batch exists to protect a green build, and nothing else.** The
dividing line is not who wrote the change but whether it can break the build:

- **Lean edits** (anything under `Fermat/`) → branch + `~/.flt-merge-batch`,
  always.
- **Tooling unrelated to the math** (`.claude/*`, `flt-*.py`, `CLAUDE.md`,
  memory) → the orchestrator commits **directly to `main`**.

Deyao's words: *"if it is a tooling fix that is unrelated to the math content,
feel free to commit directly to main"*, and *"the batch only applies to lean
code edits that may or may not change a green build to a red build"*.

**Why:** routing tooling through the merger buys nothing and costs a release
cycle of latency — the fix sits inert on an unmerged branch precisely while the
bug it fixes is live. That happened: three `flt-cycle.py` repairs (release
tagging, retirement stickiness, and a prose-match that silently deleted queued
tasks) were stranded on a branch while the buggy version was the one running.

**History worth keeping:** he first objected to a tooling commit on `main`
("this is hacky"). The objection was to doing it *silently and by accident*,
not to the act — he amended it the same day once the distinction was explicit.

**One asymmetry either way:** the merger's release step is
`git branch -f main <sha it built>`, so a commit on `main` it has not merged is
not in its history and that force-move would discard it. It merges `main` first
at every release, which is what makes direct commits safe. And it is
effectively irreversible — worktrees fast-forward to `main` at every dispatch,
so rewinding makes their branches non-ancestors, which the dispatch hook
hard-crashes on. The bar is "certainly not Lean", not "probably fine".

Related: [[flt-minimal-orchestration]], [[flt-orchestrator-role]].
