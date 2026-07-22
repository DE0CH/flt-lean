---
name: wstar-top-down-dependency-tree
description: "Deyao's directive (2026-07-16) — resolve Lean formalization efforts as a dependency tree, top-down, FLT-style, with a PROGRESS.md tree file"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 74165b05-2b0c-49ee-af63-0a6d7cb838f6
---

For the W* Lean formalization (worktree `~/cs/wstar-worktree`, branch
`lean-explicit-functor-formula`), Deyao directed the model to mirror the FLT
effort's methodology (`~/cs/flt-worktree/fermat/PROGRESS.md`): treat the
proof as a **dependency tree resolved one layer at a time, top-down** —
state the final theorem first from the strongest available facts plus
explicitly `sorry`-d gap statements, then recurse into the gaps. Maintain
`lean-stuff/LeanStuff/WStar/PROGRESS.md` with a ✓/✗/○/□ tree, a policy
section, and a dated log, updated every iteration.

**Why:** the trust interface is the statement + `#print axioms`; stating the
top theorem early pins the deliverable and makes every remaining gap a
visible, greppable `sorry` node instead of an implicit plan. It also makes
the frontier auditable while proofs are pending.

**How to apply:** each iteration picks an open node from PROGRESS.md
(topmost unstated node first), states it from available pieces + sorried
gaps, compiles, commits, updates the tree and log. Never close a node by
citation or expert appeal ([[flt-no-citation-terminal-nodes]]); sorried DATA
(choice-extracted definitions) is tracked explicitly as poisoning meaning
until its existence node closes.

**Correction (Deyao, 2026-07-18):** do NOT prove helper lemmas bottom-up
with no proof-term connection to a root node ("writing things without any
connection to the root"). The move on an open sorried node is always:
write that node's PROOF now as assembly glue, introducing newly *stated*
sorried child theorems that the proof consumes, so the compiler-generated
dependency tree links root → children; only then recurse into the
children. A lemma is legitimate only once something on the path from a
root actually uses it.
