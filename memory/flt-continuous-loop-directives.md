---
name: flt-continuous-loop-directives
description: "Deyao 2026-07-16: the FLT loop directives — top-down dependency tree, continuous tool-call loop (no wakeups, no stopping after N iterations), no deferral: every sorry is an active frontier node"
metadata:
  node_type: memory
  type: feedback
---

Consolidated from the original 2026-07-16 directives (recorded during the
dissertation-repo era as wstar-top-down-dependency-tree,
wstar-continuous-tool-loop-no-wakeup, wstar-no-deferral-all-sorries-active,
lean-continuous-sorry-loop; merged 2026-07-22 when the project split into
this repository). The full mechanism descriptions live in CLAUDE.md.

**Top-down dependency tree.** Resolve the formalization as a dependency
tree: the top theorem is proven first with every gap an explicit
stated-and-sorried node; walk the tree downward, decomposing deep nodes
and proving the provable ones; PROGRESS.md (generated) is the
authoritative tree, updated every iteration.

**Continuous tool-call loop, no wakeups.** Never schedule wakeups and
never stop after N completed iterations to report. The loop is: ask the
compiler whether any `sorry` remains; if yes, run a full iteration and
re-check. A reply containing a tool call is itself the self-prompt to
keep generating; stopping to summarize is the failure mode.

**Why:** Deyao explicitly corrected a session that stopped after two
clean committed layers — "you didn't fall apart when writing a
program... this is the mechanism you should use."

**No deferral — every sorry is an active frontier node.** Nothing is
"below" anything: never triage a sorry out of scope, never park a node
as "later"; the frontier is the whole set of open sorries.

**How to apply:** each iteration = resolve or decompose a node → verify
via lean-lsp MCP diagnostics → axiom audit → commit/push → update
PROGRESS.md → re-check the frontier and continue. See
[[flt-no-private-shielded-floating]], [[flt-glue-first-no-floating-haves]],
[[flt-no-lake-build-trust-mcp]].
