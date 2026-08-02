---
name: flt-dead-leaf-inlined-is-prove-and-reroute
description: "A consumerless leaf whose statement is inlined in its former parent should be proven and rerouted, not deleted — deletion leaves the duplication behind."
metadata: 
  node_type: memory
  type: project
  originSessionId: 0a2c901a-028e-4cb9-8021-c7b0689ea33d
  modified: 2026-08-02T06:38:23.439Z
---

The standing rule for an OPEN-but-DEAD leaf (see [[flt-consumerless-leaf-is-dead-or-duplicate]])
is to delete it. That is right only when the leaf's CONTENT is dead too. The commonest way a
leaf goes dead in this tree is different: **a re-cut re-proved the parent by another route and
INLINED the dead leaf's statement into the parent's body.** The content is then live,
duplicated, and unciteable.

**Why:** deleting drops the frontier by one and leaves the duplication; proving the leaf and
rerouting the parent through it drops the frontier by one *and* removes the duplication, for
the same effort. It also usually means the leaf's stated blocker has since been PROVEN — that
is why the re-cut happened.

**How to apply:** when the comment-stripped consumer scan returns only the declaration's own
line, do not stop. Read the parent that used to consume it (named in the leaf's docstring, or
found by grepping the CONCLUSION) and check whether the parent's body now contains the leaf's
statement. Three outcomes: parent no longer needs it ⇒ delete; parent inlines it ⇒ prove and
reroute; parent proves it under another name ⇒ delegate one to the other. Then re-grep the
leaf's stated missing input — see [[flt-audit-refuting-check-unrun.md]] — it has often landed.

Measured 2026-08-02, `flt-lean-91`: `geomPic_exists_bcDiv_of_divAct_fixed`
(`ModularCurve/HyperellipticJacobian.lean`) had one occurrence tree-wide; its 28-line statement
sat inside `geomPic_descent`; its stated blocker `placeAct_transitive` had been proven the
previous day, 265 lines ABOVE it. Prove-and-reroute was +52/−35 in one file, sorries 22 → 21,
parent's proof 33 lines → 6.

Two riders. **Adding a hypothesis is free at a dead leaf** (no call site can break) — check
only that the one consumer you are about to create already carries it. **Verify with BOTH
counts**: the build's `declaration uses 'sorry'` set and the comment-stripped source `sorry`
token count must move by the same amount, or an anonymous inner `sorry` was swapped in.
