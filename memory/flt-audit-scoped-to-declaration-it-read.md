---
name: flt-audit-scoped-to-declaration-it-read
description: "A \"hypothesis H is load-bearing\" audit is scoped to the declaration its author read; follow H to the line that spends it and ask which declaration owns that line."
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 9e7cbc40-dcc4-495b-8a15-92108e9b1509
  modified: 2026-08-01T12:37:17.238Z
---

An audit concluding **"hypothesis `H` is load-bearing and cannot be dropped"** has
established that only for the declaration its author was reading. The repair very often
belongs one or two levels UP, where it is invisible from the leaf — because from the leaf
`H` genuinely is consumed.

**Why:** `flt-lean-265` (2026-08-01) closed `exists_aut_of_isTorsionReduction_two`, the whole
residue-characteristic-`2` gap of the `B₀` cluster, open since 2026-07-29 solely because a
careful dated audit on its odd sibling said `hq2 : q ≠ 2` was load-bearing. Both of that
audit's factual bullets were true. Its conclusion — "so `q = 2` is a SEPARATE leaf" — was
false: the division by `2` is a step of a mathlib-facing lemma two levels up
(`variableChange_valuation_of_valuation_Δ_eq_one`, about valuation subrings, no `q` in it),
and the leaf spends `hq2` at exactly ONE line. The fix was a second proof of the upstream
lemma, not a second leaf.

**How to apply:** one `grep` per hypothesis — find the line that SPENDS `H`, and ask which
declaration owns it. If that is not the declaration you are auditing, your verdict is about
somebody else's proof. An audit that traces a hypothesis to a real obstruction and stops at
the module boundary yields a correct diagnosis attached to the wrong node, which becomes a
leaf nobody can close.

Reusable mathematics from the same run: **`max (v 2) (v 3) = 1` in every valuation subring of
every field** (`3 - 2 = 1`), so a `2`-inverting and a `3`-inverting proof together need no
residue-characteristic hypothesis. When a `2` blocks you, check whether `3` is a unit and look
for the relation in which your unknown appears ALONE — for Weierstrass models that is the
`b₈`-relation, which isolates `r`; `s` and `t` then fall out as roots of monic quadratics.

Same family as [[flt-leaf-cost-estimates-are-hypotheses]] and
[[flt-inventory-audits-understate-what-exists]], but about a POSITIVE verdict rather than an
absence claim, which is why it survives review: the audit is right about everything it checked.
