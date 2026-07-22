---
name: flt-glue-first-no-floating-haves
description: "Deyao 2026-07-21: proven haves stacked before a trailing sorry are floating too — write the GLUE (full assembly outline with sorried steps) first, then recursively resolve"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 4f31fd20-64ff-4ddd-97fd-59258398c883
---

Deyao (2026-07-21): accumulating fully-proven `have` bricks in front of a
single trailing `sorry` is a workaround of the no-floating policy — haves
without a written consumer are effectively floating. The policy's point is
to build the GLUE first: write the complete assembly/outline down to the
final `exact`, with every not-yet-proven step as an explicit, precisely
stated sorried `have`, then recursively resolve the sorries.

**Why:** the glue is where the design lives. Writing components first
means guessing how they will fit — the fit exists only in transcript or
thinking tokens (not durable, not checked), so components come out
subtly wrong and don't compose. Writing the glue first (a) type-checks
the composition NOW, (b) turns the remaining work into concrete,
enumerable sorried statements, (c) makes each iteration visibly close
one named gap.

**How to apply:** at any frontier, first replace the bare `sorry` with a
full skeleton: definitions and choices as real code, every believed-true
step as a sorried `have` with its exact statement, final assembly written
and compiling. Only then start proving the sorried steps, innermost
first. Statement adjustments during resolution are normal and cheap —
that is the recursion, not a failure. See also
[[flt-no-private-shielded-floating]].

**Extension (Deyao, 2026-07-22): every bound `have`/`let` must be
consumed.** Binding a proven `have` that nothing later uses is floating
at the have level; prune unused ones before committing (verify each
prune compiles). Enforced mechanically: a PreToolUse hook
(`.claude/lean-pretool-reminder.py` in the FLT worktree) reminds before
every lean-lsp call: sorry only in place of a proof (never a
proposition), every have/let consumed.

**Corollary (Deyao, 2026-07-21): `sorry` only against a stated goal.** A
`sorry` may only replace the PROOF of an explicitly written proposition
(`have h : <full statement> := by sorry`, or a stated theorem's `by
sorry`). Never a bare `sorry` covering an unstated remainder of a
tactic block, and never `(by sorry)` as an application argument whose
goal exists only implicitly in the elaborator — name the statement
first, then sorry its proof.
