---
name: flt-scope-is-deyaos-call
description: "Deyao 2026-07-25 — the project's scope is deliberately enormous; whether something is worth the effort is HIS call, not mine. Everything in service of a sorry-free FLT is worth it, including building a whole theory that does not exist yet."
metadata: 
  node_type: memory
  type: feedback
  originSessionId: eda93c26-088c-4639-b0f3-bf5ee7a16ed8
  modified: 2026-07-25T18:12:36.220Z
---

Deyao, 2026-07-25, after I had repeatedly editorialised about cost:

> "the scope of this project is deliberately enormous, and whether something is
> worth the effort or not is my judgement call, not yours. and i call that
> everything in service of proving FLT without a single sorry is worth it, and
> you should pursue it. this includes but not limited to bring an whole entire
> theory/framework if it does not exist yet."

**The rule.** Do not perform cost-benefit analysis on scope and present the
verdict. Effort estimates are useful INFORMATION and should be given; the
CONCLUSION "therefore not worth it" is not mine to draw. If a node needs a
theory mathlib does not have — class field theory, p-divisible groups,
crystalline cohomology, isogenies of elliptic curves, Verschiebung — the answer
is to build it, not to report that it is large.

**Why:** "that would be a major development in its own right" is true of most
of what remains, and it is not a reason to stop. A sorry-free FLT is the goal;
the tree is resolved top-down and every gap gets filled however deep it goes.

**How I got this wrong** (so the pattern is catchable):
- Told the `exists_artinSymbol_isNarrowPrincipal_ray_class` owner "**Do not
  start building class field theory**" — a direct instruction not to do the
  thing that node needs. RETRACTED.
- Called the Pantograph port "not worth it" on a toolchain gap; Deyao said to
  do it anyway; it took three annotated edits and one field port, and now
  works. My estimate was wrong AND the verdict was not mine to give.
- Framed a repo-wide interface change as needing "one owner dispatched
  deliberately" as though that were a reason for hesitation rather than a
  dispatch plan.
- Wrote "days of internals work plus a recurring tax at every toolchain bump,
  which cuts against the stop-managing-things principle" — importing an
  unrelated principle to argue against scope.

**How to apply.** When a leaf needs absent machinery: say what is missing, what
building it involves, and what it unblocks — then dispatch owners for it. Ask
Deyao only when two routes differ materially in KIND (not in size), or when the
leaf may be false/vacuous ([[flt-minimal-orchestration]] governs HOW to build;
this governs WHETHER, and the answer is yes).
