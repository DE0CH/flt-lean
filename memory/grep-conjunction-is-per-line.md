---
name: grep-conjunction-is-per-line
description: "`grep A | grep B` over Lean source is a false negative by construction, because signatures wrap across lines"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 7ee3d710-01bf-4478-892b-24822221e175
  modified: 2026-08-01T16:24:52.702Z
---

Never establish an absence with a conjunctive `grep A | grep B`. `grep` is
line-oriented and Lean signatures wrap, so two tokens from one declaration
routinely sit on different lines and the conjunction matches nothing.

Measured 2026-08-01 (`flt-lean-321`, `X0.lean` vs `MazurTorsion.lean`):

    44688     (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R) :
    44689     Nonempty (W.toAffine.CoordinateRing ≃ₐ[R] (C • W).toAffine.CoordinateRing) :=

`grep CoordinateRing | grep VariableChange` over `Fermat/` → **0 hits**.
`grep CoordinateRing` alone → **3334 hits, including this one.**

**Why:** the searched tokens are on adjacent but distinct lines. The failure is
silent and points the wrong way — it manufactures confident absence claims.

**How to apply:** search ONE distinctive token and read the hits; or search a
window (`grep -A6`, `rg -U`, a declaration-level scan). Reading forty hits costs
a minute; the false negative here produced a docstring instructing every future
agent to re-derive 285 lines of already-proven code.

Two riders:

* **"nothing usable" ≠ "not in the tree".** A block can be real and merely
  unreachable (here `MazurTorsion.lean` `public import`s `X0.lean`, so it is
  DOWNSTREAM and invisible from it). Write "exists at `<file>:<line>`,
  DOWNSTREAM, needs a hoist", never "missing" — only the summary sentence
  survives into the next task prompt. See [[flt-inventory-audits-understate-what-exists]].
* **Measure hoistability before understanding the mathematics.** A token scan of
  the block against every declaration in its own file says whether it is
  self-contained; if it is, "somebody should build this" becomes "move these N
  lines".

Related: [[flt-absence-audit-greps-consumer-vocabulary]],
[[audit-lacks-x-is-about-x]], [[lean-identifier-regex-swallows-brackets]].
