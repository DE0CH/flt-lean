import Lean

/-!
# The sorry gate

`#assert_no_sorry decl` makes elaboration FAIL (a hard compilation error)
whenever `decl` still depends on the `sorryAx` axiom, and additionally
enforces the project's axiom invariant (only `propext`, `Classical.choice`,
`Quot.sound` are permitted).

Purpose (Deyao, 2026-07-16): while any node of the dependency tree is open,
the root target of `lake build` must fail with an *error*, not a warning —
a failed compilation is a stronger signal to keep working than a warning.
The gate lives in the root module `Fermat.lean`, applied to
`fermat_last_theorem`, so every library module still builds incrementally;
only the final aggregator errors until the tree is sorry-free.

A gate failure is therefore the EXPECTED build outcome during development:
it means "open nodes remain — continue the loop". Any build error *other*
than the gate message is a genuine defect to fix immediately.
-/

open Lean Elab Command

/-- Fail compilation if `decl` depends on `sorryAx`; also fail if it uses
any axiom outside `propext`, `Classical.choice`, `Quot.sound`. -/
elab "#assert_no_sorry " id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverload id
  let axioms ← liftCoreM <| collectAxioms name
  if axioms.contains ``sorryAx then
    throwError "SORRY GATE FAILED: '{name}' still depends on `sorryAx` — \
      the dependency tree has open nodes. Run \
      `grep -rn \"sorry\" Fermat --include=\"*.lean\"` for the frontier and \
      continue the loop (resolve or decompose a node → lake build → \
      axiom audit → commit/push → update PROGRESS.md → re-check)."
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for ax in axioms do
    unless allowed.contains ax do
      throwError "AXIOM INVARIANT VIOLATED: '{name}' depends on the axiom \
        '{ax}', outside [propext, Classical.choice, Quot.sound]."
  logInfo m!"sorry gate passed: '{name}' is sorry-free; axioms: {axioms.toList}"
