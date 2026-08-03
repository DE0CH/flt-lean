## A target that exists only on `merger` is workable — put it in a NEW MODULE
(2026-07-31, `flt-lean-335`.) The dispatch prompt for
`exists_nonconstant_toAbelianScheme_of_baseChange_relPoint` said: it was cut on a
branch, it is on `merger`, and if it is not in your worktree, **"WAIT for the release
rather than restating it"**. The check was right — the leaf was on `merger` at
`df076668` and absent from `main` — but "wait" is not an action an agent can take. The
loop has no pause; ending the turn is death, and a worker that reports "blocked until
the release" burns a whole worktree-cycle and delivers nothing.
There is a third option between *restating it in the file* (which conflicts with the
merge worker's own copy, guaranteed, because that file is being rewritten by thousands
of lines per release) and *waiting*:
**State the theorem VERBATIM in a new module, prove it there over named atoms, and
leave the merge worker a one-line delegation to write.**
- A new file cannot conflict with anything. The only edit to the contested file is one
  `public import` line, which merges trivially wherever it lands.
- Put it under `Fermat/FLT/Mathlib/…` when the statement mentions nothing specific to
  the file it was cut from — which is common, since leaves get cut *because* they are
  the level-free residue. Then the sibling curve file wanting the same theorem gets it
  for free instead of restating it a third time.
- Use a distinct NAMESPACE (`Fermat.WeilRestriction.foo`), not a distinct name. The
  merge worker's job is then `:= Fermat.WeilRestriction.foo h₁ h₂ h₃` with the
  hypotheses in the same order, and nothing has to be renamed if the release lands
  first.
- Say so in `to_merger`. The commit alone is not read.
Cost of getting this wrong in the other direction is asymmetric: a duplicate proof of
one theorem cannot be carried (the name collides), so restating in-file forces a merge
worker to CHOOSE between two branches' mathematics; a new module forces nobody to
choose anything.
The residue's top theorem is then FREE-FLOATING until the release wires it — that is
expected and is not a defect to chase. Record it in the module docstring so the next
floating sweep does not delete it.
**Also: `lake` is not on `PATH` in a fresh agent shell**, even working locally on the
worktree's own host, and the failure is `lake: command not found` with `EXIT=127` —
which reads like a broken worktree rather than a shell setup. `export
PATH="$HOME/.elan/bin:$PATH"` first, in every Bash call (shell state does not persist
between calls).

