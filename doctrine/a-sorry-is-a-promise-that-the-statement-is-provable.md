## A `sorry` is a PROMISE that the statement is provable

(2026-07-29, orchestrator error, caught only because an agent quoted the file's
own audit back at me.)

A build was red at a call site of `one_le_break`. To unblock a release I told the
merge worker to `sorry` its body. **The statement had already been refuted 700
lines above in the same file** — the audit gave the witness (the 2-dimensional
irreducible of `S₃ = Gal(L/ℚ₃)`, both breaks `1/2`, against a claimed `≥ 1`,
because in the Swan normalisation breaks are positive RATIONALS and `≥ 1` is
Hasse–Arf for a *character* only) and ended "That theorem has been WITHDRAWN".

`sorry`ing it manufactured a **false leaf with two live consumers**, which is
strictly worse than the build error it fixed: a false leaf can never be closed,
and everything above it is worthless. The repair was to DELETE the declaration
and fix its consumers, which is what the audit had already prescribed.

So, before writing `sorry` to unblock anything:

- **Read the file's FALSITY AUDIT sections.** They outrank any instruction,
  including one from the orchestrator. This file's own rules are not a substitute
  for what a module has already established about itself.
- `sorry` is honest only when you can VOUCH the statement is provable. The clean
  case, from the same release: a tower step whose instance argument the merge made
  unreachable — proven on `main` across 241 diffed lines, so the statement is
  vouched and the regression is environmental. That one was `sorry`d correctly,
  with the deleted lines quoted verbatim in the comment so the repair is
  *restore reachability → delete the `sorry` → paste them back*.
- If you cannot vouch for it, **delete the declaration and repair its consumers.**

**Corollary — one `declaration uses 'sorry'` warning can hide SEVERAL sorries.**
`exists_isSwanExponentAt` carries FIVE inner `have … := sorry` behind a single
warning (verified on `main`: lines 4790 `hterm`, 4798 `hsep`, 4801 `hin`, 4807,
4952). The warning set counts DECLARATIONS. Three separate agents reported that
count as "three", under names that do not exist. Strip comments, grep `sorry`
tokens, compare against the warning count; a mismatch is anonymous inner sorries
that no frontier scan will ever surface and nobody will ever be dispatched at.

