## `merger` CAN BE RED — never base a branch on it without building it first
(2026-07-31, cost one agent ~90 minutes.) A task prompt described the "STATE OF
THE ART" using facts that exist only on `merger` (a structure field `smoothM`
added on 2026-07-30, and an audit written the same day). The obvious inference —
"so I must work from `merger`, otherwise the premise of my task is absent" — is
what the *previous* release windows had taught. It was wrong that day, and the
failure mode is worth stating because it is invisible from the task prompt:
**`merger` is a work-in-progress tree, not a better `main`.** Release 27 was
NOT published precisely because `ModularCurve/X0.lean` had not built since
release 25 and still had ~193 errors after nine repairs. `main` was
deliberately left at the last GREEN release, and
`~/.flt-release-lake/build` still matches it. So on `merger`:
* `lake build <anything importing X0>` fails with hundreds of errors that are
  none of your business and that you must not "fix";
* the release-artifact seed does not match the tree, so the "51 seconds"
  figure a prompt quotes becomes a multi-hour rebuild of ~5000 modules;
* you cannot verify anything, and an unverified structural edit is worth less
  than no edit.
**The rule: build before you trust a branch, and prefer `main`.** `main` is the
only tree guaranteed to pair with `~/.flt-release-lake/build`. If your task's
premise is merger-only, do the work against `main` anyway (the declarations and
the plumbing sites almost always exist there too, just at an earlier state),
verify it green, and put a precise conflict note in `to_merger` saying where the
two edits collide and how to resolve them. A verified change on `main` plus a
merge note beats an unverified change on `merger`.
Two mechanical consequences, both hit the same day:
* `queue1` records `AUDITED: <sha of main>`. **That sha is the tree the loop
  expects you to work in.** Check it (`head -1 ~/.flt-loop/queue1`) against your
  worktree's HEAD before deciding what to base on — it is the cheapest possible
  disambiguation and it is authoritative.
* If you have already advanced a worktree to `merger` and built, `git reset
  --hard main` is not enough: `.lake/build` is then a mix of merger-built and
  release-snapshot oleans and lake will rebuild everything back. **Re-run the
  seed** (`rsync -a --delete ~/.flt-release-lake/build/ .lake/build/`) before
  building; it takes seconds warm and saves hours.
Also: `lake` is not on `PATH` in a fresh agent shell. Every build line needs
`export PATH="$HOME/.elan/bin:$PATH"` first, or it dies with
`lake: command not found` and `EXIT=127` — which reads like a broken worktree
and is not one.
