## A MODULE BEHIND A RED MODULE IS UNVERIFIED — "everything else builds" means "everything lake REACHED"
(2026-07-31, `flt-lean-78`, on `Modularity/Patching.lean` at release 27.)
`RELEASE-27-HANDOVER.md` says *"Every module except `ModularCurve/X0.lean` builds"*, and
that sentence is true of the modules `lake` got to. It is not a statement about the tree.
`lake build` walks the import graph and STOPS at a failed dependency, so every module
DOWNSTREAM of the red one is not compiled, emits no diagnostic, and contributes nothing to
the `declaration uses 'sorry'` set — while looking, in every report, exactly like a module
that passed.
`Patching.lean` sits behind `X0.lean` (via `FreyCurve/MazurTorsion`; 341 Fermat modules in
its cone, checked rather than assumed) and was carrying **two hard errors**: a stranded
conclusion fragment `(∀ i, n ≤ e i) ∧` inside a tactic block, and a call site passing 17
arguments to an 18-binder theorem. Both would have surfaced as a *further* release-build
round after X0 was repaired — which is the "budget three rounds minimum" rule arriving
through the import graph rather than through the diff.
**So when a release report names ONE blocker, the honest reading is "one blocker so far".**
Before believing a module is green, check whether it is downstream of the red one:
    python3 - <<'EOF'   # BFS the ^(public )?import Fermat... edges from your module
    ...  # and ASSERT each visited file exists — a swallowed FileNotFoundError
         # truncates the walk and manufactures the answer you were hoping for
    EOF
It costs seconds. Then, since the cone genuinely cannot be compiled, the substitutes — and
be honest about which of them actually works:
* **READING the declaration your target is consumed by is what found both errors here**,
  not any scan. They were three lines apart in the one theorem that calls the leaf I was
  dispatched at. If your target is a leaf, its consumer is a cheap and high-yield place to
  look, because a re-cut edits both and a merge can land only one side.
* **Extracting explicit binder lists and diffing them against a call site VERIFIES an
  arity suspicion in seconds** — `exists_auxDeformationPresSurjection` wants eighteen and
  the call passed seventeen — and it is worth doing before you touch a signature. But run
  tree-wide it is NOISE: mine produced nine hits across `Modularity/` and
  `GaloisRepresentation/` and **all nine were false positives**, in modules that had just
  built green. Implicit and instance arguments, partial application and named arguments all
  defeat a text-level arity count. Use it to confirm, never to search.
* **Comment-nesting depth plus the depth-0 stray count** is the one scan that does find
  things blind, and the stray half is the half that pays — see the section below on an
  orphaned opener scoring zero, of which `MazurTorsion.lean` was a live instance the same
  afternoon.
A scope-balance scan over these files is not worth running as an error check: this tree's
bare `end`s and anonymous `section`s made mine report four modules, of which the ones I
could check were legitimate. Difference it against pre-merge `main` or skip it.
**The seeding note that made the check affordable**: `~/.flt-release-lake/build` rsynced over
a `merger`-based worktree left only ~60 of 5597 targets to rebuild, because the release
snapshot is most of the cone even when 206 branches have landed. Seed first, always; the
question "is my module reachable" is then minutes, not hours.
