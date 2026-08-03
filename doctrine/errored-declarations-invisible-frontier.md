## errored declarations invisible frontier

(Cut verbatim out of CLAUDE.md's `THE GOAL: fully formalize Fermat's Last Theorem, no sorry, n` section at the 2026-08-03 doctrine split; nothing reworded.)

**Third category, invisible to BOTH counts: an ERRORED declaration**
(2026-07-25). A declaration whose proof fails to elaborate — `maximum
recursion depth`, a failing tactic, anything red — is `sorryAx`-tainted and
poisons the transitive cone, but it emits **no** `declaration uses 'sorry'`
warning and contains no `sorry` token in its source. So it is missed by the
direct-sorry warning set, missed by a source scan, and its `.olean` goes
stale, silently blocking every downstream module from building. Nobody is
ever dispatched at it, because no frontier scan can see it.

Found when `lineNumerator_mul_lineNumeratorNeg` in `WeilPairingDescent.lean`
— PROVEN and verified clean in its author's worktree — began failing after
merge with `maximum recursion depth has been reached`, blocking the whole
file. It surfaced only because an agent working in that file happened to
report it. **So: errors are a separate frontier that only a build or a
per-file `diagnostics` reveals. Treat any hard error as an immediate defect
with a named owner (CLAUDE.md's sorry-gate rule (b)), and do not assume a
clean direct-sorry scan means a clean tree.** A proof that verified in one
worktree can error on main; resource-limit `set_option`s are the usual fix.

**AND AN ERRORED DECLARATION DISGUISES ITSELF AS A MISSING ONE, IN THE SAME
FILE, HUNDREDS OF LINES AWAY** (2026-07-31, `HilbertClassFieldNormal.lean`). A
heartbeat timeout does not merely fail its own declaration — the declaration is
never added to the environment, so every later USE of it reports

    error: …:1029:8: (kernel) unknown constant 'NumberField.conj_unramifiedAbelian'

and that is the error a reader's eye lands on, because it is the last one lake
prints. It reads as a rename, a bad merge, or a declaration lost to a
merge-side removal — exactly the class-6/class-7 shapes this file spends pages
on — and every one of those diagnoses sends you to `git log -m -S` instead of
to the real cause 600 lines above. Here the real cause was two
`(deterministic) timeout at isDefEq` / `at whnf` lines earlier in the same log,
and the fix was one `set_option maxHeartbeats 1600000 in`.

**So read a build log from the TOP, and never diagnose an `unknown constant`
against a name that is declared in the very file being compiled.** If the name
is right there in the source, the constant is not missing — its declaration
errored. Grep the log for `timeout`/`maximum recursion` before touching git.

Two cost-shapes worth knowing, both from that declaration:

* The timeouts were `isDefEq`/`whnf` unification through stacked
  `AlgEquiv → RingHom → FunLike` coercions over `IntermediateField` subtypes.
  Files whose OBJECTS are intermediate fields cannot avoid this, so a heartbeat
  bump there is a legitimate fix rather than a smell.
* **`let`-binding a structure literal is the expensive way to name a map;
  `obtain`-ing it from an `∃` is the cheap one.** A `let`-bound literal stays in
  the local context and every subsequent `isDefEq` unfolds it. Destructing an
  existential makes the map a genuine free variable whose only handle is its
  characterising equation, and nothing can unfold it. Same mathematics, and it
  was the difference between elaborating and not.

