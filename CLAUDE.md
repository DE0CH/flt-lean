# Project Notes — flt-lean

This repository was split out of Deyao's dissertation repo on
2026-07-22 (`git subtree split --prefix=fermat`); the full commit
history of the formalization is preserved. The project root IS the
Lean package (formerly the `fermat/` subfolder).

## THE DEGENERATE OBJECT REFUTES EVERY UNGUARDED PERFECTNESS CLAUSE

(2026-07-31.) `exists_tateWeilRawFamily_of_qAdicWeilSystem` was refuted with no
arithmetic at all: take the ZERO abelian scheme, `A = S`, `f = 𝟙 S`.
`AbelianSchemeStruct` asks for a group law plus `IsProper`, `Smooth`,
`GeometricallyConnected` — **there is no nontriviality axiom in it**, and `𝟙 S`
satisfies all three, its fibres being points. Then every `RelPoint` is a
singleton, so `TatePt` is a singleton, so the ALTERNATING clause
(`C N t t ∈ 𝔪`) and the PERFECTNESS clause (`∃ t s, IsUnit (C N t s)`) are the
same statement about the same element and contradict each other. The two proven
consumers inherited the defect, because their conclusions carry a unit clause
too.

The general shape, worth running as a standing check: **any leaf whose
conclusion asserts a UNIT VALUE, a NONDEGENERACY, or a BASIS needs a hypothesis
that the object is nonzero, and that hypothesis is easy to lose in a cut** —
the geometric half of a decomposition keeps `hdim`, the arithmetic half gets
the pairing handed to it as a binder, and nobody notices that the pairing's own
axioms are vacuously satisfiable on the zero object. Here the finite-base
sibling had exactly the right hypothesis (`hne`) with the reason written on it,
and the characteristic-zero half had simply dropped it. **When two halves of a
development mirror each other, DIFF THEIR BINDER LISTS** — that is a
five-minute check and it found this one.

Corollary about audits: this leaf carried two 2026-07-30 falsity audits, both
CORRECT, neither of which saw it. They were about the normalisation, and they
presupposed a nonzero Tate module. CLAUDE.md's existing rule — a second
restatement VOIDS the earlier audit — is what prompted re-running it from
scratch, and it earned its keep.

## AN INTERFACE PREDICATE CAN BE UNDER-COMMITTED: SATISFIED BY THE WRONG NORMALISATION

(2026-07-31, same cluster, and it is the subtler half.) `IsTraceDualFunctional`
pins a functional `θ : O → ℤ_q` by four clauses, and
`exists_traceDualFunctional_of_adicPin` PROVES it, so it looks settled. It was
not: at a RAMIFIED `I` the four clauses are satisfied by `θ_m = Tr(δ π^m ·)`
for EVERY `0 ≤ m ≤ e-1`, not only by the correct `m = 0`. Consequences:

- the third clause's hypothesis ("`φ` kills `I^k`") was one the intended input
  never satisfies — the Weil functional kills `I^{e·k}` — so the clause was
  dead at every positive level, and the leaf whose whole route it is could not
  be started;
- every constant it could return lay in `(jπ)^{(e-1)k}`, hence was a NON-UNIT,
  hence could never satisfy the consumer's perfectness clause.

**The producer was already correct** — it builds `θ` as a GENERATOR of
`Hom_{ℤ_q}(O, ℤ_q)`, which is `m = 0` on the nose — so strengthening the
statement cost its proof nothing. One `have hNk : k ≤ N` was deleted, and it
was the line that had been throwing the extra strength away.

The lesson generalises past this file: **when a leaf's prescribed route "just
does not work", check whether the INTERFACE it routes through is weaker than
the object that satisfies it.** A predicate proven inhabited is not thereby
adequate; ask what ELSE inhabits it. The mechanical test is a scaling family —
perturb the intended witness by a unit, a uniformizer power, a twist — and see
which clauses still hold. If a wrong scaling survives every clause, the
predicate cannot support any conclusion that needs the right one.

Related trap in the same vocabulary, since it cost a false start: a
"perfect pairing `𝒪_D/I^k × O/(jπ)^k → ℤ_q/q^k`" gloss in a docstring can be
WELL-DEFINED-FALSE while the formal clauses beside it are true. `Tr(δ I^k 𝒪)`
is `q^{⌊k/e⌋}ℤ_q`, not `q^k ℤ_q`, so that pairing does not descend at all for
`e ≥ 2`. Read the CLAUSES, not the gloss.

## After a fast-forward, RSYNC the release snapshot instead of rebuilding

(2026-07-31, `flt-lean-373`.) A worktree seeded at release *R* and then
fast-forwarded to a later `main` has an `.olean` set for *R*, so the first
`lake build` of anything rebuilds the whole changed cone — >10 minutes before it
even reaches your own module, and that is the state of EVERY worktree whose
targets were introduced after its seed (mine did not contain its three targets
at all until the ff).

`~/.flt-release-lake/build` is the current snapshot and `~/.flt-release-lake/sha`
names the commit it was built at. **The snapshot is valid for your tree exactly
when no commit between that sha and your HEAD touches `Fermat/`:**

    S=$(cat ~/.flt-release-lake/sha)
    git merge-base --is-ancestor $S HEAD && git log --oneline $S..HEAD -- Fermat/

Empty output → the oleans match your sources, so

    rsync -a --delete ~/.flt-release-lake/build/ /scratch/chend-flt/flt-lean-N/.lake/build/

is a complete substitute for the rebuild (2.3G, under a minute). It replaces only
the PROJECT build; `.lake/packages/mathlib/.lake/build` is a separate directory
and is untouched. Kill your own `lake`/`lean` first (**by PID after checking
`/proc/<pid>/cwd`**, never by pattern) — rsyncing under a live build is exactly
the torn-snapshot state the release seeder's own guard exists to prevent.

If the `git log` is NON-empty the snapshot is stale for those modules and you
must build; the check is cheap and there is no partial-credit version of it.

## Missing tools: brew install is pre-authorized

(Deyao, 2026-07-21.) If a needed tool is missing and available through
Homebrew, run `brew install <tool>` directly — no need to ask first.

## Fleet integration: rescan sorries at every agent completion and re-dispatch

(Deyao, 2026-07-22.) When a subagent finishes: merge and verify its
branch, then SCAN its file(s) for the sorries it left (its report lists
them; confirm against the source), and DISPATCH new agents onto those
leaves — possibly several agents per completion when the leaves are
independent (disjoint decomposable clusters get separate owners rather
than one successor inheriting the whole file by default). The loop
invariant: every sorry has an owner at all times; an agent completing
must never strand its remaining leaves unowned. Track the new leaves in
progress-entries.json (wip flags at dispatch) as part of the same
integration step.

**A prompt MENTION is not ownership — ownership is a record's own TARGET** (2026-07-27).
The rule below (grep the prompt) is necessary but not sufficient, and its naive form
manufactured a phantom *non*-dispatch. Task prompts contain "coordinate, do not edit:
`flt-lean-36` owns `X`" notes written by the orchestrator. When that worktree is
**reallocated** the note goes stale — and a later grep for `X` hits the orchestrator's
own stale claim and reads it back as evidence that `X` is owned. Self-reinforcing:
the more carefully coordination is written down, the more convincing the phantom.

So the check has three parts, all required. A leaf is owned iff some record:
(a) names it in its own **`TARGET:` line** — not merely anywhere in the prompt;
(b) is the **latest** record for its worktree (the file is append-only; earlier
records for a reallocated worktree are history, not state); and
(c) that worktree is still `claimed`.

A hit that fails any part is a stale note. `flt-lean-173` reached this conclusion
correctly against a gate this file's rule had told it to trust, and was right.

**The three-part test does NOT catch a stale claim in a COMMIT MESSAGE** (2026-07-27).
Two `ModThree.lean` leaves sat in an "each owner says the other owns it" loop.
`flt-lean-78`'s commit message ended `Still open in this cluster, owned elsewhere:
aeval_minpoly_eq_prod_sub_integralClosureLE, smul_integralClosureLE` — **true when
written, false by the time it merged**, because `flt-lean-77` closed both
concurrently on a parallel branch (`bb97c541`, which is not an ancestor of
`flt-lean-78`'s tip and reached main separately via `9269f17f`). Nobody was
dispatched at them for a cycle, and when someone finally was, there was nothing
to do.

The note lived in git history, not in `~/.flt-inflight.jsonl`, so grepping records
— however carefully — could not see it. **The only reliable ownership evidence is
the compiler**: a green `lake build`'s `declaration uses 'sorry'` warning set says
what is actually open, and it costs one build. Prefer it to any prose claim about
what is "still open", including your own from an hour ago. A leaf named as open in
a commit message, a docstring, or a report is a *hypothesis to check*, never a fact.

Corollary for agents: **do not write "still open, owned elsewhere" lists into commit
messages.** They are unmaintainable by construction — the commit is immutable and the
frontier is not. Put such observations in the final report, where the orchestrator can
act on them while they are fresh.

**Check overlap by grepping the PROMPT, not the `targets` field** (2026-07-25).
`~/.flt-inflight.jsonl`'s `targets` is harvested by a regex for bold
`**\`name\`**`, so tasks not written in that style get junk targets (one batch
recorded `['diagnostics', 'lean_leansearch', …]`). Before dispatching at a leaf,
grep the full `prompt` of every in-flight record for the leaf NAME. Skipping
this let two agents cut the SAME node — `exists_isWeaklyUniversalOnIdentified`
— along Schlessinger in two incompatible ways, producing an eight-hunk
mathematical conflict that had to go back to an author to reconcile. Noticing
that another worktree is merely "in the same file" is not enough; the file is
not the unit of ownership, the declaration is.

**"Merge FIRST, then dispatch" is an ordering, not a sequence of words**
(violated 2026-07-25). A worktree fast-forwards to main at dispatch, so a
successor dispatched at a leaf that still lives only on an unmerged branch
fast-forwards to a main WITHOUT that leaf and finds nothing — a phantom
dispatch manufactured out of a correct report. It happened with three
`Deformation.lean` successors sent off the strength of an agent's report
while its branch was still resolving a conflict. If the branch cannot be
merged yet, the successors WAIT; queue them, do not dispatch them.

Same-FILE leaves may get concurrent owners (Deyao, 2026-07-22): each
agent works in its own git worktree on its own branch, and merging
concurrent edits to one file is what git is designed to handle — leaves
are disjoint regions, so merges are clean or trivially resolvable at
integration. Do not serialize a file's independent leaves behind one
owner out of conflict fear; partition them.

## Fleet dispatch: fixed pool of 26 numbered worktrees

(Deyao, 2026-07-23; extended 2026-07-24.) Subagent dispatch runs over a
FIXED pool of 26 worktrees, each on its own same-numbered branch, each
with its own already-running systemd instance — `lake serve` on FIFOs,
scoped to that worktree. Live allocation state:
`~/.flt-worktree-pool`, one line per worktree, `<name> free` or
`<name> claimed`.

**STALE BELOW (2026-07-25): the systemd units are DELETED.** The batch
descriptions survive only for the `.lake`-on-`/scratch` layout, which is
still true and still the reason `lake` must run on the assigned host. Every
mention of `flt-report-server@` / `flt-lake-socket@` / `.report-server` is
historical — those unit files were removed from `~/.config/systemd/user`
so nothing can start them, and `.report-server` no longer exists in any
worktree.

- **Batch 1, `~/flt-lean-1` .. `~/flt-lean-13`**: template unit
  `flt-report-server@.service`, `WorkingDirectory=%h/%i`.
- **Batch 2, `~/flt-lean-14` .. `~/flt-lean-26`**: same layout as batch 3 —
  source tree in `$HOME`, only `.lake` and `.report-server` symlinked to
  `/scratch/chend-flt/flt-lean-N/`. Artifacts live off `$HOME` because a
  worktree costs ~5.4G (4.6G of it mathlib oleans in `.lake/packages`, 826M
  project build) and the 67G home volume filled up; `/scratch` is a 9.7T
  local disk. **`/tmp` is NOT an option — it is a 9.7G volume, one
  worktree's worth.** Note `/scratch` is machine-LOCAL and not backed up;
  only `.lake` and uncommitted work would be lost, since branch refs live in
  the main repo's object store.
- **ONE unit template, `flt-report-server@.service`** (`WorkingDirectory=%h/%i`),
  serves every worktree. A second template rooted at `/scratch` existed
  briefly while whole worktrees lived there; it was deleted 2026-07-25 once
  the layout settled on "sources in `$HOME`, artifacts symlinked" — there is
  deliberately only one way to run a worker.
- `.claude/worktree-pool-hook.py` resolves a pool entry by trying each
  root in `ROOTS` in order, so batch-1 names still resolve under
  `$HOME`.
- A fresh batch-2 worktree needs `lake exe cache get` run in it once
  (with `XDG_CACHE_HOME` pointed at scratch so the ltar cache does not
  refill `$HOME`) BEFORE its server is started — otherwise `lake serve`
  tries to build mathlib from source.

- **Batch 3, `~/flt-lean-27` .. `~/flt-lean-42`** (Deyao, 2026-07-24): same
  layout as batch 2 — source tree in `$HOME`, `.lake` and `.report-server`
  symlinked to `/scratch/chend-flt/flt-lean-N/`, served by the ORDINARY
  `flt-report-server@.service` template (the worktree is under `%h`).
  `.gitignore`'s `.lake/` patterns do not match symlinks, so `.lake` and
  `.report-server` are listed in `.git/info/exclude` instead.
- **Pool states**: `free`, `claimed`, and `suspended <agent-id>`. A suspended
  entry is never allocated — that is how a reduced worker count is enforced
  under memory pressure — and its third field is the stopped agent's
  transcript id, so the work can be picked up later with SendMessage.
- **RAM watchdog** (Deyao, 2026-07-24): a 10-minute cron reminds the
  orchestrator to check free memory. Procedure lives in
  `~/.flt-ram-watchdog-prompt.md`: below 200G free, restart a FEW worker LSPs
  at a time (closing their open files releases memory without interrupting the
  agents' work) and email; if that recurs 3× in an hour, suspend workers 4 at a
  time instead. Cron jobs are session-only, so **re-create it after every
  restart**.

- **Max 42 concurrent subagents**, one per worktree, 1:1. The harness cap
  `CLAUDE_CODE_MAX_CONCURRENT_SUBAGENTS` is fixed at launch (currently 50, set
  in the tmux launch line) — the pool, not that number, is the real limit.
- **FIFO task queue** (Deyao, 2026-07-23): `~/.flt-task-queue`, a
  plain text file — full agent prompts separated by lines consisting
  exactly of `=== TASK ===`. The orchestrator reorders and drops tasks
  BY HAND-EDITING THE FILE. To dispatch the queue head, spawn an agent
  whose prompt is the sentinel `{{FLT_QUEUE_POP}}`: the hook pops the
  top task, allocates a worktree, substitutes `{{FLT_WORKTREE}}`
  inside the queued prompt, and replaces the Agent call's prompt with
  the result. A pop with the pool full is denied leaving the queue
  untouched; a non-fleet spawn (no placeholder) while the queue is
  nonempty is denied with a dispatch-the-queue-first reminder.
- **Direct dispatch**: put the literal placeholder `{{FLT_WORKTREE}}`
  in the agent's prompt wherever its worktree path belongs.
  `.claude/worktree-pool-hook.py` (a `PreToolUse` hook on the `Agent`
  tool) finds a `free` entry, checks it is git-clean and its branch is
  an ancestor of main, fast-forwards it to main (`--ff-only`), marks
  it `claimed`, and substitutes the real path for the placeholder. If
  the dispatch cannot run immediately — the queue is nonempty (FIFO)
  or no worktree is free — the hook AUTO-QUEUES it: the prompt is
  appended to `~/.flt-task-queue` by the hook itself and the call is
  denied with a message giving the queue position and the
  `{{FLT_QUEUE_POP}}` instruction. **Agents own `.lake`** (Deyao,
  2026-07-25, reversing the old "never touch `.lake`" rule, which
  existed only because a systemd-managed `lake serve` owned it): the
  orchestrator advances the pointer to main and says in the prompt that
  the artifacts may be stale and may need rebuilding — and does nothing
  else about them. Managing them centrally is what turned private build
  problems into fleet-wide ones. A claimed worktree that is dirty or not an ancestor of main is
  not auto-corrected — the hook hard-crashes (traceback to stderr,
  exit 2, tool call blocked): that state means something beyond
  allocation went wrong.
- **On agent completion**: the orchestrator merges the agent's branch
  into main, then hand-edits `~/.flt-worktree-pool` to mark that
  worktree `free` again (no reliable hook fires on "the orchestrator
  finished merging" — `git merge` is just a Bash call among many, so
  this step is the orchestrator's explicit responsibility). Otherwise
  leave the worktree folder alone.
- **No per-agent server/file lifecycle management**: don't close LSP
  files, don't build reapers or memory-conservation tooling for this.
  Memory grows but stays bounded over time — accepted as fine, not a
  leak to chase.

## File edits: prefer the Write/Edit tool calls over scripts (soft rule)

(Deyao, 2026-07-22.) Edit files with the harness's Write/Edit tools by
default — not with shell/python scripts (heredoc `python3 - <<EOF`
string-replaces, `sed -i`, etc.). A scripted edit that is semantically
equivalent to a Write/Edit call (fixed string replace, whole-file
rewrite of known content) must BE a Write/Edit call: the script form
bypasses read-before-write and diff tracking for zero gain. Scripts
remain allowed where they are genuinely more capable than the tools —
e.g. programmatic transforms over structured data (bulk json updates
computed from state, generated content) — capability, not convenience,
is the test.

## THE GOAL: fully formalize Fermat's Last Theorem, no sorry, no undue axioms

(Deyao, restated 2026-07-16.) The goal is to **fully formalize Fermat's
Last Theorem in Lean 4** in this repository: the whole proof written as
Lean files that **compile without any `sorry`** and without undue
axioms (at most `propext`, `Classical.choice`, `Quot.sound`). The
method is **resolving a dependency tree**: the top theorem is proven;
every gap is an explicit stated-and-sorried node; go down the list,
fill in missing proofs, and iterate walking the tree — decompose deep
nodes into shallower ones, prove the provable ones — until the entire
tree is written and `lake build` passes the sorry gate. `PROGRESS.md`
is the authoritative tree.

**Counting the frontier: DIRECT vs TRANSITIVE sorries, and the comment
trap (2026-07-25 — both of these caused phantom dispatches).**

Two different numbers are both called "the frontier" and they are not
interchangeable:

- *Direct*: the declaration's own body contains `sorry`. This is what
  Lean's `declaration uses 'sorry'` warning reports, and it is the set of
  leaves that can be WORKED ON. **234 across 26 modules** as of `60313518`
  (release 4, 2026-07-27) — up from 175 at `0a976e16` earlier the same day.
- *Transitive*: the declaration's proof term reaches `sorryAx`, i.e. it is
  sorried **or consumes something sorried**. This is what
  `ProgressCensus.lean`'s census reports.

**A RISING count is not a regression — it is usually disclosure.** The jump to
234 is mostly the Cartier-duality island becoming visible: five `HopfAlgebra`
modules that nothing imported, hence never compiled, hence invisible to the
warning set *and* to the census. Wiring them in (`1492cecb`) made their sorries
countable for the first time. Decomposition does the same thing at smaller scale
— a node that closes over three named sub-leaves nets +2 while being real
progress. Read the delta alongside what closed, never alone.

**Do not trust a frontier number in this file — regenerate it.** The figures
above were 85/86 for a single day and were wrong by a factor of two by the next
morning: the tree grows leaves faster than prose records them, and six releases
landed during one bookkeeping run (the frontier moved 138 → 156 → 157 → 174 →
175 *while it was being counted*). Any count is stamped to a commit and stale
immediately. `flt-frontier.py`'s source scan **is** validated against the
compiler — at `a18c5c4d` it matched the build's `declaration uses 'sorry'`
warning set exactly, 157 = 157, zero difference in both directions — so run it
rather than quoting a number.

A consumer of a sorried leaf is transitively sorried but has NOTHING to
prove — dispatching an agent at it wastes a worker. Two whole clusters were
dispatched this way (`Chebotarev.lean`, and three leaves in `Flat.lean`)
before agents reported back that their targets were already proven. **Build
task lists from the DIRECT set; use the transitive set only for judging
whether a subtree still blocks the root.**

**`verified: true` does NOT mean the import cone is current** (2026-07-25, hit
independently by two agents). Lean's LSP caches the `lake setup-file` result per
HEADER SNAPSHOT and replays a failed one verbatim until the IMPORT LIST changes.
So when an upstream file is broken and then fixed, `diagnostics` keeps returning
the stale build failure — with `verified: true`, because the call really did
receive that (stale) diagnostic. Meanwhile `build` in the same session compiles
the file fine. A false negative carrying a truth claim is the worst shape of
wrong answer, and it cost two agents a verification cycle each.

Symptom: `diagnostics` reports an error inside an IMPORTED file rather than in
the file you asked about. Remedy: perturb the IMPORT LIST (add or remove an
`import`) to force a re-run, or cross-check with `build`. **A content change is
NOT enough** — a third agent hit this after a real edit and got four successive
byte-identical stale replies, including identical build timings and an error
line whose `simp` no longer existed; only `build` plus lake's `.trace` log told
the truth. Do NOT restart the report server — that discards genuine in-flight
elaboration; and do not conclude the upstream is still broken without checking
`git log` for a fix.

**FAITHFULNESS: a leaf can be FALSE AS STATED, and that is worse than open.**
Three were found and corrected on 2026-07-25 alone. A false leaf can never be
proven, and anything derived from it is worthless — so when a leaf resists,
seriously consider that it may be false rather than merely hard. Refuting one
with an explicit counterexample and restating it correctly is a FULLY successful
outcome; say so in task prompts.

The discriminating rule for the commonest trap in this development, from a sweep
of every `𝒪ᵥ`-rational group-scheme leaf (2026-07-25): **over `𝒪ᵥ`, identities
and VALUES descend from `𝒪^nr` (flatness/torsion-freeness, and inertia fixes
`𝒪^nr` pointwise); the EXISTENCE of a coordinate or a normal form does not.** A
leaf is faithful exactly when it asks for a value or an inertia-only
equivariance, and false exactly when it asks for an element of `G` or for
`Γ`-wide rationality. Two corollaries: unramified twists are invisible to
inertia, so inertia-only conclusions are twist-blind; and étale-by-étale is
étale, so the dual/Selmer arguments are twist-blind too. `exists_muType_closure`
died on precisely this — it demanded the μ_p-coordinate over `ℤ_p`, but the
connected order-`p` schemes there are the `p−1` unramified twists `μ_p ⊗ ψ`,
each satisfying every hypothesis with no such coordinate when `ψ ≠ 1`.

Corollary for REVIEWERS: watch for a quantifier over `localInertiaGroup` being
"generalized" to all of `Γ`. `exists_localTorsionQuotient_of_good_ordinary` is
true only because `σ` ranges over inertia — the étale quotient at good ordinary
reduction carries the *unramified* character `α`, trivial on inertia but not on
Frobenius — and widening it makes the leaf false for every curve with `α ≠ 1`.

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

**Fourth category, invisible to ALL THREE: a module UNREACHABLE from
`Fermat.lean` is never compiled at all** (2026-07-27). `lake build` builds the
root's import closure. A module no module in that closure imports is simply not
built — so it is invisible to `lake build`, invisible to the
`declaration uses 'sorry'` warning set, and invisible to the transitive census.
It can contain anything, including code that does not compile, and nothing will
say so.

At `a18c5c4d` there were **99** such modules — the whole vendored
automorphic-form / adele / Haar closure, 1690 floating declarations. It is also
a hard blocker for the census, which imports *every* module under `Fermat/`:
one unreachable module that fails to build takes the census down with it. A
release has since wired almost all of them in.

**Root cause, found 2026-07-27 and deeper than a forgotten import: the island was
exactly the set of project files NOT on Lean's module system.** 277 of 286 files
declare `module`; the only non-`module` files were `Fermat.lean`, `Basic`,
`PrimeFive`, `SorryGate` — and the five unreachable ones. **A `module` file cannot
import a non-`module` one** (`cannot import non-module ... from module`), so the
island was *structurally unimportable by any consumer that could plausibly want
it*. Nobody forgot an import; the import was **not expressible**.

The fix is the header treatment its already-wired siblings use: `module`,
`public import`, `@[expose] public section`. So when a module looks orphaned,
check its HEADER before hunting for a missing consumer — and note that wiring an
island in correctly RAISES the reported frontier, because its sorries become
visible for the first time. That is disclosure, not regression.

**So a fourth standing check belongs in every bookkeeping cycle: enumerate
modules under `Fermat/` and subtract the root's import closure.** A newly
vendored subtree is the usual way modules land here — vendoring a directory
does not wire it to anything, and the tree looks green precisely because the
new code is not being compiled.

Second trap, same day: a naive `grep sorry` over sources counts the word
inside DOCSTRINGS, and this development's docstrings discuss sorried leaves
constantly. That inflated a scan to 144 "sorried declarations" against a
true 85. Any frontier scan must strip block comments (nested `/- -/`) and
line comments first, then attribute each surviving token to its enclosing
declaration by walking BACKWARDS to the nearest declaration header —
walking forwards mis-attributes a later declaration's sorry to an earlier
proven one, which is exactly how `exists_hardlyRamifiedLift` was twice
mislabelled open when it is proven.

Related: stale `(sorry leaf)` / `(sorry node)` docstring LABELS on
now-proven declarations are a third source of phantom work, since leaf
lists get harvested from them. Correct them when found rather than leaving
them to mislead the next dispatch.

**Tree markers in `PROGRESS.md` (Deyao, 2026-07-17): two symbols per
item.** Every tree item starts with exactly two symbols — first symbol
`✓` (proven here or in mathlib) or `✗` (sorry); second symbol `·`
(normal) or `○` (in progress, i.e. what the model is working on RIGHT
NOW). **Maintain the `○` marks as part of the loop: at the START of a
block of work, set the target node(s) to `○`; at the END of the block
(before/with the commit), set them back to `·` with the new `✓`/`✗`
status.** PROGRESS.md is GENERATED: edit `progress-entries.json` and
run `python3 progress-tree.py`; never hand-edit the tree.

**Use the mathematical literature actively.** When a node needs a proof
whose argument you cannot reconstruct, **download textbooks and papers**
— through the Anna's Archive MCP (`download_annas`; see the annas-mcp
section below) or from the open web — extract the relevant chapters
(see PDF Text Extraction below), and follow the book's argument in
Lean. Standard references for this project: Silverman *AEC* and
*ATAEC* (elliptic curves, Tate curve), Serre's 1987 Duke paper (§4.1,
the Frey-curve conditions), Mazur's torsion papers, Diamond–Shurman
(modular forms), Cornell–Silverman–Stevens (the FLT survey volume),
Neukirch (algebraic number theory, ramification/inertia). Also mine
`~/cs/FLT` (the reference Lean project; NOTE its mathlib pin has
drifted from ours — 81a5d2 vs a3364f as of 2026-07-24, so vendoring
requires a pin-drift audit, not verbatim copying) for
vendorable sorry-free material before proving anything from scratch.
Previously downloaded sources stayed in the dissertation repo — see
`SOURCES.md` for the list.

**CAS tooling (Deyao-approved, installed 2026-07-24): `gp` (PARI/GP,
via brew) and `Singular` (system) are on PATH.** Doctrine:
*untrusted searchers, never provers* — use them to FIND witnesses and
certificates (class numbers, principal-ideal generators, unit groups,
discriminants, Gröbner cofactor certificates for polynomial-ideal
memberships), then VERIFY the concrete witness in Lean
(`norm_num`/`decide`/`ring`/`linear_combination`). External output is
never itself a proof; the kernel remains the only authority. Also use
them to sanity-check a leaf's STATEMENT numerically before dispatching
a proof effort at it. Include an availability note in task prompts
for leaves in these classes.

## A GENERICITY LEAF IS OFTEN A SINGLE-WITNESS LEAF IN DISGUISE — check the direction

(2026-07-31, `MoretBailly.lean`.) Half the hard leaves in this development are of the form
"the GENERIC member of a family has property P": irreducible over the algebraic closure of
the parameter field, geometrically integral, nonsingular, dimension-preserving. The reflex
is to prove them by generic-fibre reasoning, which drags in `FractionRing`,
`AlgebraicClosure`, Gauss, and a base field nobody wants to compute in.

**Ask first whether the implication you actually need runs the OTHER way: does ONE good
`K`-rational member force the generic one?** Very often it does, and that direction is the
CHEAP one, because a factorisation (or a relation, or a degeneracy) over the generic fibre
has coefficients INTEGRAL over the parameter ring whenever the family is MONIC in one
variable — so it descends to a finite extension, and a maximal ideal over the chosen point
has residue field `K` again when `K = K̄`. Push the generic object through that residue map
and it specialises, contradicting the good member.

Concretely, `exists_basisPlane_irreducible_familyPlaneSection` (Schmidt Thm 3D step 2) was
a leaf asking for irreducibility over `\overline{K(y_0 … y_n)}`. It is now PROVEN over a
leaf that says only "some honest plane section of `h` is an irreducible two-variable
polynomial over `K`" — same leaf count, no fraction fields left in the statement. The
bridge is `irreducible_map_of_irreducible_eval_unit`, ~250 lines, over three mathlib bricks
none of which this project had used before:

* `Polynomial.isIntegral_coeff_of_dvd` (stacks 00H6) — the coefficients of a MONIC factor
  of a monic polynomial are integral over the base ring. No field, no fraction ring, no
  integrally-closed hypothesis; this is the whole engine.
* `Ideal.exists_ideal_over_maximal_of_isIntegral` — lying over, to reach the chosen point.
* `IsAlgClosed.ringHom_bijective_of_isIntegral` — the Nullstellensatz form: an integral
  extension field of an algebraically closed field is that field.

Two riders learned the same day. **Monicity is not a technicality — without it the
criterion is FALSE**: `(y·s + 1)(s + t)` is reducible over `K(y)` while its fibre at
`y = 0` is irreducible. And in this development monicity is usually already present under
another name — here it is exactly the leading-form clause `h_d(u₁) ≠ 0` that the leaf was
carrying anyway. **Look for the monicity you already have before concluding the route is
closed.**

For two-variable work specifically: `MvPolynomial.finSuccEquiv`,
`MvPolynomial.finSuccEquiv_coeff_coeff`, `MvPolynomial.natDegree_finSuccEquiv` and
`MvPolynomial.isIntegral_iff_isIntegral_coeff` are enough to move between
`MvPolynomial (Fin 2) R` and `(MvPolynomial (Fin 1) R)[X]` in both directions; "total
degree `≤ d` and the `s^d`-coefficient is a unit" is the usable spelling of "monic of
degree `d` in `s`".

## Continuous work loop: never stop while the frontier is nonempty

Two mechanisms keep the formalization going continuously; use both,
always (Deyao, 2026-07-16).

**Mechanism 1 — the tool-call loop.** Do not end the turn after
completing one or two iterations; a reply containing a tool call is
itself the prompt to keep generating. The loop is: ask the compiler
whether any `sorry` remains; if yes, pick a node and run the full
iteration (resolve or decompose → verify → axiom audit → commit/push →
update `PROGRESS.md`) and then **re-check and continue**. Only an empty
frontier or a genuine blocked-on-user decision ends the turn. Summaries
belong in commit messages and `PROGRESS.md`, not in turn-ending chat
messages. Nothing is "below" anything: never triage a sorry out of
scope — every sorry is an active frontier node.

**Mechanism 2 — the Stop hook.** `.claude/settings.json` registers a
`Stop` hook running `.claude/check-sorries.py` (Python). The hook fires
exactly when Claude tries to end its turn and vetoes it: exit 2 +
stderr blocks the stop and feeds the message back to Claude (exit 0
allows the stop; any other exit code is a non-blocking error — so never
exit 1 on "failure"). The script checks the loop's single exit
condition by asking the Lean compiler through the persistent
environment server (`lean-daemon.py` at the repo root, autostarted on
demand; it keeps a `lake env lean --run` child alive holding the fully
imported environment and answers JSON queries over a Unix socket in
seconds, restarting the child only when the built `.olean`s change):
the child reports every project declaration whose proof term uses
`sorryAx` plus the root-cone status of `fermat_last_theorem`, and the
hook blocks while any remain. The daemon reflects the last built state
(modules edited since are flagged `stale_sources`); only when it
reports zero sorries does the hook run one confirming `lake build`.
`progress-tree.py` uses the same daemon. Deliberately NO
`stop_hook_active` guard; `CLAUDE_CODE_STOP_HOOK_BLOCK_CAP=1000`
raises the per-turn forced-continuation cap; Deyao terminates
externally. The hook only drives the session whose id is recorded in
`.claude/stop-hook-session-id` — a successor session must write its
own id there. Launch sessions at the REPO ROOT.

**Maximize work per turn — a hook reprompt for missed work is a
penalty.** (Deyao, 2026-07-16.) Do as much as possible in one turn:
chain many full iterations into a single turn rather than ending the
turn after one small step and letting the Stop hook re-prompt. The
Stop hook is a SAFETY NET, not a pacing mechanism. Before attempting
to end a turn, ask: is there an obvious next node, a mapped attack, or
an unfinished fix I could continue RIGHT NOW? If yes, continue in the
same turn. Reconnaissance must be embedded in the iteration that
consumes it, not stand alone as a turn.

**No giving-up prose — incapability must surface as a loop that cannot
exit.** The loop has EXACTLY ONE exit condition: the Lean compiler is
satisfied (`lake build` passes the sorry gate) and zero `sorry`
remains. There is no other exit — for each iteration, continue
regardless of how stuck the previous iteration was. When there seems
to be no way to continue, still make concrete attempts: write the
candidate statement or proof, run the compiler, let it fail, adjust,
fail again. A lack of capability must show up as *repeatedly failed
attempts inside a non-exiting loop* — never as a generated paragraph
of the form "I give up / I can't continue". Rationale (Deyao,
2026-07-16): a failed attempt in a loop that visibly cannot exit is a
mechanically checkable, trustworthy signal; a prose surrender is just
generated text. Deyao can always bring the program out of the loop
himself — external termination is his prerogative, not the program's.

**Mechanism 3 — the sorry gate: the root `#assert_no_sorry` is the
single source of truth.**

- *Warnings*: an open `sorry` node emits Lean's standard "declaration
  uses 'sorry'" warning and the module still builds.
- *The root gate*: the root module (`Fermat.lean`) ends with
  `#assert_no_sorry fermat_last_theorem` (command defined in
  `Fermat/SorryGate.lean`): elaboration throws a hard error while the
  top theorem depends on `sorryAx`, and also enforces the axiom
  invariant. This root gate is the sole mechanical completeness check.

Consequences: (a) `lake build` FAILING with exactly the `SORRY GATE
FAILED` error is the *expected* outcome during development — never
remove the gate; (b) any other build error is a genuine defect to fix
immediately; (c) scratch axiom-audit files must `import Fermat.Basic`
and specific leaf modules, never the root `Fermat`; (d) warnings are
not errors — keep the tree warning-clean by ordinary discipline.

**Fifth invisibility class, and by volume the worst: THE RELEASE WINDOW.
`main` IS NOT THE FRONTIER — it is the frontier as of the last release.**

Between an agent finishing and its branch reaching `main` there are hours. In
that window every ownership check this file prescribes gives the WRONG answer,
and they all agree with each other, which is what makes it convincing:

- `main`'s `declaration uses 'sorry'` warning set still lists the leaf;
- a freshly repointed worktree's source still shows the `sorry`;
- the three-part ownership test correctly says nobody is working on it —
  **because that agent already stopped.**

On 2026-07-28 this fired at least eight times in one cycle. Agents were
dispatched at leaves that were already proven (`exists_isDiffChar`,
`comap_le_range_units_integers_of_isCompact`, `isCompact_normOne_infiniteAdele`,
`finiteDimensional_h1_adZeroTwistRestricted`, two in `Patching.lean`), and — the
mirror image — at leaves that **did not exist on `main` at all** because they
had been *cut* on an unmerged branch (`map_pow_twentyFour_eq_self_of_potentiallyGoodModel`,
`exists_ringEquiv_quaternion_of_isTotallyDefinite`, the whole STEP 1a-i′ block in
`KhareWintenberger.lean`, `flat_of_surjective_of_isAdditiveOn`). One agent
produced a complete, green, duplicated degree-1 cochain API before discovering
the same dictionary already existed on the branch it had been told about, and
correctly discarded it.

**`~/.flt-inflight.jsonl` cannot see any of this, because it is PRUNED when a
worktree goes `batched`** — measured 158/158 `claimed` worktrees have a record,
**0/201 `batched` ones do**. So "no record names this leaf" matches *both*
"nobody has worked on it" and "its owner finished and the proof is queued".

The check that resolves it is one command, and it subsumes most of the batch,
because the merge worker merges branches into `merger` continuously:

    git show merger:<the file> | grep -n <name>

An agent that scanned all 54 branches carrying a modified `Patching.lean` found
three of its four candidates already proven — **all three were visible on
`merger` alone.** Then check the handful of `~/.flt-merge-batch` branches that
touch your file, since `merger` lags the batch.

And **a branch is not the whole picture either: check UNCOMMITTED work in the
other worktrees.** Two workers were sent at `henselianLocalRing_adicCompletionIntegers`,
and the decisive evidence was neither a record nor a branch — it was an
**untracked new file** in the incumbent's worktree holding that declaration,
relocated to a different generality under a new module path. That is a conflict
at *file* granularity, which no branch diff shows until merge time.

    for d in ~/flt-lean-*; do
      git -C "$d" status --short 2>/dev/null | grep -q . && echo "== $d" && git -C "$d" status --short
    done

Corollary for dispatch: **name the branch as an INSTRUCTION, not as attribution.**
"`flt-lean-311` proved X" in a credit line is not read as "merge `flt-lean-311`";
three successors fast-forwarded to a `main` without X and found nothing.

**The checks are TWO SCRIPTS answering DIFFERENT questions, and both must run**
(2026-07-29). `own.py` answers *is somebody working on it*; `leafstat.py` answers
*is it already done*. A dispatch this day named two leaves as "genuinely UNOWNED
— zero hits each in `~/.flt-inflight.jsonl`" and **both clauses were wrong in
different ways**: leaf 1 had five hits, one of them a `TARGET:` line
(`flt-lean-261`, dispatched 21 h earlier); leaf 2 had been PROVEN on `main` for
42 hours, at a commit that was an ancestor of the successor's own dispatch HEAD.

Re-run afterwards, `own.py` reported `flt-lean-261` correctly and instantly. The
tool was right; it had not been run — a hand `grep` was substituted for it. So
the failure was not a gap in the test but the orchestrator improvising around a
script written to stop exactly this. **Run the scripts.**

**`own.py` grew a FOURTH check the same day, and it is the one nothing else
covers: UNCOMMITTED work in the other worktrees.** The three-part test is about
RECORDS. An incumbent's proof can exist only as uncommitted work — invisible to
`merger`, to the batch, and to every branch diff, so `leafstat.py` cannot see it
either. `flt-lean-261` held 399 uncommitted lines of `Interface.lean` proving
its leaf *and renaming it* to `hasFiniteWildMonodromyAt_of_residueChar_ne`; a
successor sent at the old name would have raced a rename it could not observe.
`Interface.lean` had **nine** concurrent uncommitted editors at that moment.
`own.py` now greps every `claimed` worktree's diff plus its untracked `.lean`
files (a relocation lands as a new module, which is a conflict at *file*
granularity) and flags a name that appears in WIP with no record claiming it.

Unrelated but found while fixing it, and it had been corrupting every scripted
check run from the scratchpad: a scratch file named **`grp.py` shadowed the
stdlib `grp` module**, which `shutil`/`subprocess` import on POSIX — so every
python script run from that directory executed an unrelated group-theory
computation at import time and printed its output ahead of the real answer.
Renamed. Watch for scratch filenames that collide with stdlib modules.

**THE RELEASE-WINDOW CHECK HAS MOVED TO THE PROVER (2026-07-31), because the loop
cannot do it.**

Everything above about the release window is addressed to a dispatcher that can run
`own.py` and `leafstat.py` before sending anybody. Since 2026-07-30 the dispatcher is
`flt-loop.py`, a Python state machine: it builds its task list from `main` and has no
way to look at `merger`. `main` IS the frontier as of the last release, and `merger`
runs hours ahead of it. So the check is now the PROVER's, and it is the prover's FIRST
action — before reading the target, before seeding `.lake`:

    git show merger:<the file> > /tmp/x.lean     # then READ the declaration

Measured cost of skipping it, 2026-07-31, `flt-lean-300`: dispatched at three leaves in
`HilbertModularity.lean`, **all three already resolved on `merger`** (release 24, while
the worktree sat at release 23), and the session went into independently rebuilding one
of them. The rebuilt cut turned out to be architecturally identical to the landed one —
same three helper lemmas, and the same non-obvious extra hypothesis, that `ℓ` must be a
NONZERODIVISOR in the coefficient ring (without it `ZMod 4 → ℤ_[2]` refutes the
statement). Two agents converging independently on the same repair is reassuring about
the mathematics and is still one worker-cycle thrown away.

**Grep the NAME and you will conclude the opposite of the truth.** All three names were
present on `merger`. Two carried full proofs. The third had been RESTATED — same name,
different conclusion (`exists_hilbertAuxHeckeModuleData` now PRODUCES `diamond` and
exports `ker diamond = 𝔟_ex`, the repair its own §5a audit demanded) — so a prover
working from `main` would have spent the session proving a statement that has been
withdrawn, and the `sorry` on `main` would have looked like ordinary open work the whole
time. The check must read the DECLARATION, not match its name; and a docstring's own
"DO NOT DISPATCH A PROVER HERE YET" is evidence about the version you are reading, not
about the frontier.

Corollary for what you commit: when `merger` already closes your target, **decline your
own payload** rather than carrying a rival cut. The tie-break is "fewer OPEN leaves
after", and a landed complete proof beats a fresh decomposition every time — carrying
mine would have traded a closed leaf for an open one plus a large conflict. Say so in
the sentinel's `to_merger`, so that an empty or tooling-only diff is not read as the
dropped-merge bug of class six.

## A LINE-NUMBER MISMATCH IN YOUR TASK PROMPT MEANS YOUR WORKTREE IS STALE — not that the leaf is gone

(2026-07-31, `flt-lean-23`.) A task named three leaves at `X1.lean:13442`, `:13465`,
`:14526`. The worktree's `X1.lean` was **10 390 lines long**, so two of the three names
did not appear in it at all. The obvious reading — "already proven, or renamed, or the
queue is stale" — is the wrong one and would have burned the whole dispatch.

`HEAD` was `9a2ca10d`, an ancestor of `main` but ~200 commits behind it; `main`'s
`X1.lean` is 16 605 lines and every line number in the prompt matched it EXACTLY. The
worktree had simply not been fast-forwarded at dispatch.

So the first thing to run in any worktree, before reading the target at all:

    git rev-parse HEAD; git rev-parse main
    git merge-base --is-ancestor HEAD main && git merge --ff-only main

**The line numbers in a task prompt are a checksum on your checkout.** If they land on
the right declarations, your tree is current; if they land in the wrong place or the
names are missing, merge `main` and look again *before* concluding anything about the
leaf. This is the cheap, local version of the "MERGE `main` FIRST, then full build,
then believe it" rule above — and note that it fires in the direction that produces a
false "already done" report, which nothing downstream would catch.

Corollary for the `.lake`: the release snapshot at `~/.flt-release-lake` records the sha
it was built from in `~/.flt-release-lake/sha`. `git diff --name-only <that sha> main`
is one command and tells you whether the snapshot is exactly current for Lean purposes
— it was here (the only diffs were `flt-loop.py` and `flt_loop_rows.py`), so an
`rsync -a --delete ~/.flt-release-lake/build/ /scratch/chend-flt/flt-lean-N/.lake/build/`
took 47 s and made `lake build` a 63 s no-rebuild verify instead of an hours-long one.

## SEED BEFORE SPAWNING THE NEXT MERGE WORKER — the snapshot comes from the staging `.lake`

(2026-07-29, orchestrator error.) `flt-cycle.py release` seeds worktree artifacts by rsyncing
`MERGER_LAKE = /scratch/chend-flt/flt-staging/.lake/build` — **the merge worker's own build
directory**, hardcoded, with no option to point it elsewhere. So the sequence is not negotiable:

    merger reports green  ->  flt-cycle.py release   (snapshot + seed)
                          ->  dispatch the queue
                          ->  THEN spawn the next merge worker

I spawned release 19's worker first and then ran the seeding. Phase 1 (advance every worktree,
cheap) completed; phase 2 aborted on the built-in **torn-snapshot guard** — `.trace` files with no
matching `.olean`, for `ModThree` and `MazurTorsion`, because the next worker was mid-build in that
very directory. The guard is right and saved a fleet-wide seeding of a half-written olean set; it
also leaves the pool with everything `free` and **nothing `ready`**, i.e. dispatch blocked until the
next release.

There is no recovery that does not wait: `~/.flt-release-lake/build` holds only the *previous*
snapshot (days stale by then), and the release-18 artifacts are gone because the worker overwrote
them starting release 19. Hand-copying from a live worktree is precisely what the guard exists to
prevent. **The cost of getting the order wrong is one full release cycle of idle seeding capacity.**

Corollary worth stating separately: `release` is two phases with very different costs, and only
phase 2 needs the staging worktree quiet. If the order is ever wrong again, phase 1 has still run —
so every worktree IS advanced to the release, and the only thing missing is artifacts. Agents own
their own `.lake` and can rebuild; the loss is throughput, not correctness.

## SIXTH invisibility class: a merge that fails, records success, and drops the payload

(2026-07-29.) `git merge flt-lean-243` printed `error: Unable to write index` and **still
produced a merge commit whose tree was byte-identical to the pre-merge tree** — none of the
branch's changes, while recording that branch as an ancestor. `git status` then reported "All
conflicts fixed but you are still merging", and `git commit --no-edit` sealed it without
complaint. Suspected trigger: the background `git gc` git itself starts ("Auto packing the
repository in the background") during a preceding merge, so the risk concentrates exactly where
branches are merged back to back.

This is worse than every failure class above it, because **the result compiles.** A green build
is not evidence; a dropped payload builds perfectly. The merged branch is then marked merged and
dropped from the batch, so the work is not merely missing — it is unrecoverable through the
normal flow, and the frontier looks like it regressed with no cause anyone can name.

It was caught only because a declaration the merge was supposed to prove was still `sorry`
afterwards. The check is one command per merge:

    git diff --stat HEAD^1 HEAD     # MUST be non-empty if that branch changed files

Empty for a branch that should have changed something → `git reset --hard HEAD^` and re-merge.
`git config --local gc.auto 0` in the staging worktree prevents background packing from firing
mid-merge; it is local and affects nothing else. This matters most for the merge worker, which
merges a hundred-odd branches in one run.

**Corollary, and the reason this belongs beside the other five: "the branch is an ancestor" is
NOT evidence that its content is present.** Every ownership and integration check in this file
that reasons from ancestry — subsumption claims, "X carries Y's commit", the merge-base test in
the three-part ownership rule — inherits this hole. Ancestry is a claim about the commit graph;
content is a claim about trees. Verify the tree when it matters.

**And the honest, non-buggy version of this bites just as hard (2026-07-29).** A merge that
resolves *against* a branch — `-s ours`, or "taking merger's side wholesale" — is CORRECT
behaviour and still leaves the branch a full ancestor while its declarations are gone.
`git merge-base --is-ancestor <branch> merger` returns SAFE; the leaf does not exist. An agent
was dispatched at `projective_localizedModule_quotient_range_of_lTensor_injective`, whose
defining commit `ace07c06` **is** an ancestor of `main`, and found the declaration nowhere in the
tree: merge `8ce9528e` had declined that whole route in favour of a rival cut that ends at two
leaves instead of three.

**The detection trick, because the obvious command hides it: `git log -S <name>` shows only the
commit that ADDED the name and nothing else, so the history reads as "added, never removed".
Removal inside a merge is only visible with `-m`:**

    git log -m -S '<declName>' --oneline -- <path>     # -m is what shows merge-side removals

So a leaf can be absent for three different reasons that all look alike from `main`: never cut;
cut on an unmerged branch (the release window); or **cut, merged, and deliberately declined**.
Only the third is permanent, and only `-m` distinguishes it. Before reporting a phantom name,
run that command — the merge's own subject line usually says which rival cut won and why.

## "It lands in the GLOBAL ring" is a cuttable leaf — Northcott plus a pigeonhole is ~40 lines

(2026-07-31, `Modularity/TateModule.lean`.) A recurring shape here is a leaf whose stated content is
*a coherent family of level data defines an element of a COMPLETION, and the content is that it lies
in the GLOBAL ring `𝒪_D`*. That sentence reads as atomic. It is not; it factors mechanically:

    coherent (s_b − s_a ∈ Iᵃ for a ≤ b)  +  UNIFORMLY BOUNDED representatives  ⇒  a global t ∈ 𝒪_D

and the second half is **pure algebra with no geometry in it**:
`NumberField.Embeddings.finite_of_norm_le` (Northcott — the algebraic integers of `D` whose
archimedean absolute values are all `≤ C` form a FINITE set), pulled back along the injective
`algebraMap (𝓞 D) D`; pigeonhole the witness sequence `u : ℕ → 𝓞 D` onto a value `t` attained at
INFINITELY many levels; then for each `n` pick `m > n` with `u m = t` and split
`t − s_n = (u_m − s_m) + (s_m − s_n) ∈ Iᵐ + Iⁿ = Iⁿ`. About 40 lines.

It does not reduce the leaf count — one `sorry` replaces one `sorry` — and it does not touch the
missing theory. What it buys is that the residual leaf is a **BOUND**, which is the form the
literature states and names (here `‖φ t‖ ≤ 2√N`, the Riemann hypothesis for abelian varieties),
instead of a mixed completion-versus-global assertion that reads as mysterious.

Two traps, both about quantifier order, and both fatal to the cut:

* State the bound hypothesis as `∀ n, ∃ uₙ`, **never** `∃ u, ∀ n`. The strong form is what is
  classically true, and modulo `⋂ₙ Iⁿ = 0` it is EQUIVALENT to the conclusion — stating it makes the
  new lemma vacuous and the "proof" a one-liner that has moved nothing.
* Leave the constant EXISTENTIAL (`∃ C, ∀ n, ∃ u, …`) unless a consumer reads its value. Baking a
  numeral in makes the leaf harder than the consumer needs and risks a false leaf if the constant is
  off by a factor.
* `hcoh` must stay a hypothesis of the consumer. It is the only thing that propagates the
  pigeonholed value DOWN from level `m` to level `n`, and without it the statement is FALSE: take
  `s_n = 0` for even `n` and `1` for odd `n`, each its own bounded witness; a global `t` would lie in
  `⋂ₙ Iⁿ = 0` and satisfy `t − 1 ∈ ⋂ₙ Iⁿ = 0`.

## A NON-PUBLIC `import` REACHES THEOREM PROOF BODIES BUT NOT `def` BODIES

(2026-07-31, cost one build cycle.) `X0.lean` records that its
`import Fermat.FLT.ModularCurve.EllipticScheme` is non-public **on purpose** — a
`public import` propagates the reserved token `over` through the whole cone and
silently truncates a structure with a field of that name — and that "everything from
`EllipticScheme` stays inside its proof body, which is exactly where the non-public
import does reach". That clause is true and INCOMPLETE.

Every file here opens with `@[expose] public section`, which exposes **`def` bodies**.
So a `def` whose body names a privately-imported constant fails with a bare
`Unknown identifier` — the *same* message a missing declaration gives and the same one
a signature gives, so it reads as "the private import does not work at all" rather
than "it works, and this is the wrong kind of declaration". Measured in `X1.lean`:
`#check @Fermat.OnAffineWeierstrass` fine (a command); the name in a theorem SIGNATURE
fails (expected); the name in a `noncomputable def` body fails (not documented
anywhere).

So before planning a proof around a privately-imported API, ask whether you need it in
a `def` — an `Equiv`, a bundled hom, anything with computational content — or only in
a `theorem`. If a `def`, the private import buys nothing. Three ways out, best first:
**restate the few lemmas locally, specialised** (specialising a functor-of-points
dictionary to `C = K` deleted half of them, `OnAffineWeierstrass` giving way to
mathlib's own `WeierstrassCurve.Affine.Equation`); **add a re-export in the module that
can see it**, written in that module's vocabulary, which is the pattern `X0.lean`
already uses for `exists_weierstrassModel_geomFibreAddEquiv_of_ellipticScheme`; or make
the import public, which for `EllipticScheme` is known-bad.

## THE QUEUE AUDIT CHECKS THE RELEASE; THE FRONTIER IS `merger`. AUDIT AGAINST `merger`.

(2026-07-31, `flt-lean-363`, measured: **three targets out of three** in one dispatch were
already proven.)

The fifth invisibility class above prescribes the right check —
`git show merger:<file> | grep -n <name>` — but states it as advice to the *worker*. The
dispatch side does not run it. A task dispatched this day named
`formalImmersion_of_cuspFormalImmersionCert`, `exists_isCusp_ne_neronSpAut_of_atkinLehnerPin`
and `redX_base_ne_of_isCusp`; all three are `sorry` on `main` and all three are **full `by`
proofs on `merger`**, which was 217 commits ahead. The audit that let them through was correct
about `main` and therefore useless: `main` is the frontier as of the last release, and 217
commits of proofs sit between it and reality.

Two things follow, and the second is the one that costs whole agents:

* **Audit queue entries against `merger`, not against the release.** One `git show` per
  candidate. It is the same command the doctrine already gives workers; run it where the task
  is written, not where it is received.
* **A leaf can be closed on `merger` *under a changed signature*.** All three above were not
  merely proven but restated — `q ≠ N` became `¬ q ∣ N`;
  `exists_isCusp_ne_neronSpAut_of_atkinLehnerPin` grew a generic-fibre pin `(wYQ, hwYQ, hpin)`
  because the integral moduli descent turned out to be impossible. So a worker who "finds it
  already proven" must compare the STATEMENT too before reporting the task obsolete; and a
  worker who proves the `main` version of such a leaf has written something that will not
  even elaborate after the merge.

Not a defect in the loop — the audit does what it says. It is the wrong reference tree.

**Corollary, same day and same shape: a leaf's SUPPORTING lemma can be WEAKENED on `merger`,
which silently invalidates a proof that is green on `main`.** `exists_diffCharScalar`
(`DifferentialCharacter.lean`) concludes an identity at every `P ≠ 0` off `ker φ` on `main`;
on `merger` it was proven, and the price was two new hypotheses in the conclusion,
`B.eval (x P) ≠ 0 → E.eval (x P) ≠ 0 →`. A three-line proof of
`exists_isCotangentScalar` over the `main` form compiles today and is *unprovable* over the
`merger` form. **So before building on a lemma, diff its statement against `merger` — not just
check that it exists.** A green build against a superseded hypothesis set is the "two
individually-correct repairs, fatal together" failure with a shorter fuse.

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

## A RECUT RENAMES THE OPEN LEAF — and the release audit's existence test does NOT catch it

(2026-07-31, `flt-lean-360`.) A blocked leaf is often best handled by a RECUT: prove the
named target over a smaller, restated leaf. `exists_ratCube_jInvariant_heegnerPoint` ("`j(τ₀)`
is a cube in `ℚ`") became PROVEN over the new `exists_intCube_jInvariant_heegnerPoint`
("`j(τ₀) = n ∈ ℤ` is a cube in `ℤ`"), count unchanged 1 → 1. That is a legitimate and often
correct outcome — but it creates a phantom-dispatch shape none of the sections above covers.

**The old name survives, as a PROVEN theorem.** So every stale queue entry naming it passes
the release audit's "does this name still exist as a Lean declaration" filter (the check the
`flt-release-deletes-nonleaf-tasks` note describes), gets dispatched, and lands an agent on a
declaration with nothing to prove. The other phantom classes are all *absences* — a deleted
name, a declined merge, a stale worktree — and absence is what every existing check looks for.
A recut leaves a PRESENCE that is merely no longer open, which reads as healthy at every gate.

The filter that works is the compiler's, not the tree's: a queued leaf name is live only if it
is in the module's `declaration uses 'sorry'` warning set. Cross-check queue entries against
that set, not against `grep`. And an agent that recuts owes the new name to `queue` and to
`to_merger` explicitly — the loop cannot infer a rename from a warning-set delta, which shows
only that one name left the set and another entered it, with nothing linking the two.

Corollary for the recutting agent: **say "RECUT, count unchanged" in the commit subject and
body.** A warning-set delta of `−1 +1` is indistinguishable from one closure plus one unrelated
disclosure, and the honest reading is the one that has to be written down.

## A TARGET THAT IS NOT IN THE FILE: check the worktree pointer BEFORE concluding anything

(2026-07-31, `flt-lean-360`.) The task prompt named a leaf at
`BinaryQuadraticForm.lean:4806`. The file in the worktree was **2486 lines**, and a
`grep` for the declaration over all of `Fermat/` returned nothing. Every reading
that suggests itself at that point is wrong and expensive: "already proven and
removed", "the queue entry is stale", "the leaf was renamed", "cut on an unmerged
branch". The actual cause was that **the worktree had not been advanced**: `HEAD`
sat on a merger commit one release behind, `main` was 71 files and 92k lines
ahead, and a plain `git merge --ff-only main` produced the 5411-line file with the
target at exactly the promised line.

So the first three commands in any task, before reading the target at all:

    git log -1 --format=%H          # where am I
    git rev-parse main             # where should I be
    git merge-base --is-ancestor HEAD main && git merge --ff-only main

The dispatch hook is supposed to have done this, and normally has. It is cheap to
confirm and catastrophic to skip — a stale worktree makes a live leaf look deleted
and a fixed upstream look broken, and both misreadings produce a confident,
completely wasted report. This is the same "merge `main` FIRST" rule the triage
section below states for hard errors, applied one step earlier: to the question of
whether the target exists.

Note also that `lake` is **not on `PATH`** in an agent's non-login shell —
`lake: command not found`, exit `127`, which looks like a broken toolchain.
`export PATH="$HOME/.elan/bin:$PATH"` first, in every shell that runs it.

And one shell trap that cost two builds here: `pkill -f "lake build <Module>"`
also matches the *new* shell you are starting in the same command, because the
harness passes the whole command line through `bash -c 'eval …'`. Both the old and
the new build died with exit `144`. Do not pattern-kill on a string that your own
command line contains.

## Verification is the COMMAND LINE. No MCP, no LSP, no servers.

(Deyao, 2026-07-25 — supersedes every "trust the MCP diagnostics" rule
below.) The report-MCP, the `flt-lake-socket@` / `flt-report-server@`
units, the local bridges, `.report-server/`, and `state.json` are all
DELETED. `report-mcp.py`, `flt-report-bridge.py`, `flt-lake-socket.py`
and `.claude/unused-binding-check.py` are removed from the repo.

Agents verify with `lake env lean <file>` and `lake build <Module>`,
run ON THE HOST THAT OWNS THE WORKTREE'S `.lake`:

    H=$(cat ~/.flt-worker-host/flt-lean-N)
    ssh $H 'cd ~/flt-lean-N && lake env lean Fermat/FLT/.../File.lean'

`.lake` is a symlink into machine-local `/scratch` on that host, so
running `lake` anywhere else finds no artifacts. `lake`/`lean`/`elan`
are no longer in `permissions.deny`.

**Why the change.** Every persistent-server failure mode this project
hit came from documents that were opened and never closed, and from
state shared between client processes: a stale `lake setup-file`
failure replayed with `verified: true`, a false clean from an unheard
publish, four rival elaborations of one file, clients wedged on dead
FIFO handles after a server restart. A command-line invocation is a
fresh process that exits and returns its memory, so none of those can
occur — the fix is structural, not disciplinary. The cost is that each
run pays the import load (minutes for a large cone), which is exactly
why the scratch-module rule below matters more than ever.

The standing agent-facing version of this lives in
`/home/chend/.flt-agent-doctrine.md`, which every task prompt points at.

**`lake env lean` DOES NOT REBUILD IMPORTS — a partially refreshed `.lake`
manufactures phantom hard errors** (2026-07-26; cost at least four agents a
cycle each and produced a top-priority "defect repair" dispatch against a file
that was never broken).

`lake env lean <file>` sets environment variables and runs `lean`; it consumes
whatever `.olean`s happen to be on disk. `lake build <Module>` is the only
command that brings the import cone up to date. So after the worktree pointer
moves — which it does at every dispatch — **`lake build <Module>` FIRST, and
only then iterate with `lake env lean`.** An inconsistent olean set is the
default state of a freshly repointed worktree, not an exception.

Why an inconsistent set is worse than a stale one: **olean loading does not
typecheck.** A statement stored in an olean is deserialised verbatim, so an
olean compiled against an OLD signature keeps its old application arity, and the
mismatch surfaces only when a consumer uses the term — as a type mismatch, a
"rewrite failed, pattern not found", a "function expected", or a `(kernel)
application type mismatch`. All four shapes were observed from ONE cause. A
kernel error normally means "this proof is not accepted", and here it meant
"your `.lake` is inconsistent" — the most misleading possible signal.

The concrete instance: `38e8531` moved `Field.absoluteGaloisGroup.map` (and
`mapAux`, `lift_map`) above `variable [NumberField K]`, dropping an instance
argument. That is source-compatible — there is no `@`-application of it in the
tree — but NOT olean-compatible: oleans built before it store
`@Field.absoluteGaloisGroup.map ℚ Kᵥ Rat.instField _ Rat.numberField (algebraMap …)`
with `Rat.numberField` sitting in the `f` slot. Three worktrees whose
`AbsoluteGaloisGroup.olean` had been refreshed while `Semistable`/`Torsion`/
`WeilPairing` had not each reported the same four "hard errors" in
`MazurTorsion.lean`. A full `lake build` there produced `EXIT=0`, zero errors.

**Corollary for triage: "three agents confirmed it independently" is NOT
independent confirmation** when all three verified the same way in worktrees
sharing the same defect. Before treating a hard error as a source defect,
confirm it survives a complete `lake build` of the module, and check the olean
mtimes in dependency order:

    d=/scratch/chend-flt/flt-lean-N/.lake/build/lib/lean/Fermat/FLT
    stat -c '%y %n' $d/Deformations/RepresentationTheory/AbsoluteGaloisGroup.olean \
                    $d/FreyCurve/Semistable.olean $d/EllipticCurve/WeilPairing.olean

A downstream olean older than an upstream one it really imports means the set is
inconsistent and every diagnostic from it is untrustworthy.

**A FULL-CONE BUILD IS NOT ENOUGH — MERGE `main` FIRST** (2026-07-26, and this
corrects the rule immediately above). An agent applied exactly the test
prescribed here — a complete `lake build` of the cone — the error survived it,
and **the error was still not real**: its tree was ~250 commits stale and
current `main` already carried the repair. A full build proves the tree it is
given is broken; it says nothing about whether that tree is current. The two
failure modes are different and the build only separates one of them:

* *inconsistent oleans* → a full `lake build` clears it;
* *stale sources* → only `git fetch && git merge main` clears it.

So the triage order is **merge `main`, then full build, then believe it**. The
same defect (`MazurTorsion.lean`'s `map_baseChange` rewrite) was diagnosed
independently by at least seven agents and repaired on branches by six of them,
every one of which was working from a base that predated the fix landing. That
is not seven confirmations; it is one bug and seven stale checkouts.

**THE LINE NUMBERS IN YOUR OWN TASK PROMPT ARE A FREE STALENESS DETECTOR — check
them first, before anything else** (2026-07-31, measured). The loop generates a
task prompt's `Fermat/…:NNNN` references by scanning **`main` at the moment the
task is written**; the worktree hook fast-forwards the worktree at the moment the
task is *dispatched*. Those are different times, and under the loop they are
routinely hours apart: `flt-lean-318` was handed three targets at lines
3495/16362/17378 and opened a `TateModule.lean` whose copies of them were at
3303/14089/15105 — the checkout was `1411711d` (2026-07-30 11:54) against a `main`
of `d451d20b` (2026-07-31 00:25), **380 commits and +3057 lines in that one file**.

So the check costs one `grep -n` and settles it: if a target's line number in the
prompt does not match the worktree, the worktree is BEHIND `main` and everything
you are about to read is stale — merge before you read, not after your first
confusing result. The failure it prevents is the expensive one: reading a
docstring's absence table, route history or "already refuted" list from a version
that has since been rewritten, and then proving or re-refuting against it.

Do not "fix" the discrepancy by trusting the prompt's numbers and seeking around
them. A prompt is a snapshot of a file you do not have.

**There is NO Lean MCP of any kind (Deyao, 2026-07-25).** Both the
`lean-lsp` MCP and the per-worktree `report-flt-lean-N` servers are gone;
`.mcp.json` holds exactly one entry, `annas-mcp`, which is for downloading
literature and has nothing to do with Lean. So neither the
`lean_leansearch` / `lean_loogle` / `lean_local_search` / `lean_run_code` /
`lean_multi_attempt` tools nor `diagnostics` / `build` exist — task prompts
must not offer them. Substitutes: search mathlib by reading it (`grep`/`Grep` over
`.lake/packages/mathlib`) and by the names other owners have already
recorded in docstrings; prototype in a throwaway scratch module verified
through the report MCP, which is the same loop the performance rule already
prescribes and is what agents were mostly doing anyway.

## `lake build` DOES NOT LOCK — a second build in the same worktree runs RIVAL elaborations

(2026-07-31, measured.) Launching `lake build <Mod>` while an earlier `lake build` is still
running in the SAME worktree does **not** block or queue. Both proceed, and `ps` shows the two
`lake` processes each with their own `lean` children **elaborating the same files**, writing the
same `.olean` paths in `/scratch/chend-flt/flt-lean-N/.lake/build`:

    3307744 lake  lake build Fermat.FLT.FreyCurve.MazurTorsion
    3315601 lean    …/Fermat/FLT/FreyCurve/Semistable.lean      <- child of 3307744
    3330028 lake  lake build Fermat.FLT.FreyCurve.MazurTorsion   <- second invocation
    3330679 lean    …/Fermat/FLT/FreyCurve/Semistable.lean      <- child of 3330028, SAME file

The natural sequence that produces it is innocent: start a baseline build in the background, edit
the file while it runs, then start the verification build. The doctrine's "two rival elaborations
writing one `.olean`" warning was written about a self-detached `ssh`; it applies just as much to
two ordinary foreground builds, and nothing in `lake` prevents it.

**Before launching a build, check for one already running, by cwd:**

    ssh $H 'for p in $(pgrep "^lake$"); do
              case "$(readlink /proc/$p/cwd)" in $HOME/flt-lean-N) echo "$p BUSY";; esac
            done'

**If you find yourself with two, the cheapest safe move is usually to let BOTH finish.** They are
building the same sources, so they write byte-identical content; the torn-olean risk comes from
*killing* one mid-write, not from the overlap. Then run one more `lake build` of the target and
require the `Build completed successfully` line — a replay is cheap and it is what certifies the
artifacts are consistent. Kill only if you must, by PID after a cwd check, never by pattern.

## Verify in a scratch module, not in the giant file

(Deyao, 2026-07-25, from a measurement — this is the fleet's single
biggest throughput lever.) **Develop against a throwaway scratch module
that imports only what you need, and do exactly ONE final blocking
verify against the real target file.** Delete the scratch before
committing. Agents who worked this way cut their round trip from **~30
minutes to ~1 minute**; several discovered it independently and reported
it unprompted.

Why, measured rather than assumed: **elaboration is single-threaded —
one core per file.** Sampling every `lean --worker` on this 96-core
machine (a `/proc` utime+stime delta, *not* `ps pcpu`, which is a
lifetime average and misleads) found 101 workers consuming **11.1 cores
between them**, 77 of them idle, the busiest at 1.29 cores. iowait was
0–3%; RAM had 1.5 TB free. So the fleet is **not** disk-, CPU- or
memory-bound, and moving `.lake` to tmpfs or deduplicating the 62
mathlib copies would buy nothing. What costs wall-clock is that a
15k-line file such as `Modularity/Interface.lean` re-elaborates on ONE
core however many are idle beside it. The only way to go faster is to
elaborate less.

Corollaries: batch edits and verify once rather than per-edit; a
client-side timeout means the server is still elaborating, so re-issuing
attaches rather than restarting (see the single-flight section); and
splitting oversized modules is what converts idle cores into throughput,
because the file is the unit of elaboration.

## Sorry and have discipline (glue-first, no floating)

- **Glue first.** At any frontier, first replace the bare `sorry` with
  a full skeleton: definitions and choices as real code, every
  believed-true step as a sorried `have` with its exact statement,
  final assembly written and compiling. Only then prove the sorried
  steps. Proven `have` bricks stacked in front of a trailing `sorry`
  with no written consumer are floating.
- **`sorry` only against a stated goal.** A `sorry` may only replace
  the PROOF of an explicitly written proposition (`have h : <full
  statement> := by sorry`). Never a bare `sorry` covering an unstated
  remainder, never `(by sorry)` as an application argument.
- **Every bound `have`/`let` must be consumed** (Deyao, 2026-07-22).
  Prune unused ones before committing (verify each prune compiles).
  **This is now the AGENT's own responsibility** — the enforcing hook
  (`.claude/unused-binding-check.py`) was deleted on 2026-07-25 along with
  the MCP it fired on. Nothing checks it for you; Lean's own
  `unusedVariables` linter is the closest thing to a signal.
- **Never use `private` to dodge the free-floating check** — open the
  consumer sorry first, always top-down.

## Free-floating code: definition and policy

**Free-floating code** is any project declaration that is not in the
transitive used-constant cone of the root theorem
`fermat_last_theorem` — i.e. no proof term reachable from the root
actually uses it (a sorried body contributes no dependency edges, so
material built bottom-up for a still-sorried consumer is free-floating
until the consumer's proof skeleton is written to consume it). Only
crossings into external libraries are exempt. Free-floating code is
not allowed: the Stop hook verifies this with the Lean compiler. The
cone itself is computed inside `ProgressCensus.lean`'s `runCensus` (the
`"floating"` field of its JSON output, via ImportGraph's
`Name.transitivelyUsedConstants` — already a vendored transitive
dependency through mathlib's own lakefile, not a hand-rolled BFS),
obtained through `progress-tree.py`'s census, which since 2026-07-25 runs
as ONE `lake env lean ProgressCensus.lean` over ssh on the worktree's
assigned host — no resident server, no cache file. Each run pays the
import load of the project cone (minutes), so run it once per bookkeeping
cycle rather than in a loop, and keep the tree BUILT: the census reads
oleans and dies with `object file '….olean' does not exist` if they are
stale.
`free-floating.py` is a thin standalone entry point over the same
query, applying only the keep-list filter below. Blocks with
instructions to commit and delete. Work top-down.

**Deleted free-floating content (2026-07-18): see the deletion commit
below.** The sweep removed 19 whole modules (the ModThree/Dickson–PGL2
clusters, `TateCurveConstruction`, `TateUniformization`, `OddAbsIrred`
among them) at file granularity with import-closure. The deleted
material — including the full nonarchimedean Lambert/bilateral
machinery for the Tate uniformisation and the ℂ-analytic
`weierstrass_equation` development — remains available in git history;
recover pieces with `git show <deletion-commit>^:<path>`.

DELETION-COMMIT: `52297bf2d7bfe856d7ce01736f0113c11f6fa613` — recover
deleted files with
`git show 52297bf2d7bfe856d7ce01736f0113c11f6fa613^:<path>`.
(This is the post-split hash; the pre-split dissertation-repo hash was
`8282dfb03cd1a390fd979a1d38fa2bb3b863ac20`.)

**Elaboration-invisible dependency classes (learned 2026-07-18).** The
term-level cone under-approximates what elaboration needs; deleting a
"floating" declaration in these classes breaks the build even though
no cone proof term mentions it. Every deletion must be build-verified
(revert-on-red), and these classes must be skipped or handled
specially:

1. *Auto-generated members* (`rec`/`casesOn`/`mk`/`injEq`/`ext`/…)
   share their source lines with the parent declaration.
2. *Instances consumed by typeclass synthesis then inlined*.
3. *rfl-`@[simp]` lemmas* used by `simp` without appearing in proof
   terms.
4. *Syntax-level `simp`-argument references* that never fire.
5. *Section/namespace scaffolding* inside or adjacent to reported
   declaration ranges.
6. *Module-system opaque exports*; also `example` blocks pin their
   instance dependencies at elaboration.

Build-verified members of these classes are recorded in
`free-floating-keep.json`; `free-floating.py` subtracts them and
reports them as `kept_invisible`. Reduce residual floaters by writing
the consuming proofs, not by further blind sweeps.

## Filesystem hazard: macOS case-insensitivity

The filesystem is case-INSENSITIVE: `Fermat` and `fermat` are the SAME
path. On 2026-07-16 an `rm -rf` of a stray capital-F directory deleted
the entire project including its `.lake` cache; recovery worked only
because the tree was committed-clean. Rules: never `rm -rf` a path
that differs from a real path only by case; prefer `git clean -n`
(dry run); keep the tree committed before destructive operations.

## AN AUDIT'S "BLOCKED ON MISSING STRUCTURE" VERDICT EXPIRES — RE-CHECK THE NAMED PRECONDITION

(2026-07-31.) A leaf's atomicity audit is usually written as a conditional: *this cut is
blocked, and it becomes available exactly when X exists*. The condition is the useful part
and it is the part nobody re-reads. `X18.two_divisible_pic`'s descent-axis bullet said the
`2`-descent cut "needs residue fields `κ(v)` and the norms `N_{κ(v) ⊗ L / L}` — precisely
the degree theory `PlaceData` deliberately omits … so the cut is available exactly when
someone extends `PlaceData` with residue fields."

**No extension was ever needed and none happened.** A valuation determines its own valuation
ring, so `O_v`, `m_v`, `κ(v) = O_v ⧸ m_v` and `deg v = [κ(v) : K]` are definable from the
`ord` axioms `PlaceData` already had — and by 2026-07-30 they were IN THE SAME FILE
(`PlaceData.valRing`, `valMax`, `residue`, `degOf`), with `exists_degreeMap` PROVEN over
them, roughly 3600 lines above the audit that declared them absent. The verdict was written
before that work and was never re-read against it.

This is the same failure as the VOID-AUDIT rule above, in the other direction: there, a
statement changed under a valid audit; here, the WORLD changed under a valid audit. Both
produce an audit that is honest, internally correct, carries a date, and is wrong.

So, two rules:

- **When an audit says "blocked until X exists", grep for X before believing it.** One
  `grep -n` is the whole check, and its answer is a fact rather than an opinion.
- **Separate "structurally blocked" from "expressible but very large" in the verdict, and
  say which you mean.** Only the first is a reason never to dispatch. Here the arithmetic
  obstruction (`#Sel₂ = 1`: class groups and `S`-units of a degree-`6` field) is entirely
  real and unchanged — but "nobody can even state it" and "somebody would have to build a
  lot" call for opposite decisions, and the bullet had been read as the first for days.

Corollary for whoever writes the audit: phrase the precondition so it is GREPPABLE — name
the declaration you would need, not the capability. "needs `PlaceData.residue`" would have
been refuted by the next reader in ten seconds; "needs the degree theory `PlaceData`
deliberately omits" survived because there was nothing to look up.

## A DECLINE IS A COMMIT, NOT A SHRUG — ancestry is the only receipt for a branch

(2026-07-30, medic.) The loop hands a merge worker a list of branches and gets
no itemised answer back — a sentinel says `panic: false` and one line of prose.
So it has exactly one way to tell, per branch, whether that branch was dealt
with: **is it an ancestor of the main you published?** Everything the merger is
allowed to do produces one. A merge does. So does a DECLINE, *provided* it is
recorded the way the class-7 section above prescribes — `git checkout HEAD --
<the files>`, then commit the merge, so the diff against the first parent is
empty on purpose and the message says the payload was declined.

`git merge --abort` and moving on is not a decline. It leaves no receipt, and
the branch is indistinguishable from one you never reached.

That distinction used to cost the work. Adopting a release discharged the whole
claim on the strength of the release being *complete* — main moved, snapshot
and audit current — which says nothing about how much of the payload got
merged. A merger that merged 18 of its 55 branches and was killed before
reporting had the other 37 dropped in one assignment, their worktrees pinned in
`awaiting_merge` for ever, because a worker is freed only by its branch
BECOMING an ancestor of main and nothing was left to merge it. **78 worktrees —
one full day of the fleet's output — were stranded that way**, and nothing
noticed until an invariant check summed two numbers that had never been summed.

Row 10 now folds the unlanded remainder of a claim back into the batch, so a
merger running out of time is safe: merge what you can, publish, and the rest is
re-offered next release. But that only works if a decline is a decline. An
unrecorded one comes back to the next merge worker for ever.

General form, and this is the third time it has bitten in a week: **an
assignment to a field that holds a CLAIM ON WORK is a deletion of work.** Every
other hand-off in the loop is a fold or a move. Both leaks — `r11_action`'s
`.inflight = list(batch)` and `r7_action`'s `.inflight = None` — were single
assignments, and both were invisible because the state they produced is
indistinguishable from a state where the work never existed.

## What the merge batch is for: Lean edits that could turn a green build red

(Deyao, 2026-07-26.) **The batch exists to protect a green build, and nothing
else.** So the dividing line is not "who wrote it" but "can it break the
build":

- **Lean code edits** — anything under `Fermat/` — go to a branch and into
  `~/.flt-merge-batch`, always. They can turn green into red, which is exactly
  what the merger exists to catch.
- **Tooling unrelated to the math content** — `.claude/*`, `flt-*.py`,
  `CLAUDE.md`, memory files — the orchestrator **commits directly to `main`**.
  It cannot make the Lean build red, so routing it through a merge worker buys
  nothing and costs a release cycle of latency: the fix is inert on an
  unmerged branch precisely while the bug it fixes is live.

Deyao amended this the same day he first objected to a tooling commit on
`main`, so both halves are his: the objection was to the orchestrator doing it
*silently and by accident*, not to the act itself.

**One asymmetry to remember either way.** The merger's release step is
`git branch -f main <the sha it built>`, so a commit on `main` that the merger
has not merged is not in its history and that force-move would discard it. In
practice the merger merges `main` before moving it (it has done so at every
release), which is what makes direct tooling commits safe. If you ever see a
release drop one, that is the mechanism.

And note it is effectively irreversible: worktrees fast-forward to `main` at
every dispatch, so within minutes a dozen sit ON the commit, and rewinding
`main` makes their branches non-ancestors of it — which the dispatch hook
hard-crashes on, by design. So the bar for a direct commit is "certainly not
Lean", not "probably fine".

## git is allowed — except force-push

Claude may run `git` commands; exercise ordinary caution with
history-destructive operations. **`git push --force` remains
explicitly banned**: `permissions.deny` in `.claude/settings.json`
blocks all variants. Plain `git commit` (ssh-signing is automatic via
Deyao's agent; if signing fails with "No private key found", the
agent — Bitwarden — is locked: ask Deyao). Commit trailers: the
standard Co-Authored-By and Claude-Session lines.

## Anna's Archive MCP (annas-mcp)

The server is `annas-mcp.py` at the repo root, registered in the
committed `.mcp.json` with `"ANNAS_KEY": "${ANNAS_KEY}"` — the secret
is NEVER stored in the repo; export `ANNAS_KEY` in the shell
environment before launching Claude Code. The script itself reads
`os.environ["ANNAS_KEY"]`.

The `download_annas` tool wraps Anna's Archive
`dyn/api/fast_download.json`, which returns ONE `download_url` per
call. Mirror selection is via the optional `domain_index` /
`path_index` parameters.

**Quota accounting (empirically verified).** Anna's quota tracks
DISTINCT md5s, not raw API calls. Retrying the *same* md5 with a
different `domain_index` (e.g. to dodge a TLS error or 404) is
**free** after the first call that day; a *new* md5 costs one slot.

**SSL / TLS errors on a download URL**: usually a broken cert chain on
that CDN mirror. Retry the *same md5* with a different `domain_index`
(free). **Keep certificate verification on** — never `verify=False`;
a persistent TLS failure means the file is not safe to download.

## "The pin has no Riemann–Roch" is TRUE and often IRRELEVANT — check for a NORM first

(2026-07-31, flt-lean-133.) Three separate leaves in `ModularCurve/X0.lean` were
priced at "needs `Γ(A,−)` as a functor to `R`-modules together with its rank", i.e. a
Riemann–Roch development. For the pole-order one that price was wrong by a whole
development, and the reason generalises.

**A finite free algebra has a NORM, and the degree of the norm is the invariant you
were about to build by hand.** `WeierstrassCurve.Affine.CoordinateRing` is free of
rank 2 over `R[X]`, so `ord z := (Algebra.norm R[X] z).degree` is defined at this pin
with no new theory, and it IS the pole order along the point at infinity (`ord x = 2`,
`ord y = 3`). Everything a degree function needs is already proven upstream:
`Algebra.norm` is a `MonoidHom` and `Polynomial.degree_mul` is additive over a domain,
so `ord` is additive on products *for free*; `CoordinateRing.degree_norm_smul_basis`
computes it as `max (2 • deg p) (2 • deg q + 3)` in the `{1, Y}` basis, which gives
`max` on sums; and `CoordinateRing.degree_norm_ne_one` is exactly "the value semigroup
is `⟨2,3⟩`". That was enough to prove the linear shape of any SURJECTIVE
`R[W] → R[W']` over a domain — no sheaves, no cohomology, no `𝒪(nO)`.

So before accepting "absent from the pin", ask what STRUCTURE the object already has:
finite free ⟹ norm, trace, characteristic polynomial, discriminant. A `grep` for the
missing *theory name* (`RiemannRoch`, `CartierDivisor`) will always come back empty
and always feels conclusive; a grep for the *invariant you actually need* on the
object you actually have will not.

Two corollaries that cost nothing and were both worth more than the proof:

- **Where an argument BREAKS tells you what the leaf is really about.** The
  domain-only step was "leading terms do not cancel", i.e. `gr R[W] = R[t²,t³]` is a
  domain iff `R` is. So the general-`R` residue is purely NILPOTENT — which promoted
  the file's own `ℚ[ε]/(ε²)` counterexample from a peripheral warning to a statement
  of the whole remaining problem, and re-priced the attack from Riemann–Roch to
  deformation theory.
- **Prove the hypothesis you wish you had.** The leaf took an arbitrary compatible
  `Φ`; two open immersions with equal range plus `ι` being a monomorphism force `Φ`
  to be the canonical equivalence, so surjectivity was free and was the only thing
  the argument consumed. A leaf stated for "an arbitrary `Φ` with `hΦ`" was never a
  generalisation, and nobody had checked.

## PDF Text Extraction

When extracting text from a PDF, the output will be read by an AI, not
a human. Preserve as much information as possible. First try
`pdftotext -layout <input>.pdf <output>.txt`. OCR only when that
output is empty or garbled.

**Use the NATIVE tools — `tesseract`, `pdftoppm` and `pdftotext` are all on
PATH, and Docker is NOT available on this machine** (2026-07-27; the
`ocrmypdf` Docker recipe previously documented here could never have run).
This route recovered Fontaine's Prop. 1.7(i)(a) from an image-only GDZ scan
where `pdftotext` returned nothing but the cover sheet:

```
pdftoppm -r 300 -gray -f <first> -l <last> <input>.pdf /tmp/pg
for f in /tmp/pg-*.png; do tesseract "$f" "${f%.png}" --psm 6; done
cat /tmp/pg-*.txt > <output>.txt
```

`--psm 6` ("assume a single uniform block of text") is what makes running
text come out readable; the default page-segmentation mode shreds
two-column mathematics. OCR page RANGES you actually need rather than whole
books — 300 dpi greyscale is a few seconds per page. Expect mathematical
notation to survive poorly: read OCR output for the ARGUMENT, then restate
the mathematics yourself rather than trusting transcribed formulas.

## Freeing a worktree needs a LIVE-PROCESS check, not a clean `git status`

(2026-07-27, orchestrator error.) `flt-lean-86` was marked `ready` and dispatched into **while another
agent was still working in it**. Two agents then shared one worktree: the newcomer found *two* `lean`
processes elaborating `WeilPairing.lean` into the same `.olean`, its `git add -A` swept the other agent's
uncommitted `HasseBound.lean` edits into an unrelated commit, and when it restored the file the other
agent **rewrote it again** — which is how the collision was finally diagnosed. It also made
`MazurTorsion` look red (two errors) from a defect that was neither on `main` nor in either agent's work.

The trigger was a *correct* observation read as the wrong conclusion. A completing agent reported that
`flt-lean-86` "sits at `81eb57e2`, clean, and its branch was fast-forwarded — nobody is working on it."
Every clause was true at the instant it was measured. **A worktree between edits is indistinguishable
from an idle one by `git status` alone**, and an agent doing a 25-minute `lake build` touches nothing for
25 minutes.

So the rule is: **before promoting any worktree out of `claimed`, check the OWNING HOST for live
processes**, not just the tree:

    H=$(cat ~/.flt-worker-host/flt-lean-N)
    ssh $H "pgrep -af '[l]ean.*flt-lean-N'"

and cross-check `python3 flt-owner.py --all` (latest dispatch per worktree, from the transcripts) against
the completion notifications actually received. **The notification stream is the ground truth for "this
agent has stopped"** — a third party's report that a slot looks idle is not. This is the same principle
`.claude/skills/fleet-revive/SKILL.md` states for staleness sweeps ("staleness cannot distinguish working
from dead"), applied to the promotion direction.

Corollary, and the reason this was recoverable: the intruding agent **tagged the other agent's WIP**
(`flt-lean-86-hassebound-wip`) before touching anything, and left the working tree dirty by design. When
a collision is discovered, preserve first and report loudly; do not clean up to make `git status` tidy.

## A `∀ P : <presentation structure>` LEAF IS ONLY AS TRUE AS THE STRUCTURE PINS ITS OBJECT

(2026-07-31, generalising a refutation found 2026-07-30.) `X1.lean` and `X0.lean` state most
of their geometry as `∀ P : Gamma1GITPresentation N (Spec K), <property of P.A>`. That shape
is only sound for properties the FIELDS force. `Gamma1GITPresentation.classify_dM` pins the
coarse ring `B = A^G` — it says `Spec (algebraMap B A)` IS the classifying map of the
universal family — and pins `A` **not at all**. `smoothCurve_A_of_gamma1GITPresentation` was
refuted on exactly that gap, by an explicit inhabitant nobody had looked for.

**The test is cheap and mechanical: PINCH the honest presentation.** Given any inhabitant `P₀`
with ring `A₀`, group `G₀`, invariants `B₀`, and a `G₀`-stable ideal `0 ≠ I ⊊ A₀`, set

    A := A₀ ×_{A₀ ⧸ I} A₀,   G := G₀ × ℤ⧸2   (G₀ diagonal, the generator swapping),
    dM := (Spec Δ)^* dM₀     for Δ : A₀ → A, a ↦ (a, a).

Every field survives — each datum is a pullback along an explicit ring map, `pr₁ ∘ Δ = id`
carries `cover`, and `A^G = B₀` keeps `classify_dM` — while `Spec A` is two copies of
`Spec A₀` glued along `V(I)`, i.e. nodal. **So no property that fails at a node is provable
from these axioms**, and any leaf asserting one is FALSE, not merely hard.

Two corollaries worth having in advance:

* **The swap is what keeps `B` pinned, and it is also why the pinch is not universal.**
  Dropping it (`G := G₀` alone) would break far more — the two components stop being
  exchanged — but then `A^{G₀} = B₀ ×_{B₀ ⧸ (I ∩ B₀)} B₀ ≠ B₀`, and `classify_dM` rejects it.
  So the pinch family only ever attacks properties destroyed by GLUING (regularity,
  smoothness, normality, being a domain), never properties preserved by it (reducedness,
  Krull dimension, transitivity of `G` on components). Check which side your leaf is on
  before assuming the refutation transfers: `transitiveMinimalPrimes_tensorProduct_of_`
  `gamma1GITPresentation` was audited against the pinch on 2026-07-31 and survives it.
* **The repair is to MOVE the citation, not to weaken the statement.** `Gamma1RigidifiedModuli`
  carries `universal`, a fine-moduli property WITH a uniqueness clause, so it pins `Spec A` up
  to unique isomorphism. State the citation there and carry it down as a structure FIELD
  (`smoothM : SmoothOfRelativeDimension 1 strM` is the worked example). Weakening the
  conclusion instead just makes a second universally-quantified guess of the kind that was
  just refuted.

**And a field added this way SHRINKS the class every other leaf in the file quantifies over.**
Once `smoothM` is a field the pinched `P` is not an inhabitant, so every route audit written
earlier was performed against a strictly larger class — those audits are not void, but they
are not evidence about the new class either. Re-run the ones that turned on a missing
regularity/normality precondition; that precondition is now free.

## A "DOES NOT USEFULLY SPLIT" VERDICT IS SCOPED TO THE CONSTRUCTION ITS AUTHOR HAD IN MIND

(2026-07-31, `ArtinSymbol.lean`.) `closure_frobAt_eq_top` (Chebotarev) carried a careful,
honest docstring verdict: *"audited, faithful, and deliberately NOT decomposed"*, with a
numbered list of three ingredients the fixed-field reduction would need and which the pin
does not have. **Two of the three did not exist.** They were consequences of one unstated
design choice — that the fixed field `M = L^H` should be GALOIS over `K`, so that one can
speak of `frobAt K M`. Galois-ness forces `H` normal, which forces transporting
`Algebra.IsUnramifiedAt` along an automorphism (obstacle 1), and `frobAt K M` forces
functoriality of `arithFrobAt` down a tower (obstacle 2). But the reduction never needs
`frobAt K M`: the only thing wanted from `M` is that its primes have residue degree `1`,
and that is read straight off the congruence `σ y ≡ y^(N𝔭) (mod Q)` restricted to `𝓞 M`,
with `M` used as a RING and no Galois structure at all. With that, the reduction is ~90
lines against mathlib as it stands, and the residual leaf is a clean density statement
naming no Frobenius and no Galois group.

**So when a docstring says a node does not decompose, read the obstacle list as a claim
about ONE route.** Ask which of the obstacles are forced by the goal and which are forced
by the author's chosen intermediate object; the second kind vanishes when you weaken the
intermediate object to the least structure the argument actually uses. The tell here was
that every listed obstacle mentioned `M` being Galois, while the conclusion mentions only
`Subgroup.closure`.

Two corollaries worth keeping separate:

- **The verdict was still right about the OTHER cut it considered**, and said so: the
  contrapositive ("for every proper `H` there is an unramified `Q` with `frobAt K L Q ∉ H`")
  trades one leaf for an equivalent one. The discriminator between a real cut and noise is
  whether the residual statement stops mentioning the project's own vocabulary. That test
  also correctly REJECTS the analogous cut on the sibling leaf `artinMap_toPrincipalIdeal`
  (reduce abelian reciprocity to the cyclic case): the residual still mentions `frobAt` and
  `Gal(L/K)`, and is where the classical proof spends all its effort.
- **Do not add the infrastructure an obstacle list names once you no longer need it.**
  Tower functoriality of `frobAt` is genuinely missing and genuinely reusable — and adding
  it here would have been FREE-FLOATING code, since nothing in the cone consumes it. An
  obstacle that dissolves is not a licence to build it anyway.

## TWO INDIVIDUALLY-CORRECT REPAIRS CAN BE FATAL TOGETHER

(2026-07-27.) `exists_artinDivisorNormIndex_le_ray_class` was refuted-and-restated once (making `mm` an
OUTPUT rather than an input), and a later integration added a support clause to the conclusion
(`∀ w, w.asIdeal ∣ mm → w.asIdeal ∣ mm₀`). **Each change is right in isolation. Together they made the
leaf FALSE**: the support clause confines the chosen `mm` to primes already dividing `mm₀` — enlargement
is permitted only in the EXPONENTS — while the only hypothesis on `mm₀` was `mm₀ ≠ ⊥`. A caller may then
supply an `mm₀` missing a ramified prime, and no admissible `mm` is reachable at all.

Witness: `F = ℚ`, `χ` cutting out `ℚ(i)`, `ℓ = 2`, `k = 1`, `mm₀ = ⊤`. No height-one prime divides `⊤`,
so `mm = ⊤`, `Im = ⊤`, and `P = ⊤` (the congruence is vacuous, i.e. `h⁺(ℚ) = 1` in the formal language),
giving `(P ⊔ N).relIndex Im = 1` against `A.relIndex Im = 2`. The conclusion reads `2 ≤ 1`. Not a
unit-ideal corner case: `mm₀ = (3)` refutes it identically.

**Why no ordinary check catches this.** Both edits pass review against the statement as it stood when each
was made. A falsity audit performed before the second edit certifies a statement that no longer exists,
and the audit *label* survives to say the leaf was checked. So a leaf can carry an honest, correct
FALSITY AUDIT and still be false.

**The rule: when a leaf is restated a second time, the earlier audit is VOID, not inherited.** Re-run it
against the composite statement and write a SECOND audit; do not reason "the first audit covered the hard
part". The repair here was one hypothesis (`hmm₀ram : ∀ w, IsRamifiedCharRayClass F χ w → w.asIdeal ∣ mm₀`)
that the consumer **already held and was discarding** — so the fix cost nothing, and the consumer's
statement did not change. That is the usual shape: the missing hypothesis is often already in the caller's
hand.

## SEVENTH invisibility class: A CLEAN MERGE THAT DOES NOT COMPILE — the interface split

(2026-07-30, release 22, three instances in one batch.) The six classes above are all about
*not seeing work*. This one is about *seeing a merge succeed*. Every check this file prescribes
for a merge — no conflict markers, `git diff --stat HEAD^1 HEAD` non-empty, the sorry counts,
the `declaration uses 'sorry'` warning set — passed on all three, and the tree did not build.

The shape is always the same. **An interface change and its call sites are ONE edit, and a merge
can split them across the conflict boundary.** The half that conflicts gets resolved; the half
that does not conflict lands unexamined; and the two halves now contradict each other.

- `RelativePicard.lean`: `flt-lean-133` CLOSED `nonempty_modTensor_assocPic` by hoisting, deleting
  the leaf and re-pointing the call sites *its base had*. `main` had gained more call sites since.
  Both edits merged without conflict; six calls to a deleted declaration survived.
- `ArtinConductor.lean`: `flt-lean-197` split break POSITIVITY into its own clause, so one theorem
  returns `⟨pos, counting⟩` and another takes two binders. The SIGNATURES were the non-conflicting
  half; the CALL SITES were the conflicted half, resolved to `ours`, still passing one conjunction.
- `Patching.lean`/`Interface.lean`: two owners threaded DIFFERENT hypotheses (`hp5`, `hgen`) through
  the same six-theorem positional argument chain. Signature edits merged cleanly, so the callees
  bind both; each side's call line passes only its own. **Neither `ours` nor `theirs` compiles** —
  and the conflict looks like a trivial whitespace disagreement. Positional argument lists are
  what make this a merge hazard at all.

**Corollary, and it inverts the obvious rule: resolving every conflict to `ours` is NOT a safe way
to decline a payload.** Twice this release it left the tree broken, because the branch's chain
straddled the boundary:
`flt-lean-366`'s three new leaves landed non-conflictingly while the two proven helpers they call
sat in the dropped half (seven live references to nothing); `flt-lean-123`'s hoist inserted 5164
lines into `X0.lean` while `MazurTorsion.lean` kept its copy (duplicate declarations). **To decline
a payload, `git checkout HEAD -- <the files>`** and let the diff against the first parent be empty
on purpose. Say so in the commit message, because an empty payload otherwise reads as the
dropped-merge bug of class six.

**Two checks catch this class before the build, and both cost seconds.**

1. *Duplicate declaration names, WITHIN a file and ACROSS files*, diffed against the previous
   release so the tree's many legitimate same-last-component names in different namespaces do not
   drown the new ones. Two real errors this release: `Gamma0AtlasOver.bcUniversal_transport`
   declared twice in `X0.lean` by two branches whose regions were too far apart to conflict, and
   `Fermat.isInvertibleSheaf_modPullback` declared in two modules one of which imports the other.
   A per-file scan cannot see the second.
2. *Per merge: names declared on the BRANCH but absent from the resolved file, grepped
   (comments stripped) against the resolved file.* This is what found `flt-lean-366`'s breakage
   before a build ran.
3. *A binder RENAMED to `_x` in a SIGNATURE while the body still says `x`.* This is the
   cheapest-to-detect shape of the split and it was live on `merger` at `f6755e85`
   (2026-07-31): `ProperPushforward.lean`'s `eq_span_one_sup_smul_top_appTop_of_isIso_appTop_fiber`
   read `(_hm : m.IsMaximal)` while its body still called
   `exists_point_ker_Γevaluation_eq_of_isMaximal S m hm` — `unknown identifier 'hm'`, i.e. the
   whole module red. It arises when a branch reproves a theorem from a new upstream fact (here
   a hoisted `surjective_appTop_of_isIso_appTop_fiber`), so the hypothesis goes unused and gets
   underscored; the signature edit merges cleanly and the body replacement lands in the
   conflicted half. Grep the resolved file for a signature binder `_foo` whose declaration body
   mentions `foo` — seconds, no build, and it catches the whole class.

And the standing one, which is what caught the rest: **the release build is not optional and its
first failure is not its last.** Fix, rebuild, repeat — FOUR rounds this release, and the reason is
structural rather than bad luck. **The errors are serialised behind each other by the import
graph**, so round *n* only reveals what round *n−1*'s failure was hiding: one interface change
(`IsSwanExponentAt` gaining a third clause) broke a consumer in its own module, found in round 1,
and a second consumer 79 000 lines away in another module from another branch, found only in round
4 after twenty minutes of elaboration. Budget three rounds minimum, and schedule nothing behind the
first green one.

## A DOCSTRING'S "WHAT PROVING IT NEEDS" IS ABOUT A CONSTRUCTION, NOT ABOUT THE STATEMENT

(2026-07-31, `flt-lean-214`.) `exists_involutionSignSplitting` in `X0.lean` had stood
open since 2026-07-28 behind this estimate, written by its author and never re-derived:

> **What proving it needs**: abelian varieties over a field — absent from mathlib
> entirely — together with the quotient of an abelian scheme by an abelian subscheme
> as a faithfully flat map, and fppf descent to see that such a quotient is an
> epimorphism of schemes.

Every clause is a true statement about `P^± := A / B^∓`, the CLASSICAL construction.
None of it was needed. `IsInvolutionSignSplitting` never asks for a quotient: it asks
for a surjective flat epimorphism `p b` on which `ι` acts by `±1`, with finite joint
kernel and a descent for commuting endomorphisms. **`Im(1 ± ι)` is one**, it is
isogenous to the quotient, and nothing in the structure distinguishes them. The leaf
closed over machinery that was already in the file — the image theorem, `flat_`/
`epi_of_surjective_of_isAdditiveOn`, `finite_torsion_geomPt_of_abelianScheme`,
rigidity, and the `EffectiveEpi` that `epi_of_surjective_of_isAdditiveOn` discards.

This is the SECOND time the same substitution has paid in this one file — the first
is recorded on `exists_abelianImage_of_isAdditiveOn` as "the CHEAP replacement for
Poincaré reducibility that the image-not-kernel cut buys". So it is a pattern, not a
coincidence: **over a field, an IMAGE is cheap (scheme-theoretic image + Cartier gives
smoothness) and a QUOTIENT is expensive (fppf descent, the subscheme's own geometry),
and the two are isogenous.** Whenever a leaf's stated obstruction is a quotient, ask
first whether an image satisfies the conclusion.

The general rule, and it applies to every leaf in this development:

- **An absence table is evidence about the ROUTE its author searched.** It is not a
  theorem about the statement, and it does not expire loudly — it just sits there
  looking authoritative while the file grows the machinery that makes it false.
- Before accepting "this needs a theory we do not have", **read the CONCLUSION alone,
  field by field, and ask what each field actually demands.** Here the answer was
  visible in the structure's own docstring: it already said `ker_finite` "is the
  `2`-torsion argument", which is true of the image construction and says nothing
  about quotients.
- The cost of the check is one careful read. The cost of not making it was three days
  of a node the fleet believed was blocked on a missing subtree.

Corollary for anyone WRITING a leaf: say "the construction I have in mind needs X",
not "proving it needs X". The two read identically to the next agent and only one of
them is true.

## A DOCSTRING THAT ARGUES TWO LEAVES ARE EQUIVALENT IS A LEAF-MERGE WAITING TO BE PERFORMED

(2026-07-31, `flt-lean-217`, and it closed two leaves for 30 lines of Lean.)

`X1.lean` carried two open citation leaves, `exists_gamma1RigidifiedModuliScheme`
(`∃ R`) and `isAffine_of_gamma1RigidifiedModuliScheme` (`∀ R, IsAffine R.M`), split
out of one node the day before. The second one's docstring contained this, under the
heading "Why the `∀` is legitimate":

> `universal` is a **fine** moduli property, so any two inhabitants are related by a
> unique isomorphism … `IsAffine` is invariant under isomorphism of schemes. So
> "the Katz–Mazur `𝔐(𝒫, 𝒮)` is affine" and "every inhabitant … has affine `M`" are
> the same statement.

That paragraph was written to *justify the quantifier* — and it is simultaneously a
complete proof that the two leaves are ONE leaf. Nobody read it as one, because it
sits under a heading about faithfulness. Writing it in Lean
(`nonempty_iso_gamma1RigidifiedModuliScheme`: feed each scheme's universal family to
the other's `universal`, then kill both round trips with `universal`'s uniqueness
clause applied to the scheme's OWN universal family) is 30 lines over
`IsBaseChangeOfGamma1.refl`/`.comp`, and it collapses `∃ R` + `∀ R, IsAffine R.M`
into the single `∃ R, IsAffine R.M`. Both names and signatures survive as theorems,
so no consumer changed.

**So: prose of the form "these are the same statement", "this follows from that by
rigidity/uniqueness/invariance", "legitimate as a `∀` because …" is a proof sketch,
not a caveat.** If it is right, one of the two leaves is free. Grep the file's
faithfulness sections for it before dispatching anyone at either leaf.

The structural version, worth checking whenever a structure has a fine-moduli or
universal-property field: **a `∃!`-valued field makes the structure a contractible
groupoid, so `∀ R, P R.M` and `∃ R, P R.M` coincide for every isomorphism-invariant
`P`.** The same merge is available verbatim on the `Γ₀` side of this development
(`X0.lean`'s `exists_rigidifiedModuliScheme` / `isAffine_of_rigidifiedModuliScheme`
over `RigidifiedModuliScheme`, whose `universal` is the same shape and carries no
`m ≫ strM = g` conjunct, so the transcription should be shorter). It was not done
from `flt-lean-217` because that file is owned separately.

Related, and the reason the 2026-07-30 split happened at all: the split's own
docstring recorded the trade honestly as "`1 -> 2` open leaves, not `1 -> 1`". A
split that ADMITS it raises the count is exactly the place to ask whether the second
residue is real, because a leaf that a sibling's docstring can already derive is not
a citation — it is unwritten Lean.

## RIVAL CUTS ARE OFTEN COMPLEMENTARY — check before choosing

(2026-07-30.) Nine of 57 branches in one batch were declined because another agent had cut the
same node differently. In one case that verdict would have been wrong. `flt-lean-134` proved
sub-leaf (γ) of `exists_relNormDivisorHom_ray_class` OUTRIGHT and left (α) over a fresh sorry;
`flt-lean-343` proved (α) OUTRIGHT and left (γ) over a fresh sorry. **Taking either branch whole
keeps an avoidable open node; taking one proof from each closes both.** It cost one careful read
of four hunks and netted zero new sorries where either alone netted one.

So when two branches cut one node, the question is not "which cut is better" but "did they close
different halves". Ask it first. The tie-breakers, in the order that has actually decided cases:

- **fewer OPEN leaves after**, not fewer leaves created — `flt-lean-44`'s divisor-set cut left ONE
  leaf and closed 23 of 32 cases outright, against a bound-cut that left TWO and closed none;
- **named beats anonymous** — a cut leaving 8 NAMED leaves beats one leaving 4 declarations with 4
  anonymous inner sorries inside them, even though the headline count is worse, because an inner
  sorry is ownerless by construction;
- **already integrated and consumed by neighbours**, which is the merge worker's only defensible
  ground when the mathematics is genuinely equivalent (two complete proofs of one theorem cannot
  both be carried — the name collides — so that is a CHOICE, not a merge, and it belongs to an
  author; record the rejected branch's sha in the merge commit).

**And a branch that was right when dispatched can be wrong when it lands.** `flt-lean-91` and
`flt-lean-195` independently generalised `EllipticScheme.lean`'s reverse Riemann-Roch chain from
`ℚ` to an arbitrary field, both truthfully reporting "NO LEAF WAS ADDED" — true at their base,
where the three leaves were open. They were PROVEN at `ℚ` by the time the branches merged, so the
same edit would have traded one closed leaf for three re-opened ones. Re-derive a branch's own
accounting against the release, never against its base; and when you decline for this reason, queue
the follow-up, because the work usually got CHEAPER (here: generalise the PROOFS, and both targets
close with no new sorry).

## MERGING NINETY BRANCHES: the policy that works, and the four checks that must go with it

(2026-07-31, release 24 — 92 branches, 51 clean, 41 conflicting, 1 declined.)

**Resolving to `ours` by default LOSES PAYLOAD, and the loss is silent.** Measured on this
batch: a plain `ours` resolution dropped branch-added declarations in 17 of the 41 conflicting
branches — 71 of them from `flt-lean-362` alone. The branch still becomes an ancestor, the
build is green, and nothing says the work is gone.

The policy that preserved both sides, per conflict hunk:

- **base empty** (both sides ADDED at the same point) → `ours + theirs`, *unless* every
  declaration `theirs` introduces is already declared in `ours` — then `ours` alone, because
  the same content reached `main` by another route and the union would duplicate it;
- **base non-empty** → `ours + theirs` whenever `theirs` declares a name the BRANCH ADDED
  (absent at the merge base) that `ours` does not have; otherwise `ours` plus the blocks
  `theirs` purely INSERTED relative to base (`difflib` opcodes, `insert` only).

That took 41 conflicting branches down to 7 needing hand work. **But the policy is only safe
because of the checks, and three of the four had to be fixed before they told the truth:**

1. *Every branch-added declaration is present in the resolved file.* Compute "branch added" as
   branch-decls minus MERGE-BASE-decls — not minus `main`'s, which flags every name `main`
   legitimately deleted.
2. *No newly duplicated declaration name*, **diffed against pre-merge `main`** — this tree has
   many legitimate same-name pairs.
   - **Qualify by NAMESPACE.** `fieldAct_mul`/`_one`/`_xx`/`_yy` exist in both `GeomPic` and
     `ConstFieldExt` in `HyperellipticJacobian.lean`; a flat scan calls all four duplicates.
   - **Keep DOTS in the name.** A regex ending the name at the first dot collapses
     `IsCharRootMultiset.eq_roots` and four siblings onto `IsCharRootMultiset` and reports it
     five times over.
   - **Strip comments LINE-granularly** (a block starts at a line whose first token is `/-`,
     ends at a line containing `-/`). Character-level nesting goes wrong on this tree's
     docstrings and then the scan cannot see real declarations at all.
3. *Block-comment nesting depth returns to zero in every file.* **This is the new one and it is
   the cheapest check in the list.** A conflict hunk can begin INSIDE a docstring; keeping
   `ours` keeps the `/--` while the `-/` was on the side you dropped, and the docstring then
   swallows the rest of the file. Four files this release. Lean says `unterminated comment` at
   the LAST LINE, thousands of lines from the damage, and the module plus everything importing
   it fails — twenty minutes into the release build. The scan finds all four in a second.
   The mirror case also occurs: `MordellWeil19.lean` kept HEAD's `-/` and then the branch's
   paragraph landed *after* it as bare prose, so 25 lines of English were parsed as Lean.
4. *The release build, three rounds minimum* — for the reason release 22 recorded: the errors
   are serialised behind each other by the import graph.

**And a fifth failure this policy CREATES, which no declaration-level check can see: a
duplicated HYPOTHESIS.** Two branches gave `DualStruct.weil_nondegenerate` the same level gate
in two different styles — one a named binder `(_hnF : (n : F) ≠ 0)`, one an anonymous
`(n : F) ≠ 0 →` — and the union demanded it twice while the sole consumer supplied it once.
That produced 22 `(kernel) application type mismatch` errors plus a
`declaration has metavariables`, all reported at the USE site, which reads exactly like a
broken proof and is not one. **When two branches repair the same statement, the union of their
edits is not the repair.** Diff the two signatures against the merge base before taking both.

Finally, the merge-order effect, since it is cheap to exploit: conflicts are evaluated against
`main` *as it stands when you merge*, so a branch that conflicts in one order can be clean in
another. 15 of this batch's branches went clean on a second pass simply because the earlier
merges had landed first.

## THE FIRST TWO COMMANDS OF EVERY TASK: `git merge --ff-only main`, then `git show merger:<file>`

(2026-07-31, `flt-lean-232`, both measured on the fleet rather than inferred.) A prover agent
under the Python loop can be handed a worktree that is hundreds of commits stale AND a target
that was proven a day earlier. Both are cheap to detect and neither is detectable from inside
the task prompt.

**1. YOUR WORKTREE MAY NOT BE AT `main`, AND THE LOOP WILL NOT SAY SO.** `flt-lean-232` was
dispatched at `9a2ca10d` with `main` at `d451d20b` — **704 commits behind**. A sweep of the 112
live jobs at that moment found **23 behind `main`, 6 of them by the full 704**; the other 17 were
2 behind, which is only the tooling commits after the rebaseline sha and harmless. So this is not
a one-off: it is roughly 5% of dispatches, silently.

**THE CAUSE IS THAT NOTHING ADVANCES A WORKTREE — NOT THE LOOP, NOT THE RELEASE, NOBODY.** This
is worth stating plainly because the old orchestrator DID repoint at dispatch, the sections above
still describe that hook, and it is gone. Read the production code: `flt-loop.py`'s `do_spawn`
composes a prompt and runs `cd <worktree> … claude`, and that is the whole of it — no `merge`, no
`checkout`, no `branch -f`. The merge worker works in `~/flt-staging`; its five ordered duties are
merge, build the snapshot, rewrite `queue1`, stamp `AUDITED:`, stamp the snapshot sha. **None of
them touches a pool worktree.** So a worktree sits at whatever `main` was when its last occupant
last merged, indefinitely.

Which is exactly why the current ones are current: **the agents advance them.** The merge worker's
queued task text opens with *"Run `git merge main`, then `lake build …`"*, so every agent on a
merger-written task drags its worktree forward as a side effect. Tasks that lack that line — older
`queue1` entries, and the one that produced this section — leave the worktree wherever it was. The
repair belongs in the queue text, and it is one line: **put `git merge --ff-only main` in every
task's preamble.**

**Do not "fix" this in `flt-loop-fs.py`.** That file is the SIMULATOR — its `repo()` is
`~/.flt-loop/repo`, a stand-in repository for testing `flt_loop_rows.py`, not `~/flt-lean` — and
its `grepo("branch", "-f", j["worktree"], "main")` is simulation, not the dispatcher. It would not
work against the real pool anyway; git refuses to force a branch that a linked worktree has
checked out, which is every worktree in the pool:

    $ cd ~/flt-lean && git branch -f flt-lean-232 <sha>
    fatal: cannot force update the branch 'flt-lean-232' used by worktree at '/home/chend/flt-lean-232'
    EXIT=128

Any loop-side repoint has to run INSIDE the worktree (`git -C <wt> merge --ff-only main`), and
`--ff-only` rather than a forced checkout, so that a worktree still holding someone's uncommitted
work fails loudly instead of losing it.

**The free detector is the line number in your own prompt.** The task said
`Fermat/FLT/ModularCurve/X1.lean:15893`; the file had **10391 lines**. A `Read` at that offset
returns "the file is shorter than the provided offset", and a `grep` for the target returns
NOTHING — which reads exactly like "this leaf does not exist / was renamed" and is the wrong
conclusion. Before believing any such absence:

    git merge-base --is-ancestor HEAD main && git rev-list --count HEAD..main   # 0 = current
    git merge --ff-only main                                                    # if behind

It is safe: the worktree is clean at dispatch and its branch is an ancestor of `main`, so this is
a fast-forward, never a merge. Do it FIRST, before reading anything.

**2. THEN CHECK `merger`, BECAUSE THE LOOP'S QUEUE AUDIT STRUCTURALLY CANNOT.** `queue1` records
its audit as `AUDITED: <main sha>`, and `flt-loop-fs.py`'s release-time audit computes
`open_leaves()` from the repo at `main`. That is correct by its own contract and it means the loop
**cannot see a leaf proven on `merger` and not yet released** — every such leaf is re-dispatched,
guaranteed, once per release window. This is the fifth invisibility class above, but under the
Python loop it is no longer a judgement call that a careful orchestrator might catch: it is
mechanical, and the only thing standing in front of it is the agent.

`exists_nonconstant_toAbelianScheme_of_notGeometricallyRational` was `sorry` on `main` and
**PROVEN on `merger`** (via `flt-lean-34`, merger commit `df076668`), by decomposition into two
new residues. One command would have found it, and it is the same command CLAUDE.md already
prescribes:

    git show merger:Fermat/FLT/ModularCurve/X1.lean | grep -n <your target>

**3. IF YOUR TARGET IS ALREADY DONE, DO NOT GO LEAF-SHOPPING ON `main` — THE FLEET IS SATURATED.**
Measured the same day: `flt-frontier.py` gave **320 direct leaves** and 112 live jobs named all but
**3** of them in a `TARGET:` line. All three turned out to be accounted for anyway — two were
already `queue2` targets, and the third
(`exists_globalFrobCharScalar_atPrime_of_coherentLevelScalar_finiteBase`) was **already proven on
the unmerged branch `flt-lean-101`** and re-cut there into a queued successor. **Unowned work on
`main` was empty**, and taking an owned leaf duplicates a live agent.

Note what the third one shows: a leaf can be simultaneously open on `main`, absent from every
live `TARGET:` line, and finished — and the evidence lived in the BODY of an unrelated queue
entry, not in any ownership record. So grep `queue1`/`queue2` in FULL, not just their `TARGET:`
lines, before concluding anything is free.

The work that IS unowned is the **residues cut on `merger` since the last release** — new leaves
nobody can be dispatched at, because they do not exist on `main`. Those belong in your `queue`,
written as full task prompts. That is the highest-value output an agent with a finished target
has, and it is invisible to everyone else by construction.

**Do NOT re-prove the target on `main` "so the branch carries it".** `merger` already has it; a
second proof of the same theorem is a name collision the merge worker must resolve by discarding
one, which is a choice that belongs to an author, not a merge.

## A DECLINED DECOMPOSITION IS A STANDING TASK — the reason it was declined goes stale

(2026-07-30, `flt-lean-203`.) `nonempty_fullTranslationDatum_two`'s docstring contained a
paragraph headed **"THE DECOMPOSITION THAT WOULD PAY FOR ITSELF, and it is uniform in `q`"**,
naming the exact cut that merges it with `nonempty_preTranslationDatum_three_of_intCoeff_pos`,
and ending: *"That cut is NOT made here only because
`exists_potentiallyGoodModel_of_jIntegral_three` has a live owner and restructuring it under
them would cost a merge conflict for no mathematical gain."*

The mathematics in that paragraph was right and the coordination reason was **two days stale**.
Making the cut took one 60-line proven bridge
(`nonempty_translationDatum_of_full_of_ne_two`: in residue characteristic `q ≠ 2`, `2` is a
unit of `A`, so `ha₁`/`ha₃` give `u⁻¹s, u⁻³t ∈ A` and the three `s`/`t`-corrections
`u⁻²s²`, `u⁻⁴(2st)`, `u⁻⁶t²` are products of those) and turned **two open leaves into one**,
with no signature change anywhere.

So: **when a docstring names a decomposition and declines it for a COORDINATION reason —
"has a live owner", "would conflict with", "is owned elsewhere" — that is a queued task, not
a closed axis.** Re-check the reason; ownership in this fleet turns over in hours. Distinguish
it from a decline for a MATHEMATICAL reason, which does not go stale: the same file's
**"AXIS SEARCHED AND CLOSED: `(ψ, r)` MUST STAY IN ONE EXISTENTIAL"** on
`exists_fundamentalCharacter_of_semistabilityDefect` comes with an explicit counterexample
(`N = 29`, `e = 4`, `ψ' = ψ_L^15`) and should be believed.

Corollary for anyone tempted by the same merge elsewhere: **two per-prime leaves whose
docstrings state the SAME residual obstruction are one leaf.** Both of these ended with "THE
ONE REMAINING GAP IS ... residue degree `1`", written out twice over two different datum
structures. Grep for repeated obstruction sentences across sibling leaves before proving
anything.

## Verifying a BLOCK MOVE inside a file: sort both versions and diff

Relocating a declaration to satisfy Lean's define-before-use order is a common repair, and a
hand-retyped 100-line block can be silently corrupted in a docstring where nothing will ever
catch it. The check costs two commands and is exact:

    git show HEAD:<file> | sort > /tmp/old.txt
    sort <file>          > /tmp/new.txt
    diff -q /tmp/old.txt /tmp/new.txt      # identical multiset => the move was byte-exact

Any output means content changed as well as moved, which for a *pure* relocation is a defect.
Do the move programmatically (slice the line list, reinsert) rather than by retyping; that is
the case the "prefer Write/Edit" rule exempts as capability rather than convenience, and this
diff is what makes it auditable. Watch the blank lines at both the source and destination
seams — the multiset check catches a doubled blank line too.

## `simpa using h` can normalise the HYPOTHESIS to `True` and still fail

Symptom, and it reads as nonsense: `Type mismatch: After simplification, term h has type True
but is expected to have type <the goal>`. It means simp PROVED `h`'s statement while leaving
the goal unproved — which sounds impossible, since it is simping both.

It happens when a simp lemma rewrites a TYPE INDEX and thereby unlocks an instance for one
side only. Concrete instance (`MazurTorsion.lean`, `N = 1` branch of
`exists_weilPairing_mu_nondeg_of_coprime`): `h : ((1 : ℕ) : ℤ) • ↑x = 0` where
`x : ↥(E.nTorsion 1)`. Normalising `((1:ℕ):ℤ)` to `1` lets `Submodule.torsionBy_one` rewrite
the submodule to `⊥`, whose carrier is a `Subsingleton`, so `eq_iff_true_of_subsingleton`
closes `h`. In the GOAL the same term sits under the `nTorsion` abbrev, which blocks that
rewrite, so the goal only reaches `x = 0`.

Fix: replace `simpa` with `simp only [<the two lemmas you actually want>] at h` plus an
explicit `exact`. General rule — when a `simpa` fails with `has type True`, the problem is
that simp is doing MORE on one side, so name the rewrites instead of widening them.

## Run the `merger` check as step ZERO, not after the proof is built

(flt-lean-250, 2026-07-31.) Dispatched at `exists_hilbertClassField_artinIso` and
`exists_surjective_aut_classGroupQuotient`, I read the file, designed a decomposition, and
proved four of its pieces in Lean — *then* ran

    git show merger:<the file> | grep -n <the target name>

and found both targets already PROVEN on `merger`, in a strictly stronger form, over exactly
the decomposition I had just re-derived (an existence-theorem leaf, the Artin iso recovered by
counting, tower-functoriality of the Frobenius, and transfer of `relNormClassSubgroup` along a
`K`-algebra iso). The check is the one this file already prescribes for the release window; it
cost nothing and it worked. It was simply run too late. **Run it, for every declaration a task
prompt names, BEFORE reading the file.** Task prompts are generated from `main`, and `main` is
the frontier as of the last release.

**And when `merger`'s copy of the file is bigger than `main`'s, read `merger`'s.** The useful
output is not only "already proven" but "already DECOMPOSED": the frontier has moved to names
that only that branch knows. Here the sole remaining leaf,
`exists_unramifiedAbelian_card_classGroup_le_finrank`, **does not exist on `main` at all** — so
it emits no `declaration uses 'sorry'` warning in any build of `main`, no source scan can see
it, no ownership record names it, and a queue audit run against `main` would DELETE a task
naming it. A decomposition performed on an unmerged branch is a *sixth* way for open work to be
invisible, and the only instrument that sees it is the merger's copy of the file.

Corollary for verification: checking out `merger`'s version of a file into your own worktree
and building it is cheap (one module, minutes) and tells the merge worker something it does not
otherwise know — that the branch is green, and the exact warning set it lands with.

## RUN THE `merger` CHECK AS YOUR FIRST ACTION, NOT AS TRIAGE AFTERWARDS

(2026-07-31, `flt-lean-233`, measured.) The FIFTH invisibility class above already gives the
command and already says `merger` is where the answer lives. This is about WHEN to run it.

I was dispatched at three leaves in `ArtinConductor.lean`. I read the file, derived a proof of the
first, and committed it green — and only then ran

    git show merger:Fermat/FLT/Deformations/RepresentationTheory/ArtinConductor.lean | grep -n <name>

which showed **two of the three already PROVEN on `merger` the previous day**, one of them by an
essentially identical argument found independently. The whole run's Lean output had to be reverted
as a rival cut. The check costs one command and five seconds; running it after the work instead of
before cost an agent-run.

So: **before reading the target declaration, grep `merger` for every leaf named in your prompt** —
all of them, not just the one you intend to start with. A queue task is audited against `main` at
release time, and `main` is the frontier as of the last release; a task written a day ago can name
leaves that were closed hours later. Two of three is not an unusual hit rate for a file under
active work.

And when the answer comes back "already proven", the honest deliverable is the DECLINE, made by
you: revert your payload, name your own commit sha so the rival proof stays recoverable, and say
which tiebreak decided it. Leaving both proofs for the merge worker is a guaranteed name collision
on a file it must resolve blind.

## A CUT-ANALYSIS SAYING A ROUTE "CANNOT BE AVOIDED" IS A HYPOTHESIS ABOUT A PROOF

(Same run, and the reason the leaf fell at all.) `mem_gp_one_of_dvd_smul_unif_sub` carried a
careful, signed analysis concluding it "CANNOT BE AVOIDED" without the monogenicity
`𝒪_L = 𝒪_0[unif]` plus Hensel: `δ_x(σ) := (σ•x − x)/unif mod 𝔪` is a DERIVATION in `x`, so it is
"determined by its value on a ring GENERATOR, and nothing weaker". The analysis was right about the
derivation and right about the two substitute routes it examined (both re-verified dead). It was
wrong about the conclusion, and the counter-proof is forty lines.

The move that dissolves it is worth naming, because it generalises: **attack a `∀ x` by CASES on
the element, not by a normal form for it.** Here `mem_gp`'s quantifier splits as unit / non-unit;
non-units are `unif · y` by `unif_spec`, and a UNIT is soft because `R^×` is, modulo `𝔪`, torsion of
order prime to `p` — the residue field of a finite level is FINITE. A derivation is determined on a
generating set, but the generating set may be `{unif} ∪ R^×` rather than `{unif}`, and then no
generator theory is needed at all.

Two agents a day apart found exactly this proof, both against the docstring's own "impossible".
So the standing rule: **a cut-analysis records which routes were tried, and that is all it records.**
Read it for the dead ends it certifies — those are real and save time — and re-derive the negative
conclusion yourself. The same applies to any "needs new theory" or "ATOMIC" verdict in this tree.

## "TENSOR COMMUTES WITH FILTERED COLIMITS" IS ALMOST NEVER THE STEP YOU HAVE TO FORMALISE

(2026-07-31, from closing Half A of [Stacks 00R6],
`exists_le_idealTensorComparison_eq_zero_of_isNoetherianFlatDescentSystem`.)

Several leaves in this development are cut with a docstring that ends "…tensor products
commute with filtered colimits, so the element already dies at a finite stage". Taken
literally that sentence is a whole module-theoretic colimit development — the colimit of
`↥(𝔪 C_j) ⊗_{C_j} D_j` over `j`, built from nothing but the ring-level `surj`/`sep`
fields — and `Ring.DirectLimit` is deliberately banned here, so there is nothing to build
it out of. A prover who takes it literally is looking at hundreds of lines before the
leaf's own argument starts.

**The substitute is mathlib's EQUATIONAL CRITERION FOR FLATNESS**,
`Module.Flat.isTrivialRelation_of_sum_smul_eq_zero` (`@[stacks 00HK]`, in
`Mathlib/RingTheory/Flat/EquationalCriterion.lean`). It converts flatness at the COLIMIT
into a **finite amount of data**: from `∑_k a_k x_k = 0` it returns `b_{kp}` and `y_p`
with `x_k = ∑_p b_{kp} y_p` and `∑_k a_k b_{kp} = 0`. Finite data is exactly what
`c_surj`/`d_surj`/`c_sep`/`d_sep`/`directed` descend, one element and one equation at a
time. No colimit of modules is ever constructed; only ring elements and ring equations
are ever moved. The whole colimit step came to ~90 lines.

Two things that fall out and generalise:

- **`exists_ub_finset_of_directed` / `exists_ub_fintype_of_directed`** (added to
  `AbelianSchemeIsogeny.lean`): pairwise directedness upgraded to finite sets and to
  fintype-indexed families, stated for a bare `le : Λ → Λ → Prop` with reflexivity,
  transitivity and directedness as arguments. Every descent argument in this development
  needs one, and there was none — check for them before writing a `Finset.induction` by
  hand. They apply verbatim to `NoetherianLocalBaseSystem` and `NoetherianLocalExtSystem`
  as well as to `IsNoetherianFlatDescentSystem`.

- **`M ⊗[R] S` is NOT an `S`-module in mathlib.** `TensorProduct.leftModule` acts on the
  LEFT factor; there is no right-hand counterpart, so a docstring step of the form "…so
  its submodule is f.g. because `D` is Noetherian", where the submodule sits inside
  `↥𝔪 ⊗[C] D`, is *not directly expressible*. The fix that worked, and it is reusable:
  present the tensor by TUPLES — if `I = (a_1,…,a_r)` then every element of `↥I ⊗[C] M`
  is `∑_k ⟨a_k⟩ ⊗ₜ x_k` (`exists_repr_tmul_of_span_range`) — and run the finite-generation
  argument on the kernel of an honestly `D`-linear map `D^r → D` instead. Do not go
  looking for `TensorProduct.rightModule`; it is not there.

## A DOCSTRING'S CLAIM ABOUT THE IMPORT GRAPH IS A HYPOTHESIS, AND A FALSE ONE PICKS THE EXPENSIVE PLAN

(2026-07-31.) This file already treats a stale `(sorry leaf)` label as a phantom-work source.
The same failure at MODULE scale is worse, because it does not produce a wasted dispatch — it
produces a wasted *architecture*, and the agent that follows it never learns the plan was
avoidable.

`ProjectiveModelOverField.lean`'s header stated, twice, that "`EllipticScheme.lean` is
DOWNSTREAM of `MoretBailly.lean` and so cannot be imported there". Both closures were walked
at `7080929d`, with no module missing from either walk: `EllipticScheme` reaches 56 `Fermat.*`
modules and does not contain `MoretBailly`; `MoretBailly` reaches 170 and does not contain
`EllipticScheme`. **They are INCOMPARABLE.** So the import is available in either direction —
`MoretBailly` importing `EllipticScheme` adds 7 modules and no cycle.

What the false claim was buying: `exists_projGroupLawOverField_geomFibreAddEquiv` wants the ℚ
group-law development at a general base, and its docstring accordingly plans a REWRITE of an
11 832-line chart interface inside a 51 000-line module — ~20 minutes of elaboration per
iteration. The reachable plan is to generalise `ProjCoords`/`exists_projAdd` IN PLACE in
`EllipticScheme.lean`, recover ℚ as `(F := ℚ)`, and import. Nobody had checked, because the
header said not to.

**So before planning around "module A cannot see module B", walk the closures.** It is ten
lines and seconds of runtime:

    def imports(m):  # m.replace('.','/') + '.lean', regex ^(public )?import (Fermat[\w.]*)$
    def closure(m):  # BFS; ASSERT every visited module's file EXISTS — a silent
                     # FileNotFoundError truncates the walk and manufactures "incomparable"

The assertion matters more than the BFS: a swallowed missing file is exactly how this check
produces the answer you were hoping for.

Corollary, and the reason to fix the docstring rather than just route around it: an import-graph
claim is *cheap to verify and expensive to believe*, so it should never be carried as prose
without a stamp. Write the commit it was measured at, the way frontier counts are stamped.

## A LEAF'S OWN ROUTE NOTE IS SCOPED TO WHERE THE LEAF SITS — check declaration ORDER before believing "must be written here"

(2026-07-31, `exists_stepanovJetLinearForms` in `MoretBailly.lean`.) The leaf's docstring said
the weighted-degree bookkeeping "has to be written here". It does not: `stepanovTotalFilt` and
the whole `StepanovFilt` calculus — `mem_add/_sub/_mul/_sum/_prod/_det`, `lift`, and even
division by a monic `F` with the filtration preserved (`stepanov_exists_wd_rem`) — already
existed, **1600 lines BELOW the leaf in the same file**, together with the entire
`stepanovDerivX`/`stepanovJet` API the leaf's four proof steps run on (another 2100 lines down,
including a fully proven `stepanov_jet_dvd_core`).

So the leaf was not missing machinery; it was **positioned above it**. Every "MISSING AT THIS
PIN" and "has to be written here" claim in a route note is implicitly *as of this line number*,
and line numbers move under merges while the prose does not. A `grep` that finds the name and
stops has confirmed existence, not USABILITY.

The check is one command and belongs in every scoping pass, before any Lean is written:

    grep -n '<the machinery>\|<your leaf>' <file>     # compare the LINE NUMBERS

If the machinery is below, the first move is a HOIST, not a proof — and the hoist is its own
verified step, because a several-hundred-line move in a file with concurrent editors is exactly
the merge shape the class-7 note above warns about. Budget it separately and say so in the
report; do not start the mathematics on top of an unhoisted base.

Corollary in the other direction, from the same day: the route note for
`exists_irreducible_hypersurface_fractionRing_ringEquiv_rat` predicted its last step would be
"several lemmas, not one", and it was four lines — because `Module.Finite.of_isLocalization` is
registered in mathlib as an INSTANCE at exactly the pair wanted. **Route notes are estimates made
without the compiler. Re-price both directions before trusting one.**

### Two mathlib techniques from that proof, both reusable in this development

- **Use `IsField` as a PROP; never install `IsField.toField`.** Adding a `Field` instance to a
  ring that already has a `CommRing` from elsewhere (a `Localization`, a quotient) puts a second
  ring structure in scope and makes every later instance unify through structure eta.
  `IsField.mul_inv_cancel` is a plain existence statement and is usually all that is wanted.
- **To show a localisation at a SMALL submonoid is already the whole fraction ring**, do not
  prove it is a field and transport: use `IsLocalization.isLocalization_of_is_exists_mul_mem`,
  whose hypothesis is `∀ x ∈ S⁰, ∃ m, m * x ∈ M`. Combining `IsField.mul_inv_cancel` with
  `IsLocalization.surj` produces that `m` directly, and the result is `IsFractionRing S
  (Localization M)` with no field structure anywhere in the proof.

## A FALSITY AUDIT THAT SEARCHES ONE SUB-FAMILY PROVES NOTHING — and "hypothesis ⟺ conclusion" is the tell

(2026-07-31.) `IsShortExact.exists_lift_ker_le_span_cartierDual` in
`Fermat/FLT/Mathlib/RingTheory/HopfAlgebra/ShortExact.lean` carried **two** dated FALSITY AUDITS,
both careful, both correct, both concluding "searched, not refuted". They had also both noticed
the same odd thing and written it down as *weak evidence for* the leaf:

> "the hypothesis keeps turning out to be equivalent to the conclusion rather than merely
> implying it, which is why no counterexample has been produced."

**That coincidence was the refutation, not evidence against one.** When a hypothesis you did not
choose keeps coming out *exactly* equivalent to the conclusion across independent-looking
examples, the examples are not independent — you have picked a sub-family in which some identity
forces them together. Find the identity, then vary whatever it constrains.

Here the audits had searched `G' = μ_p`, `G'' = ℤ/p` — **the two groups always of the same
order**. In that shape the one non-trivial fibre of `G → G''` occurs exactly once, so
`Module.Free R O(G)` and the conclusion are literally the same condition on `[L] ∈ Pic(R)`.
Widening the quotient by one factor of `p` (`G'' = ℤ/p²`) makes the bad fibre occur `p` times,
and `p·[L] = 0` makes the hypothesis VACUOUS while the conclusion is untouched. With `p = 2`,
`R = ℤ[√-5]`, `Pic = ℤ/2`, the counterexample is three lines — **over a Dedekind base, which one
of the two audits had explicitly ruled out** ("a counterexample must have Krull dimension ≥ 2").
That ruling-out was a true statement about the sub-family read as a statement about the leaf.

Three transferable rules:

- **An audit's scope is part of its verdict.** Record which family was searched *in the verdict
  sentence*, not just in the working. "No counterexample" is not a result; "no counterexample
  with `ord G'' = ord G'`" is.
- **Vary the parameter you did not think of as a parameter.** Both audits varied the base ring
  (dimension, `Pic`, `K₀`, characteristic) and neither varied the *relative size* of the two
  ends. The unvaried parameter is where the counterexample lives, essentially by construction.
- **Multiplicity kills K-theoretic obstructions.** If a hypothesis says "`m` copies of `P` are
  free" and the conclusion says "`P` is free", they are the same statement only when `m` is prime
  to the order of `[P]` in `K̃₀`. Check that arithmetic before believing a hypothesis is
  load-bearing.

And the repair worth copying: when a leaf is refuted, look for the hypothesis the *real* consumer
already has. Here the whole chain (five declarations) gained `[IsLocalRing R]`, which is true at
the only intended base (`𝒪ᵖᵥ`), makes `CartierDual R A'` semilocal, and turns the remaining
mathematics from "global triviality of a torsor" into mathlib's
`Module.free_of_flat_of_finrank_eq`. Cost: zero, because a grep showed every mention of the
chain outside its own file was a docstring. **Grep for term-level consumers before assuming a
hypothesis cannot be added; in this development most of the tree is not consumed yet.**

**And the refutation paid for itself immediately, which is the general pattern.** Once the false
GLOBAL statement was replaced by the true LOCAL one, the leaf stopped being atomic: it fell in one
sitting to `flat + constant fibre rank` (a new, strictly smaller, Zariski-local sorry) plus two
proven steps — `finite_maximalSpectrum_of_isLocalRing_of_module_finite` (new, ~35 lines, pure
commutative algebra) and mathlib's `Module.nonempty_basis_of_flat_of_finrank_eq`. A leaf that has
resisted every cut for days is worth suspecting of being false *precisely because* falsity is what
makes it uncuttable: no cut can be found, because there is nothing true underneath to cut into.
"Atomic on every axis tried" is evidence about the statement, not only about the prover.

## "FINITE FLAT" OVER A FIELD IS EMPTY — and the leaf it nearly made false

(2026-07-31, caught before it was written down.) A leaf of the shape *"a closed
subscheme of a `ℚ̄`-scheme is determined by its `ℚ̄`-points"* is the residue of at
least three separate nodes in `ModularCurve/X0.lean`. The natural hypotheses to
copy across from the object at hand — a `CyclicSubgroupOfOrder`, whose fields are
`isClosedImmersion`, `isFinite`, `flat` — give a statement that is **FALSE**:

* over a FIELD every module is flat, so `IsFinite + Flat` says only "finite", and
  `A = 𝔸¹`, `C₁ = ` the origin, `C₂ = Spec ℚ̄[ε]` are two finite flat closed
  subschemes with the same `ℚ̄`-points (the only `Spec ℚ̄ ⟶ Spec ℚ̄[ε]` kills `ε`)
  that are not isomorphic.

Reducedness here does **not** come from flatness; it comes from Cartier's theorem,
which needs the GROUP structure — in this tree that is
`CyclicSubgroupOfOrder.etale_of_specQBase`, and the hypothesis to state is
`AlgebraicGeometry.Etale`, not `Flat`. Two further hypotheses are equally
load-bearing and equally easy to drop: `IsAlgClosed` (over `ℚ`,
`Spec ℚ[x]/(x²+1)` and `∅` have the same `ℚ`-points) and `IsClosedImmersion`
(`Spec K ⊔ Spec K` onto one point versus `Spec K`).

General form, and it is the cheap habit: **when a leaf says "determined by its
points", write down what happens at a NON-REDUCED subscheme, at a NON-CLOSED
point, and over a NON-ALGEBRAICALLY-CLOSED base, before you write the binders.**
Each of the three has a two-line counterexample, and each survives review, because
the hypotheses were copied verbatim from a structure where they were sufficient
*in combination with a field the leaf no longer mentions*.

## THE SAME MISSING LEMMA, RECORDED THREE TIMES UNDER THREE NAMES

(2026-07-31.) Before cutting a bespoke leaf, grep the file for the gap you are
about to name. `X0.lean` recorded one statement — the one above — in three
places under three phrasings: as item 3 of
`nonempty_isBaseChangeOf_of_isIso_isWeierstrassModel`'s itemisation ("both are
finite étale, hence reduced, hence determined by their geometric points"), as the
"WHAT REMAINS OF (b)" paragraph of
`exists_gamma0Datum_specQ_isBaseChangeOf_liesIn_of_weierstrassQForm` ("the passage
from `ℚ̄`-points to closed subschemes"), and as the SCOPE paragraph of
`liesIn_spanScheme_iff_mem_zmultiples` ("the new conjunct is about `ℚ̄`-POINTS and
NOT about `T`-points"). None of the three names the other two.

Cutting it ONCE, in the generality that covers all three, turns a 1-leaf-for-2
trade into a 1-leaf-for-2 where one of the two is already owed elsewhere — which
is the difference between adding work and disclosing it. The tell is verbal
rather than structural, so it takes a grep for the *mathematical content* ("points
determine", "reduced", "subscheme"), not for a declaration name.

## A ROUTE AUDIT NEVER CHECKS DECLARATION ORDER — and that is a whole blocking axis

(2026-07-31, flt-lean-210, found by trying to walk a route the file certified as open.)

Every audit shape this project writes — ROUTE AUDIT, ATOMICITY AUDIT, CUT-OBSTRUCTION AUDIT —
reasons about *mathematics* and about *what exists in the tree*. None of them reasons about
**where in the file it exists**, and in a 31k-line module that is a live, independent way for a
leaf to be unattackable.

`exists_framedGaloisRep_descent_hilbertTraceSubring_of_isWeaklyUniversal`
(`HardlyRamified/HilbertModularity.lean`) carried a section headed "ROUTE OBSTRUCTION FOUND —
REPAIRED. THE BINDER IS NOW ON THIS NODE", ending "**The route described below is therefore
AVAILABLE, and a prover dispatched at this leaf now has one**", and the consumer's summary agreed:
"The route is available; the leaf is attackable." The binder repair was real and the mathematics
was right. **Every declaration the route spends sits ~1000–2000 lines BELOW the leaf**, so Lean
forbids the appeal — and restating any of them above it would duplicate a live declaration, which
is worse. The docstring even records the block correctly for ONE of those declarations
(`exists_framedGaloisRep_hilbertTraceSubring`, "blocked mechanically: both live BELOW this point")
without noticing it applies to the whole route.

So: **before certifying a route as available, `grep -n` the line number of every declaration it
spends and compare it with the leaf's own.** It costs one command. And when you record a route,
record the line numbers, because they are the part of an audit that a reader cannot re-derive from
the mathematics.

Two corollaries:

- **The repair is a RELOCATION, and relocations are the worst shape for a merge** (a ~950-line
  block move conflicts with any concurrent edit inside it). So measure it, write the recipe into
  the docstring, and queue it as its OWN commit touching nothing else — do not attempt it while
  the file has another owner. The measurement that makes it safe is one grep: the names declared
  in the moved block, searched for *in code* across the range it moves over.
- **"Blocked, it is another module's region" is the same error one level up, and it is usually
  wrong about CUTS.** The same file declined its own next cut on the ground that the repair lives
  in `Modularity/MoretBailly.lean`. Proving the sub-leaves does live there; **stating** them cost
  nothing, because that module is a `public import` and every name in their signatures was already
  in scope. The cut was taken from the consumer's file, no other file was touched, and it exposed
  a second obstruction nobody had recorded. This is CLAUDE.md's "STATING a theory is not PROVING
  it" in its commonest disguise: an obstruction to the PROOF written down as an obstruction to the
  CUT.

## A loop-dispatched worktree can be HUNDREDS of commits stale, and `lake` is not on `PATH`

(2026-07-31, `flt-lean-235`, cost ~10 minutes but would have cost a whole run had it gone
unnoticed.) Two facts about the state a prover agent actually wakes up in, neither of which is
stated in the task prompt:

- **`lake`/`lean`/`elan` are NOT on the default `PATH`** of a fleet worker's shell. The first
  command run was `lake build …`, which returned `lake: command not found` and **exit 127** — a
  build log that looks like a build failure. Every shell needs
  `export PATH="$HOME/.elan/bin:$PATH"` prepended; it does not persist between Bash calls.
- **The worktree may not be at `main`.** `flt-lean-235` was dispatched sitting on an old `merger`
  commit, **704 commits behind `main`**, with a `.lake/build` to match. The task prompt's line
  numbers were `main`'s, so every one of them pointed at unrelated code, and a repo-wide grep for
  the three target declarations returned **nothing at all** — which reads exactly like "these
  leaves were deleted/renamed since the queue was written", the diagnosis that ends a run in a
  `to_merger` note instead of a proof.

So the first two commands of any prover run, before reading the target file:

    export PATH="$HOME/.elan/bin:$PATH"
    git merge-base --is-ancestor HEAD main && git merge --ff-only main

Then seed artifacts rather than building mathlib: `~/.flt-release-lake/sha` names the commit the
snapshot was built at; if `git log --name-only <sha>..main` touches no `.lean` file the snapshot is
**exactly current** for Lean, and

    rsync -a --delete ~/.flt-release-lake/build/ .lake/build/

turns a 704-commit-stale tree into a green one. `lake build <Module>` then confirmed
`Build completed successfully (5590 jobs)` in a couple of minutes with nothing to elaborate.

Corollary for triage: **"the declaration does not exist anywhere in the tree" is a
wrong-checkout symptom before it is a rename symptom.** Check `git log --oneline -1 main` against
`git log --oneline -1` before believing a grep that returns zero.

## THE `sorry`-WARNING SET IS THE EXACTLY-WRONG EVIDENCE IN THE RELEASE WINDOW

(2026-07-31, `flt-lean-235`. The release-window section above already prescribes the check that
would have caught this; this is a note on WHY an agent following the rest of this file skips it.)

Three leaves were dispatched. I fast-forwarded to `main`, ran `lake build` on the module, and read
the `declaration uses 'sorry'` warning set: all three target line numbers were in it — `42221`,
`53124`, `53285` — matching the task prompt exactly. That is the compiler speaking, and this file
says in bold that **the compiler is the only reliable ownership evidence**. So I started work.

**All three were already PROVEN on `merger`**, over a new file
`Fermat/FLT/NumberField/CyclotomicIdealSymbol.lean` that does not exist on `main` at all. I spent
the run rebuilding a strictly weaker version of one of them, and it had to be thrown away.

The two rules are in tension and the tension is not marked:

- *"Prefer the compiler to any prose claim about what is still open"* is about **`main` being
  wrong in the direction of claiming a leaf is CLOSED** — a stale docstring, a commit message, an
  agent's report.
- The **release window** is `main` being wrong in the other direction: a leaf that is closed on an
  unmerged branch is still `sorry` on `main`, so the warning set lists it, **truthfully and
  uselessly**. A green build cannot see work that has not merged, and by construction the work you
  are being dispatched at is the work most likely to be in flight.

So: **a build tells you the state of the tree you built, and the tree you built is `main`.** For
"is this leaf still open" that is not an answer. Run, before the first edit and before trusting any
line number:

    git show merger:<the file> | grep -n '^theorem <name>'   # then read the body: `sorry` or not?

and check `~/.flt-loop/queue2` / `~/.flt-merge-batch` for branches touching the same file. One
command, ten seconds, ahead of a multi-hour build.

Two smaller traps met on the way, both worth avoiding:

- **Do not `awk` for `/^theorem |^\/--/` to find where a declaration's body ends.** Statements in
  this development run to a hundred lines and the naive scan reports "not sorry" for a sorried leaf
  and vice versa. Locate the `^theorem <name>` line, then print forward and READ it.
- **A superseded branch is worse than an empty one.** My version proved the same theorem over ONE
  large leaf; `merger`'s proves it over FIVE small ones plus a reusable ideal-symbol lemma. Merging
  mine would have cost a conflict resolution and risked replacing the better proof with the worse.
  When your work is superseded rather than partial, **revert the Lean change** and report it —
  the value left is the report, not the code.

## NARROW A TERMINAL LEAF BY SPLITTING ON WHAT THE PROVEN BRANCH ACTUALLY CONSUMES

(2026-07-31, `Interface.lean`'s Serre local criterion.) When a leaf sits behind a
`by_cases`, the split condition is usually the *natural-language* hypothesis somebody
had in mind ("the inertia image is commutative"), not the thing the proven branch's
proof actually uses. Read the proven branch top to bottom and find where the positive
hypothesis is consumed. If it is consumed once, through a **one-directional
implication**, then **the conclusion of that implication is a strictly weaker splitting
condition** — and re-splitting there moves a real class of cases out of the sorry leaf
for zero mathematics.

The instance: the abelian branch took
`∀ σ τ ∈ localInertiaGroup, Commute (σ₀.toLocal σ) (σ₀.toLocal τ)` and used it in
exactly one step — fed through `hfix : σ₀.toLocal σ = 1 → σ r = r` to get
"inertia COMMUTATORS FIX `r`". `hfix` is one-way: `r` can be fixed by far more than
`ker (σ₀.toLocal)`. Splitting on the commutator condition instead moved the whole class
"`r` lies in the maximal subextension abelian over the maximal unramified one" into the
PROVEN branch, while `ℚ₃(σ₀)` itself stays nonabelian. Separating witness, which is what
makes this a cut rather than a rewording: `Gal ≅ S₃` très ramifiée, `r ∈ ℚ₃(μ₃)` — the
commutator `A₃` fixes `r`, so the new condition holds and the old one fails.

Three things this costs, all of which must be in the same commit:

- **The sorry count does not move.** A narrowing closes nothing. Say so plainly; a
  reviewer counting warnings will otherwise read the commit as no-op.
- **The renamed leaf's earlier FALSITY AUDIT is VOID.** Re-run it. Here it passed with
  no mathematics — only hypotheses were strengthened, so the new statement is *implied
  by* the old, and any counterexample refutes both. That argument is short and it is
  the one to look for first when a restatement only strengthens hypotheses.
- **The old branch's theorem can become FREE-FLOATING.** Rewiring the `by_cases` removes
  its only consumer. Either keep it consumed (a subsumed outer branch, two lines, with a
  comment saying why) or delete it in the same edit — do not merely bypass it.

And check for a *further* widening before stopping, because the answer is often no and
recording that saves the next owner the search: here the descent lemma consumes `hcomm`
only to build `(σ τ) r = (τ σ) r`, which looks weaker and is provably equivalent, since
the cyclotomic character kills commutators and so the commutator fixes `ζ^a · r` iff it
fixes `r`. That condition is optimal for that machinery; any further widening has to
come from a different tool.

## A NUMERICAL FORMULA CAN DEGENERATE — check the dimension before calling a leaf ATOMIC

(2026-07-31, `ringKrullDim_stalk_eq_zero_of_mono_of_curve_over_field`.) The leaf's own
docstring named its content correctly — "THE DIMENSION FORMULA FOR FINITE-TYPE `K`-SCHEMES,
and that is the whole of it", `dim 𝒪_{X,x} + trdeg_K κ(x) = dim X` — and concluded that
neither `trdeg` nor the formula "is in the pin as a statement about stalks, which is why
this is a leaf and not a step". Both clauses are true. The conclusion drawn from them was
still too pessimistic, and the reason generalises.

**In relative dimension `1` every term of that formula is `0` or `1`, so the EQUATION
degenerates to a DICHOTOMY**: `ringKrullDim 𝒪_{X,x} = 0` iff `κ(x)` is transcendental over
`K`. A dichotomy between two Props needs no arithmetic and no `trdeg` — it is a statement
about `Algebra.IsAlgebraic` alone, and `Algebra.IsAlgebraic` composes (`IsAlgebraic.trans`)
exactly where `trdeg` would have needed additivity. The whole development came to ~250
lines. So before accepting "this needs theory `T`", ask whether the instance of `T` you
actually need is a degenerate one; the general theory being absent from the pin says
nothing about the special case.

Two reusable facts found on the way, both worth knowing before attacking anything about
smooth curves over a field:

* **`Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial` is the whole
  toolkit.** It factors a smooth chart as `K → K[X₁,…,Xₙ] → A` with the second map ÉTALE,
  and étale gives `Module.Flat` (hence `Algebra.HasGoingDown`) and
  `Algebra.QuasiFinite` (hence `Algebra.QuasiFinite.eq_of_le_of_under_eq`: two primes with
  the same contraction, one below the other, are equal). Minimality of a prime and the
  vanishing of its contraction are then each other, in one line per direction. The same
  lemma is what closed `isDiscreteValuationRing_stalk_of_smoothOfRelativeDimension_one` in
  `CurveExtension.lean` after three audits had declared "smooth ⟹ regular is absent from
  the pin".
* **`Mathlib/AlgebraicGeometry/Morphisms/FormallyUnramified.lean` carries an instance
  `Algebra.IsSeparable (Y.residueField (f x)) (X.residueField x)`** for `f` formally
  unramified and locally of finite type. So "the residue extension along a quasi-finite map
  is finite/algebraic" is `inferInstance`, not a sub-leaf. `Mono f` supplies
  `FormallyUnramified f` through the diagonal.

**AND THE ONE PLACE THE BOOKKEEPING IS NOT FREE: a `K`-algebra structure on `κ(x)` must be
CANONICAL, never a chart's.** A statement comparing an invariant at `x : X` and at
`u x : J` over a common base `Spec K` needs `IsScalarTower K κ(u x) κ(x)`, and that holds
only if both `K`-structures come from the STRUCTURE MORPHISMS
(`strX.residueFieldMap`, `jstr.residueFieldMap`), where `hu : u ≫ jstr = strX` can be fed
in through `Scheme.Γevaluation_naturality` and `Scheme.Hom.comp_appTop`. A chart-derived
`Algebra K ↥(X.residueField x)` is a different term of the same type, and every transitivity
lemma silently fails to apply to it. The fix is to define the canonical one as a
`@[reducible] def` (not an instance — it depends on data), state the chart lemma with
`letI := that`, and discharge the mismatch once with `Algebra.algebra_ext`. Budget for that
step: it was a third of the proof.

## A "MISSING THEORY" VERDICT WRITTEN BY SOMEONE WHO COULD NOT IMPORT IT IS AN IMPORT FACT IN DISGUISE

(2026-07-31, `flt-lean-83`, `exists_frickeSlash_eq_smul_of_isNewEigenformAt`.) The leaf's
docstring said, in the file's usual careful style, that the proof "needs a genuinely missing
theory: Hecke operators as OPERATORS on `S₂(Γ₀(M))` … the commutation `W_M T_n = T_n W_M` …
and multiplicity one for the newspace", and backed it with a grep over `Fermat/`, the mathlib
pin and `~/cs/FLT/` that "returns no operator-level Hecke theory anywhere on this pin".

Every piece of that theory is PROVEN in this tree, in `Modularity/Interface.lean`:
`heckeTransform_slash_atkinLehnerRep` (the double-coset commutation),
`heckeOp_comm_atkinLehnerOp`, `heckeOp_apply_eq_smul_of_isWeightTwoEigenform` (the exact step
declared impossible — a coefficient-recurrence eigenform IS an operator eigenvector),
`exists_smul_of_heckeOp_eq_smul_of_not_dvd_level` (strong multiplicity one, in the leaf's own
conclusion shape) and the assembled `atkinLehnerOp_apply_eq_neg_qCoeff_smul`. Five
declarations, zero `sorry` among them.

**The mechanism, and it is systematic rather than a slip.** `Interface.lean` `public import`s
`ModularCurve/X0.lean`, so from inside `X0.lean` none of those names resolves, nothing
completes them, and no `example` referencing one will elaborate. An author working there
experiences the material as *absent*, and writes that down as a fact about the pin. The grep
that "confirms" it is then run with a mental filter for what could be used here, which is
exactly the filter that excludes the answer. Same shape as the self-certifying grep, but the
filter is the module graph rather than a spelling.

Two consequences worth acting on:

* **Run absence greps with NO import filter, then check reachability separately.** "Does it
  exist" and "may I name it here" are different questions and must be answered by different
  commands. Merging them turns a 200-line hoist into a "subtree to be built".
* **A cost-wall verdict in a file that sits UPSTREAM of the project's big interface module is
  suspect by default.** `X0.lean` had recorded this same error once before, for `heckeOp`
  itself; the repair was the hoist into `Modularity/HeckeOperator.lean` (612 lines, verbatim,
  justified by a reference scan showing the block named nothing else in `Interface.lean`),
  and `X0.lean` now imports it. That precedent is the template, not a one-off — when a leaf
  in an upstream module reports missing modular-forms theory, look for it in
  `Interface.lean` and price the hoist before pricing the mathematics.
* **Then actually PRICE it, by computing the closure rather than reading the section
  headings.** The five declarations above look like a `qCoeff`-plus-`AtkinLehner` shortlist;
  their transitive closure inside `Interface.lean` is **204 declarations and ≈ 9 000
  non-comment lines**, because multiplicity one runs on the Petersson inner product and drags
  in a fundamental-domain measure-theory block, the degeneracy operators, the oldform
  subspace and the Sturm bound. "The theory exists" and "the hoist is cheap" are separate
  claims; the first was the correction here, the second would have been a second error.
  A closure of that size must be dispatched as its own task and must not race a concurrent
  editor of the same file.
* **Compute the closure of what you ACTUALLY need, not of the headline theorem.** Dropping
  the one declaration whose conclusion names the eigenvalue's VALUE
  (`atkinLehnerOp_apply_eq_neg_qCoeff_smul`) took the closure from 204 declarations
  containing one `sorry` to **193 declarations containing none** — because the leaf being
  closed says `∃ c` and never asks what `c` is. A closure computed from the theorem that
  looks like your goal will routinely be bigger and dirtier than the one your goal needs.

The residue after such a hoist is usually small and is where the real work is. Here it is one
leaf: this file's `IsNewEigenformAt` (the sequence is not a stabilization) against
`Interface`'s `eigensystem_minimal` (no smaller divisor level realizes the eigensystem). The
two carriers do NOT bridge definitionally, and the needed direction is Atkin–Lehner Thm 1 /
Diamond–Shurman Thm 5.8.3.

## THE CM SURVEY, DONE ONCE SO IT IS NOT REDONE: what this pin does and does not have

(2026-07-31, flt-lean-159, while working the `MazurCMForm` cluster in
`MazurTorsion.lean`.  Every line below was checked by `grep`/`ls` against
`.lake/packages/mathlib` at our pin, not recalled.)

Four leaves in this tree ask for complex multiplication in one form or another
(`minpoly_eq_of_isCMJInvariant`, `exists_isCMJInvariant_ne_of_not_equivalent`,
`nonempty_isCMByRamifiedMaximalOrder_geomPoint_mazurLevel`,
`Fermat.exists_cmEndomorphism_of_mem_isolatedCMJInvariants`).  Every one of them
is a *theory build*, and here is exactly which theory is missing, so the next
agent does not spend its first hour rediscovering it:

* **No lattices in `ℂ`, no analytic `j`-function, no uniformisation.**
  `Mathlib/NumberTheory/ModularForms/` has Eisenstein series, `Δ`, the `η`
  function and `q`-expansions — and no `j`, and nothing relating a lattice to an
  elliptic curve.  So Cox's route 3(a) is not "cite mathlib", it is "build the
  theory".
* **No class group of a NON-MAXIMAL order.**  `ClassGroup` in mathlib is for
  Dedekind domains; `ℤ[√−n]` of conductor `> 1` is not one.  The form class group
  and the Cox Theorem 7.7 isomorphism do not exist either.
* **No Hilbert/ring class polynomial, no ring class field.**
* The ALGEBRAIC route (Silverman *ATAEC* II, `E ↦ E/E[𝔞]`) is gated inside this
  tree rather than by mathlib: it needs `Ideal (End W)`, hence a `CommRing`
  instance on `End W`, and `WeierstrassCurve.End.mul_comm_charZero` is an OPEN
  LEAF; it also needs quotients by finite subgroups, which this tree lacks.

**And one trap that looks like it should be free and is not.**  Galois-STABILITY
of "`x` is a CM `j`-invariant" — `IsCMJInvariant n x → IsCMJInvariant n (σ x)` —
would narrow two of those leaves considerably (with it, "there are two distinct
CM `j`-invariants" collapses to "one of them is irrational").  It is NOT
available: **mathlib's `WeierstrassCurve.Affine.Point.map` maps between BASE
CHANGES of one curve `W'` over a fixed base ring, along an `F →ₐ[S] K`.**  It
does not transport a curve over `ℚ̄` along a ring automorphism of `ℚ̄` to the
different curve `W.map σ`.  That transport, and with it the transport of
`IsIsogeny` (whose `IsRationalMap` certificate is a polynomial identity in
`veluPointX`/`veluPointY`, so it does conjugate — the mathematics is easy, the
API is absent), is a real ~200-line build in `Isogeny.lean`.  Price it before
promising it.

**What IS free, and was harvested 2026-07-31**: over `ℚ̄/ℚ`, `∃ σ, σ x = y` and
`minpoly ℚ x = minpoly ℚ y` are interchangeable in one line —
`Normal.minpoly_eq_iff_mem_orbit` (`Mathlib/FieldTheory/Normal/Basic.lean`).
Any CM leaf phrased with a `Gal(ℚ̄/ℚ)`-orbit should be restated with minimal
polynomials, where the arithmetic is visible and the bookkeeping is gone.
