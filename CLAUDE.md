# Project Notes — flt-lean

This repository was split out of Deyao's dissertation repo on
2026-07-22 (`git subtree split --prefix=fermat`); the full commit
history of the formalization is preserved. The project root IS the
Lean package (formerly the `fermat/` subfolder).

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

And the standing one, which is what caught the rest: **the release build is not optional and its
first failure is not its last.** Fix, rebuild, repeat — FOUR rounds this release, and the reason is
structural rather than bad luck. **The errors are serialised behind each other by the import
graph**, so round *n* only reveals what round *n−1*'s failure was hiding: one interface change
(`IsSwanExponentAt` gaining a third clause) broke a consumer in its own module, found in round 1,
and a second consumer 79 000 lines away in another module from another branch, found only in round
4 after twenty minutes of elaboration. Budget three rounds minimum, and schedule nothing behind the
first green one.

## HOW TO CUT A LEAF YOU CANNOT PROVE: three moves that worked on three CM leaves in one run

(2026-07-31, `flt-lean-175`, on `BinaryQuadraticForm.lean`'s Heegner cluster.) An agent handed
three leaves each documented as "a project in its own right" — Weber's theorem, the modular
polynomial `Φ_N`, the first main theorem of complex multiplication — closed all three AS STATED
by recutting, adding zero net sorries across two of them. None of the three was proven. The
moves generalise, and each has a mechanical obligation you must discharge.

**1. MEASURE WHICH HYPOTHESIS EACH HALF NEEDS — the class-number hypothesis was on the wrong
half.** `natDegree_minpoly_weberAlpha_le` (`deg α ≤ 3`, `α = ζ₈⁻¹f₂(τ₀)²`) carried `hcl`
(`h(−p) = 1`). But the statement conflates a STRUCTURAL claim (`α ∈ ℚ(α⁴)` — Weber's descent)
with a NUMERICAL one (that degree is `3`, because `h(−4p) = 3h(−p) = 3`). Only the second needs
`hcl`. `PARI/GP` settled it in minutes: `deg α = deg α⁴` at `h(−p) = 1, 3, 5` alike, so the
structural half is class-number-FREE, and it became the leaf while the arithmetic became glue.

The same run found the sharp hypothesis the old statement had been MASKING: at `p ≡ 1 mod 4`,
`deg α > deg α⁴` (`p = 5`: `4` vs `2`), so the new leaf is FALSE there — `p ≡ 3 mod 4` is
load-bearing and nobody had noticed, because `hcl` is vacuous at those `p` and was covering it.
**A hypothesis that makes a leaf vacuous also hides which OTHER hypothesis is doing the work.**

So: before attacking a leaf, ask of each hypothesis "which HALF of the conclusion needs this",
and test it numerically. `algdep` on a high-precision value answers degree questions directly
(400 digits, accept only residual `< 10⁻²⁹⁰` AND coefficient height `< 10³⁰` — the height test
is essential, `algdep` returns a spurious height-`10¹²³` relation at every degree otherwise).

**2. A TWO-CLAUSE EXISTENTIAL SPLITS IFF THE FIRST CLAUSE PINS THE WITNESS.**
`∃ Φ, P Φ ∧ Q Φ` becomes `∃ Φ, P Φ` and `∀ Φ, P Φ → Q Φ` — two independently ownable leaves —
exactly when `P` determines `Φ`. That is the whole obligation, and it is usually easy: for
`Φ_N`, `P` says `Φ.map (eval at j(z))` is a given product for every `z ∈ ℍ`, `Polynomial.map`
is coefficientwise, and `j` is non-constant, so rival `Φ`s differ by coefficients vanishing at
infinitely many points. Discharge it IN THE DOCSTRING; without it the second leaf is unusable,
because a prover cannot tell which `Φ` it is talking about. The payoff is large: the second
leaf gets to ASSUME the first, which for `Φ_N` removed the entire construction from Kronecker's
`q`-expansion computation.

**3. QUANTIFY OVER ROOTS OF THE MINIMAL POLYNOMIAL, NOT OVER A `Finset` OF CLASSES.** The CM
leaf's docstring said a finer cut "needs a `Finset` of form classes and a `form ↦ τ_f` map,
i.e. new infrastructure". Both halves of that obstruction evaporate if the leaf ranges over
`aeval x (minpoly ℚ y) = 0` instead of over a class group, and RETURNS the point alongside the
form. Neither the class group nor the `τ_f` map is then definable at all. Generally: when a cut
looks blocked on infrastructure, check whether the infrastructure is only there to INDEX
something the leaf could hand back existentially.

**THE TRAP THAT COMES WITH MOVE 3, AND IT IS INVISIBLE IN THE STATEMENT.** `minpoly ℚ x = 0`
for transcendental `x`, and `Polynomial.aeval x 0 = 0` holds for EVERY `x`. So a hypothesis
"`x` is a root of `minpoly ℚ y`" is satisfied by ALL of `ℂ` when `y` is transcendental — and a
conclusion that can hold for only countably many `x` then makes the leaf FALSE. Any leaf stated
through `minpoly` has a silent ALGEBRAICITY dependency on its subject. Say so in the audit and
name what discharges it; here it was the OTHER open leaf of the same file, which means the two
CM leaves are not independent and a reviewer must not treat them as such.

**AND THE COUNT IS NOT THE MEASURE.** Move 1 and move 3 were net zero (one leaf closed, one
opened); move 2 was `+1`. What improved is that `hcl` now appears in ONE leaf instead of three,
that the two `Φ_N` halves share no technique, and that each residue is a statement with a name
in a textbook. Report the recut that way, not by the delta.

**4. PROVE ONE BULLET AND HAND IT BACK AS A HYPOTHESIS — the only recut that does NOT void the
earlier faithfulness audit.** (2026-07-31, same file, next run.) A leaf whose docstring says
"three things must be shown: A, B, C" splits without any pinning obligation at all: prove `A`
outright, and restate the leaf as `A → conclusion`. The old statement comes back by feeding the
proof in, so it is one leaf replacing one leaf with the *same conclusion*, and the residual
prover is left with strictly fewer theories to know.

`exists_intPolynomial_eq_prod` (`Φ_N` exists) listed `Γ`-invariance of `∏_t (X − j(t·z))`,
holomorphy-plus-cusp, and `q`-expansion integrality. The first is elementary and was PROVEN —
`exists_triangularReps_right_mul` (right multiplication by `γ` permutes `triangularReps N`,
via Hermite normal form and a `T^k` absorption) plus `triangularReps_eq_of_right_mul`
(injectivity, which is where `triangular_unique` gets spent) plus `Finset.prod_bij`, with
surjectivity free from injectivity on a finite set. The leaf now takes that as `hinv` and is
PURE ANALYSIS.

Why this is safe in a way the other moves are not: **adding a hypothesis can only weaken a
statement.** `CLAUDE.md`'s "a leaf restated a second time VOIDS its earlier audit" rule exists
because the composite CONCLUSION changed (`exists_artinDivisorNormIndex_le_ray_class` gained a
support clause). Here the conclusion is untouched, so the audit — including a machine-checked
one — carries over verbatim. Say so in the docstring; a reader who sees "RECUT" will otherwise
correctly assume the audit is void.

The one real obligation is that `hinv` be USABLE. State it in the strongest form your proof
actually produces, not the form the leaf's bullet was phrased in: the invariance was proved as
an equality of POLYNOMIALS, though the bullet asked only for each elementary symmetric
function, because the consumer then gets its coefficientwise version by one
`congrArg (Polynomial.coeff · k)` — whereas going the other way costs an ext.

**AND THE TRAP THAT COSTS A BUILD ROUND, which is a direct consequence of the scratch-module
doctrine: your new proof may call a helper that lives LATER in the target file.** The scratch
imports the whole module, so every declaration is in scope and the ordering constraint is
invisible there — it appears only on the first real build, as `Unknown identifier` for a name
you can see with your own eyes. Here `denom_ne_zero_of_det` sat ~1000 lines below the insertion
point and had to be hoisted. So when a scratch-verified block first fails in the file, read the
error before assuming a proof broke: a forward reference is far likelier than an elaboration
difference, and the fix is a move, not a proof.

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
