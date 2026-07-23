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

Same-FILE leaves may get concurrent owners (Deyao, 2026-07-22): each
agent works in its own git worktree on its own branch, and merging
concurrent edits to one file is what git is designed to handle — leaves
are disjoint regions, so merges are clean or trivially resolvable at
integration. Do not serialize a file's independent leaves behind one
owner out of conflict fear; partition them.

## Fleet dispatch: fixed pool of 13 numbered worktrees

(Deyao, 2026-07-23.) Subagent dispatch runs over a FIXED pool of 13
worktrees, `~/flt-lean-1` .. `~/flt-lean-13`, each on its own
same-numbered branch, each with its own `flt-report-server@flt-lean-N`
systemd instance (the template unit `flt-report-server@.service`,
`WorkingDirectory=%h/%i`) already running — `lake serve` on FIFOs,
scoped to that worktree. Live allocation state: `~/.flt-worktree-pool`,
one line per worktree, `<name> free` or `<name> claimed`.

- **Max 13 concurrent subagents**, one per worktree, 1:1.
- **Dispatch**: put the literal placeholder `{{FLT_WORKTREE}}` in the
  agent's prompt wherever its worktree path belongs.
  `.claude/worktree-pool-hook.py` (a `PreToolUse` hook on the `Agent`
  tool) finds a `free` entry, checks it is git-clean and its branch is
  an ancestor of main, fast-forwards it to main (`--ff-only`), marks it
  `claimed`, and substitutes the real path for the placeholder. Never
  touch `.lake` directly — the worktree's own `lake serve` instance
  rebuilds incrementally on its own. No free worktree → the hook denies
  the tool call. A claimed worktree that is dirty or not an ancestor of
  main is not auto-corrected — the hook hard-crashes (traceback to
  stderr, exit 2, tool call blocked): that state means something beyond
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
`~/cs/FLT` (the reference Lean project, same mathlib pin) for
vendorable sorry-free material before proving anything from scratch.
Previously downloaded sources stayed in the dissertation repo — see
`SOURCES.md` for the list.

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

## No lake build in iterations; trust the MCP diagnostics

(Deyao, 2026-07-21.) Skip `lake build` inside work iterations — the
lean-lsp MCP diagnostics are the verification gate; the Stop hook still
builds at the endgame. (A single-module `lake build` to refresh the
daemon's state is fine when the staleness note matters.)

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
  Enforced by the PreToolUse hook `.claude/lean-pretool-reminder.py`,
  which fires before every lean-lsp call.
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
not allowed: the Stop hook verifies this with the Lean compiler
through `free-floating.py` (cone BFS over `getUsedConstantsAsSet`)
and blocks with instructions to commit and delete. Work top-down.

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

## git is allowed — except force-push

Claude may run `git` commands; exercise ordinary caution with
history-destructive operations. **`git push --force` remains
explicitly banned**: `permissions.deny` in `.claude/settings.json`
blocks all variants. Plain `git commit` (ssh-signing is automatic via
Deyao's agent; if signing fails with "No private key found", the
agent — Bitwarden — is locked: ask Deyao). Commit trailers: the
standard Co-Authored-By and Claude-Session lines.

## Report-lsp MCP (report-mcp.py): diagnostics + build per worktree

(Deyao, 2026-07-23.) `report-mcp.py` at the repo root is a minimal MCP
server exposing exactly two tools — `diagnostics(file_path)` and
`build(clean=False)` — talking directly over one `flt-report-server`
instance's FIFOs (the same Content-Length-framed JSON-RPC protocol as
`progress-tree.py`'s report-server client). It takes `--socket-dir` —
the target instance's `.report-server` directory (holding
`req.fifo`/`resp.fifo`/`lock`/`state.json`) — as an argument rather than
doing any root-detection: the argument IS the routing, not a project
path to derive it from (the project path, needed for `build`'s cwd and
for resolving relative `file_path` args, is just `--socket-dir`'s
parent).

`lake serve` is single-rooted for its whole process lifetime (verified
empirically via an isolated toy-project test) — a server rooted at one
directory cannot correctly open or elaborate a file living under a
different worktree. So there is one `report-mcp.py` process, and one
`flt-report-server@<name>` systemd instance, PER worktree — 14 total
(main + `flt-lean-1..13`), each independently rooted. `.mcp.json`
registers all 14 as separate entries (`report-flt-lean`,
`report-flt-lean-1` .. `report-flt-lean-13`), each pointing
`--socket-dir` at its matching worktree's `.report-server`. An agent
working in `flt-lean-N` uses the `report-flt-lean-N` entry.

`diagnostics` syncs the file with on-disk content (`didOpen` the first
time, `didChange` after) and blocks on `textDocument/waitForDiagnostics`
— no polling/settle heuristics needed. The `initialize` handshake is
shared per SERVER SESSION via `.report-server/state.json` (the unit's
`ExecStartPre` clears it on every (re)start): its presence means some
earlier client already initialized this session (`lake serve` errors
if sent `initialize` twice), so a client only sends it when the file is
absent, then writes a marker.

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
output is empty or garbled, with the `ocrmypdf` Docker image:

```
docker run --rm -v <abs-pdf-dir>:/data jbarlow83/ocrmypdf \
  --rotate-pages --deskew --force-ocr -l eng \
  /data/<input>.pdf /data/<input>-ocr.pdf
pdftotext -layout <abs-pdf-dir>/<input>-ocr.pdf <output>.txt
```
