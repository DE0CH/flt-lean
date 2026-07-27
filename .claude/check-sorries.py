#!/usr/bin/env python3
"""Stop hook for the FLT formalization loop (Deyao, 2026-07-16).

Exit-code protocol (Claude Code Stop hooks):
  exit 0 -> allow Claude to stop (the loop exit condition is met);
  exit 2 -> BLOCK the stop; stderr is fed back to Claude as the reason;
  any other exit code -> non-blocking error, Claude stops anyway.

The loop has exactly one exit condition: zero sorried declarations in
the project and the root gate (`#assert_no_sorry fermat_last_theorem`)
clean. The check runs the census route (Deyao, 2026-07-23: the
resident lean-daemon.py middleman is deleted): `python3
progress-tree.py --census`, which queries the resident REPORT SERVER
— `lake serve` run as the systemd user unit flt-report-server.service,
its stdin/stdout on FIFOs under `.report-server/` — for one JSON
object with every project declaration whose proof term uses `sorryAx`
(the compiler's own verdict) plus the root-cone sorry/axiom status.
Seconds on a warm session; changed modules pay their incremental
rebuild inside the census run. The hook NEVER
runs a whole-project `lake build` (Deyao, 2026-07-22 — nothing
automatic does): the endgame verdict rests on the census's evidence
alone, and the insurance build confirming a zero-sorry state is
Deyao's manual job.
Deliberately NO `stop_hook_active` guard: while the exit condition is
unmet the hook keeps blocking (the built-in block cap /
CLAUDE_CODE_STOP_HOOK_BLOCK_CAP bounds a single turn); Deyao terminates
the loop externally when he chooses.

ORCHESTRATOR MODE (Deyao, 2026-07-22): the driven session now
ORCHESTRATES parallel subagents that edit disjoint Lean files, then
integrates, verifies, and commits their results. The blocking messages
below are therefore framed for an orchestrator, not a hands-on prover:
uncommitted files are usually agents' work-in-flight (routine churn),
reported as INFORMATION — committing half-edits or rebuilding
per-iteration would be wrong. The mechanics (session guard, census
run, exit-code semantics) are unchanged.
"""

import glob
import json
import os
import subprocess
import sys
import time

# Liveness gate (Deyao, 2026-07-22, generic rework): an orchestrator
# with ANY live background work — subagents, background bash tasks,
# workflows — should not be reprompted on every stop, because every one
# of those produces a task notification on completion that re-prompts
# the session by itself. This hook is a CATCH-ALL for exactly the case
# where nothing else can wake the session. The gate runs FIRST,
# immediately after the session guard: any wakeable work LIVE -> exit 0
# instantly (no daemon query, no sorry counting, no free-floating
# check). Liveness source: the harness's own on-disk traces for the
# CURRENT session id (no manually maintained registry) — a file under
# any liveness root modified within the last 15 minutes = live.
# Verified on disk 2026-07-22 for session 8e948ad7-…:
#   /tmp/claude-*/<slug>/<session_id>/tasks/            (*.output)
#   ~/.claude/projects/<slug>/<session_id>/subagents/   (agent-*.jsonl,
#       plus a subagents/workflows/ subdir — covered by recursive walk)
#   ~/.claude/projects/<slug>/<session_id>/workflows/   (wf_*.json)
# where <slug> is the project dir with '/' and '.' mapped to '-'
# (-home-chend-flt-lean). Override for testing: LIVENESS_DIRS, a
# colon-separated list of roots that replaces the defaults.
# FAIL OPEN (Deyao, 2026-07-22): this hook is a back-to-work nudge, not
# a safety net — automation failure is acceptable. Block only on the
# clean positive case (sorries remain AND the scan succeeded AND no
# trace is fresh); every ambiguous or error path allows the stop.
LIVENESS_STALE_SECONDS = 15 * 60


def _default_liveness_dirs(project_dir: str, session_id: str) -> list:
    """Roots holding the harness's wakeable-work traces for this session."""
    slug = project_dir.replace("/", "-").replace(".", "-")
    roots = glob.glob(f"/tmp/claude-*/{slug}/{session_id}/tasks")
    session_base = os.path.join(
        os.path.expanduser("~"), ".claude", "projects", slug, session_id)
    roots.append(os.path.join(session_base, "subagents"))
    roots.append(os.path.join(session_base, "workflows"))
    return roots


def background_work_is_idle(project_dir: str, session_id: str) -> bool:
    """True iff the liveness scan succeeded AND no trace file is fresh.

    A fresh file (mtime within LIVENESS_STALE_SECONDS) under any root
    means some background work can still re-prompt the session. Roots
    that do not exist contribute nothing (a session that never launched
    background work is genuinely idle). Fail open: any error returns
    False, i.e. the stop is allowed.
    """
    try:
        env_dirs = os.environ.get("LIVENESS_DIRS")
        if env_dirs is not None:
            roots = [d for d in env_dirs.split(":") if d]
        else:
            if not session_id:
                return False  # cannot derive the roots; fail open
            roots = _default_liveness_dirs(project_dir, session_id)
        now = time.time()
        for root in roots:
            for dirpath, _dirs, files in os.walk(root):
                for name in files:
                    path = os.path.join(dirpath, name)
                    if now - os.path.getmtime(path) < LIVENESS_STALE_SECONDS:
                        return False  # live wakeable work
    except Exception:
        return False  # fail open: idleness not cleanly established
    return True


def main() -> int:
    try:
        hook_input = json.load(sys.stdin)
        caller_session = str(hook_input["session_id"])
    except Exception as exc:
        # graceful (harness-facing hook, Deyao 2026-07-22): without a
        # readable session id the guard cannot attribute this stop —
        # allow it with one informative line, never act on a made-up id
        sys.stderr.write(
            f"Stop hook: could not read session_id from hook input "
            f"({exc!r}); allowing the stop.\n")
        return 0

    project_dir = os.environ.get("CLAUDE_PROJECT_DIR")
    if not project_dir:
        return 0  # cannot locate the project; do not wedge the session

    # Session guard (Deyao, 2026-07-21; amended 2026-07-27): the
    # continuous-loop reprompting is meant for exactly one designated session,
    # recorded on disk. Any OTHER session that triggers this hook (e.g. an
    # accidentally launched chat in the same worktree) must NOT be driven into
    # the loop -- so it is ALLOWED TO STOP, with one line on stderr.
    #
    # It used to be blocked instead (exit 2 + "warn the user, repeatedly").
    # That was wrong in the only way that matters: the loop exists to drive
    # the ONE designated session, and a session that is not it has, by
    # definition, nothing to continue. Blocking it did not protect anything
    # -- it just wedged an unrelated session into an unbreakable reprompt
    # cycle whose only available action was to emit the same warning again.
    # Allowing the stop is also what the two branches below already do when
    # the designation is unreadable or empty; this branch was the outlier.
    id_file = os.path.join(project_dir, ".claude", "stop-hook-session-id")
    try:
        with open(id_file, "r", encoding="utf-8") as fh:
            designated_session = fh.read().strip()
    except OSError as exc:
        # no readable designation -> no session may be driven (the hook
        # only ever drives the RECORDED session); allow with one line
        sys.stderr.write(
            f"Stop hook: cannot read {id_file} ({exc}); no designated "
            "session — allowing the stop.\n")
        return 0
    if not designated_session:
        sys.stderr.write(
            f"Stop hook: {id_file} is empty; no designated session — "
            "allowing the stop.\n")
        return 0
    if caller_session != designated_session:
        sys.stderr.write(
            f"Stop hook: the FLT loop drives session {designated_session}, "
            f"not {caller_session} — allowing the stop.\n")
        return 0

    fermat = project_dir  # flt-lean: the project root IS the Lean package
    if not os.path.isdir(os.path.join(fermat, "Fermat")):
        return 0

    # LIVENESS GATE, FIRST (Deyao, 2026-07-22 generic rework): the hook
    # is only needed when NOTHING wakeable exists — subagents, background
    # bash tasks, and workflows all re-prompt the orchestrator via task
    # notifications on completion. While any such trace for THIS session
    # is fresh — or liveness cannot be cleanly established (fail open,
    # nudge-not-safety-net) — allow the stop instantly, skipping the
    # census run, sorry counting, and free-floating check entirely.
    # Only a clean all-stale scan falls through to the pipeline below.
    try:
        if not background_work_is_idle(project_dir, caller_session):
            return 0
    except Exception:
        return 0  # any liveness-check failure counts as LIVE (fail open)

    # THE check: the DIRECT frontier, read from source by flt-frontier.py.
    #
    # WHY NOT THE CENSUS ANY MORE (2026-07-26). This block used to run
    # `progress-tree.py --census`, i.e. `lake env lean ProgressCensus.lean`
    # in THIS checkout. Under the release model the orchestrator's checkout
    # is never built — the merger builds in `~/flt-staging` — so the census
    # died on `object file '….olean' does not exist` at every single stop
    # and the hook fell straight through its fail-open path. A check that
    # can only fail open is not a check; the hook was silently disabled for
    # as long as the release model has been in force.
    #
    # `flt-frontier.py` scans SOURCE (comment-stripped, sorries attributed
    # backwards to their enclosing declaration header — see its docstring
    # for the traps that shape encodes) and needs no oleans, no build, no
    # server. ~5s. It is the same scan `flt-cycle.py preflight` and
    # `flt-unowned.py` already run, so the hook now agrees with the rest of
    # the fleet tooling by construction instead of by coincidence.
    #
    # WHAT IS LOST, deliberately: the census also reported the root-cone
    # axiom status and the free-floating set, neither of which a source
    # scan can see. Both are now the merger's business — it is the only
    # party with a built tree, and the sorry gate in `Fermat.lean` is what
    # actually enforces the root invariant at build time. The hook's job is
    # narrower and honest: "is the frontier empty?".
    try:
        proc = subprocess.run(
            [sys.executable, os.path.join(fermat, "flt-frontier.py"),
             "--json"],
            cwd=fermat,
            capture_output=True,
            text=True,
            timeout=600,
        )
        if proc.returncode != 0:
            raise RuntimeError(
                (proc.stderr.strip() or proc.stdout.strip()
                 or f"exit {proc.returncode}")[-2000:])
        leaves = json.loads(proc.stdout)
    except Exception as exc:
        # FAIL OPEN (Deyao, 2026-07-22): the hook is a nudge, not a safety
        # net. Terse by design — a hook message must never instruct anyone
        # to start servers or rebuild (Deyao, 2026-07-23).
        sys.stderr.write(
            f"Stop hook: frontier scan unavailable or failed "
            f"({type(exc).__name__}: {exc}); allowing the stop (fail open).\n"
        )
        return 0

    try:
        sorries = [f"{lf['name']} ({lf['module']})" for lf in leaves]
    except (KeyError, TypeError) as exc:
        sys.stderr.write(
            f"Stop hook: malformed frontier response ({exc!r}); "
            "allowing the stop.\n")
        return 0
    # The source scan cannot speak to the root cone or to build state; the
    # sorry gate and the merger own those. Kept as constants so the
    # reporting below stays structurally intact.
    root, root_open, stale, unbuilt = {}, False, [], []

    if not sorries and not root_open:
        # Endgame (Deyao, 2026-07-22): NOTHING automatic runs `lake build`
        # — this hook decides on the census's evidence alone. Zero sorries
        # + clean root cone + no caveats -> allow. If the verdict is
        # incomplete (stale sources or unbuilt modules), still allow
        # (fail open, nudge not gate) with a one-line note; the insurance
        # build confirming the zero-sorry state is Deyao's manual job.
        if stale or unbuilt:
            sys.stderr.write(
                "Note: census reports zero sorried declarations, but the "
                f"verdict is partial ({len(stale)} stale-source, "
                f"{len(unbuilt)} unbuilt module(s)) — allowing the stop; "
                "Deyao's own insurance `lake build` would confirm it.\n"
            )
        return 0

    # Idleness was already established by the gate above; prepend the
    # no-live-work line to the blocking message.
    if sorries:
        print(
            "NO LIVE BACKGROUND WORK: nothing running can re-prompt this "
            "session, and sorries remain — dispatch agents or integrate "
            "now.",
            file=sys.stderr,
        )

    # Uncommitted changes: INFORMATION for the orchestrator, not an order
    # to commit everything — most dirty files are subagents' work-in-flight.
    dirty = ""
    try:
        status = subprocess.run(
            ["git", "status", "--porcelain"],
            cwd=project_dir,
            capture_output=True,
            text=True,
            timeout=60,
        )
        dirty = status.stdout.strip()
    except Exception:
        pass

    if dirty:
        print(
            "UNCOMMITTED CHANGES (information): the working tree is "
            "dirty. Files owned by still-running agents are work-in-"
            "flight and must NOT be committed. Commit only integrated "
            "AND verified work: your own bookkeeping files and the "
            "outputs of agents that have completed and been verified. "
            "Dirty files:",
            file=sys.stderr,
        )
        for line in dirty.splitlines()[:8]:
            print(f"  {line}", file=sys.stderr)

    if unbuilt:
        print(
            f"UNBUILT MODULES (information): {len(unbuilt)} project "
            "module(s) have no .olean yet, so the census could not check "
            "them — expected during agent churn. Run a consolidated "
            "rebuild at integration points, not per-iteration:",
            file=sys.stderr,
        )
        for mod in unbuilt[:5]:
            print(f"  {mod}", file=sys.stderr)

    if sorries:
        stale_note = (
            f" ({len(stale)} module(s) edited since their last build — "
            "counts reflect the built state)" if stale else ""
        )
        print(
            f"Not done: {len(sorries)} DIRECT sorried declaration(s) remain "
            f"in the FLT tree{stale_note}. Continue orchestrating the "
            "release cycle: `python3 flt-cycle.py preflight` (every branch "
            "an ancestor of main, every worker state consistent, every "
            "sorry owned by a queued task or a live agent — queueing IS "
            "ownership); queue tasks for anything `flt-unowned.py` reports; "
            "`flt-cycle.py release` to hand the green main out; dispatch "
            "the queue; `flt-cycle.py done <wt>` as agents report, and hand "
            "the batch to the ONE merge worker. Next open nodes:",
            file=sys.stderr,
        )
        for entry in sorries[:5]:
            print(f"  {entry}", file=sys.stderr)
    elif root_open:
        print(
            "Not done: no sorried declarations, but the root "
            "`fermat_last_theorem` cone is not clean: "
            f"missing={root.get('missing')} coneSorry={root.get('coneSorry')} "
            f"badAxioms={root.get('badAxioms')}.",
            file=sys.stderr,
        )

    # OWNERSHIP POINTER. The `wip`/`○` marks in progress-entries.json used
    # to be the live ownership map, and this hook used to demand they be
    # kept current at both transitions. Under the release model (Deyao,
    # 2026-07-26) PROGRESS.md regeneration is DROPPED for speed, so that
    # instruction is retired: ownership now lives in `~/.flt-task-queue`
    # (queueing IS ownership) plus the live-agent set, and `flt-unowned.py`
    # is what reconciles them.
    print(
        "OWNERSHIP: the loop invariant is that every direct sorry has an "
        "owner at all times. Run `python3 flt-unowned.py --verbose`; for "
        "each name it reports, append a task to `~/.flt-task-queue` with a "
        "leading ``TARGET: `name` `` block (the ownership scan reads those "
        "blocks, not the prose).",
        file=sys.stderr,
    )
    # Deyao (2026-07-18): the continuation must keep the user informed
    # of the frontier size in the chat itself.
    print(
        f"REPORT TO THE USER: state plainly in your next user-visible "
        f"message that {len(sorries)} sorried declaration(s) currently "
        "remain in the FLT dependency tree (and restate the updated count "
        "at the end of every turn), so the user can track the loop's "
        "progress without reading the tree.",
        file=sys.stderr,
    )
    # Free-floating detection (Deyao, 2026-07-18/23, compiler-verified):
    # the SAME census response above already carries "floating" --
    # ProgressCensus.lean's runCensus computes every project declaration
    # outside the transitive used-constant cone of `fermat_last_theorem`
    # (a sorried consumer contributes no edges, so bottom-up material
    # shows here until its consumer's proof skeleton is written), via
    # ImportGraph's Name.transitivelyUsedConstants. No separate
    # subprocess, no cache file: the language server's own incremental
    # elaboration is the cache. free-floating.py applies the SAME
    # keep-list filter for standalone/manual use.
    try:
        keep_path = os.path.join(fermat, "free-floating-keep.json")
        keep = {}
        if os.path.exists(keep_path):
            keep_data = json.load(open(keep_path))
            keep = {k: v for k, v in keep_data.items()
                    if not k.startswith("_")}
        raw = resp.get("floating", [])
        floating = [f for f in raw if f["name"] not in keep]
        if floating:
            from collections import Counter
            counts = Counter(f["module"] for f in floating)
            print(
                f"FREE-FLOATING CODE: {len(floating)} project "
                "declaration(s) are outside the dependency cone of "
                "`fermat_last_theorem`. Free-floating code is "
                "not allowed: assign an owner to resolve it top-down "
                "(write the consuming proof skeleton, or delete the "
                "material after its verified state is committed). "
                "Worst modules:",
                file=sys.stderr,
            )
            for mod, n in counts.most_common(6):
                print(f"  {n:5d}  {mod}", file=sys.stderr)
    except Exception:
        pass
    return 2


if __name__ == "__main__":
    sys.exit(main())
