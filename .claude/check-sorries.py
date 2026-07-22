#!/usr/bin/env python3
"""Stop hook for the FLT formalization loop (Deyao, 2026-07-16).

Exit-code protocol (Claude Code Stop hooks):
  exit 0 -> allow Claude to stop (the loop exit condition is met);
  exit 2 -> BLOCK the stop; stderr is fed back to Claude as the reason;
  any other exit code -> non-blocking error, Claude stops anyway.

The loop has exactly one exit condition: zero sorried declarations in
the project and the root gate (`#assert_no_sorry fermat_last_theorem`)
clean. The check queries the persistent Lean environment server
(`fermat/lean-daemon.py`, autostarted on demand — seconds per query
instead of a full `lake build`): the daemon's Lean child reports every
project declaration whose proof term uses `sorryAx` (the compiler's own
verdict) plus the root-cone sorry/axiom status. The daemon's environment
reflects the last BUILT state of each module; modules edited since are
reported as `stale_sources` and surfaced in the block message. Only in
the endgame (daemon reports zero sorries) does the hook run one real
`lake build` to confirm against fresh sources and the actual root gate.
Deliberately NO `stop_hook_active` guard: while the exit condition is
unmet the hook keeps blocking (the built-in block cap /
CLAUDE_CODE_STOP_HOOK_BLOCK_CAP bounds a single turn); Deyao terminates
the loop externally when he chooses.

ORCHESTRATOR MODE (Deyao, 2026-07-22): the driven session now
ORCHESTRATES parallel subagents that edit disjoint Lean files, then
integrates, verifies, and commits their results. The blocking messages
below are therefore framed for an orchestrator, not a hands-on prover:
uncommitted files and unbuilt modules are usually agents' work-in-flight
(routine churn), reported as INFORMATION — committing half-edits or
rebuilding per-iteration would be wrong. The mechanics (session guard,
daemon query, exit-code semantics, endgame build) are unchanged.
"""

import glob
import json
import os
import subprocess
import sys
import time

# Fleet-aware gate (Deyao, 2026-07-22): an orchestrator waiting on live
# background agents should not be reprompted on every stop — task
# notifications wake it. Liveness source: the orchestrator-maintained
# fleet registry; an agent is ALIVE iff any file matching its
# transcript_glob was modified within the last 15 minutes.
# FAIL OPEN (Deyao, 2026-07-22): this hook is a back-to-work nudge, not
# a safety net — automation failure is acceptable. Block only on the
# clean positive case (sorries remain AND the registry is readable AND
# no transcript is fresh); every ambiguous or error path allows the stop.
FLEET_STALE_SECONDS = 15 * 60


def fleet_is_idle(project_dir: str) -> bool:
    """True iff the registry is readable AND no agent transcript is fresh.

    Fail open: any error (missing/unreadable registry, bad shape, glob
    or stat failure) returns False, i.e. the stop is allowed.
    """
    reg_path = os.environ.get("FLEET_REGISTRY_PATH") or os.path.join(
        project_dir, ".claude", "fleet-registry.json")
    try:
        with open(reg_path, "r", encoding="utf-8") as fh:
            agents = json.load(fh).get("agents", [])
        now = time.time()
        for agent in agents:
            pattern = agent.get("transcript_glob")
            if not pattern:
                continue
            for path in glob.glob(pattern):
                if now - os.path.getmtime(path) < FLEET_STALE_SECONDS:
                    return False  # a live agent -> fleet not idle
    except Exception:
        return False  # fail open: idleness not cleanly established
    return True


def main() -> int:
    caller_session = ""
    try:
        hook_input = json.load(sys.stdin)
        caller_session = str(hook_input.get("session_id", ""))
    except Exception:
        pass  # malformed/absent input must not disable the gate

    project_dir = os.environ.get("CLAUDE_PROJECT_DIR")
    if not project_dir:
        return 0  # cannot locate the project; do not wedge the session

    # Session guard (Deyao, 2026-07-21): the continuous-loop reprompting is
    # meant for exactly one designated session, recorded on disk. Any OTHER
    # session that triggers this hook (e.g. an accidentally launched chat in
    # the same worktree) must NOT be driven into the loop: block its stop
    # with a standing refusal so it only warns the user, repeatedly.
    id_file = os.path.join(project_dir, ".claude", "stop-hook-session-id")
    try:
        with open(id_file, "r", encoding="utf-8") as fh:
            designated_session = fh.read().strip()
    except OSError:
        designated_session = ""
    if designated_session and caller_session != designated_session:
        sys.stderr.write(
            "The stop hook is intended to be used by session "
            f"{designated_session}, and you are {caller_session}, so there "
            "is NO SAFE ACTION to continue. Warn the user instead "
            "(repeatedly, after each time this stop hook fires): "
            '"the STOP HOOK ran, this is probably not intended."\n'
        )
        return 2

    fermat = project_dir  # flt-lean: the project root IS the Lean package
    if not os.path.isdir(os.path.join(fermat, "Fermat")):
        return 0

    # THE check: ask the persistent Lean environment server for the
    # compiler-verified list of sorried declarations and the root-cone
    # status (seconds, no build).
    try:
        proc = subprocess.run(
            [sys.executable, os.path.join(fermat, "lean-daemon.py"),
             "--query", '{"cmd": "sorries"}'],
            cwd=fermat,
            capture_output=True,
            text=True,
            timeout=3000,
        )
        resp = json.loads(proc.stdout)
        if "error" in resp:
            raise RuntimeError(resp["error"])
    except Exception as exc:
        # FAIL OPEN (Deyao, 2026-07-22): the hook is a nudge, not a
        # safety net — a daemon hiccup must not block the stop.
        sys.stderr.write(
            f"Stop hook: lean daemon query failed ({exc}); allowing the "
            "stop (fail open).\n"
        )
        return 0

    sorries = [f"{s['name']} ({s['module']})" for s in resp["sorried"]]
    root = resp.get("root", {})
    stale = resp.get("stale_sources", [])
    unbuilt = resp.get("unbuilt_modules", [])
    root_open = (
        root.get("missing", True)
        or root.get("coneSorry", True)
        or root.get("badAxioms")
    )

    if not sorries and not root_open and not unbuilt:
        # Endgame: the daemon (last-built state) says done. Confirm against
        # fresh sources and the actual root gate with one real build.
        proc = subprocess.run(
            ["lake", "build"],
            cwd=fermat,
            capture_output=True,
            text=True,
            timeout=3000,
        )
        if proc.returncode == 0:
            return 0  # compiler-verified: gate passed, no sorries anywhere
        sys.stderr.write(
            "Not done: the daemon reports zero sorried declarations, but "
            "the confirming `lake build` fails — fix the build; the loop "
            "exit condition is a clean build through the root sorry "
            "gate.\n"
        )
        for line in (proc.stdout + proc.stderr).splitlines():
            if line.startswith("error"):
                sys.stderr.write(f"  {line}\n")
        return 2

    # FLEET-AWARE GATE (sorries-present branch only): while >=1 registered
    # agent is alive — or the fleet state cannot be cleanly established
    # (fail open) — allow the stop silently; task notifications wake the
    # orchestrator. Only a readable registry with all transcripts stale
    # falls through to the full blocking message with one prepended
    # FLEET IDLE line.
    if sorries:
        if not fleet_is_idle(project_dir):
            return 0
        print(
            "FLEET IDLE: no live agents detected (registry "
            ".claude/fleet-registry.json; stale >15min) while sorries "
            "remain — re-dispatch or integrate now.",
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
            "module(s) have no .olean yet, so the daemon could not check "
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
            f"Not done: the Lean compiler reports {len(sorries)} sorried "
            f"declaration(s) in the FLT dependency tree{stale_note}. "
            "Continue orchestrating: ensure every open node has an owner "
            "(a running agent, or an explicit orchestrator decision to "
            "defer); dispatch new agents for orphaned nodes; monitor "
            "running agents; integrate, verify (lean-lsp MCP diagnostics "
            "or module builds), and commit completed work; then re-check. "
            "Next open nodes:",
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

    # Deyao (2026-07-20, orchestrator framing 2026-07-22): the `wip`/`○`
    # pointer in progress-entries.json is the live ownership map — one
    # cluster of marks per running agent — updated at BOTH transition
    # moments (dispatch and completion/integration), always via
    # progress-entries.json + the snapshot pipeline, never by
    # hand-editing PROGRESS.md.
    print(
        "WORK-IN-PROGRESS POINTER: keep progress-entries.json's `wip` "
        "flags current at BOTH transitions — AT DISPATCH: immediately set "
        "`wip: true` on exactly the node(s) the dispatched (or "
        "re-dispatched) agent owns; AT COMPLETION/INTEGRATION: clear "
        "`wip` on nodes the agent no longer owns and set it on newly "
        "created leaves that got new owners. Multiple concurrent `wip` "
        "marks are EXPECTED (one cluster per running agent) — the flags "
        "are the live ownership map; regenerate PROGRESS.md via the "
        "snapshot pipeline after each such update.",
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
    # Free-floating detection (Deyao, 2026-07-18, compiler-verified):
    # `free-floating.py` asks the Lean compiler for every project
    # declaration outside the transitive used-constant cone of
    # `fermat_last_theorem` (a sorried consumer contributes no edges,
    # so bottom-up material shows here until its consumer's proof
    # skeleton is written). The hook reads the cache and flags
    # staleness; regenerating (`python3 free-floating.py`) is part of
    # the integration workflow, like progress-tree.py.
    try:
        cache_path = os.path.join(fermat, "free-floating.json")
        cached = json.load(open(cache_path))
        latest = 0.0
        for dirpath, _dirs, files in os.walk(
                os.path.join(fermat, "Fermat")):
            for name in files:
                if name.endswith(".lean"):
                    try:
                        latest = max(latest, os.path.getmtime(
                            os.path.join(dirpath, name)))
                    except OSError:
                        pass
        stale = cached.get("key") != str(latest)
        floating = cached.get("floating", [])
        if floating:
            from collections import Counter
            counts = Counter(f["module"] for f in floating)
            marker = " (STALE cache — rerun `python3 free-floating.py` " \
                "at the next integration point)" if stale else ""
            print(
                f"FREE-FLOATING CODE: {len(floating)} project "
                "declaration(s) are outside the dependency cone of "
                f"`fermat_last_theorem`{marker}. Free-floating code is "
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
