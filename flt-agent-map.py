#!/usr/bin/env python3
"""Maintain the worktree <-> agent-transcript mapping.

WHY THIS EXISTS (Deyao, 2026-07-25). It was originally judged unnecessary,
because every agent's own transcript already records which worktree it works in,
so a *resume* never needs the map. That reasoning is right for resumes and wrong
for everything else: any operation that must act on SPECIFIC worktrees needs the
reverse direction, worktree -> agent. Two cases already hit:

  * suspending N workers for CPU/memory relief -- you must stop the AGENTS of
    those particular worktrees, and stop them BEFORE their lake serve, or they
    sit retrying against dead FIFOs instead of parking cleanly;
  * telling the owner of a specific leaf that its target was just proven by
    someone else, which otherwise degrades into broadcasting a conditional
    message to every candidate.

WHY IT CANNOT LIVE IN THE DISPATCH HOOK. The harness mints the agent id AFTER
the PreToolUse hook returns, so `worktree-pool-hook.py` can never know it; it
records worktree, targets and the full prompt in ~/.flt-inflight.jsonl, and the
id has to be joined on afterwards. This script does that join, from the one
source that is always authoritative: the agents' own transcripts.

METHOD. For each subagent transcript, read the first few lines and take the
first /home/chend/flt-lean-N path that appears -- that is the worktree its task
prompt named. Keep the most recently modified transcript per worktree (a worktree
is reused across successive owners, and the newest is the current one). Join
against the pool state and the in-flight registry, and write a TSV.

The transcript scan is the fallback that always works; it recovered 30/30
mappings when the registry held only 10 records. Prefer the registry's
dispatched_at/targets when present, since they are recorded at dispatch time and
cannot be confused by transcript reuse.

Usage:  python3 flt-agent-map.py            # rebuild and print a summary
        python3 flt-agent-map.py --for flt-lean-7    # one worktree's agent id
"""

import glob
import json
import os
import re
import sys

HOME = "/home/chend"
POOL = f"{HOME}/.flt-worktree-pool"
INFLIGHT = f"{HOME}/.flt-inflight.jsonl"
OUT = f"{HOME}/.flt-agent-map.tsv"
PROJECTS = f"{HOME}/.claude/projects/-home-chend-flt-lean"

WT_RE = re.compile(r"/home/chend/(flt-lean-\d+)\b")


def newest_transcript_per_worktree():
    """worktree -> (agent_id, mtime), newest transcript wins."""
    best = {}
    for sess in glob.glob(f"{PROJECTS}/*/subagents"):
        for f in glob.glob(os.path.join(sess, "agent-*.jsonl")):
            aid = os.path.basename(f)[len("agent-"):-len(".jsonl")]
            try:
                mt = os.path.getmtime(f)
            except OSError:
                continue
            wt = None
            try:
                with open(f, errors="replace") as fh:
                    for i, line in enumerate(fh):
                        if i > 8:
                            break
                        m = WT_RE.search(line)
                        if m:
                            wt = m.group(1)
                            break
            except OSError:
                continue
            if wt and (wt not in best or mt > best[wt][1]):
                best[wt] = (aid, mt)
    return best


def pool_state():
    st = {}
    try:
        for line in open(POOL):
            p = line.split()
            if p:
                st[p[0]] = (p[1], p[2] if len(p) > 2 else "")
    except OSError:
        pass
    return st


def registry():
    """worktree -> newest record from the dispatch hook."""
    recs = {}
    try:
        for line in open(INFLIGHT):
            try:
                r = json.loads(line)
            except ValueError:
                continue
            w = r.get("worktree")
            if w and (w not in recs or r.get("dispatched_at", "") >= recs[w].get("dispatched_at", "")):
                recs[w] = r
    except OSError:
        pass
    return recs


def build():
    tr, st, reg = newest_transcript_per_worktree(), pool_state(), registry()
    rows = []
    for wt in sorted(st, key=lambda s: int(s.split("-")[-1])):
        status, extra = st[wt]
        aid = ""
        # a suspended entry's third field IS the transcript id, and is
        # authoritative -- it was recorded at the moment the agent was stopped.
        if status == "suspended" and extra:
            aid = extra
        elif wt in tr:
            aid = tr[wt][0]
        r = reg.get(wt, {})
        rows.append((wt, status, aid or "-", r.get("dispatched_at", "-"),
                     ",".join(r.get("targets", [])) or "-"))
    with open(OUT, "w") as fh:
        fh.write("worktree\tpool_state\tagent_id\tdispatched_at\ttargets\n")
        for r in rows:
            fh.write("\t".join(r) + "\n")
    return rows


def main():
    if "--for" in sys.argv:
        wt = sys.argv[sys.argv.index("--for") + 1]
        for r in build():
            if r[0] == wt:
                print(r[2])
                return 0
        print("-")
        return 1
    rows = build()
    live = [r for r in rows if r[1] in ("claimed", "reclaiming")]
    known = [r for r in live if r[2] != "-"]
    print(f"wrote {OUT}: {len(rows)} worktrees")
    print(f"  live (claimed/reclaiming): {len(live)}, of which mapped: {len(known)}")
    unmapped = [r[0] for r in live if r[2] == "-"]
    if unmapped:
        print(f"  UNMAPPED live worktrees (cannot be targeted): {' '.join(unmapped)}")
    from collections import Counter
    print("  by state:", dict(Counter(r[1] for r in rows)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
