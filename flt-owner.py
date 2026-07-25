#!/usr/bin/env python3
"""Who owns this? Resolve leaf name / worktree -> AGENT ID, from disk.

WHY THIS EXISTS (2026-07-25). The orchestrator misrouted agent messages THREE
times in one session by resolving agent-to-worktree from DISPATCH ORDER --
"the fourth queue pop must be the fourth task" -- instead of reading the
transcripts. Twice an agent caught it and refused; once a wrong agent deleted
the real owner's scratch files. The correct method was written down after the
first occurrence and still not reached for, because it is a discipline that has
to be actively recalled at exactly the moment a message is being composed.

So it is a tool now, not a discipline. Run it before every SendMessage:

    python3 flt-owner.py exists_framedGaloisRep_traceSubring
    python3 flt-owner.py flt-lean-15
    python3 flt-owner.py --all

GROUND TRUTH is the first user message of each subagent transcript, which the
dispatch hook writes: "Your worktree is /home/chend/flt-lean-N". The task text
in that same message names the leaves. Nothing here is inferred from ordering.

Only the LATEST dispatch per worktree counts -- pool slots are recycled, and a
prior occupant's transcript is not the current owner. That was the first bug:
six resume messages went to previous occupants.
"""

import glob
import json
import os
import re
import sys

SESSION_ROOT = "/home/chend/.claude/projects/-home-chend-flt-lean"
WORKTREE_RE = re.compile(r"Your worktree is /home/chend/(flt-lean-\d+)\b")
# Leaf names as the task prompts write them: `name` in backticks.
NAME_RE = re.compile(r"`([A-Za-z_][A-Za-z0-9_.']{5,})`")
# Only names in the TARGET block count as OWNED. Task prompts deliberately name
# SIBLING leaves too ("...have DIFFERENT owners: X, Y -- do not touch them"), so
# a whole-prompt match reports five owners for one leaf and is worse than
# useless: it looks authoritative while being wrong. The TARGET block runs from
# the "TARGET"/"TARGET CLUSTER" heading to the end of that paragraph.
TARGET_RE = re.compile(r"TARGET(?: CLUSTER)?\s*:(.*?)(?:\\n\\n|\n\n)", re.S)


def _sessions():
    for d in sorted(glob.glob(os.path.join(SESSION_ROOT, "*", "subagents"))):
        yield d


def load():
    """worktree -> {agent, ts, names}, keeping only the latest dispatch each."""
    best = {}
    for sub in _sessions():
        for f in glob.glob(os.path.join(sub, "agent-*.jsonl")):
            aid = os.path.basename(f)[len("agent-"):-len(".jsonl")]
            head = []
            try:
                with open(f, errors="ignore") as fh:
                    for i, line in zip(range(40), fh):
                        head.append(line)
            except OSError:
                continue
            blob = "".join(head)
            m = WORKTREE_RE.search(blob)
            if not m:
                continue
            wt = m.group(1)
            ts = ""
            for line in head:
                if WORKTREE_RE.search(line):
                    try:
                        ts = json.loads(line).get("timestamp", "") or ""
                    except Exception:
                        pass
                    break
            tm = TARGET_RE.search(blob)
            names = set(NAME_RE.findall(tm.group(1))) if tm else set()
            prev = best.get(wt)
            if prev is None or ts > prev["ts"]:
                best[wt] = {"agent": aid, "ts": ts, "names": names}
    return best


def main():
    args = [a for a in sys.argv[1:]]
    table = load()
    if not args or args[0] == "--all":
        for wt in sorted(table, key=lambda w: int(w.rsplit("-", 1)[1])):
            r = table[wt]
            print(f"{wt:14s} {r['agent']}  {r['ts'][:19]}")
        return 0
    q = args[0]
    if WORKTREE_RE.pattern and re.fullmatch(r"flt-lean-\d+", q):
        r = table.get(q)
        print(f"{q}: {r['agent']} (dispatched {r['ts'][:19]})" if r
              else f"{q}: no dispatch found")
        return 0 if r else 1
    hits = [(wt, r) for wt, r in table.items() if q in r["names"]]
    if not hits:
        print(f"no current owner mentions `{q}`")
        return 1
    for wt, r in sorted(hits, key=lambda kv: kv[1]["ts"], reverse=True):
        print(f"{wt:14s} {r['agent']}  {r['ts'][:19]}")
    if len(hits) > 1:
        print(f"\nWARNING: {len(hits)} current owners mention `{q}` -- read the "
              f"prompts before messaging; this is also how duplicate cuts start.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
