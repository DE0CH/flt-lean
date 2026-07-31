#!/usr/bin/env python3
"""Row-level tests for the loop's transition table. Run: python3 flt-loop-rows-test.py

Written after the release-27 panic, whose whole content was that the table had
no row for an outcome the merge worker's own prompt prescribes. `--dry-run`
could not have caught it: it evaluates the ONE state on disk, so it says which
row fires now and nothing about the states the machine can reach. These are
synthetic states -- the cheapest way to ask "and what happens when THIS occurs".

The state dicts are hand-built rather than loaded, so they are toy worlds: no
hosts and no worktrees, which means dispatch (row 12) can never fire in them.
Assert on the row you are testing and on the state it leaves behind, not on
what fires in a world with no fleet in it.
"""
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from flt_loop_rows import step                                    # noqa: E402


def base(**kw):
    s = {"stop": False, "main": "m2", "rebaselined": "m1",
         "snapshot": {"sha": "m2"}, "snapshot_current": True, "audit_current": True,
         "rebaseline_current": False,
         "queue1": {"audited": "m2", "tasks": ["t"]}, "queue2": [], "merger_inbox": [],
         "batch": ["flt-lean-9"], "inflight": ["flt-lean-1", "flt-lean-2"],
         "jobs": {},
         "workers": {"flt-lean-1": "awaiting_merge", "flt-lean-2": "awaiting_merge"},
         "worker_host": {}, "ancestor": {}, "healthy": {}, "hosts": {},
         "quota_block": None, "probe": {"served": False},
         "log": [], "git": [], "email": []}
    s.update(kw)
    return s


def merger(sentinel):
    return {"kind": "merger", "worktree": "flt-staging", "payload": [],
            "token": "t", "retries": 0, "started": True, "alive": False,
            "sentinel": sentinel}


SEN = {"queue": ["fix X0"], "to_merger": ["X0 is red"], "to_medic": ""}

# 1. HELD -- reported, published nothing, because the tree it built was red.
#    This is release 27, and before row 21 existed it was a PANIC.
s = base(rebaseline_current=True, jobs={"merger": merger(SEN)})
f = step(s)
print("1 HELD           ->", f, "| batch", s["batch"], "| inflight", s["inflight"],
      "| queue2", s["queue2"], "| inbox", s["merger_inbox"])
assert f == 21 and s["inflight"] is None
assert s["batch"] == ["flt-lean-1", "flt-lean-2", "flt-lean-9"]   # claim refolded
assert s["queue2"] == ["fix X0"] and s["merger_inbox"] == ["from merger: X0 is red"]
assert "merger" not in s["jobs"]

# 2. DELIVERED -- main gained Lean content, snapshot and audit current.
s = base(jobs={"merger": merger(SEN)},
         ancestor={"flt-lean-1": True, "flt-lean-2": False})
f = step(s)                       # row 7 first: the landed branch is discharged
print("2a landed        ->", f)
assert f == 7
f = step(s)
print("2 DELIVERED      ->", f, "| batch", s["batch"], "| rebaselined", s["rebaselined"],
      "| queue2", s["queue2"], "| inbox", s["merger_inbox"])
assert f == 10 and s["rebaselined"] == "m2"
assert s["queue2"] == ["fix X0"], "a delivered merger's queue must still be relayed"
assert s["merger_inbox"] == ["from merger: X0 is red"]
assert s["batch"] == ["flt-lean-2", "flt-lean-9"], s["batch"]     # unlanded refolded

# 3. DIED -- stopped with no sentinel at all.
s = base(rebaseline_current=True, jobs={"merger": merger(None)})
f = step(s)
print("3 DIED           ->", f, "| batch", s["batch"])
assert f == 9

# 4. HELD *and* reporting a fault in the loop: the panic row sits above every
#    consumer, so it wins and the record is kept for the medic to look at.
s = base(rebaseline_current=True,
         jobs={"merger": merger(dict(SEN, to_medic="the state dir is torn"))})
f = step(s)
print("4 HELD+to_medic  ->", f, "| jobs", sorted(s["jobs"]))
assert f == 5 and "medic" in s["jobs"] and "merger" in s["jobs"]

# 5. A TOOLING COMMIT moved main and changed no Lean input. There is no release
#    here, so the baseline must not advance -- the bug that would have let a
#    held release be signed for as a delivery.
s = base(rebaseline_current=True, jobs={}, batch=[], inflight=None, workers={})
f = step(s)
print("5 tooling commit ->", f, "(no fleet in this toy state, so dispatch cannot "
      "fire;\n                       what matters is that ADOPT does not)")
assert f != 10 and s["rebaselined"] == "m1", (f, s["rebaselined"])

# 6. ...but real Lean movement with no merger record still re-baselines.
s = base(jobs={}, batch=[], inflight=None, workers={})
f = step(s)
print("6 rebaseline     ->", f, "| rebaselined", s["rebaselined"])
assert f == 10 and s["rebaselined"] == "m2"

# 7. A medic's own sentinel is delivered like everybody else's.
s = base(rebaseline_current=True, workers={}, jobs={"medic": {
    "kind": "medic", "worktree": "flt-lean", "payload": "why", "token": "t",
    "retries": 0, "started": True, "alive": False,
    "sentinel": {"go": True, "why": "fixed", "queue": ["repair X0"],
                 "to_merger": ["a held release is legal now"], "to_medic": ""}}})
f = step(s)
print("7 medic verdict  ->", f, "| queue2", s["queue2"], "| inbox", s["merger_inbox"])
assert f == 2 and s["queue2"] == ["repair X0"]
assert s["merger_inbox"] == ["from medic: a held release is legal now"]

print("\nall 7 pass")
