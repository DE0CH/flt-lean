#!/usr/bin/env python3
"""flt-loop-status.py -- one screen of "is the loop healthy".

Written for the 10-minute watch. Everything here is read-only; it takes no
lock and never writes to the state, so running it can never disturb the loop.

The four things that actually indicate trouble, in order of severity:
  * the loop process is gone            -> nothing is driving the fleet
  * a medic exists                      -> the loop panicked and is in SAFE MODE
  * the transition log has not advanced -> ticking but wedged, or crashing
  * zero live agents with work queued   -> dispatching is broken
"""
import json
import pathlib
import subprocess
import sys
import time

STATE = pathlib.Path.home() / ".flt-loop"
HOSTS = ["cyclops", "dazzler", "forge", "gambit", "nightcrawler", "nocturne",
         "polaris", "quicksilver", "shadowcat", "vanisher", "wolverine"]


def rd(p, d=""):
    try:
        return pathlib.Path(p).read_text()
    except OSError:
        return d


def loop_pid():
    p = rd(STATE / "loop.lock").strip()
    if p.isdigit():
        try:
            if b"flt-loop.py" in pathlib.Path("/proc/%s/cmdline" % p).read_bytes():
                return int(p)
        except OSError:
            pass
    return None


def live_agents():
    import concurrent.futures as cf

    def one(h):
        try:
            r = subprocess.run(
                ["ssh", "-o", "BatchMode=yes", "-o", "ConnectTimeout=8", h,
                 r"pgrep -a -u $USER . 2>/dev/null | grep -o 'flt-job-[0-9a-f]\+' | sort -u"],
                capture_output=True, text=True, timeout=30)
            return h, len(set(r.stdout.split()))
        except Exception:
            return h, None
    with cf.ThreadPoolExecutor(max_workers=len(HOSTS)) as ex:
        return dict(ex.map(one, HOSTS))


def main():
    out, alarms = [], []
    # A quota block explains both silence and the absence of live processes,
    # so it must be read BEFORE either is called an alarm -- otherwise the
    # watch reports "spawning is broken" every ten minutes throughout a wait
    # that is entirely correct, and the real alarms drown in it.
    # There is no deadline any more: the block is a fact re-checked by probing
    # the credential on disk, because a rotator can swap accounts underneath us.
    qb = rd(STATE / "quota-blocked").strip()
    blocked = bool(qb)
    if blocked:
        import json as _j
        try:
            since = _j.loads(qb).get("since", 0)
            mins = int((time.time() - since) / 60)
            out.append("quota        : REFUSED %d min ago -- not spawning; probing "
                       "every tick with the key on disk" % mins)
        except Exception:
            out.append("quota        : REFUSED -- not spawning; probing")

    pid = loop_pid()
    out.append("loop pid       : %s" % (pid or "NOT RUNNING"))
    if not pid:
        alarms.append("the loop process is not running -- nothing is driving the fleet")

    log = subprocess.run(["git", "-C", str(STATE), "log", "--format=%ct %s", "-40"],
                         capture_output=True, text=True).stdout.splitlines()
    if log:
        last = int(log[0].split()[0])
        age = int(time.time() - last)
        out.append("last transition: %ds ago -- %s" % (age, log[0].split(" ", 1)[1][:70]))
        # Idle is silent by design, so a quiet log is only alarming when there
        # is work that should be producing transitions.
        if age > 3600 and not blocked:
            alarms.append("no transition committed for %d minutes" % (age // 60))
    out.append("transitions    : %d in the last 40" % len(log))

    jobs = sorted((STATE / "jobs").glob("*.json"))
    kinds = {}
    for f in jobs:
        try:
            kinds[json.loads(f.read_text())["kind"]] = kinds.get(
                json.loads(f.read_text())["kind"], 0) + 1
        except Exception:
            pass
    out.append("job records    : %s" % (kinds or "none"))
    if (STATE / "jobs" / "medic.json").exists():
        alarms.append("A MEDIC IS IN FLIGHT -- the loop panicked and is in SAFE MODE")

    q1 = rd(STATE / "queue1").splitlines()
    aud = q1[0] if q1 else "(empty)"
    ntasks = rd(STATE / "queue1").count("=== TASK ===") + (1 if len(q1) > 1 else 0)
    out.append("queue1         : %s, %d tasks" % (aud, ntasks))
    out.append("queue2         : %d tasks"
               % (rd(STATE / "queue2").count("=== TASK ===") + 1
                  if rd(STATE / "queue2").strip() else 0))
    out.append("batch/inflight : %d / %d"
               % (len(rd(STATE / "batch").split()), len(rd(STATE / "inflight").split())))

    if "--fast" not in sys.argv:
        la = live_agents()
        tot = sum(v for v in la.values() if v)
        out.append("live agents    : %d  %s" % (tot, la))
        if tot == 0 and kinds.get("agent") and not blocked:
            alarms.append("%d agent records but ZERO live processes -- spawning is broken"
                          % kinds["agent"])

    tail = rd(STATE / "email.log").strip().splitlines()[-4:]
    if tail:
        out.append("recent emails  :")
        out += ["    " + t[:100] for t in tail]

    print("\n".join(out))
    if alarms:
        print("\nALARMS:")
        for a in alarms:
            print("  * " + a)
    return 1 if alarms else 0


if __name__ == "__main__":
    sys.exit(main())
