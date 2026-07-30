#!/usr/bin/env python3
"""flt-hosts.py -- what every worker host is actually doing, in parallel.

The loop needs three numbers per host to place work: how loaded it is (CPU),
how much memory is left (the RAM veto), and how many of its worktrees are
busy. It also needs to know what is running that nobody owns, which is the
same query -- an orphan is just a process whose worktree has no live job.

Written as a script rather than a shell fan-out because `pgrep -c` exits
non-zero when it matches nothing, so the obvious `pgrep -c ... || echo 0`
prints TWO lines and every field after it shifts by one. That silently
misaligned an eleven-host table on the first attempt.
"""
import concurrent.futures as cf
import json
import subprocess
import sys

HOSTS = ["cyclops", "dazzler", "forge", "gambit", "nightcrawler", "nocturne",
         "polaris", "quicksilver", "shadowcat", "vanisher", "wolverine"]

PROBE = r'''
python3 - <<'PY'
import os, glob, json, subprocess
def procs(pat):
    # Exclude THIS process and its children. pgrep matches on the whole
    # command line, and the probe's own command line contains every pattern it
    # searches for -- so an unfiltered count reports a baseline of one on
    # every host and makes an idle machine look busy.
    me = {os.getpid(), os.getppid()}
    out = subprocess.run(["pgrep","-af",pat],capture_output=True,text=True).stdout
    keep = []
    for l in out.splitlines():
        if not l.strip():
            continue
        pid = int(l.split()[0])
        if pid in me or "pgrep" in l or "flt-hosts" in l:
            continue
        keep.append(l)
    return keep
lean   = procs(r"lean --")
claude = procs(r"claude")
mem = {}
for ln in open("/proc/meminfo"):
    k,v = ln.split(":"); mem[k] = int(v.split()[0])
load = float(open("/proc/loadavg").read().split()[0])
ncpu = os.cpu_count()
tmp = 0
for p in glob.glob("/tmp/*"):
    try: tmp += os.path.getsize(p)
    except OSError: pass
print(json.dumps({
  "lean": len(lean), "claude": len(claude),
  "avail_gb": round(mem.get("MemAvailable",0)/1048576,1),
  "load": load, "ncpu": ncpu, "util": round(load/ncpu,3),
  "tmp_mb": round(tmp/1048576,1),
  "lean_sample": lean[:3],
}))
PY
'''


def probe(h):
    try:
        r = subprocess.run(["ssh", "-o", "BatchMode=yes", "-o", "ConnectTimeout=12",
                            h, PROBE], capture_output=True, text=True, timeout=90)
        return h, json.loads(r.stdout.strip().splitlines()[-1])
    except Exception as e:
        return h, {"error": str(e)[:60]}


def main():
    with cf.ThreadPoolExecutor(max_workers=len(HOSTS)) as ex:
        res = dict(ex.map(probe, HOSTS))
    print("%-14s %6s %7s %8s %7s %7s %8s" %
          ("host", "lean", "claude", "avail_G", "util", "ncpu", "tmp_MB"))
    for h in HOSTS:
        d = res[h]
        if "error" in d:
            print("%-14s  %s" % (h, d["error"]))
            continue
        print("%-14s %6d %7d %8.1f %7.2f %7d %8.1f" %
              (h, d["lean"], d["claude"], d["avail_gb"], d["util"], d["ncpu"],
               d["tmp_mb"]))
    if "--json" in sys.argv:
        print(json.dumps(res, indent=1))
    return res


if __name__ == "__main__":
    main()
