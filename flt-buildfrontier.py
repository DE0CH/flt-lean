#!/usr/bin/env python3
"""Harvest the AUTHORITATIVE frontier from the merger's release build log.

Why this exists (Deyao, 2026-07-27): the merger runs a full `lake build` for
every release, and that build already emits the exact `declaration uses 'sorry'`
warning set. Re-deriving it with a source scan is strictly worse -- a source scan
cannot see the ERRORED-declaration class (a proof that fails to elaborate is
`sorryAx`-tainted, emits no sorry warning, and contains no `sorry` token), it has
to hand-strip nested block comments to avoid counting docstring prose, and it has
to attribute each token backwards to its enclosing declaration. The build already
did all of that correctly and for free.

So: parse the log, don't scan the tree.

Usage:
    flt-buildfrontier.py [--log HOST:PATH] [--names-only] [--errors]

Default log is the staging host's most recent /tmp/build-rel*.log.
"""
import argparse
import re
import subprocess
import sys

WARN = re.compile(
    r"^warning: (?P<file>[^:]+):(?P<line>\d+):\d+: declaration uses .sorry.",
    re.M)
ERR = re.compile(r"^error: (?P<file>[^:]+):(?P<line>\d+):\d+: (?P<msg>.*)$", re.M)
DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:private |protected |public |noncomputable |partial |unsafe |scoped )*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+"
    r"([A-Za-z_À-￿][A-Za-z0-9_.'À-￿]*)")


def staging_host():
    return open("/home/chend/.flt-worker-host/flt-staging",
                encoding="utf-8").read().strip()


def fetch_log(spec):
    if spec:
        host, path = spec.split(":", 1)
    else:
        host = staging_host()
        path = subprocess.run(
            ["ssh", "-o", "ConnectTimeout=10", host,
             "ls -t /tmp/build-rel*.log | head -1"],
            capture_output=True, text=True).stdout.strip()
        if not path:
            sys.exit("no /tmp/build-rel*.log on %s" % host)
    out = subprocess.run(["ssh", "-o", "ConnectTimeout=10", host, "cat " + path],
                         capture_output=True, text=True)
    if out.returncode:
        sys.exit("could not read %s:%s" % (host, path))
    return host, path, out.stdout


TREE = "/home/chend/flt-lean"


def decl_at(path, line):
    """Walk BACKWARDS from `line` to the nearest declaration header."""
    try:
        src = open(TREE + "/" + path, encoding="utf-8").read()
    except OSError:
        return None
    lines = src.split("\n")
    for i in range(min(line, len(lines)) - 1, -1, -1):
        m = DECL.match(lines[i])
        if m:
            return m.group(1)
    return None


def main():
    global TREE
    ap = argparse.ArgumentParser()
    ap.add_argument("--log", help="HOST:PATH of a build log")
    ap.add_argument("--names-only", action="store_true")
    ap.add_argument("--errors", action="store_true",
                    help="also report hard errors (the invisible frontier)")
    ap.add_argument("--tree", default=TREE,
                    help="source tree the log was built from (default %s). "
                         "THE MERGER MUST PASS ITS STAGING WORKTREE: during a "
                         "cycle /home/chend/flt-lean is still the PREVIOUS "
                         "release, so line numbers there resolve to the wrong "
                         "declarations." % TREE)
    a = ap.parse_args()
    TREE = a.tree.rstrip("/")

    host, path, log = fetch_log(a.log)
    hits = [(m.group("file"), int(m.group("line"))) for m in WARN.finditer(log)]

    rows, by_file = [], {}
    for f, ln in hits:
        name = decl_at(f, ln) or "?"
        rows.append((f, ln, name))
        by_file.setdefault(f, []).append((ln, name))

    if a.names_only:
        for _, _, n in rows:
            print(n)
        return

    print("# frontier from %s:%s" % (host, path))
    print("# %d direct sorries across %d modules\n" % (len(rows), len(by_file)))
    for f in sorted(by_file):
        print("%s (%d)" % (f, len(by_file[f])))
        for ln, n in sorted(by_file[f]):
            print("  %6d  %s" % (ln, n))

    if a.errors:
        errs = [m for m in ERR.finditer(log)
                if "SORRY GATE FAILED" not in m.group("msg")]
        print("\n# hard errors (invisible to every sorry scan): %d" % len(errs))
        for m in errs:
            print("  %s:%s  %s" % (m.group("file"), m.group("line"),
                                   m.group("msg")[:110]))


main()
