#!/usr/bin/env python3
"""Merge-worker checks that a conflict scan and a payload check cannot do.

Written at release 22 (2026-07-30), after three merges that produced NO conflict
marker, passed `git diff --stat HEAD^1 HEAD`, and did not compile.  See CLAUDE.md,
"SEVENTH invisibility class: A CLEAN MERGE THAT DOES NOT COMPILE".  Each
subcommand below caught at least one real error in that release.

    leaves [PATH ...]
        Per-declaration direct-sorry scan.  Strips nested block comments and line
        comments FIRST, then attributes each surviving `sorry` token to the
        enclosing declaration by walking BACKWARDS to the nearest header (walking
        forwards mis-attributes -- CLAUDE.md).  Reports tokens against
        declarations per file: a mismatch is ANONYMOUS INNER SORRIES, which no
        frontier scan can name and nobody will ever be dispatched at.
        Validated against the compiler at release 22: 253 = 253 over the 24
        modules built at the time of checking, zero differences.

    dup REV [REV_BASELINE]
        Namespace-qualified declaration names declared more than once WITHIN one
        file, and (separately) in MORE THAN ONE file.  The tree has many
        legitimate same-last-component names in different namespaces, so pass a
        baseline revision -- normally the previous release -- and only the NEW
        collisions are printed.  Found `Gamma0AtlasOver.bcUniversal_transport`
        (twice in X0.lean, two branches, regions too far apart to conflict) and
        `Fermat.isInvertibleSheaf_modPullback` (two modules, one importing the
        other -- a per-file scan cannot see this one).

    orphan BRANCH PATH [PATH ...]
        Names declared on BRANCH but not in the working-tree file, still CALLED
        (comments stripped) in the working-tree file.  This is the straddling
        chain: a branch's edit spans a conflict boundary, the conflicted half is
        resolved to `ours`, and the non-conflicting half survives referring to
        declarations that went away with the dropped half.  Found flt-lean-366's
        breakage before a build ran.  Expect benign hits when a declaration was
        deliberately RELOCATED to another module -- check the name's new home
        before believing a report.

Exit status is 0 unless a check found something; `leaves` always exits 0.
"""
import collections
import glob
import os
import re
import subprocess
import sys

DECL = re.compile(
    r'^(?:@\[[^\]]*\]\s*)?'
    r'(?:private\s+|protected\s+|public\s+|noncomputable\s+|partial\s+|unsafe\s+'
    r'|scoped\s+|local\s+|nonrec\s+)*'
    r'(theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+([^\s\(\{\[:]+)')
SORRY = re.compile(r'(?<![A-Za-z_])sorry(?![A-Za-z_])')


def strip_comments(src):
    """Blank out nested `/- -/` blocks and `--` tails, preserving line numbers."""
    out, depth, i = [], 0, 0
    while i < len(src):
        if src.startswith("/-", i):
            depth += 1; i += 2; out.append("  "); continue
        if src.startswith("-/", i) and depth:
            depth -= 1; i += 2; out.append("  "); continue
        if depth:
            out.append("\n" if src[i] == "\n" else " "); i += 1; continue
        if src.startswith("--", i):
            j = src.find("\n", i); j = len(src) if j < 0 else j
            out.append(" " * (j - i)); i = j; continue
        out.append(src[i]); i += 1
    return "".join(out)


def qualified_decls(src):
    """[(lineno, namespace-qualified name, kind)] for a comment-stripped source."""
    ns, out = [], []
    for n, line in enumerate(src.split("\n")):
        s = line.strip()
        if s.startswith("namespace "):
            ns.append(s.split()[1])
        elif s.startswith("end ") and ns and s.split()[1:2] == [ns[-1]]:
            ns.pop()
        m = DECL.match(line)
        if m:
            out.append((n + 1, ".".join(ns + [m.group(2).split(".{")[0]]), m.group(1)))
    return out


def show(rev, path):
    return subprocess.run(["git", "show", "%s:%s" % (rev, path)],
                          capture_output=True, text=True).stdout


def tracked(rev):
    return [f for f in subprocess.run(
        ["git", "ls-tree", "-r", "--name-only", rev, "Fermat/"],
        capture_output=True, text=True).stdout.split() if f.endswith(".lean")]


def cmd_leaves(paths):
    paths = paths or sorted(glob.glob("Fermat/**/*.lean", recursive=True))
    tot_d = tot_t = 0
    for p in paths:
        src = strip_comments(open(p, encoding="utf-8").read())
        lines = src.split("\n")
        headers = qualified_decls(src)
        tokens = [n + 1 for n, line in enumerate(lines) if SORRY.search(line)]
        if not tokens:
            continue
        owners = collections.OrderedDict()
        for t in tokens:
            prev = [h for h in headers if h[0] <= t]
            owners.setdefault(prev[-1][1] if prev else "<file scope>", []).append(t)
        tot_d += len(owners); tot_t += len(tokens)
        flag = "   <-- ANONYMOUS INNER SORRIES" if len(tokens) != len(owners) else ""
        print("%s  %d declarations / %d tokens%s" % (p, len(owners), len(tokens), flag))
        for name, ls in owners.items():
            print("    %-70s %s" % (name, ls))
    print("\nTOTAL: %d sorried declarations, %d sorry tokens" % (tot_d, tot_t))
    return 0


def collisions(rev):
    within, across = {}, collections.defaultdict(set)
    for f in tracked(rev):
        decls = qualified_decls(strip_comments(show(rev, f)))
        # instances may legitimately repeat a name; everything else may not
        names = collections.Counter(n for _, n, k in decls if k != "instance")
        for n, c in names.items():
            if c > 1:
                within.setdefault(f, {})[n] = c
            across[n].add(f)
    return within, {n: sorted(v) for n, v in across.items() if len(v) > 1}


def cmd_dup(rev, baseline=None):
    w, a = collisions(rev)
    bw, ba = collisions(baseline) if baseline else ({}, {})
    hits = 0
    print("== declared more than once WITHIN one file")
    for f, d in sorted(w.items()):
        for n, c in sorted(d.items()):
            if bw.get(f, {}).get(n) != c:
                print("   %s :: %s  x%d   (baseline: %s)"
                      % (f, n, c, bw.get(f, {}).get(n, "absent"))); hits += 1
    print("== declared in MORE THAN ONE file")
    for n, fs in sorted(a.items()):
        if ba.get(n) != fs:
            print("   %s : %s   (baseline: %s)" % (n, fs, ba.get(n, "absent"))); hits += 1
    print("new collisions: %d" % hits)
    return 1 if hits else 0


def cmd_orphan(branch, paths):
    hits = 0
    for f in paths:
        mine = strip_comments(open(f, encoding="utf-8").read())
        theirs = strip_comments(show(branch, f))
        last = lambda src: {n.split(".")[-1] for _, n, _ in qualified_decls(src)}
        only = last(theirs) - last(mine)
        for n, line in enumerate(mine.split("\n")):
            if DECL.match(line):
                continue
            for name in only:
                if re.search(r'(?<![A-Za-z0-9_.])%s(?![A-Za-z0-9_])' % re.escape(name), line):
                    print("%s:%d  calls %s -- declared only on %s" % (f, n + 1, name, branch))
                    hits += 1
    print("orphaned references: %d" % hits)
    return 1 if hits else 0


def main():
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    cmd, rest = sys.argv[1], sys.argv[2:]
    if cmd == "leaves":
        sys.exit(cmd_leaves(rest))
    if cmd == "dup":
        sys.exit(cmd_dup(rest[0], rest[1] if len(rest) > 1 else None))
    if cmd == "orphan":
        sys.exit(cmd_orphan(rest[0], rest[1:]))
    sys.exit(__doc__)


main()
