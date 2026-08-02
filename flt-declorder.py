#!/usr/bin/env python3
"""Which declarations in a Lean file USE a name declared LATER in the same file?

`tools/merge/semmerge.py` merges hunks; it does not REORDER them.  So when two
branches each move a declaration, the merge can land a consumer ABOVE its
producer — a breakage no diff shows, because every line is present and correct
and only their ORDER is wrong.  At release 29 that was the largest single cause
of breakage in `X0.lean`, in five separate clusters.

The tell is `Unknown identifier` for a name `grep` finds in the same file.  The
mistake is to hunt for a missing import; the fix is to compare the two line
numbers.  This finds every such pair in one pass, before a build, in a second —
so the clusters are enumerated up front instead of one per twenty-minute
elaboration round.

THE RELEASE CHECK IS ONE COMMAND, and it is the way to run this:

    ./flt-declorder.py Fermat --sweep --rev $(cat ~/.flt-release-lake/sha)

Single file, for iterating on one repair:

    ./flt-declorder.py Fermat/FLT/ModularCurve/X0.lean

Output is one line per offending pair, `consumer -> producer`, grouped into
CLUSTERS: a set of declarations whose forward references overlap has to be
repaired as a unit, and the cluster is what you hand to `flt-hoistcheck.py`.

CALIBRATION, measured 2026-08-01 and worth re-running whenever this is touched
(a scan that reports nothing is indistinguishable from a scan that is broken):

* RECALL — on `X0.lean` at `9a6f34ee^`, the last tree where the release-29
  breakage was still present, it reports **12 pairs in 8 clusters**, which is
  every cluster the release-29 handover names BY HAND plus one nobody had
  listed.  Nothing in that list was found by any other instrument.
* PRECISION — on the green tree at `280981f1` (402 files, `lake build` clean
  apart from the expected `SORRY GATE FAILED`) it reports **0** with `--rev`,
  and ~20 pairs without it.

Those ~20 are the one class it cannot decide: a short name that ALSO exists in
the import closure resolves to mathlib's and is not a forward reference at all
(`mk_embedding`, `map_surjective`).  They are STABLE — they are in the green
tree too — so differencing against the last green revision removes them
exactly, which is the same discipline `xdup.py` and `scopecheck.py` already
need.  **Do not read a bare run's output as an error list; difference it.**

Three smaller things it cannot see, all rare enough not to have fired above:
`where`/`let`-bound locals shadowing a file-level name; projections generated
by a `structure`; and a later lemma reached only through notation or a `simp`
set.

Conversely it does NOT under-report the class it exists for: a genuine
use-before-declaration always shows up here, because Lean's own resolution rule
is exactly the textual one this implements.

The tokeniser is deliberately NOT a `\\w` regex — Lean names contain `₀₁₂` and
Unicode letters, and `\\w` splits on the subscripts, turning `c₄_nonCMModelX`
into a spurious hit on `c`.  Same tokeniser as `flt-hoistcheck.py`; keep them
in step.
"""

import argparse
import re
import sys
from collections import defaultdict

DECL = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)?'
    r'(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|scoped\s+)*'
    r'(theorem|lemma|def|abbrev|structure|inductive|instance|class|opaque)\s+'
    r'([^\s:({\[]+)')
SCOPING = re.compile(r'^\s*(namespace|end)\b\s*(\S*)')
MIN_LEN = [12]
# Lines that ATTACH to the declaration below them.  A declaration's body must
# stop before its successor's attachment run, or the successor's own name --
# `@[to_additive piEquivPiSubtypeProd]` -- is read as a forward reference from
# the declaration above.  This was 1 of the 2 false-positive sources.
ATTACH = re.compile(r'^\s*(@\[|attribute\b|open\b.*\bin\b|set_option\b.*\bin\b'
                    r'|omit\b.*\bin\b|include\b.*\bin\b|variable\b.*\bin\b|$)')


def strip_comments(lines):
    """Drop `--` line comments and (nested) `/- -/` blocks, keeping line count."""
    out, depth = [], 0
    for ln in lines:
        res, i = [], 0
        while i < len(ln):
            if depth == 0 and ln.startswith("--", i):
                break
            if ln.startswith("/-", i):
                depth += 1
                i += 2
                continue
            if depth > 0 and ln.startswith("-/", i):
                depth -= 1
                i += 2
                continue
            if depth == 0:
                res.append(ln[i])
            i += 1
        out.append("".join(res))
    return out


def tokens(text):
    """Identifier-ish tokens.  See the module docstring on why not a regex."""
    out, cur = set(), []
    for ch in text:
        if ch.isalnum() or ch in "_.'!?" or (ord(ch) > 127 and ch.isalpha()):
            cur.append(ch)
        elif cur:
            out.add("".join(cur))
            cur = []
    if cur:
        out.add("".join(cur))
    return out


def declarations(clean):
    """[(line, short_name, full_name)] for every declaration, in file order.

    `full_name` is the enclosing `namespace` stack plus the declared name, which
    is what a qualified reference from elsewhere in the file has to match.
    """
    out, stack = [], []
    for i, ln in enumerate(clean):
        m = SCOPING.match(ln)
        if m:
            if m.group(1) == "namespace":
                stack.append(m.group(2))
            elif stack and m.group(2) and stack[-1] == m.group(2):
                stack.pop()
            continue
        m = DECL.match(ln)
        if m:
            name = m.group(2)
            full = ".".join([s for s in stack if s] + [name])
            out.append((i + 1, name.split('.')[-1], full))
    return out


def attached(clean):
    """attached[i] iff line i+1 belongs to the DECLARATION BELOW it.

    An `@[...]` attribute may span several lines and may contain a nested
    docstring (`@[to_additive foo /-- ... -/]`), so a line-shaped test is not
    enough -- bracket depth is carried across lines.  Getting this wrong reads
    the successor's own name out of its attribute list as a forward reference
    from the declaration above.
    """
    flags = [False] * len(clean)
    i = 0
    while i < len(clean):
        ln = clean[i]
        if ATTACH.match(ln):
            depth = ln.count('[') - ln.count(']')
            flags[i] = True
            j = i
            while depth > 0 and j + 1 < len(clean):
                j += 1
                flags[j] = True
                depth += clean[j].count('[') - clean[j].count(']')
            i = j
        i += 1
    return flags


def body_end(flags, next_decl_line):
    """Last line of a body whose successor's declaration is at `next_decl_line`."""
    e = next_decl_line - 1
    while e >= 1 and flags[e - 1]:
        e -= 1
    return e


def scan(path):
    """[(consumer_line, consumer_name, producer_line, producer_name)], sorted."""
    raw = open(path).read().split("\n")
    clean = strip_comments(raw)
    decls = declarations(clean)
    if not decls:
        return None
    flags = attached(clean)

    # A declaration's body runs to the line before its successor's attachments.
    spans = []
    for k, (line, name, full) in enumerate(decls):
        end = body_end(flags, decls[k + 1][0]) if k + 1 < len(decls) else len(clean)
        spans.append((line, end, name))

    # short name -> FIRST line declaring it.  A name declared twice is its own
    # bug (the duplicate-declaration class); the first is what Lean sees first.
    first, first_full = {}, {}
    for line, name, full in decls:
        first.setdefault(name, line)
        first_full.setdefault(full, line)

    def resolve(tk):
        """Lines this token could refer to, as a local declaration.

        A DOTTED token is either a QUALIFIED name (`Rat.HeightOneSpectrum.foo`)
        or DOT NOTATION on a term (`hx.foo`).  Only the second is a reference to
        this file's short name `foo`; the first names somebody else's `foo` and
        matching it on the last component is a namespace collision.  They are
        told apart by the case of the head: namespaces are capitalised here and
        term variables are not.  This was the other false-positive source.
        """
        if '.' not in tk:
            return [first.get(tk)]
        head, last = tk.split('.', 1)[0], tk.split('.')[-1]
        if head[:1].isupper():                      # qualified: full name only
            return [first_full.get(tk)]
        return [first.get(last)]                    # dot notation on a term

    pairs = []          # (consumer_line, consumer_name, producer_line, producer_name)
    for start, end, name in spans:
        body = "\n".join(clean[start - 1:end])
        for tk in tokens(body):
            cand = tk.split('.')[-1]
            if len(cand) < MIN_LEN[0] or cand == name:
                continue
            for p in resolve(tk):
                if p is not None and p > start:
                    pairs.append((start, name, p, cand))
    pairs.sort()
    return pairs


def git_show(rev, path):
    """`git show rev:path` into a temp file, or None if it is not there."""
    import subprocess, tempfile
    r = subprocess.run(["git", "show", f"{rev}:{path}"],
                       capture_output=True, text=True)
    if r.returncode != 0:
        return None
    fh = tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False)
    fh.write(r.stdout)
    fh.close()
    return fh.name


def sweep(root, rev):
    """Scan every .lean under `root`, differencing against `rev`.  Exit status
    is the number of files with surviving forward references."""
    import os
    bad = 0
    for dirpath, _, names in os.walk(root):
        for nm in sorted(names):
            if not nm.endswith(".lean"):
                continue
            path = os.path.join(dirpath, nm)
            pairs = scan(path)
            if not pairs:
                continue
            if rev:
                b = git_show(rev, path)
                if b:
                    known = {(cn, pn) for _, cn, _, pn in (scan(b) or [])}
                    os.unlink(b)
                    pairs = [p for p in pairs if (p[1], p[3]) not in known]
            if pairs:
                bad += 1
                print(f"{path}: {len(pairs)} forward reference(s)")
                for cl, cn, pl, pn in pairs:
                    print(f"    :{cl} {cn} -> {pn} declared {pl - cl} lines "
                          f"LATER at :{pl}")
    print(f"\n{bad} file(s) with declaration-order breakage.")
    return bad


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("file", help="a .lean file, or a DIRECTORY with --sweep")
    ap.add_argument("--sweep", action="store_true",
                    help="walk the directory and check every .lean under it; "
                         "this is the release check -- one command, ~seconds")
    ap.add_argument("--rev", metavar="REV",
                    help="with --sweep: git revision of the last GREEN tree to "
                         "difference against, e.g. $(cat ~/.flt-release-lake/sha)")
    ap.add_argument("--min-len", type=int, default=12,
                    help="ignore names shorter than this; short names are "
                         "overwhelmingly mathlib's, not this file's (default 12)")
    ap.add_argument("--baseline", metavar="FILE",
                    help="a known-GREEN version of the same file (e.g. "
                         "`git show <release-sha>:<path>`).  Pairs present in "
                         "BOTH are subtracted, keyed by NAMES rather than by "
                         "line numbers so that unrelated edits do not shift "
                         "them.  This is what makes the residual false "
                         "positives -- short names that also exist in the "
                         "import closure -- disappear.")
    ap.add_argument("--quiet", action="store_true",
                    help="print only the cluster summary")
    args = ap.parse_args()
    MIN_LEN[0] = args.min_len

    if args.sweep:
        sys.exit(1 if sweep(args.file, args.rev) else 0)

    pairs = scan(args.file)
    if pairs is None:
        sys.exit(f"no declarations found in {args.file}")

    if args.baseline:
        base = scan(args.baseline) or []
        known = {(cn, pn) for _, cn, _, pn in base}
        dropped = len(pairs)
        pairs = [p for p in pairs if (p[1], p[3]) not in known]
        dropped -= len(pairs)
        print(f"baseline {args.baseline}: {len(known)} known pair(s), "
              f"{dropped} subtracted.\n")

    if not pairs:
        print(f"{args.file}: no forward references.  Declaration order is "
              f"topological (for names >= {args.min_len} chars).")
        return

    # Cluster: consumers and producers linked by a shared pair, unioned.
    parent = {}

    def find(x):
        parent.setdefault(x, x)
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(x, y):
        parent[find(x)] = find(y)

    for cl, cn, pl, pn in pairs:
        union(cl, pl)

    clusters = defaultdict(list)
    for cl, cn, pl, pn in pairs:
        clusters[find(cl)].append((cl, cn, pl, pn))

    if not args.quiet:
        for cl, cn, pl, pn in pairs:
            print(f"{args.file}:{cl}  {cn}\n"
                  f"    -> uses {pn}, declared {pl - cl} lines LATER at :{pl}")

    print(f"\n{len(pairs)} forward reference(s) in {len(clusters)} cluster(s).")
    for root in sorted(clusters):
        ps = clusters[root]
        lines = sorted({l for p in ps for l in (p[0], p[2])})
        print(f"  cluster {lines[0]}..{lines[-1]}  "
              f"({len(ps)} reference(s), span {lines[-1] - lines[0]} lines)")
    print("\nEach cluster is repaired as a UNIT.  Feed its span to "
          "flt-hoistcheck.py to price the move.")


if __name__ == "__main__":
    main()
