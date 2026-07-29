#!/usr/bin/env python3
"""flt-hidden-sorries.py — find sorries that NO frontier scan can see.

Lean emits ONE `declaration uses 'sorry'` warning per declaration, however many
`sorry` tokens the body contains. So a declaration carrying

    have h1 : P := by sorry
    have h2 : Q := by sorry

is counted once by the compiler, once by a source scan that keys on
declarations, and once in every leaf table — while holding two obligations.
Nobody is ever dispatched at the second one, because no tool reports it.

CLAUDE.md records the worst instance: `exists_isSwanExponentAt` carries FIVE
inner sorries behind a single warning, and three separate agents reported that
count as "three" under names that do not exist. On 2026-07-29 an agent found
another in the wild — `exists_artinNormSubgroups_ramified_ray_class`
(ModThree.lean) hides `have hbase : ... := by intro _ _ _ _ _ _ _; sorry`.

This script does the check tree-wide, from source alone, with no build:

  1. strip nested block comments and line comments (this tree's docstrings
     discuss sorried leaves constantly -- a naive grep inflated one count from
     85 to 144);
  2. attribute every surviving `sorry` token to its enclosing declaration by
     walking BACKWARDS to the nearest declaration header (walking forwards
     mis-attributes a later declaration's sorry to an earlier proven one, which
     is how `exists_hardlyRamifiedLift` was twice mislabelled open);
  3. report declarations holding MORE THAN ONE token, and any token that lands
     outside a declaration at all.

Usage:  flt-hidden-sorries.py [path ...]     (default: Fermat/)
"""
import re
import sys
from pathlib import Path

ROOT = Path("/home/chend/flt-lean")

HDR = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"(?:private |protected |noncomputable |partial |unsafe )*"
    r"(theorem|lemma|def|instance|abbrev|structure|class|example)\s+"
    r"([A-Za-z_][A-Za-z0-9_.'!?]*)?")


def strip_comments(text):
    """Drop nested `/- -/` blocks and `--` line comments, preserving newlines.

    Newlines are preserved so line numbers stay meaningful in the report.
    """
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif text.startswith("-/", i) and depth:
            depth -= 1
            i += 2
        elif depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            if j < 0:
                break
            out.append(" " * (j - i))
            i = j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


# `sorry` as a token, not as a substring of an identifier (`sorryAx`) and not
# inside a longer word.
SORRY = re.compile(r"(?<![A-Za-z0-9_'])sorry(?![A-Za-z0-9_'])")


def scan(path):
    src = strip_comments(path.read_text(errors="replace"))
    lines = src.splitlines()

    # line number -> enclosing declaration (name, header line), by walking back
    headers = []
    for i, l in enumerate(lines):
        m = HDR.match(l)
        if m:
            headers.append((i, m.group(2) or "<anonymous>"))

    def owner(idx):
        lo, hi, best = 0, len(headers) - 1, None
        while lo <= hi:
            mid = (lo + hi) // 2
            if headers[mid][0] <= idx:
                best = headers[mid]
                lo = mid + 1
            else:
                hi = mid - 1
        return best

    hits = {}
    orphans = []
    for i, l in enumerate(lines):
        for _ in SORRY.finditer(l):
            o = owner(i)
            if o is None:
                orphans.append(i + 1)
            else:
                hits.setdefault(o, []).append(i + 1)
    return hits, orphans


def main():
    targets = sys.argv[1:] or ["Fermat"]
    files = []
    for t in targets:
        p = (ROOT / t) if not Path(t).is_absolute() else Path(t)
        files += sorted(p.rglob("*.lean")) if p.is_dir() else [p]

    total_decls = total_tokens = 0
    hidden = []
    for f in files:
        hits, orphans = scan(f)
        for (hline, name), lns in hits.items():
            total_decls += 1
            total_tokens += len(lns)
            if len(lns) > 1:
                hidden.append((f, hline + 1, name, lns))
        for o in orphans:
            hidden.append((f, o, "<OUTSIDE ANY DECLARATION>", [o]))

    hidden.sort(key=lambda r: -len(r[3]))
    print(f"files scanned            : {len(files)}")
    print(f"sorried declarations     : {total_decls}   <- what the warning set reports")
    print(f"sorry TOKENS             : {total_tokens}")
    print(f"HIDDEN (tokens - decls)  : {total_tokens - total_decls}"
          f"   <- obligations no frontier scan can see\n")
    if not hidden:
        print("No declaration holds more than one sorry. Nothing is hidden.")
        return
    for f, hline, name, lns in hidden:
        rel = f.relative_to(ROOT) if str(f).startswith(str(ROOT)) else f
        print(f"{len(lns)}x  {rel}:{hline}  {name}")
        print(f"      sorries at lines: {', '.join(map(str, lns))}")


main()
