#!/usr/bin/env python3
"""Find SORRIED declarations that nothing in the tree consumes.

WHY THIS EXISTS
===============

A leaf can be open, compile, emit its `declaration uses 'sorry'` warning, pass the
three-part ownership test and survive `leafstat.py` -- and still be worth NOTHING to
close, because no proof term in the project reaches it.  Closing it moves the count
and not the project, and until somebody deletes it it keeps drawing dispatches.

CLAUDE.md calls this the seventh invisibility class.  Every frontier instrument we
have answers "is this leaf OPEN".  None answers "does anything USE it".  This does.

The commonest way orphans are manufactured is a node cut twice (or three times) by
concurrent branches: each cut lands, each re-points the parent, the merge keeps ONE
parent body, and the losing cuts' residues stay in the file as ordinary-looking open
leaves.  See the `flt-lean-93` section in CLAUDE.md for a worked three-way instance in
`ModularCurve/X0.lean` -- three sorries in one 300-line block, of which two were dead,
and each of the three docstrings claimed to be the live one.

    tools/merge/orphanleaf.py                 # whole tree, working copy
    tools/merge/orphanleaf.py --root DIR      # another checkout
    tools/merge/orphanleaf.py --file F.lean   # restrict the REPORT to one file
                                              # (the SCAN is always tree-wide --
                                              #  a consumer may live anywhere)

Exit status is 0 always: this is a REVIEW list, not a gate.  Every hit needs one
human read before anything is deleted (see CAVEATS).

TWO BUGS THIS HAS ALREADY HAD, both of which make it under- or over-report silently;
if you touch the matching code, re-check them:

  1. DOT NOTATION.  `X.foo` is reached as `h.foo`, so a consumer never contains the
     qualified name.  Matching must be on the LAST COMPONENT, and the regex must NOT
     have `.` in its negative lookbehind -- with `.` there, every dot-notation call
     site is invisible and half the tree looks orphaned.
  2. EXPLICIT UNIVERSE PARAMETERS.  `theorem foo.{u, v} ...` makes a naive name regex
     capture `foo.{u,`, whose last component is `{u,` and which matches nothing.  Ten
     `Patching.lean` declarations were reported as orphans for exactly this reason.
     (`tools/merge/frontier.py` has the same trap, recorded in CLAUDE.md.)

CAVEATS -- read before deleting anything
========================================

* This is a TOKEN scan over comment-stripped source, so it is a heuristic in both
  directions.  It cannot see a name reached only through `simp`/`aesop`/instance
  search, and it counts a name that merely appears in a `variable` line.
* A hit is a CANDIDATE.  Confirm with `grep -n` and by reading the parent's PROOF
  BODY -- never its docstring, which is what is wrong in these cases.
* An orphan is not automatically deletable.  Prefer, in order: (a) if a rival cut won,
  make the loser a corollary of the winner and then delete it, folding its analysis
  into the winner's docstring -- the analysis is usually the valuable part; (b) if the
  parent was re-routed by mistake, restore the consumption; (c) delete.
  Do NOT delete a leaf that has a live owner (`own.py`).
* Free-floating PROVEN declarations are a different (also forbidden) thing and are not
  reported here; `ProgressCensus.lean`'s `floating` field is what sees those.
"""

import argparse
import os
import re
import subprocess
import sys

DECL = re.compile(r'^(?:noncomputable\s+|private\s+|protected\s+|partial\s+)*'
                  r'(theorem|lemma|def|abbrev|structure|instance)\s+(\S+)')


def strip_comments(text: str) -> str:
    """Blank out `--` line comments and NESTED `/- -/` blocks, preserving line count."""
    out = []
    i, n, depth = 0, len(text), 0
    while i < n:
        if depth == 0 and text.startswith('--', i):
            j = text.find('\n', i)
            j = n if j < 0 else j
            out.append(' ' * (j - i))
            i = j
            continue
        if text.startswith('/-', i):
            depth += 1
            out.append('  ')
            i += 2
            continue
        if text.startswith('-/', i) and depth > 0:
            depth -= 1
            out.append('  ')
            i += 2
            continue
        out.append(' ' if (depth > 0 and text[i] != '\n') else text[i])
        i += 1
    return ''.join(out)


def decl_name(raw: str) -> str:
    """`foo.{u, v}` -> `foo`.  See bug 2 in the module docstring."""
    return raw.split('.{')[0].rstrip('.')


def lean_files(root: str):
    try:
        out = subprocess.run(['git', 'ls-files', 'Fermat'], cwd=root,
                             capture_output=True, text=True, check=True).stdout.split()
    except Exception:
        out = []
        for d, _, fs in os.walk(os.path.join(root, 'Fermat')):
            for f in fs:
                out.append(os.path.relpath(os.path.join(d, f), root))
    # SorryGate.lean contains the token `sorry` inside a STRING LITERAL in its `elab`.
    return [f for f in out if f.endswith('.lean') and not f.endswith('SorryGate.lean')]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--root', default=os.path.dirname(
        os.path.dirname(os.path.dirname(os.path.abspath(__file__)))),
        help='repository root (default: the repo this script lives in -- NOT a '
             'hardcoded staging path; see CLAUDE.md on tools that hardcode one)')
    ap.add_argument('--file', action='append', default=[],
                    help='restrict the REPORT to these files; the scan stays tree-wide')
    args = ap.parse_args()
    root = args.root

    files = lean_files(root)
    if not files:
        print(f'no Lean files under {root}/Fermat', file=sys.stderr)
        return 0

    stripped, sorried = {}, []
    for f in files:
        try:
            txt = strip_comments(open(os.path.join(root, f), encoding='utf-8').read())
        except Exception:
            continue
        stripped[f] = txt
        lines = txt.split('\n')
        decls = [(i, decl_name(m.group(2)))
                 for i, l in enumerate(lines, 1) if (m := DECL.match(l))]
        for k, (i, name) in enumerate(decls):
            end = decls[k + 1][0] - 1 if k + 1 < len(decls) else len(lines)
            if re.search(r'\bsorry\b', '\n'.join(lines[i - 1:end])):
                sorried.append((f, i, name))

    # Pre-filter, so the expensive regex runs on a handful of files rather than all of
    # them (378 leaves x 400 files of raw regex is ~25 minutes; this is ~1).
    #
    # THE PRE-FILTER IS WHERE THE THIRD BUG WAS.  Tokenising on "alnum or _ ' ." makes
    # `foo.{u, v}` yield the token `foo.` -- with a TRAILING DOT -- which equals
    # neither `foo` nor anything ending in `.foo`, so every declaration with explicit
    # universe parameters was filtered out of its own consumers' files and reported as
    # an orphan.  Stripping trailing dots when building the set is the fix; if you
    # touch this, re-check `exists_traceGenerated_auxDeformationDatum`, which IS
    # consumed (`Patching.lean`) via `name.{uK, uW, uR}`.
    def tokens(text: str):
        out, cur = set(), []
        for ch in text:
            if ch.isalnum() or ch in "_'.":
                cur.append(ch)
            elif cur:
                out.add(''.join(cur).strip('.'))
                cur = []
        if cur:
            out.add(''.join(cur).strip('.'))
        # also index every dotted suffix, so `h.foo` is found when looking for `foo`
        return out | {t.split('.')[-1] for t in out if '.' in t}

    tokset = {f: tokens(t) for f, t in stripped.items()}

    orphans = []
    for f, i, name in sorried:
        last = name.split('.')[-1]
        # NOTE: no `.` in the lookbehind -- that is what makes dot notation visible.
        pat = re.compile(r"(?<![A-Za-z0-9_'])" + re.escape(last) + r"(?![A-Za-z0-9_'])")
        uses = 0
        for g, txt in stripped.items():
            if last not in tokset[g]:
                continue
            c = len(pat.findall(txt))
            if g == f:
                c -= 1              # its own declaration line
            uses += max(c, 0)
            if uses:
                break
        if uses == 0:
            orphans.append((f, i, name))

    keep = set(args.file)
    shown = [o for o in orphans if not keep or o[0] in keep]
    print(f'sorried declarations scanned : {len(sorried)}')
    print(f'ORPHAN CANDIDATES (no code use anywhere outside their own declaration): '
          f'{len(orphans)}')
    if keep:
        print(f'  (reporting {len(shown)} in the {len(keep)} requested file(s))')
    for f, i, n in sorted(shown):
        print(f'  {f}:{i}  {n}')
    if shown:
        print('\nEach hit is a CANDIDATE -- read the module docstring of this script '
              'before deleting anything.')
    return 0


if __name__ == '__main__':
    sys.exit(main())
