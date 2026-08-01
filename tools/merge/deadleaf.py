#!/usr/bin/env python3
"""Report sorried declarations that NOTHING IN THE TREE CONSUMES.

A leaf with no consumer is worth nothing to close: proving it moves the frontier
count and moves the project not at all.  Worse, it keeps drawing dispatches --
every such leaf is a phantom task waiting to be issued, and one of them issued
the task that produced this script (`exists_chartAtInfinity_of_finite_toAffineLine`,
deleted 2026-08-01; see CLAUDE.md, "WHEN BOTH RIVAL ROOTS ARE STILL OPEN").

NO OTHER INSTRUMENT SEES THIS.  The declaration is open, so `lake build` emits its
`declaration uses 'sorry'` warning truthfully; a source scan finds the token; the
frontier scans count it; `own.py` and `leafstat.py` correctly report it unowned.
Every one of them answers "is this leaf open", and none answers "does anything
reach it".

## Usage

    python3 tools/merge/deadleaf.py                # whole tree, repo-relative
    python3 tools/merge/deadleaf.py --root DIR     # another checkout
    python3 tools/merge/deadleaf.py --verbose      # also print live leaves' hit counts

ROOT defaults to the repository this script lives in -- NOT to a hardcoded
staging path.  (Three scanners in this repo have shipped with `ROOT` pinned to
`/home/chend/flt-staging`, which silently reports the merge worker's tree with
its line numbers; see CLAUDE.md.  Do not reintroduce that.)

## How it decides

Comment-strip every `.lean` file under `Fermat/` (nested block comments and line
comments, blanked out so line numbers are preserved), attribute each surviving
`sorry` token to the nearest declaration header ABOVE it, then search the whole
stripped tree for the declaration's LAST NAME COMPONENT, preceded by anything
that is not an identifier character (so `Foo.bar`, `h.bar` and bare `bar` all
count) and followed by a non-identifier character.  Its own declaration line is
excluded.  Zero hits => reported.

## Reading the output -- three things it is NOT

* **"No consumer" is not "delete it".**  A cut that lands before its parent is
  rewired legitimately has no consumer for a while, and a leaf at the top of its
  own subtree may be waiting for glue somebody is writing.  The report is a list
  of things to CHECK, not a work order.  Check the parent's proof body first:
  if the parent is PROVEN and its body names a DIFFERENT leaf, you have a rival
  cut and this leaf lost it.
* **When it IS a rival-cut orphan, deletion is not automatic either.**  Compare
  the two roots: keep the arrangement whose root is IMPLIED by the rival's root,
  so the tree owes the weaker obligation.  If the loser is strictly stronger and
  the winner is itself open, it cannot be demoted to a proven corollary and
  deletion is right; salvage its docstring analysis onto the survivor first.
* **It UNDER-reports, deliberately.**  Matching is by last name component, so a
  dead `Foo.bar` is called live if any unrelated `Bar.bar` is used anywhere.
  That is the safe direction: a false "live" costs nothing, a false "dead"
  invites a wrong deletion.

## Calibration (2026-08-01, at the release-33 tree)

378 sorried declarations, **36** with zero code consumers.  The run independently
rediscovers two orphans CLAUDE.md documents from earlier tasks --
`map_add_relPointWeierstrassEquiv` (`ModularCurve/X1.lean`, the semantic-merge
orphan of `flt-lean-113`) and `exists_pow_Pz_mul_mem_idl`
(`Mathlib/.../ProjectiveEquationAdd2.lean`, the duplicated-cut pair) -- which is
the check that it works.  **Re-run this calibration whenever you touch the
script**; a scanner that reports nothing is indistinguishable from a scanner that
is broken.
"""

import argparse
import os
import re
import subprocess
import sys

DECL = re.compile(
    r'^(?:@\[[^\]]*\]\s*)?'
    r'(?:private\s+|protected\s+|noncomputable\s+|public\s+|scoped\s+|partial\s+|unsafe\s+)*'
    r'(theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s\(\{\[:]+)'
)
SORRY = re.compile(r"(^|[^A-Za-z0-9_.'])sorry([^A-Za-z0-9_']|$)")


def strip_comments(text: str) -> str:
    """Blank out Lean comments, preserving every newline so line numbers survive.

    Block comments NEST in Lean, so this tracks depth rather than scanning for the
    first terminator; a line comment only starts a comment at depth 0.
    """
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
        c = text[i]
        out.append(' ' if (depth > 0 and c != '\n') else c)
        i += 1
    return ''.join(out)


def repo_root() -> str:
    here = os.path.dirname(os.path.abspath(__file__))
    try:
        return subprocess.run(['git', '-C', here, 'rev-parse', '--show-toplevel'],
                              capture_output=True, text=True, check=True).stdout.strip()
    except Exception:
        return os.path.abspath(os.path.join(here, '..', '..'))


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--root', default=None, help='repository root (default: this script\'s repo)')
    ap.add_argument('--verbose', action='store_true', help='also print consumer counts for live leaves')
    args = ap.parse_args()

    root = args.root or repo_root()
    base = os.path.join(root, 'Fermat')
    if not os.path.isdir(base):
        print(f'deadleaf: no Fermat/ under {root}', file=sys.stderr)
        return 2

    files = []
    for d, _, fs in os.walk(base):
        for f in fs:
            if f.endswith('.lean'):
                files.append(os.path.relpath(os.path.join(d, f), root))
    files.sort()

    stripped = {}
    for f in files:
        with open(os.path.join(root, f), encoding='utf-8') as fh:
            stripped[f] = strip_comments(fh.read()).split('\n')

    # (file, 1-indexed line, name) for each declaration whose body contains a sorry
    leaves, seen = [], set()
    for f in files:
        lines = stripped[f]
        decls = []
        for i, line in enumerate(lines):
            m = DECL.match(line)
            if m and m.group(2):
                decls.append((i, m.group(2)))
        for i, line in enumerate(lines):
            if not SORRY.search(line):
                continue
            owner = [d for d in decls if d[0] <= i]
            if not owner:
                continue
            name = owner[-1][1]
            if name in seen:
                continue
            seen.add(name)
            leaves.append((f, owner[-1][0] + 1, name))

    dead = []
    for (f, ln, name) in leaves:
        short = name.split('.')[-1]
        if len(short) < 4:      # too short to match reliably; treat as live
            continue
        pat = re.compile(r"(^|[^A-Za-z0-9_'])" + re.escape(short) + r"([^A-Za-z0-9_']|$)")
        hits = 0
        for g in files:
            for j, line in enumerate(stripped[g], 1):
                if g == f and j == ln:
                    continue
                if pat.search(line):
                    hits += 1
        if hits == 0:
            dead.append((f, ln, name))
        elif args.verbose:
            print(f'live {hits:5d}  {f}:{ln}  {name}')

    print(f'sorried declarations: {len(leaves)}')
    print(f'\n=== SORRIED DECLARATIONS WITH ZERO CODE CONSUMERS ({len(dead)}) ===')
    for f, ln, name in dead:
        print(f'{f}:{ln}  {name}')
    print('\nEach is a leaf whose closure would move the count and not the project.'
          '\nCheck the parent\'s PROOF BODY before acting: a proven parent naming a'
          '\ndifferent leaf means a rival cut landed and this one lost.')
    return 0


if __name__ == '__main__':
    sys.exit(main())
