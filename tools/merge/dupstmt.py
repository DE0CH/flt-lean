#!/usr/bin/env python3
"""Find DUPLICATE LEAVES: two sorried declarations with different NAMES and the
same STATEMENT.

Why this exists, and why `xdup.py` cannot do it.  `xdup.py` and `checks.py
check-dup` answer "is one NAME declared twice".  They are the right check for the
merge damage they were written for, and they are structurally blind to the
failure this script catches: two agents cut the same node under two different
names, so the tree carries one theorem as two open leaves.  Every instrument then
reports it as ordinary work --

  * `lake build` emits a `declaration uses 'sorry'` warning for each, truthfully;
  * a frontier scan counts two leaves, because there are two `sorry` bodies;
  * the ownership tests pass, because nobody is working on either;
  * `check-dup`/`xdup` are silent, because the names differ.

-- and the frontier goes UP while the mathematics stands still.  Measured
instance (2026-07-31, `ModularCurve/X0.lean` at merger `9e7f6e4b`):
`isNormalDimOne_rigidifiedModuliData_specF` and
`isReduced_isIntegrallyClosed_ringKrullDim_of_rigidifiedModuliData_specF` were
the same statement ~980 lines apart, differing only in how the `N n l : Nat`
binders were GROUPED, and the second-cut one had no consumer at all.  A prover
was dispatched at it.

Normalisation, and what it is allowed to ignore.  We compare the declaration's
full text minus its name: binder-name cosmetics (a leading `_`, which this
project adds and removes as a hypothesis becomes used or unused), whitespace and
line breaks, and binder GROUPING -- `(N n : Nat)` against `(N : Nat) (n : Nat)`.
Everything else is significant, so a genuine difference in a hypothesis or a
conjunct keeps two leaves apart.  Grouping is normalised by expanding every
`(a b c : T)` into `(a : T) (b : T) (c : T)`.

Usage:
    tools/merge/dupstmt.py                    # whole tree under Fermat/
    tools/merge/dupstmt.py path/to/File.lean  # one file
    tools/merge/dupstmt.py --all              # not just sorried decls

Exit status is 1 if any duplicate group was found, else 0.
"""

import re
import sys
import pathlib
from collections import defaultdict

DECL = re.compile(
    r'^(?:@\[[^\]]*\]\s*)*'
    r'(?:private\s+|protected\s+|noncomputable\s+|partial\s+)*'
    r'(theorem|lemma)\s+([^\s({\[:]+)'
)
# a line that opens a new top-level block and therefore ENDS the previous decl
BOUNDARY = re.compile(
    r'^(?:@\[|/--|/-!|/-|theorem\b|lemma\b|def\b|abbrev\b|structure\b|class\b|'
    r'instance\b|inductive\b|namespace\b|end\b|section\b|variable\b|open\b|'
    r'noncomputable\b|private\b|protected\b|set_option\b|omit\b|attribute\b|'
    r'universe\b|import\b|macro\b|syntax\b|notation\b|declare_\w+\b|deriving\b)'
)


def strip_comments(lines):
    """Line-granular block-comment stripping, per the release-26 note: a block
    starts at a line whose first token is `/-` and ends at a line containing
    `-/`.  Character-level nesting goes wrong on this tree's prose docstrings."""
    out, depth = [], 0
    for i, line in enumerate(lines, 1):
        s = line.lstrip()
        if depth == 0 and (s.startswith('/-')):
            # single-line block comment?
            if '-/' in line[line.index('/-') + 2:]:
                out.append((i, ''))
                continue
            depth = 1
            out.append((i, ''))
            continue
        if depth > 0:
            if '-/' in line:
                depth = 0
            out.append((i, ''))
            continue
        out.append((i, line.split('--')[0] if line.lstrip().startswith('--') else line))
    return out


def expand_binders(text):
    """`(N n l : Nat)` -> `(N : Nat) (n : Nat) (l : Nat)`, and the same for
    `{..}` and `[..]`, so binder GROUPING stops being significant."""
    def one(m):
        op, body, cl = m.group(1), m.group(2), m.group(3)
        if ':' not in body:
            return m.group(0)
        names, _, ty = body.partition(':')
        names = names.split()
        if len(names) <= 1 or any(not re.match(r'^[^\s:()\[\]{}]+$', n) for n in names):
            return m.group(0)
        return ' '.join(f'{op}{n} :{ty}{cl}' for n in names)
    # non-nested binder groups only; good enough and never merges distinct types
    return re.sub(r'([(\{\[])([^()\[\]{}]*)([)\}\]])', one, text)


def normalise(name, text):
    t = text
    t = re.sub(r'\b' + re.escape(name) + r'\b', 'SELF', t)
    t = expand_binders(t)
    t = re.sub(r'(?<![\w.])_+(?=[A-Za-z])', '', t)   # drop leading _ on identifiers
    t = re.sub(r'\s+', ' ', t).strip()
    return t


def split_binders(norm):
    """Split a normalised declaration into (list of binder groups, conclusion).

    Walks the header at bracket depth 0 and stops at the `:` that introduces the
    statement.  Returns (None, None) if that `:` cannot be located, so the caller
    can fall back to exact comparison rather than guess.
    """
    if not norm.startswith('theorem SELF') and not norm.startswith('lemma SELF'):
        return None, None
    i = norm.index('SELF') + 4
    binders, depth, cur = [], 0, ''
    while i < len(norm):
        c = norm[i]
        if depth == 0 and c == ':':
            return binders, norm[i + 1:].strip()
        if c in '([{':
            if depth == 0:
                cur = ''
            depth += 1
            if depth == 1:
                i += 1
                continue
        elif c in ')]}':
            depth -= 1
            if depth == 0:
                binders.append(cur.strip())
                i += 1
                continue
        if depth >= 1:
            cur += c
        i += 1
    return None, None


def reorder_key(norm):
    """A key that additionally ignores the ORDER of the binders.

    Reordering independent binders is a real way for one node to be cut twice --
    it is exactly how the 2026-07-31 X0 duplicate hid, `(N n l : Nat) (hN) ...`
    against `(N : Nat) (hN) (n l : Nat) ...`.  This is a REVIEW signal, not an
    error: reordering is only sound when the moved binders are independent, so a
    hit has to be read before it is acted on.
    """
    binders, concl = split_binders(norm)
    if binders is None or not concl:
        return None
    return (tuple(sorted(binders)), concl)


def decls(path):
    raw = pathlib.Path(path).read_text().split('\n')
    stripped = strip_comments(raw)
    out, cur = [], None
    for i, line in stripped:
        if cur is not None and line.strip() and BOUNDARY.match(line) and i != cur['line']:
            cur['text'] = '\n'.join(cur['buf'])
            out.append(cur)
            cur = None
        m = DECL.match(line)
        if m:
            cur = {'kind': m.group(1), 'name': m.group(2), 'line': i,
                   'file': str(path), 'buf': [line]}
            continue
        if cur is not None:
            cur['buf'].append(line)
    if cur is not None:
        cur['text'] = '\n'.join(cur['buf'])
        out.append(cur)
    for d in out:
        d['sorried'] = re.search(r'(?<![\w.])sorry(?![\w.])', d['text']) is not None
        d['norm'] = normalise(d['name'], d['text'])
    return out


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    only_sorried = '--all' not in sys.argv[1:]
    if args:
        files = [pathlib.Path(a) for a in args]
    else:
        files = sorted(pathlib.Path('Fermat').rglob('*.lean'))

    groups, rgroups = defaultdict(list), defaultdict(list)
    for f in files:
        try:
            for d in decls(f):
                if only_sorried and not d['sorried']:
                    continue
                if len(d['norm']) < 40:      # too short to be a meaningful match
                    continue
                groups[d['norm']].append(d)
                rk = reorder_key(d['norm'])
                if rk is not None:
                    rgroups[rk].append(d)
        except Exception as e:                # a scanner bug must not read as "clean"
            print(f'ERROR scanning {f}: {e}', file=sys.stderr)
            return 2

    def report(tag, gs, seen):
        n = 0
        for key, ds in sorted(gs.items(), key=lambda kv: -len(kv[1])):
            names = {d['name'] for d in ds}
            if len(ds) < 2 or len(names) < 2:
                continue
            if frozenset(names) in seen:
                continue
            seen.add(frozenset(names))
            n += 1
            print(f'{tag}  {len(ds)} declarations share one statement:')
            for d in ds:
                print(f'    {d["file"]}:{d["line"]}  {d["name"]}')
            sample = ds[0]['norm']
            print(f'    normalised: {sample[:200]}{"..." if len(sample) > 200 else ""}')
            print()
        return n

    seen = set()
    found = report('DUP-STMT ', groups, seen)
    found_r = report('DUP-STMT-REORDER (review: sound only if the moved binders '
                     'are independent)', rgroups, seen)

    scope = 'sorried' if only_sorried else 'all'
    print(f'scanned {len(files)} file(s), {scope} declarations; '
          f'{found} exact + {found_r} reordered duplicate-statement group(s)')
    return 1 if (found or found_r) else 0


if __name__ == '__main__':
    sys.exit(main())
