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

THREE KEYS, in decreasing strength, reported separately because they carry
different amounts of evidence:

  DUP-STMT          exact after the normalisation above -- an error;
  DUP-STMT-REORDER  additionally ignores the ORDER of the binders -- review;
  DUP-STMT-ALPHA    additionally ignores their NAMES and the KIND of their
                    brackets -- review, and the noisiest.

The third was added 2026-07-31 after the first two BOTH missed a live pair:
`relPicEquiv_of_locally_relPicEquiv` and `relPicEquiv_of_forall_restrict` in
`ModularCurve/RelativePicard.lean` are one theorem cut twice a day apart and
kept by a merge, differing only by `{L L'}` against `(A B)`, `_hL/_hloc`
against `_hA/_hcov`, and one implicit-vs-explicit `strX`.  The second had ZERO
code consumers and a queued task naming it.  Calibration on the tree of
2026-07-31: with that pair present the alpha key reports it and NOTHING else,
so `0 exact + 0 reordered + 0 alpha` is the state to expect from a clean tree.

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


IDENT = re.compile(r"(?<![\w.'])([A-Za-z_][A-Za-z0-9_'!?]*)")
# `∀ t : T,` / `∃ U,` / `fun z =>` — a variable bound INSIDE a type, which the
# positional renaming of the TOP-LEVEL binders cannot reach.  Measured
# 2026-07-31: the two `RelativePicard.lean` copies of the Zariski-sheaf leaf
# agreed under `alpha_key` in every component except `∀ t : T` against
# `∀ x : T`, so without this the key still misses them by one character.
LOCALBIND = re.compile(
    r"(?:∀|∃|fun|λ|Σ|∑|⨆|⨅|⋃|⋂)\s+((?:[A-Za-z_][A-Za-z0-9_'!?]*\s*)+)(?=[:,]|=>)")


def local_alpha(s, start=0):
    """Rename variables bound inside `s` by `∀`/`∃`/`fun`/… to `b0, b1, …`, in
    order of first binding.  A heuristic, and deliberately so: it is only ever
    used for the WEAKEST of the three keys, whose hits are review signals."""
    sub, n = {}, start
    for m in LOCALBIND.finditer(s):
        for nm in m.group(1).split():
            if nm not in sub:
                sub[nm] = f'b{n}'
                n += 1
    if not sub:
        return s
    return IDENT.sub(lambda m: sub.get(m.group(1), m.group(1)), s)


def alpha_key(norm):
    """A key that additionally ignores the NAMES of the binders and the KIND of
    the brackets around them.

    Measured 2026-07-31, `ModularCurve/RelativePicard.lean`:
    `relPicEquiv_of_locally_relPicEquiv` and `relPicEquiv_of_forall_restrict`
    are one theorem cut twice a day apart, and BOTH keys above miss them,
    because the two copies differ by an alpha-renaming of the binders
    (`{L L'}` against `(A B)`, `_hL/_hL'/_hloc` against `_hA/_hB/_hcov`) rather
    than by grouping.  `split_binders` has already thrown the brackets away, so
    explicit-vs-implicit is free here; renaming positionally is the rest.

    This is the WEAKEST of the three keys and therefore the noisiest: two
    genuinely different theorems whose statements differ only in the names of
    their variables are, after all, the same statement, and in a tree with many
    parallel `X`/`X'` developments that can be a legitimate pair.  Read the hit;
    do not act on it unread.
    """
    binders, concl = split_binders(norm)
    if binders is None or not concl:
        return None
    sub, shape = {}, []
    for b in binders:
        head, sep, ty = b.partition(':')
        names = head.split() if sep else []
        if names and all(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'!?]*", n) for n in names):
            slots = []
            for n in names:
                sub.setdefault(n, f'v{len(sub)}')
                slots.append(sub[n])
            shape.append((tuple(slots), ty.strip()))
        else:
            # instance-implicit and anonymous binders: no name to rename
            shape.append(((), b.strip()))

    def ren(s):
        return local_alpha(IDENT.sub(lambda m: sub.get(m.group(1), m.group(1)), s))

    return (tuple((slots, ren(ty)) for slots, ty in shape), ren(concl))


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

    groups, rgroups, agroups = (defaultdict(list), defaultdict(list),
                                defaultdict(list))
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
                ak = alpha_key(d['norm'])
                if ak is not None:
                    agroups[ak].append(d)
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
    found_a = report('DUP-STMT-ALPHA (review: same statement up to RENAMING the '
                     'binders; the weakest key, read before acting)', agroups, seen)

    scope = 'sorried' if only_sorried else 'all'
    print(f'scanned {len(files)} file(s), {scope} declarations; '
          f'{found} exact + {found_r} reordered + {found_a} alpha-renamed '
          f'duplicate-statement group(s)')
    return 1 if (found or found_r or found_a) else 0


if __name__ == '__main__':
    sys.exit(main())
