#!/usr/bin/env python3
"""Print the namespace/section OPEN-CLOSE PAIRING of a Lean file, and flag orphans.

Why this exists, and why it is not `scopecheck.py`
--------------------------------------------------
`scopecheck.py` answers "is this file's scope nesting suspicious", over-reports by
design (~167 hits on a green tree), and must be differenced against a baseline.
This script answers a different and sharper question: **which opener does each
`end` actually close?**  That is what identifies a LOST OPENER, because the
symptom of one is not an imbalance at the end of the file — it is every later
`end` closing the WRONG thing, silently, until the last one has nothing left.

Release 34 had four red modules and three of them were exactly this.  In none of
them did the compiler mention a scope: a lost `section Slices` + its
`variable {σ} {R} [CommRing R]` reported as 64 x `failed to synthesize Semiring R`,
and a lost `open CategoryTheory` reported as `expected token` at the column of a
`≫`.  See CLAUDE.md, "A LOST SCOPE LINE REPORTS AS A TYPE ERROR".

Usage
-----
    tools/merge/scopepair.py <path>                    # working tree
    tools/merge/scopepair.py <rev>:<path>              # any git revision
    tools/merge/scopepair.py --quiet <path>            # orphans/unclosed only

Diagnostic use: print the pairing for the merged file AND for each contributing
branch (the ones whose line count differs from main's).  The branch that balances
is the one whose structure the merge should have preserved, and the first line at
which the two pairings disagree is the insertion point.

Note on the vocabulary
----------------------
`@[expose] public noncomputable section` does not start with `section`, and every
file in this tree opens with one.  A scan keyed on `startswith('section ')`
therefore reports one orphan close per file and you will learn to ignore the
output.  This matches the section TOKEN anywhere in the leading modifier run, so
a clean file reports nothing at all.
"""
import re, subprocess, sys

OPEN = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|public|noncomputable|scoped|partial|unsafe)\s+)*(namespace|section)\b(.*)$')
CLOSE = re.compile(r'^end\b(.*)$')

def load(src):
    if ':' in src and not src.startswith('/') and not src.startswith('.'):
        r = subprocess.run(['git', 'show', src], capture_output=True, text=True)
        if r.returncode:
            sys.exit(f"scopepair: cannot read {src}")
        return r.stdout.split('\n')
    with open(src) as fh:
        return fh.read().split('\n')

def mask(lines):
    """Blank out block-comment and line-comment content, PRESERVING line count."""
    out, depth = [], 0
    for line in lines:
        buf, i = '', 0
        while i < len(line):
            if depth == 0 and line.startswith('--', i):
                break
            if line.startswith('/-', i):
                depth += 1; i += 2; continue
            if line.startswith('-/', i) and depth > 0:
                depth -= 1; i += 2; continue
            if depth == 0:
                buf += line[i]
            i += 1
        out.append(buf)
    return out

def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    quiet = '--quiet' in sys.argv
    if len(args) != 1:
        sys.exit(__doc__)
    lines = mask(load(args[0]))
    stack, bad = [], 0
    for i, line in enumerate(lines, 1):
        s = line.strip()
        m = OPEN.match(s)
        if m:
            rest = m.group(2).strip()
            nm = rest.split()[0] if rest else ''
            # `namespace A.B.C` opens THREE nested scopes and may be closed in
            # pieces from the right (`end C`, then `end A.B`).  Push one frame per
            # component so the pairing is faithful.
            if m.group(1) == 'namespace' and '.' in nm:
                parts = nm.split('.')
                for k, part in enumerate(parts):
                    stack.append((i, s if k == len(parts) - 1 else f'namespace {part}', part))
            else:
                stack.append((i, s, nm))
            continue
        m = CLOSE.match(s)
        if m:
            name = m.group(1).strip()
            if not stack:
                print(f"  ORPHAN CLOSE {i}: {s!r}"); bad += 1; continue
            oi, os_, oname = stack.pop()
            # `end A.B` closes `namespace A` then `namespace B` (Lean allows one
            # dotted `end` to close several nested namespaces), so peel from the right.
            while name and oname and name != oname and name.endswith('.' + oname) and stack:
                name = name[:-(len(oname) + 1)]
                oi, os_, oname = stack.pop()
            flag = '' if (name == oname or (not name and not oname)) else '   <== MISMATCHED NAME'
            if flag: bad += 1
            if not quiet or flag:
                print(f"  {i}: {s!r:38} <- {oi}: {os_!r}{flag}")
    for i, s, nm in stack:
        # An anonymous `section` left open at EOF is legal: Lean closes it for you,
        # and every module in this tree opens with `@[expose] public section`.
        # A NAMED scope left open is always a wound.
        if not nm:
            continue
        print(f"  UNCLOSED {i}: {s!r}"); bad += 1
    sys.exit(1 if bad else 0)

if __name__ == '__main__':
    main()
