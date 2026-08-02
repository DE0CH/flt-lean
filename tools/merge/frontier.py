#!/usr/bin/env python3
"""Direct-sorry frontier: strip comments, then attribute each `sorry` token to the
nearest declaration header ABOVE it. Emits `file<TAB>line<TAB>qualified-name`."""
import re, pathlib, sys, collections
# ROOT used to be hardcoded to `/home/chend/flt-staging`, the merge worker's
# worktree.  Run from anywhere else that silently scanned a DIFFERENT tree and
# printed ITS counts and ITS line numbers under repo-relative paths, so the
# output was indistinguishable from a scan of your own worktree — measured
# 2026-07-31 in flt-lean-281, where it reported an unchanged count across an
# edit that the compiler said added a leaf.  Same defect the memory note
# `flt-hidden-sorries-scans-main-repo` records for its sibling script.
# Default to the repository this file lives in; `--root DIR` overrides.
# `--root` is read FIRST: `parents[2]` raises IndexError for a copy of this
# script placed anywhere shallower than `<repo>/tools/merge/`, and it used to be
# evaluated unconditionally, so `--root` could not rescue it.
if '--root' in sys.argv:
    ROOT = pathlib.Path(sys.argv[sys.argv.index('--root') + 1]).resolve()
else:
    ROOT = pathlib.Path(__file__).resolve().parents[2]
# IDENTIFIER CLASS.  `Ͱ-Ͽ` (Greek, U+0370-U+03FF) was MISSING until 2026-08-01
# and this tree names declarations with Greek constantly (`preΨ`, `χA`, `Δ`,
# `isOfFinOrder_χ`).  A missing range does not merely mangle a name, it fails in
# two distinct ways: a name that BEGINS with Greek makes the whole line fail to
# match, so every `sorry` under it is attributed to the PREVIOUS declaration --
# i.e. a proven theorem is reported as the leaf and the real leaf is invisible;
# and a name that merely CONTAINS Greek is TRUNCATED at it, so no queue entry
# naming the true declaration can ever match the frontier row and the leaf reads
# as permanently uncovered.  Measured on 2026-08-01: 413 declarations tree-wide
# were affected, 6 of them open leaves.  Keep this class in sync with
# `dupstmt.py`/`gentask.py`; do NOT widen it to `À-￿`, which swallows the
# bracket characters `⟨⟩←▸` (see the memory note
# `lean-identifier-regex-swallows-brackets`).
DECL = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|public\s+|local\s+|scoped\s+)*'
    r'(theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|example)\s+'
    r"([A-Za-z_À-ɏͰ-Ͽᴀ-ᶿ℀-⅏][A-Za-z0-9_À-ɏͰ-Ͽᴀ-ᶿ₀-ₜ⁰-ⁿ℀-⅏.'!?]*)")
NS = re.compile(r'^\s*namespace\s+(\S+)')
ENDNS = re.compile(r'^\s*end\s*(\S*)\s*$')
SORRY = re.compile(r"(?<![A-Za-z0-9_'])sorry(?![A-Za-z0-9_'])")

def strip(lines):
    out, depth = [], 0
    for ln in lines:
        s = ln.strip()
        if depth == 0:
            if s.startswith('/-'):
                depth += 1
                if '-/' in ln[ln.index('/-')+2:]: depth -= 1
                out.append(''); continue
            if s.startswith('--'): out.append(''); continue
            # strip a trailing line comment
            k = ln.find('--')
            out.append(ln[:k] if k >= 0 and '"' not in ln[:k] else ln)
        else:
            if '-/' in ln: depth -= 1
            out.append('')
    return out

res = []
for p in sorted(ROOT.glob('Fermat/**/*.lean')):
    lines = p.read_text(encoding='utf-8', errors='replace').split('\n')
    code = strip(lines)
    heads, stack = [], []
    for i, ln in enumerate(code):
        m = NS.match(ln)
        if m: stack.append(m.group(1)); continue
        m = ENDNS.match(ln)
        if m:
            if stack and (not m.group(1) or m.group(1) == stack[-1]): stack.pop()
            continue
        m = DECL.match(ln)
        # `.rstrip('.')`: `theorem foo.{u}` captures `foo.`, because the name class
        # contains `.` and the match stops at `{`.  A row ending in `.` has an EMPTY
        # last component, and CLAUDE.md's queue audit keys on exactly that component
        # -- so an un-normalised row silently matched every task.  Fixed at source
        # here rather than in each consumer.
        if m: heads.append((i, '.'.join(stack + [m.group(2).rstrip('.')]) if m.group(2) else '?'))
    seen = set()
    for i, ln in enumerate(code):
        if not SORRY.search(ln): continue
        owner = None
        for (j, q) in reversed(heads):
            if j <= i: owner = (j, q); break
        if owner and owner not in seen:
            seen.add(owner)
            res.append((str(p.relative_to(ROOT)), owner[0]+1, owner[1]))
        elif owner is None:
            res.append((str(p.relative_to(ROOT)), i+1, '<no-enclosing-decl>'))
byfile = collections.Counter(r[0] for r in res)
if '--count' in sys.argv:
    for f, n in sorted(byfile.items()): print('%4d  %s' % (n, f))
    print('TOTAL', len(res), 'across', len(byfile), 'modules')
else:
    for f, l, q in res: print('%s\t%d\t%s' % (f, l, q))
