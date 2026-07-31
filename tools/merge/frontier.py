#!/usr/bin/env python3
"""Direct-sorry frontier: strip comments, then attribute each `sorry` token to the
nearest declaration header ABOVE it. Emits `file<TAB>line<TAB>qualified-name`."""
import re, pathlib, sys, collections
ROOT = pathlib.Path('/home/chend/flt-staging')
DECL = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|public\s+|local\s+|scoped\s+)*'
    r'(theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|example)\s+'
    r"([A-Za-z_À-ɏᴀ-ᶿ℀-⅏][A-Za-z0-9_À-ɏᴀ-ᶿ₀-ₜ⁰-ⁿ℀-⅏.'!?]*)")
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
        if m: heads.append((i, '.'.join(stack + [m.group(2)]) if m.group(2) else '?'))
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
