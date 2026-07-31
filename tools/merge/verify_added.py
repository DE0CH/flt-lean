#!/usr/bin/env python3
"""For each merged branch, list declarations it ADDED (vs its merge base) that are
absent from the current tree -- matched on the LAST COMPONENT, so namespace
re-qualification is not mistaken for a dropped payload."""
import re, subprocess, sys, os

DECL = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|public\s+)*'
    r'(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom)\s+'
    r'([A-Za-z_À-ɏͰ-Ͽᴀ-ᵿ℀-⅏][A-Za-z0-9_À-ɏͰ-Ͽᴀ-ᵿ₀-ₜ⁰-ⁿ℀-⅏.\'!?]*)')


def strip(lines):
    out, d = [], 0
    for ln in lines:
        s = ln.strip()
        if d == 0:
            if s.startswith('/-'):
                d = 1
                if '-/' in ln[ln.index('/-') + 2:]:
                    d = 0
                out.append(''); continue
            if s.startswith('--'):
                out.append(''); continue
            out.append(ln)
        else:
            if '-/' in ln:
                d = 0
            out.append('')
    return out


def names(text):
    return {m.group(1).split('.')[-1] for m in
            (DECL.match(l) for l in strip(text.split('\n'))) if m}


def gs(rev, path):
    p = subprocess.run(['git', 'show', '%s:%s' % (rev, path)], capture_output=True, text=True)
    return p.stdout if p.returncode == 0 else None


bad = 0
for b in sys.argv[1:]:
    base = subprocess.run(['git', 'merge-base', 'HEAD', b], capture_output=True, text=True).stdout.strip()
    files = subprocess.run(['git', 'diff', '--name-only', base, b, '--', 'Fermat/'],
                           capture_output=True, text=True).stdout.split()
    miss = {}
    for f in files:
        tb, tt = gs(base, f), gs(b, f)
        if tt is None:
            continue
        added = names(tt) - (names(tb) if tb else set())
        if not added:
            continue
        cur = ''
        if os.path.exists(f):
            cur = open(f, encoding='utf-8', errors='replace').read()
        gone = added - names(cur)
        # a declaration may have been relocated to another file in the tree
        if gone:
            allsrc = subprocess.run(['git', 'grep', '-h', '-E',
                                     r'^\s*(theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom)\s'],
                                    capture_output=True, text=True).stdout
            tree = names(allsrc)
            gone = gone - tree
        if gone:
            miss[f] = sorted(gone)
    if miss:
        bad = 1
        print('%s:' % b)
        for f, g in miss.items():
            print('   %s' % f)
            for n in g:
                print('      %s' % n)
sys.exit(bad)
