#!/usr/bin/env python3
"""Report namespace/section scope imbalances in Lean files.

An `end X` with no matching open `namespace X`/`section X`, or a scope left
open at EOF, is a merge artifact: the opener lived in inter-block glue that a
declaration-level merge dropped.
"""
import re, sys

NS = re.compile(r'^namespace\s+(\S+)\s*$')
SEC = re.compile(r'^section\s*(\S*)\s*$')
END = re.compile(r'^end\s*(\S*)\s*$')


def mask(lines):
    out, d = [], 0
    for ln in lines:
        s = ln.strip()
        if d == 0:
            if s.startswith('/-'):
                out.append(True)
                if '-/' not in ln[ln.index('/-') + 2:]:
                    d = 1
                continue
            out.append(s.startswith('--'))
        else:
            out.append(True)
            if '-/' in ln:
                d = 0
    return out


bad = 0
for p in sys.argv[1:]:
    L = open(p, encoding='utf-8', errors='replace').read().split('\n')
    m = mask(L)
    st = []
    probs = []
    for i, ln in enumerate(L, 1):
        if m[i - 1]:
            continue
        x = NS.match(ln)
        if x:
            st.append(('namespace', x.group(1), i)); continue
        x = SEC.match(ln)
        if x:
            st.append(('section', x.group(1), i)); continue
        x = END.match(ln)
        if x:
            nm = x.group(1)
            if not st:
                probs.append('line %d: `end %s` with nothing open' % (i, nm)); continue
            k, n, o = st[-1]
            if nm == '':
                if k != 'section' or n != '':
                    probs.append('line %d: bare `end` closes %s %s (opened %d)' % (i, k, n, o))
                st.pop()
            elif n == nm:
                st.pop()
            else:
                # `end A.B.C` may close a chain opened as `namespace A` / `namespace B.C`,
                # and `end C` may close `namespace A.B.C` when A.B are still wanted open.
                parts = nm.split('.')
                stack_tail = []
                j = len(st)
                while j > 0 and len('.'.join(stack_tail)) < len(nm):
                    stack_tail.insert(0, st[j - 1][1]); j -= 1
                if '.'.join(stack_tail) == nm:
                    del st[j:]
                elif n.endswith('.' + nm) or n == parts[-1]:
                    st.pop()
                else:
                    probs.append('line %d: `end %s` but innermost open is %s %s (line %d)'
                                 % (i, nm, k, n, o))
                    names = [x[1] for x in st]
                    if nm in names:
                        while st and st[-1][1] != nm:
                            st.pop()
                        st.pop()
    for k, n, o in st:
        probs.append('EOF: %s %s opened at line %d never closed' % (k, n, o))
    if probs:
        bad = 1
        print('== %s' % p)
        for q in probs:
            print('   ' + q)
sys.exit(bad)
