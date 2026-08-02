#!/usr/bin/env python3
"""Find PROVEN declarations whose OPENING docstring still claims `(sorry leaf`/`(sorry node`.

A stale `(sorry leaf)` header on a now-proven declaration is a phantom-work source:
queue entries and leaf lists get harvested from docstrings, so the label draws a
dispatch at a declaration with nothing to prove.  CLAUDE.md records the phenomenon
("They come in CLUSTERS, and the sweep is cheap and compiler-validated"); this is
that sweep, as a script rather than a paragraph.

GROUND TRUTH IS THE COMPILER, never a source grep: the sorried set is taken from the
build log's `declaration uses 'sorry'` warning LINE NUMBERS, each attributed to the
declaration it falls inside.

    lake build <Mod> > /tmp/b.log 2>&1
    python3 tools/merge/stalelabel.py /tmp/b.log

CAVEAT, and it is the fourth invisibility class: a module the build never REACHED
contributes no warnings, so every declaration in it looks proven.  Files with zero
warnings are reported separately rather than scanned, unless --force is given.
"""
import sys, re, bisect, argparse, pathlib, collections

WARN = re.compile(r"warning: ([^\s:]+\.lean):(\d+):\d+: declaration uses ['`]sorry['`]")
DECL = re.compile(r'^(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*'
                  r'(theorem|lemma|def|abbrev|instance|structure|class|inductive)\b')
MODIFIER = re.compile(r'^(set_option|open|attribute|omit|include|variable)\b.*\bin$')

def comment_mask(src):
    """True at every character inside a comment.  Block comments NEST in Lean."""
    mask = bytearray(len(src)); i = 0; depth = 0
    while i < len(src):
        if depth == 0 and src.startswith('--', i) and not src.startswith('-/', i):
            j = src.find('\n', i); j = len(src) if j < 0 else j
            for k in range(i, j): mask[k] = 1
            i = j; continue
        if src.startswith('/-', i):
            depth += 1; mask[i] = mask[i + 1] = 1; i += 2; continue
        if src.startswith('-/', i) and depth > 0:
            depth -= 1; mask[i] = mask[i + 1] = 1; i += 2; continue
        if depth > 0: mask[i] = 1
        i += 1
    return mask

def scan(path, warn_lines):
    src = pathlib.Path(path).read_text()
    lines = src.split('\n'); mask = comment_mask(src)
    starts = []; off = 0
    for ln in lines: starts.append(off); off += len(ln) + 1
    def in_comment(i):
        return mask[starts[i]] == 1 if starts[i] < len(mask) else True

    decls = []
    for i, ln in enumerate(lines):
        if in_comment(i): continue
        m = DECL.match(ln)
        if not m: continue
        rest = ln[m.end():].strip()
        nm = (rest.split()[0] if rest else '<anon>')
        for c in ':({[': nm = nm.split(c)[0]
        decls.append((i, nm))
    dl = [d[0] + 1 for d in decls]
    sorried = set()
    for w in sorted(warn_lines):
        p = bisect.bisect_right(dl, w) - 1
        if p >= 0: sorried.add(dl[p])
    declset = {d[0] for d in decls}

    out = []
    for (i, nm) in decls:
        if i + 1 in sorried: continue
        j = i - 1
        while j >= 0 and (lines[j].strip() == '' or lines[j].strip().startswith('@[')
                          or MODIFIER.match(lines[j].strip())):
            j -= 1
        if j < 0 or not lines[j].rstrip().endswith('-/'): continue
        k = j
        while k >= 0 and not lines[k].lstrip().startswith('/--'): k -= 1
        if k < 0: continue
        # the docstring must be THIS declaration's: no declaration and no other
        # comment terminator may lie between its opener and its closer
        if any(k < d < i for d in declset): continue
        if any(lines[t].rstrip().endswith('-/') for t in range(k, j)): continue
        head = ' '.join(lines[k:min(k + 3, j + 1)])
        if '(sorry leaf' not in head and '(sorry node' not in head: continue
        # A header that labels ITSELF proven, or says the old label was stale, is
        # recording history rather than claiming a leaf.  Match the LABEL form
        # (`(PROVEN`, `**PROVEN`), never a bare `PROVEN`: the commonest true positive
        # of all says "... which is PROVEN over it" about a DIFFERENT declaration, and
        # a bare-word filter silently drops it — that was this tool's own first bug.
        if re.search(r'\(\s*\*{0,2}\s*PROVEN', head) or re.search(r'\*\*PROVEN', head): continue
        if 'stale' in head.lower(): continue
        out.append((k + 1, i + 1, nm, lines[k].strip()))
    return out, len(decls)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('log', help='lake build log containing the sorry warnings')
    ap.add_argument('--root', default='.', help='repository root (default: cwd)')
    ap.add_argument('--force', action='store_true',
                    help='also scan files with zero warnings (may not have been built)')
    a = ap.parse_args()
    root = pathlib.Path(a.root)

    warns = collections.defaultdict(list)
    for line in pathlib.Path(a.log).read_text(errors='replace').split('\n'):
        m = WARN.search(line)
        if m: warns[m.group(1)].append(int(m.group(2)))

    files = sorted(p for p in (root / 'Fermat').rglob('*.lean'))
    total = unbuilt = 0
    for p in files:
        rel = str(p.relative_to(root))
        if rel not in warns and not a.force:
            unbuilt += 1; continue
        hits, _ = scan(p, warns.get(rel, []))
        if not hits: continue
        print(f'\n=== {rel}  ({len(hits)} stale)')
        for (dline, cline, nm, txt) in hits:
            print(f'  STALE-LABEL  doc L{dline}  decl L{cline}  {nm}')
            print(f'               {txt[:96]}')
        total += len(hits)
    print(f'\nTOTAL stale labels: {total}')
    if unbuilt and not a.force:
        print(f'({unbuilt} files had no sorry warning in this log and were SKIPPED — '
              f'they may simply not have been built.  Use --force to scan them.)')
    return 0

if __name__ == '__main__':
    sys.exit(main())
