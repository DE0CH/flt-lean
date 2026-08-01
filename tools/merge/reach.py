#!/usr/bin/env python3
"""Source-level REACHABILITY of every declaration under `Fermat/` from the root
`fermat_last_theorem`.

Motivation.  A `sorry` leaf can be OPEN, compile, emit its
`declaration uses 'sorry'` warning, pass every ownership check -- and still be
worth nothing to close, because nothing consumes it.  CLAUDE.md calls this the
seventh invisibility class; release 27 manufactured a batch of them, because a
branch that DECOMPOSES a leaf and a branch that PROVES it outright merge
cleanly (they touch different regions), the resolution keeps the proof, and the
decomposition's residual leaf plus all its machinery are orphaned.

What this computes.  Comment-stripped sources; one node per top-level
declaration; an edge `D -> N` whenever `D`'s text mentions a name resolving to
declaration `N`; then a BFS from `fermat_last_theorem`.  Anything unreached is
free-floating in the source sense.

Deliberate biases, both towards FEWER false orphans:

  * names are indexed by EVERY DOTTED SUFFIX of their qualified name, so
    `hA.gamma0_mul` and a bare `gamma0_mul` both resolve.  This OVER-links
    (two declarations sharing a last component are conflated), which can only
    make a dead declaration look alive -- never the reverse.
  * a declaration's own STATEMENT counts as part of it, so a leaf mentioned
    only in some live theorem's binder list is reached.

Known non-defect: `Fermat/SorryGate.lean` contains the token `sorry` inside a
STRING LITERAL in its `elab`; it is skipped, as every scan in this tree must.

Usage:
    tools/merge/reach.py [--root DIR] [--all] [--why NAME] [--json OUT]
"""
import re, sys, json, pathlib, collections

ROOT = pathlib.Path(__file__).resolve().parents[2]
if '--root' in sys.argv:
    ROOT = pathlib.Path(sys.argv[sys.argv.index('--root') + 1]).resolve()

IDENT = r"[A-Za-z_À-ɏᴀ-ᶿ℀-⅏][A-Za-z0-9_À-ɏᴀ-ᶿ₀-ₜ⁰-ⁿ℀-⅏.'!?]*"
DECL = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)*'
    r'(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|public\s+|local\s+|scoped\s+)*'
    r'(theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|example)\s+'
    r'(' + IDENT + r')')
# an anonymous `instance :` still opens a declaration; it can never be NAMED,
# so it is a node with no in-edges, but its body must still contribute edges.
ANON = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+|local\s+|scoped\s+)*instance\s*[:({\[]')
NS = re.compile(r'^\s*namespace\s+(\S+)')
ENDNS = re.compile(r'^\s*end\s+(\S+)\s*$')
SECT = re.compile(r'^\s*section\b')
ENDBARE = re.compile(r'^\s*end\s*$')
TOKEN = re.compile(IDENT)
SORRY = re.compile(r"(?<![A-Za-z0-9_'])sorry(?![A-Za-z0-9_'])")


def strip_comments(lines):
    """Blank out block comments (nesting) and line comments; keep line count."""
    out, depth = [], 0
    for ln in lines:
        if depth == 0:
            res, i = [], 0
            while i < len(ln):
                if ln.startswith('/-', i):
                    depth += 1
                    i += 2
                    while i < len(ln) and depth:
                        if ln.startswith('/-', i):
                            depth += 1; i += 2
                        elif ln.startswith('-/', i):
                            depth -= 1; i += 2
                        else:
                            i += 1
                elif ln.startswith('--', i):
                    break
                else:
                    res.append(ln[i]); i += 1
            out.append(''.join(res))
        else:
            i = 0
            while i < len(ln) and depth:
                if ln.startswith('/-', i):
                    depth += 1; i += 2
                elif ln.startswith('-/', i):
                    depth -= 1; i += 2
                else:
                    i += 1
            out.append(ln[i:] if not depth else '')
    return out


def scan_file(path, rel):
    """-> list of (qualified_name_or_None, start_line, end_line, text)."""
    raw = path.read_text(encoding='utf-8', errors='replace').split('\n')
    lines = strip_comments(raw)
    nsstack, opened = [], []          # opened: what each `end` should pop
    decls = []                        # (name|None, start_idx)
    for i, ln in enumerate(lines):
        m = NS.match(ln)
        if m:
            nsstack.append(m.group(1)); opened.append(('ns', m.group(1))); continue
        if SECT.match(ln):
            opened.append(('sec', None)); continue
        m = ENDNS.match(ln)
        if m:
            if opened and opened[-1][0] == 'ns':
                opened.pop()
                if nsstack: nsstack.pop()
            elif opened:
                opened.pop()
            continue
        if ENDBARE.match(ln):
            if opened:
                kind, _ = opened.pop()
                if kind == 'ns' and nsstack: nsstack.pop()
            continue
        m = DECL.match(ln)
        if m:
            short = m.group(2)
            full = '.'.join(nsstack + [short]) if nsstack else short
            decls.append((full, i)); continue
        if ANON.match(ln):
            decls.append((None, i))
    res = []
    for k, (name, start) in enumerate(decls):
        end = decls[k + 1][1] if k + 1 < len(decls) else len(lines)
        res.append((name, start + 1, end, '\n'.join(lines[start:end])))
    return res


def main():
    show_all = '--all' in sys.argv
    why = None
    if '--why' in sys.argv:
        why = sys.argv[sys.argv.index('--why') + 1]

    files = sorted(p for p in (ROOT / 'Fermat').rglob('*.lean'))
    root_file = ROOT / 'Fermat.lean'
    if root_file.exists():
        files.append(root_file)

    nodes = {}            # id -> dict(name, file, line, text, sorry)
    suffix = collections.defaultdict(set)   # dotted suffix -> {id}
    for p in files:
        rel = str(p.relative_to(ROOT))
        if rel.endswith('SorryGate.lean'):
            continue
        for name, s, e, text in scan_file(p, rel):
            nid = len(nodes)
            nodes[nid] = dict(name=name, file=rel, line=s, text=text,
                              sorry=bool(SORRY.search(text)))
            if name:
                parts = name.split('.')
                for j in range(len(parts)):
                    suffix['.'.join(parts[j:])].add(nid)

    # edges
    out = collections.defaultdict(set)
    for nid, nd in nodes.items():
        seen = set()
        for tok in TOKEN.findall(nd['text']):
            parts = tok.split('.')
            for j in range(len(parts)):
                key = '.'.join(parts[j:])
                if key in suffix:
                    seen |= suffix[key]
        seen.discard(nid)
        out[nid] = seen

    roots = suffix.get('fermat_last_theorem', set())
    if not roots:
        print('FATAL: fermat_last_theorem not found', file=sys.stderr); sys.exit(2)

    reached, stack = set(roots), list(roots)
    while stack:
        n = stack.pop()
        for m in out[n]:
            if m not in reached:
                reached.add(m); stack.append(m)

    if why:
        tgt = suffix.get(why, set())
        if not tgt:
            print(f'no declaration named {why}'); return
        rev = collections.defaultdict(set)
        for a, bs in out.items():
            for b in bs: rev[b].add(a)
        for t in tgt:
            nd = nodes[t]
            print(f"{nd['file']}:{nd['line']}  {nd['name']}  "
                  f"{'REACHED' if t in reached else 'UNREACHED'}")
            cons = sorted(rev[t], key=lambda i: (nodes[i]['file'], nodes[i]['line']))
            if not cons:
                print('    (no consumers at all)')
            for c in cons:
                cn = nodes[c]
                print(f"    <- {cn['file']}:{cn['line']} {cn['name']} "
                      f"[{'reached' if c in reached else 'UNREACHED'}]")
        return

    orphan_sorries = [n for n, d in nodes.items()
                      if d['sorry'] and d['name'] and n not in reached]
    orphan_sorries.sort(key=lambda i: (nodes[i]['file'], nodes[i]['line']))
    tot_sorry = sum(1 for d in nodes.values() if d['sorry'] and d['name'])

    print(f'# declarations: {len(nodes)}   reached from root: {len(reached)}')
    print(f'# sorried declarations: {tot_sorry}   of them UNREACHED: {len(orphan_sorries)}')
    print()
    for n in orphan_sorries:
        d = nodes[n]
        print(f"{d['file']}\t{d['line']}\t{d['name']}")

    if show_all:
        print()
        print('# ALL unreached declarations (sorried or not)')
        for n in sorted(nodes, key=lambda i: (nodes[i]['file'], nodes[i]['line'])):
            d = nodes[n]
            if d['name'] and n not in reached:
                print(f"{d['file']}\t{d['line']}\t{d['name']}\t{'SORRY' if d['sorry'] else ''}")


if __name__ == '__main__':
    main()
