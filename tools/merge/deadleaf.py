#!/usr/bin/env python3
"""Open leaves that NOTHING CONSUMES — the invisibility class no other scan sees.

A leaf can be open, compile, emit `declaration uses 'sorry'`, pass every ownership
test, and be worth nothing to close, because no proof term in the project reaches
it.  `frontier.py` counts it, `xdup.py`/`dupstmt.py` are silent (no duplicated name,
no duplicated statement), and the build is green.  It draws dispatches for ever.

Two ways a tree acquires one, and they have OPPOSITE repairs:

  DELETE x REFACTOR   one branch deletes the leaf's consumer, another refactors it.
                      The leaf is garbage: delete it, and say in the docstring where
                      to recover the text from.
  CUT x HOIST         one branch CUTS a node into halves in file F, another HOISTS
                      the parent OUT of F into an upstream module (taking its
                      pre-cut body, since that is what a hoist copies).  The halves
                      are then DOWNSTREAM of their own consumer and unconsumable,
                      and no relocation of the parent can fix it if its position is
                      what breaks an import cycle.  The leaf is MISPLACED: move it
                      UP to the parent's new home and prove the parent over it.

So when this reports a leaf, the question is not "is it dead" but WHERE DID ITS
CONSUMER GO.  The `hint:` lines below answer that mechanically: they list the
declarations a dead leaf's own docstring names which live in a module the leaf's
file IMPORTS.  A hit there is the CUT x HOIST signature.

METHOD, and its two deliberate biases.

  * comment-stripped source only, so a docstring mention is never a use;
  * declarations are resolved by LAST COMPONENT (`hA.gamma0_mul` never contains the
    string `IsAtkinLehnerMatrix.gamma0_mul`, so a qualified-name scan cannot see dot
    notation).  That UNDER-reports: an unrelated declaration sharing a last component
    keeps a genuinely dead leaf off the list.  Under-reporting is the safe direction
    for a scan whose output a human acts on.
  * `instance`s and `@[simp]`/`@[instance]`-tagged declarations are EXCLUDED from the
    report entirely: they are consumed by SEARCH, not by name, so a name-based scan
    can say nothing about them (CLAUDE.md's elaboration-invisible dependency classes).

USAGE

    tools/merge/deadleaf.py                 # every Fermat/**.lean under this repo
    tools/merge/deadleaf.py --root DIR      # another worktree
    tools/merge/deadleaf.py --all-decls     # also list PROVEN consumerless declarations
                                            # (free-floating candidates, noisier)

Exit status is 1 if any dead leaf was found, else 0.
"""
import re, sys, pathlib, collections

ROOT = pathlib.Path(__file__).resolve().parents[2]
if '--root' in sys.argv:
    ROOT = pathlib.Path(sys.argv[sys.argv.index('--root') + 1]).resolve()
ALL_DECLS = '--all-decls' in sys.argv

# Identifier class.  Do NOT hand-roll unicode ranges here: the one `frontier.py` and
# friends use (`À-ɏᴀ-ᶿ℀-⅏`) has no GREEK block, so it truncates every name containing
# `Ψ`/`Δ`/`Γ` — `not_monic_dvd_preΨ_mod_nonCMModelThirtySevenA` and its `...B` sibling
# both come out as `not_monic_dvd_pre`, which makes them look like a duplicate pair AND
# makes every real use of them unresolvable, hence a false DEAD LEAF.  `\w` under
# Python's unicode default covers every letter block at once; `[^\W\d]` is "word
# character that is not a digit", i.e. letter or underscore.  (And never `À-￿`, which
# swallows `⟨⟩←▸` — see CLAUDE.md.)
IDENT = r"[^\W\d][\w.'!?]*"
DECL = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|public\s+|local\s+|scoped\s+)*'
    r'(theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|example)\s+'
    r'(' + IDENT + r')')
ATTR = re.compile(r'^\s*@\[')
NS = re.compile(r'^\s*namespace\s+(\S+)')
ENDNS = re.compile(r'^\s*end\s*(\S*)\s*$')
SORRY = re.compile(r"(?<![A-Za-z0-9_'])sorry(?![A-Za-z0-9_'])")
IMPORT = re.compile(r'^\s*(?:public\s+)?import\s+(Fermat[\w.]*)\s*$')
# backtick-quoted names inside docstrings
TICK = re.compile(r'`(' + IDENT + r')`')


def strip_comments(lines):
    """Blank out every comment line; keep code lines at their original index."""
    out, depth = [], 0
    for ln in lines:
        s = ln.strip()
        if depth == 0:
            if s.startswith('/-'):
                depth += 1
                if '-/' in ln[ln.index('/-') + 2:]:
                    depth -= 1
                out.append('')
                continue
            if s.startswith('--'):
                out.append('')
                continue
            k = ln.find('--')
            out.append(ln[:k] if k >= 0 and '"' not in ln[:k] else ln)
        else:
            if '-/' in ln:
                depth -= 1
            out.append('')
    return out


def tokens(text):
    """Identifier-ish tokens.  Split on anything that is not alphanumeric/_/'/. --
    NEVER a unicode character class: `À-￿` swallows ⟨⟩←▸ and eats the names inside
    an anonymous constructor."""
    cur, out = [], []
    for ch in text:
        if ch.isalnum() or ch in "_'.":
            cur.append(ch)
        else:
            if cur:
                out.append(''.join(cur))
                cur = []
    if cur:
        out.append(''.join(cur))
    return out


# `Fermat.lean` (the root module, with the sorry gate) and `ProgressCensus.lean` sit
# at the REPO ROOT, not under `Fermat/`.  A scan that misses them calls anything they
# name consumerless.
files = sorted(ROOT.glob('Fermat/**/*.lean')) + sorted(ROOT.glob('*.lean'))
files = [f for f in files if f.name != 'lakefile.lean']
if not files:
    sys.exit('no Lean sources under %s' % ROOT)

mod_of = {}          # path -> module name
imports = {}         # module -> set of directly imported Fermat modules
decls = []           # (file, line, qualified, short, kind, tagged, sorried, extent_text, doc_text)
for p in files:
    raw = p.read_text(encoding='utf-8', errors='replace').split('\n')
    rel = str(p.relative_to(ROOT))
    mod = rel[:-5].replace('/', '.')
    mod_of[rel] = mod
    imports[mod] = {m.group(1) for m in (IMPORT.match(l) for l in raw) if m}
    code = strip_comments(raw)
    heads, stack = [], []
    for i, ln in enumerate(code):
        m = NS.match(ln)
        if m:
            stack.append(m.group(1)); continue
        m = ENDNS.match(ln)
        if m:
            if stack and (not m.group(1) or m.group(1) == stack[-1]):
                stack.pop()
            continue
        m = DECL.match(ln)
        if m:
            # `theorem foo.{u, v}` leaves a trailing `.` on the name; strip it, or
            # `split('.')[-1]` is the empty string and matches everything.
            name = m.group(2).rstrip('.')
            # is the declaration attribute-tagged?  look upward through @[...] lines
            tagged = bool(ATTR.match(ln))
            j = i - 1
            while j >= 0 and (ATTR.match(code[j]) or code[j].strip() == ''):
                if ATTR.match(code[j]):
                    tagged = True
                j -= 1
            heads.append((i, '.'.join(stack + [name]), name, m.group(1), tagged))
    for k, (i, qual, short, kind, tagged) in enumerate(heads):
        end = heads[k + 1][0] if k + 1 < len(heads) else len(code)
        body = '\n'.join(code[i:end])
        # the docstring is whatever raw text sits between the previous decl and this one
        prev = heads[k - 1][0] if k else 0
        doc = '\n'.join(raw[prev:i])
        decls.append(dict(file=rel, mod=mod, line=i + 1, qual=qual, short=short,
                          kind=kind, tagged=tagged,
                          sorried=bool(SORRY.search(body)), body=body, doc=doc))

# transitive import closure, so "is that module upstream of mine" is answerable
closure = {}
def imp_closure(m, seen=None):
    if m in closure:
        return closure[m]
    seen = seen or set()
    if m in seen:
        return set()
    acc = set()
    for q in imports.get(m, ()):
        acc.add(q)
        acc |= imp_closure(q, seen | {m})
    closure[m] = acc
    return acc
for m in list(imports):
    imp_closure(m)

by_short = collections.defaultdict(list)
for d in decls:
    by_short[d['short']].append(d)

# consumers[i] = indices of declarations whose BODY names decls[i]
consumers = collections.defaultdict(set)
for k, d in enumerate(decls):
    used = set()
    for t in tokens(d['body']):
        for part in (t, t.split('.')[-1]):
            if part in by_short:
                used.add(part)
    for part in used:
        for tgt in by_short[part]:
            if tgt is not d:
                consumers[id(tgt)].add(k)

dead = []
for d in decls:
    if d['kind'] in ('instance', 'example') or d['tagged']:
        continue
    if not consumers[id(d)]:
        if d['sorried'] or ALL_DECLS:
            dead.append(d)

n_leaf = 0
for d in sorted(dead, key=lambda x: (x['file'], x['line'])):
    tag = 'DEAD LEAF ' if d['sorried'] else 'consumerless'
    if d['sorried']:
        n_leaf += 1
    print('%s  %s:%d  %s' % (tag, d['file'], d['line'], d['qual']))
    # CUT x HOIST hint: names its docstring quotes that live UPSTREAM of it.
    # Short names (`K`, `M`, `N`, field names) match everything and say nothing, so
    # require a name long enough to be a project declaration.
    up = []
    for nm in dict.fromkeys(TICK.findall(d['doc'])):
        short = nm.split('.')[-1]
        if len(short) < 10 or '_' not in short:
            continue
        for tgt in by_short.get(short, ()):
            if tgt['mod'] != d['mod'] and tgt['mod'] in closure.get(d['mod'], ()):
                up.append('%s (%s)' % (tgt['qual'], tgt['file']))
    for u in list(dict.fromkeys(up))[:6]:
        print('    upstream name in its docstring (a MOVED consumer looks like this): %s' % u)

print()
percount = collections.Counter(d['file'] for d in dead if d['sorried'])
for f, n in sorted(percount.items(), key=lambda kv: -kv[1]):
    print('%4d  %s' % (n, f))
print('%d dead leaf/leaves; %d consumerless declarations scanned over %d files'
      % (n_leaf, len(dead), len(files)))
sys.exit(1 if n_leaf else 0)
