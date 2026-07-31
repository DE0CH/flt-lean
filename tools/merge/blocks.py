#!/usr/bin/env python3
"""Declaration-BLOCK extraction, shared by the cross-file de-duplication tooling.

`xdup.py` finds that a name is declared in two modules of one import cone; it
reports a LINE, not an extent.  Removing the downstream copy needs the extent --
the doc comment and attributes that belong to the declaration, and nothing else.

The model is Lean 4's own layout rule: a COMMAND starts at column 0 and every
line of its body is indented or blank.  So the file is a sequence of commands,
cut at the column-0 lines that are not inside a block comment, and a declaration
BLOCK is `[doc comment] [attributes] <declaration>` -- the comment and attribute
commands immediately preceding a declaration, with no blank-line gap large
enough to detach them, plus the declaration command itself.

Structural commands (`namespace`, `end`, `section`, `variable`, `open`, ...) are
never part of a block, which is what makes a block safe to delete: the scoping
that the file's OTHER declarations depend on survives untouched.

Namespace qualification uses the same stack model as `xdup.py` -- deliberately,
including its known weakness on giant modules with bare `end`s, so that the two
tools agree on names.
"""
import re, sys, json

DECL = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|public\s+|local\s+|scoped\s+)*'
    r'(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom)\s+'
    r"([A-Za-z_À-ɏᴀ-ᶿ℀-⅏][A-Za-z0-9_À-ɏᴀ-ᶿ₀-ₜ⁰-ⁿ℀-⅏.'!?]*)")
NS = re.compile(r'^\s*namespace\s+(\S+)')
ENDNS = re.compile(r'^\s*end\s*(\S*)\s*$')

# A declaration head whose name is anonymous (`instance : Foo := ...`) still has
# to be recognised as a declaration, or the block after it is mis-attributed.
ANONDECL = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|public\s+|local\s+|scoped\s+)*'
    r'(?:theorem|lemma|def|abbrev|instance|example|structure|class|inductive|opaque|axiom)\b')

STRUCTURAL = re.compile(
    r'^(?:namespace|end|section|variable|open|import|universe|attribute|set_option|'
    r'suppress_compilation|deriving|macro|notation|syntax|elab|declare_syntax_cat|'
    r'@\[expose\]|module|public\s+import|public\s+section|noncomputable\s+section|#)')


def comment_mask(lines):
    """depth[i] = block-comment nesting depth ENTERING line i."""
    depth, out = 0, []
    for ln in lines:
        out.append(depth)
        i, n = 0, len(ln)
        while i < n:
            if depth == 0 and ln.startswith('--', i):
                break                      # line comment: rest of line is inert
            if ln.startswith('/-', i):
                depth += 1; i += 2; continue
            if depth and ln.startswith('-/', i):
                depth -= 1; i += 2; continue
            i += 1
    return out


def commands(lines):
    """Cut the file at column-0 lines that are not inside a block comment."""
    depth = comment_mask(lines)
    starts = [i for i, ln in enumerate(lines)
              if ln[:1] not in ('', ' ', '\t') and depth[i] == 0]
    if not starts:
        return []
    out = []
    for k, s in enumerate(starts):
        e = starts[k + 1] if k + 1 < len(starts) else len(lines)
        out.append((s, e))
    return out


def kind(lines, s):
    head = lines[s]
    if head.startswith('/-'):
        return 'comment'
    if head.startswith('@['):
        # `@[simp] theorem foo` is an attribute AND a declaration on one line.
        return 'decl' if ANONDECL.match(head) else 'attr'
    if STRUCTURAL.match(head):
        return 'structural'
    if ANONDECL.match(head):
        return 'decl'
    return 'other'


def blocks(path):
    """[(name_or_None, qualified_or_None, block_start, block_end, decl_line)] , 0-indexed, end exclusive."""
    lines = open(path, encoding='utf-8', errors='replace').read().split('\n')
    cmds = commands(lines)
    stack, out, pending = [], [], []
    for (s, e) in cmds:
        k = kind(lines, s)
        if k == 'structural':
            m = NS.match(lines[s])
            if m:
                stack.append(m.group(1))
            else:
                m = ENDNS.match(lines[s])
                if m and stack and (not m.group(1) or m.group(1) == stack[-1]):
                    stack.pop()
            pending = []
            continue
        if k in ('comment', 'attr'):
            pending.append((s, e))
            continue
        if k == 'decl':
            m = DECL.match(lines[s])
            name = m.group(1) if m else None
            # A comment ABUTS the declaration (no blank line between) exactly
            # when it is that declaration's doc comment; one separated by a
            # blank run is a section header belonging to the file, not to this
            # declaration, and must survive the declaration's removal.
            bs = s
            for (ps, pe) in reversed(pending):
                last = pe - 1
                while last >= ps and not lines[last].strip():
                    last -= 1
                if last + 1 != bs:          # blank line(s) before what follows
                    break
                bs = ps
            out.append((name, '.'.join(stack + [name]) if name else None, bs, e, s))
            pending = []
            continue
        pending = []
    return lines, out


def norm(lines, s, e):
    """Whitespace-normalised body text, comments stripped, for equality testing."""
    depth = comment_mask(lines[s:e])
    keep = []
    for i, ln in enumerate(lines[s:e]):
        if depth[i]:
            continue
        j = ln.find('--')
        if j >= 0 and depth[i] == 0:
            ln = ln[:j]
        # drop a same-line block comment entirely
        ln = re.sub(r'/-.*?-/', ' ', ln)
        ln = re.sub(r'/-.*$', ' ', ln)
        ln = re.sub(r'^.*?-/', ' ', ln) if '-/' in ln and '/-' not in ln else ln
        if ln.strip():
            keep.append(' '.join(ln.split()))
    return ' '.join(keep)


if __name__ == '__main__':
    lines, bs = blocks(sys.argv[1])
    print(json.dumps([{'name': n, 'qual': q, 'start': a + 1, 'end': b, 'decl': d + 1}
                      for (n, q, a, b, d) in bs][:int(sys.argv[2]) if len(sys.argv) > 2 else None],
                     indent=1))
