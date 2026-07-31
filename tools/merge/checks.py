#!/usr/bin/env python3
"""Post-merge safety checks (CLAUDE.md release-22/24 checklist).

  check-branch  <branch> <file>...   every branch-ADDED decl present in resolved file
  check-dup     <file>...            no duplicate namespace-qualified decl name
  check-comment <file>...            block-comment nesting depth returns to zero
  check-binder  <file>...            signature binder _foo whose body mentions foo
"""
import re, sys, subprocess, collections

DECL = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|public\s+)*'
    r'(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom)\s+'
    r'([A-Za-z_À-ɏͰ-Ͽᴀ-ᵿ℀-⅏][A-Za-z0-9_À-ɏͰ-Ͽᴀ-ᵿ₀-ₜ⁰-ⁿ℀-⅏.\'!?]*)')
NS = re.compile(r'^\s*namespace\s+(\S+)')
ENDNS = re.compile(r'^\s*end\s*(\S*)\s*$')


def strip_comments(lines):
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
            out.append(ln)
        else:
            if '-/' in ln:
                depth -= 1
            out.append('')
    return out, depth


def qualified_decls(lines):
    """Return {qualified_name: [line numbers]} — namespace-qualified, dots kept."""
    code, _ = strip_comments(lines)
    stack = []
    res = collections.defaultdict(list)
    for i, ln in enumerate(code, 1):
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
            res['.'.join(stack + [m.group(1)])].append(i)
    return res


def read(path):
    with open(path, encoding='utf-8', errors='replace') as f:
        return f.read().split('\n')


def gitshow(rev, path):
    p = subprocess.run(['git', 'show', '%s:%s' % (rev, path)],
                       capture_output=True, text=True)
    if p.returncode != 0:
        return None
    return p.stdout.split('\n')


def main():
    mode = sys.argv[1]
    bad = 0
    if mode == 'check-branch':
        branch = sys.argv[2]
        files = sys.argv[3:]
        for f in files:
            base = subprocess.run(['git', 'merge-base', 'HEAD', branch],
                                  capture_output=True, text=True).stdout.strip()
            bl = gitshow(branch, f)
            ba = gitshow(base, f)
            if bl is None:
                continue
            bdecl = set(qualified_decls(bl))
            badecl = set(qualified_decls(ba)) if ba is not None else set()
            added = bdecl - badecl
            cur = set(qualified_decls(read(f)))
            missing = added - cur
            if missing:
                bad = 1
                print('MISSING-FROM-RESOLVED %s %s: %s' % (branch, f, sorted(missing)))
    elif mode == 'check-dup':
        for f in sys.argv[2:]:
            d = qualified_decls(read(f))
            for k, v in sorted(d.items()):
                if len(v) > 1:
                    bad = 1
                    print('DUPLICATE %s %s at lines %s' % (f, k, v))
    elif mode == 'check-comment':
        for f in sys.argv[2:]:
            _, depth = strip_comments(read(f))
            if depth != 0:
                bad = 1
                print('COMMENT-DEPTH %s = %d' % (f, depth))
    elif mode == 'check-binder':
        for f in sys.argv[2:]:
            lines = read(f)
            code, _ = strip_comments(lines)
            i = 0
            while i < len(code):
                m = DECL.match(code[i])
                if m:
                    j = i
                    sig = []
                    while j < len(code) and ':=' not in code[j] and not re.search(r'\bby\b\s*$', code[j]):
                        sig.append(code[j]); j += 1
                    if j < len(code):
                        sig.append(code[j])
                    k = j + 1
                    body = []
                    while k < len(code) and not DECL.match(code[k]):
                        body.append(code[k]); k += 1
                    sigtxt = '\n'.join(sig); bodytxt = '\n'.join(body)
                    for nm in set(re.findall(r'[\(\{\[]\s*(_[A-Za-z][A-Za-z0-9_\']*)', sigtxt)):
                        if re.search(r'(?<![A-Za-z0-9_\'])' + re.escape(nm[1:]) + r'(?![A-Za-z0-9_\'])', bodytxt):
                            bad = 1
                            print('UNDERSCORED-BINDER %s:%d %s uses %s' % (f, i + 1, m.group(1), nm[1:]))
                    i = k
                else:
                    i += 1
    sys.exit(bad)


main()
