#!/usr/bin/env python3
"""Declaration-level 3-way merge for Lean files.

    semmerge.py <branch> <file>

Splits BASE / OURS(HEAD) / THEIRS(branch) into declaration blocks (docstring +
attributes + header + body) keyed by namespace-qualified name, then:

  * theirs ADDED a declaration (not in base, not in ours)  -> splice it in
  * theirs CHANGED a block that ours left equal to base    -> take theirs
  * BOTH changed a block                                   -> keep ours, REPORT
  * theirs added `import` lines                            -> union into header

Writes the result to <file>; prints a report of every decision that is not a
pure addition.
"""
import re, sys, subprocess, collections

DECL = re.compile(
    r'^(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|public\s+|scoped\s+|local\s+)*'
    r'(theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom|example)\b'
    r'(?:\s+([A-Za-z_À-ɏͰ-Ͽᴀ-ᵿ℀-⅏][A-Za-z0-9_À-ɏͰ-Ͽᴀ-ᵿ₀-ₜ⁰-ⁿ℀-⅏.\'!?]*))?')
NS = re.compile(r'^\s*namespace\s+(\S+)')
ENDNS = re.compile(r'^\s*end\s*(\S*)\s*$')
ATTACH = re.compile(r'^\s*(@\[|set_option\b|open\b.*\bin\s*$|attribute\b)')


def comment_mask(lines):
    """True where the line is entirely comment / inside a block comment."""
    mask, depth = [], 0
    for ln in lines:
        s = ln.strip()
        if depth == 0:
            if s.startswith('/-'):
                mask.append(True)
                rest = ln[ln.index('/-') + 2:]
                if '-/' not in rest:
                    depth = 1
                continue
            mask.append(s.startswith('--'))
        else:
            mask.append(True)
            if '-/' in ln:
                depth = 0
    return mask


def split_blocks(text):
    """-> (items, names) where items is a list of ('glue', lines) / ('decl', qname, lines)."""
    lines = text.split('\n')
    mask = comment_mask(lines)
    stack = []
    heads = []          # (index, qname)
    for i, ln in enumerate(lines):
        if mask[i]:
            continue
        m = NS.match(ln)
        if m:
            stack.append(m.group(1)); continue
        m = ENDNS.match(ln)
        if m:
            if stack and (not m.group(1) or m.group(1) == stack[-1]):
                stack.pop()
            continue
        m = DECL.match(ln)
        if m and m.group(2):
            heads.append((i, '.'.join(stack + [m.group(2)])))

    # attach preceding docstring / attribute run to each head
    starts = []
    for (i, q) in heads:
        j = i
        while j > 0:
            p = lines[j - 1]
            if p.strip() == '':
                break
            if mask[j - 1] or ATTACH.match(p):
                j -= 1
                # walk to the top of a block comment
                if mask[j] and '-/' in lines[j] and not lines[j].strip().startswith('--'):
                    k = j
                    while k > 0 and not re.match(r'^\s*/-', lines[k]):
                        k -= 1
                    j = k
                continue
            break
        starts.append((j, i, q))

    items, cur, seen = [], 0, set()
    for (s, i, q) in starts:
        if s < cur:            # overlapping attachment, fold into previous
            continue
        if s > cur:
            items.append(('glue', None, lines[cur:s]))
        # block ends where the next block starts; provisional, fixed below
        items.append(('decl', q, [i]))   # placeholder, filled after
        cur = s
        seen.add(q)
    # rebuild with real extents
    items = []
    bounds = [(s, i, q) for (s, i, q) in starts]
    bounds = [b for k, b in enumerate(bounds) if k == 0 or b[0] >= bounds[k - 1][0]]
    cur = 0
    for k, (s, i, q) in enumerate(bounds):
        if s < cur:
            continue
        if s > cur:
            items.append(('glue', None, lines[cur:s]))
        end = len(lines)
        for (s2, i2, q2) in bounds[k + 1:]:
            if s2 > s:
                end = s2
                break
        items.append(('decl', q, lines[s:end]))
        cur = end
    if cur < len(lines):
        items.append(('glue', None, lines[cur:]))
    names = {}
    for kind, q, ls in items:
        if kind == 'decl':
            names.setdefault(q, []).append(ls)
    return items, names


def gs(rev, path):
    p = subprocess.run(['git', 'show', '%s:%s' % (rev, path)],
                       capture_output=True, text=True)
    return p.stdout if p.returncode == 0 else None


def main():
    branch, path = sys.argv[1], sys.argv[2]
    base = subprocess.run(['git', 'merge-base', 'HEAD', branch],
                          capture_output=True, text=True).stdout.strip()
    tb, to, tt = gs(base, path), gs('HEAD', path), gs(branch, path)
    if tt is None:
        print('%s: absent on branch, keeping ours' % path); return
    if to is None:
        with open(path, 'w') as f: f.write(tt)
        print('%s: absent on ours, taking theirs whole' % path); return
    if tb is None:
        tb = ''

    bi, bn = split_blocks(tb)
    oi, on = split_blocks(to)
    ti, tn = split_blocks(tt)

    def txt(ls): return '\n'.join(ls).strip()

    def docsplit(ls):
        """Leading comment/attribute run vs the code that follows."""
        m = comment_mask(ls)
        i = 0
        while i < len(ls) and (m[i] or ATTACH.match(ls[i]) or ls[i].strip() == ''):
            i += 1
        return ls[:i], ls[i:]

    def bodysorry(ls):
        """`sorry` token in CODE (comments stripped) inside this block."""
        m = comment_mask(ls)
        return any(re.search(r'(?<![A-Za-z0-9_\'])sorry(?![A-Za-z0-9_\'])', l)
                   for l, c in zip(ls, m) if not c)

    added, taken, conflicted, samepos = [], [], [], []

    # 1. decide, per theirs-name, what to do
    take_theirs = {}          # qname -> lines
    for q, blks in tn.items():
        tbk = blks[0]
        if q in on:
            obk = on[q][0]
            bbk = bn[q][0] if q in bn else None
            if txt(obk) == txt(tbk):
                continue
            odoc, ocode = docsplit(obk)
            tdoc, tcode = docsplit(tbk)
            bdoc, bcode = docsplit(bbk) if bbk is not None else (None, None)
            # docstring: whichever side changed it (ours wins if both)
            doc = odoc if (bdoc is None or txt(odoc) != txt(bdoc)) else tdoc
            if bcode is not None and txt(ocode) == txt(bcode) and txt(tcode) != txt(bcode):
                take_theirs[q] = doc + tcode; taken.append(q)
            elif bcode is not None and txt(tcode) == txt(bcode):
                if txt(doc) != txt(odoc):
                    take_theirs[q] = doc + ocode
                continue                      # theirs' code unchanged, ours evolved
            elif txt(ocode) == txt(tcode):
                take_theirs[q] = doc + ocode   # code agrees, only prose differed
                continue
            else:
                conflicted.append(q)
        elif q not in bn:
            take_theirs[q] = tbk; added.append(q)
        # q in base but not ours: ours deleted it deliberately -> skip

    # A BOTH-CHANGED block that CONSUMES one of theirs' new declarations must come
    # from theirs, or the new declaration lands orphaned (class-7 interface split).
    shortadd = {a.split('.')[-1] for a in added}
    rescued = []
    for q in list(conflicted):
        tb_txt, ob_txt = txt(tn[q][0]), txt(on[q][0])
        used = {s for s in shortadd
                if re.search(r'(?<![A-Za-z0-9_\'])' + re.escape(s) + r'(?![A-Za-z0-9_\'])', tb_txt)
                and not re.search(r'(?<![A-Za-z0-9_\'])' + re.escape(s) + r'(?![A-Za-z0-9_\'])', ob_txt)}
        if used and not (not bodysorry(on[q][0]) and bodysorry(tn[q][0])):
            odoc, _ = docsplit(on[q][0])
            _, tcode = docsplit(tn[q][0])
            take_theirs[q] = odoc + tcode
            conflicted.remove(q); rescued.append((q, sorted(used)))

    # 2. rebuild ours, substituting and splicing
    out = []
    inserted = set()
    ours_names_seq = [q for k, q, _ in oi if k == 'decl']
    theirs_seq = [q for k, q, _ in ti if k == 'decl']
    # for each added name, find the theirs-predecessor that exists in ours
    anchor = {}
    for idx, q in enumerate(theirs_seq):
        if q in added:
            a = None
            for p in reversed(theirs_seq[:idx]):
                if p in on:
                    a = p; break
            anchor.setdefault(a, []).append(q)

    tblk = {q: tn[q][0] for q in tn}
    # names with no anchor (start of file) go before the first ours decl
    head_adds = anchor.get(None, [])

    first_decl_done = False
    for kind, q, ls in oi:
        if kind == 'glue':
            out.extend(ls); continue
        if not first_decl_done and head_adds:
            for a in head_adds:
                out.extend(tblk[a]); inserted.add(a)
            first_decl_done = True
        first_decl_done = True
        if q in take_theirs and q in on:
            out.extend(take_theirs[q])
        else:
            out.extend(ls)
        for a in anchor.get(q, []):
            if a not in inserted:
                out.extend(tblk[a]); inserted.add(a)
    for a in added:
        if a not in inserted:
            out.extend(tblk[a]); inserted.add(a)

    res = '\n'.join(out)

    # 3. union new import lines (real header imports only: module path, no prose)
    IMP = re.compile(r'^(public\s+)?import\s+[A-Za-z_][A-Za-z0-9_.]*\s*$')
    oimp = [l for l in to.split('\n') if IMP.match(l)]
    timp = [l for l in tt.split('\n') if IMP.match(l)]
    newimp = [l for l in timp if l not in oimp and l.strip().split()[-1]
              not in [x.strip().split()[-1] for x in oimp]]
    if newimp and oimp:
        rl = res.split('\n')
        last = max(i for i, l in enumerate(rl) if l in oimp)
        rl[last + 1:last + 1] = newimp
        res = '\n'.join(rl)

    with open(path, 'w') as f:
        f.write(res)

    print('%s' % path)
    if added:      print('   ADDED    (%d): %s' % (len(added), ' '.join(sorted(added)[:40])))
    if taken:      print('   TOOK-THEIRS (%d): %s' % (len(taken), ' '.join(sorted(taken)[:40])))
    for q, u in rescued:
        print('   TOOK-THEIRS (consumes new %s): %s' % (','.join(u), q))
    if conflicted:
        print('   BOTH-CHANGED, kept ours (%d):' % len(conflicted))
        for q in sorted(conflicted):
            os_, ts_ = bodysorry(on[q][0]), bodysorry(tn[q][0])
            flag = ''
            if os_ and not ts_:
                flag = '   <<<< OURS SORRIED, THEIRS PROVEN -- REVIEW'
            elif ts_ and not os_:
                flag = '   (ours proven, theirs sorried: ours wins)'
            print('      %-70s ours_sorry=%s theirs_sorry=%s%s' % (q, os_, ts_, flag))
    if newimp:     print('   NEW IMPORTS: %s' % newimp)


main()
