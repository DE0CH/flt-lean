import json, re, sys

path = 'PROGRESS.md'
src = open(path).read()
lines = src.split('\n')

# The tree section: from the "## Tree" heading to the next "## " heading.
tree_start = next(i for i,l in enumerate(lines) if l.startswith('## Tree'))
tree_end = next(i for i in range(tree_start+1, len(lines)) if lines[i].startswith('## '))

marker_re = re.compile(r'^(\s*)- (✅✅|✅|❌)([·🟪])(.*)$')

# 1. Parse into a structured tree (list of nodes with indent, line no, mark, label head).
nodes = []
for i in range(tree_start, tree_end):
    m = marker_re.match(lines[i])
    if m:
        indent, mark, state, rest = m.groups()
        mark = '✅' if mark.startswith('✅') else mark  # ✅✅ recomputed fresh
        label = rest.strip()[:100]
        nodes.append({'line': i, 'indent': len(indent), 'mark': mark,
                      'state': state, 'label': label, 'children': []})

# Build hierarchy by indentation (stack).
roots, stack = [], []
for n in nodes:
    while stack and stack[-1]['indent'] >= n['indent']:
        stack.pop()
    if stack:
        stack[-1]['children'].append(n)
    else:
        roots.append(n)
    stack.append(n)

# 2. Compute subtree-sorry-freeness: node PROVEN iff its own mark is ✅
#    and every child subtree is PROVEN.
def resolve(n):
    kids = [resolve(c) for c in n['children']]
    ok = (n['mark'] == '✅') and all(kids)
    n['proven'] = ok
    return ok
for r in roots:
    resolve(r)

def strip(n):
    return {'line': n['line']+1, 'mark': n['mark'], 'state': n['state'],
            'proven': n['proven'], 'label': n['label'],
            'children': [strip(c) for c in n['children']]}
json.dump([strip(r) for r in roots], open('progress-tree.json','w'),
          ensure_ascii=False, indent=1)

# 3. Rewrite the marker lines: ✅ with proven subtree -> ✅✅ ; others unchanged.
count2 = 0
for n in nodes:
    if n['mark'] == '✅' and n['proven']:
        i = n['line']
        lines[i] = marker_re.sub(lambda m: f"{m.group(1)}- ✅✅{m.group(3)}{m.group(4)}",
                                 lines[i], count=1)
        count2 += 1
open(path,'w').write('\n'.join(lines))
print(f"nodes: {len(nodes)}, double-ticked (PROVEN subtrees): {count2}")
