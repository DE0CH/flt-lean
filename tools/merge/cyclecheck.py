#!/usr/bin/env python3
"""Import-cycle check for the project's own modules.

Release 28 lost its first two build rounds to a cycle

    X0 --> FreyCurve/IsogenySignature --> HyperellipticJacobian --> X0

introduced by one branch that added the last edge under a comment asserting
"there is no cycle, since X0.lean does not mention" that file.  The DIRECT edge
really was absent; the other two were years old.

What makes this worth a standing check rather than a code review is the failure
mode: `lake build` does not report a red module, it fails on the ROOT target with
`build cycle detected` and NOTHING in the project builds.  That reads like a
catastrophically broken tree rather than one bad import line, and the cycle
message names lake job identifiers (`+Fermat.X:importInfo`) rather than the edge
that closed the loop.

Cost: about a second.  Run it before the first build of every release, beside
commentscan.py and scopecheck.py.

Usage: cyclecheck.py [root]        exit 1 if any cycle is found
"""
import os
import re
import sys

IMPORT = re.compile(r'^(?:public\s+)?import\s+(Fermat[\w.]*)\s*$', re.M)


def module_path(mod):
    return mod.replace('.', '/') + '.lean'


def read_imports(mod, root):
    p = os.path.join(root, module_path(mod))
    if not os.path.exists(p):
        # ASSERT rather than skip.  A swallowed missing file truncates the walk
        # and manufactures the "no cycle" answer you were hoping for -- which is
        # exactly how the release-28 cycle was argued to be absent.
        raise FileNotFoundError(p)
    with open(p, encoding='utf-8') as fh:
        return IMPORT.findall(fh.read())


def all_modules(root):
    out = []
    for dirpath, _, files in os.walk(os.path.join(root, 'Fermat')):
        for f in files:
            if f.endswith('.lean'):
                rel = os.path.relpath(os.path.join(dirpath, f), root)
                out.append(rel[:-len('.lean')].replace('/', '.'))
    return sorted(out)


def find_cycles(root):
    mods = all_modules(root)
    graph, missing = {}, []
    for m in mods:
        try:
            graph[m] = read_imports(m, root)
        except FileNotFoundError as e:      # unreachable for a listed module
            missing.append(str(e))
    for m, deps in list(graph.items()):
        for d in deps:
            if d not in graph:
                missing.append(f"{m} imports {d}, which has no source file")
    # iterative DFS with an explicit colour map; the graph is ~300 nodes
    WHITE, GREY, BLACK = 0, 1, 2
    colour = {m: WHITE for m in graph}
    cycles = []
    for start in graph:
        if colour[start] != WHITE:
            continue
        stack = [(start, iter(graph.get(start, [])))]
        colour[start] = GREY
        path = [start]
        while stack:
            node, it = stack[-1]
            advanced = False
            for nxt in it:
                if nxt not in graph:
                    continue
                if colour[nxt] == GREY:
                    i = path.index(nxt)
                    cycles.append(path[i:] + [nxt])
                elif colour[nxt] == WHITE:
                    colour[nxt] = GREY
                    path.append(nxt)
                    stack.append((nxt, iter(graph.get(nxt, []))))
                    advanced = True
                    break
            if not advanced:
                colour[node] = BLACK
                stack.pop()
                if path:
                    path.pop()
    return cycles, missing, len(graph)


if __name__ == '__main__':
    root = sys.argv[1] if len(sys.argv) > 1 else os.getcwd()
    cycles, missing, n = find_cycles(root)
    for m in missing:
        print("MISSING  " + m)
    seen = set()
    for c in cycles:
        key = tuple(sorted(set(c)))
        if key in seen:
            continue
        seen.add(key)
        print("CYCLE    " + " -> ".join(c))
    print(f"(scanned {n} modules under Fermat/)")
    sys.exit(1 if (cycles or missing) else 0)
