#!/usr/bin/env python3
"""Generate a queue task for every UNCOVERED open leaf.

The queue-coverage invariant the release owes is

    every open sorry is queued, or held by a live agent

and the leaves that fall through are, by construction, the ones NOBODY has
written a prompt for -- typically residues cut on a branch during the release
window, which exist on `merger` and on no ownership record anywhere.

A task is only useful if it carries the context a prover needs, and for this
tree that context is the leaf's OWN DOCSTRING: it holds the route, the audit,
the counterexample and the "what remains" list.  So each generated task quotes
it rather than paraphrasing.  The standing per-task preamble (merge main, check
merger, PATH, verification) is the same for every leaf and is emitted verbatim.

Usage: gentask.py <uncovered.json> <frontier.tsv>   > tasks.txt
"""
import json, sys, re, pathlib

ROOT = pathlib.Path('/home/chend/flt-staging')

PREAMBLE = """Work in {{FLT_WORKTREE}}, on its same-named branch.

BEFORE YOUR FIRST EDIT, in this order -- each is one command and each has cost a
previous agent a whole run:

  export PATH="$HOME/.elan/bin:$PATH"      # lake is NOT on PATH in your shell;
                                           # a missing lake exits 127 with an
                                           # empty log that reads like a clean build
  git rev-list --count HEAD..main          # MUST be 0; if not:
  git merge --ff-only main
  git show merger:{FILE} | grep -n 'theorem {NAME}'

The last one is the release-window check and it is the one that matters: task
prompts are generated from `main`, and `main` is the frontier as of the last
release.  If `merger` already proves your target, or has RESTATED it, say so in
your sentinel and do NOT carry a rival cut -- read the DECLARATION, not just the
name, because a leaf can be closed under a changed signature.

If the line number below does not land on the declaration, your worktree is
stale -- merge `main` before concluding anything about the leaf.

Verify with `lake build <Module>` and `lake env lean <file>` on the command line.
There is no Lean MCP and no report server.  Require a literal `EXIT=0` AND a
`Build completed successfully (NNNN jobs)` line before believing a build; the
absence of the word "error" is also what a build that never started looks like.

Develop against a SCRATCH module that `public import`s the target's module and
restates your target under a primed name -- measured at 6 s per round against
~25 min for a full build of the big modules.  Only use names declared BEFORE
your target's line, and do the one real build at the end.
"""

TAIL = """
A refutation with an explicit counterexample is a FULL SUCCESS, not a failure --
say so plainly and restate the leaf correctly.  So is discovering the leaf is
already proven elsewhere, or that it is DEAD (no consumer reaches it): grep the
comment-stripped tree for consumers of your target and of each declaration that
consumes it before proving anything, because closing a leaf nothing reaches
moves the count and not the project.
"""


def strip_block_comments_keep_doc(lines):
    return lines


def docstring_above(lines, decl_idx):
    """Return the `/-- ... -/` block immediately above a 0-indexed decl line."""
    i = decl_idx - 1
    while i >= 0 and lines[i].strip() == '':
        i -= 1
    if i < 0 or not lines[i].rstrip().endswith('-/'):
        return []
    j = i
    while j >= 0 and not lines[j].lstrip().startswith('/--'):
        j -= 1
    if j < 0:
        return []
    return lines[j:i + 1]


def main(uncov_path, frontier_path):
    uncov = set(json.load(open(uncov_path)))
    rows = []
    for ln in open(frontier_path, encoding='utf-8'):
        f, l, n = ln.rstrip('\n').split('\t')
        if n.split('.')[-1] in uncov:
            rows.append((f, int(l), n))
    cache = {}
    out = []
    for f, l, n in rows:
        if f not in cache:
            cache[f] = (ROOT / f).read_text(encoding='utf-8').split('\n')
        lines = cache[f]
        short = n.split('.')[-1]
        doc = docstring_above(lines, l - 1)
        # cap the quoted docstring: these run to 300 lines in this tree
        if len(doc) > 120:
            doc = doc[:120] + ['', '  [... docstring truncated; READ IT IN FULL IN THE FILE ...]']
        body = PREAMBLE.replace('{FILE}', f).replace('{NAME}', short)
        t = [f"TARGET: `{short}`", f"({f}:{l})", "", body]
        if doc:
            t += ["", "ITS OWN DOCSTRING, quoted so you can judge before opening the file --",
                  "treat its ROUTE and its cost estimates as HYPOTHESES (they were written",
                  "before anyone tried), but its FALSITY AUDITS as binding until you refute",
                  "them yourself.  An absence claim ('not in mathlib', 'nowhere stated') is",
                  "scoped to the import cone and the DATE it was written -- re-grep it:", ""]
            t += ['    ' + d for d in doc]
        t.append(TAIL)
        out.append('\n'.join(t))
    print('\n=== TASK ===\n'.join(out))
    print(f"\n<!-- generated {len(out)} tasks -->", file=sys.stderr)


if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2])
