#!/usr/bin/env python3
"""Find OPEN LEAVES THAT ARE ALSO DEAD -- the seventh invisibility class.

A leaf can be open, compile, emit its `declaration uses `sorry`` warning, pass
`own.py` and `leafstat.py`, and still be worth nothing to close, because no
chain of citations from `fermat_last_theorem` reaches it.

The naive one-hop check ("does anything consume this?") does NOT find these.
flt-lean-256 was dispatched at a leaf with TWO real code call sites, both in
proven theorems; the chain died two hops up at a PROVEN theorem with no
consumer at all.  Only the transitive walk sees it.

TWO CLASSES.  ~23% of open leaves are outside the root's cone at any time and
almost all of that is normal, so the split is the whole point of the script:

  PENDING    the leaf's upward closure reaches a SORRIED declaration.  A sorried
             body contributes no dependency edges, so material built bottom-up
             ahead of its consumer is out of the cone BY CONSTRUCTION.  Ordinary
             work in progress.  Leave it alone.  (37 on 2026-08-01.)

  CANDIDATE  every maximal element of the closure is PROVEN and consumed by
             nothing.  This is the project's free-floating condition at leaf
             granularity, and it is the class that contains genuinely dead work.
             (47 on 2026-08-01, after one was removed.)

*** A CANDIDATE IS NOT A DELETION ORDER.  READ THIS BEFORE ACTING ON ONE. ***

Most candidates are PROVEN top-level package theorems that are the intended
endpoint of their subtree and whose consumer has simply not been written yet --
`exists_moretBailly_seed_of_five_le`, `redPt_injective_three` and the like.
Deleting those destroys live work, which is the exact failure CLAUDE.md records
against `dc6836b9` (35 declarations deleted where 18 were poisoned).

What distinguishes a genuinely DEAD island is one further check, and it is not
mechanical: the island's INTENDED CONSUMER must be verifiably ABSENT -- deleted,
with the commit that removed it -- rather than merely unwritten.  The case this
script was written from (`flt-lean-256`, Threeadic.lean, 2026-08-01) had
`exists_ordinary_line_of_flat_hopf_package` occurring NOWHERE in the tree, on
`main` or on `merger`, having gone with a refuted cone in `0c5c678c`.  That is
the evidence to look for; the closure alone does not supply it.

So: use this to produce a review list, never a patch.

Usage:
    python3 tools/merge/deadleaf.py                # scan the repo this file is in
    python3 tools/merge/deadleaf.py --root DIR
    python3 tools/merge/deadleaf.py --pending      # also list the PENDING ones

Exit status is 0 unless the scan itself could not run: a candidate list is a
report, not a gate, and a gate that fails on every release is a gate nobody runs.
"""
import argparse
import os
import re
import sys

# The root of the dependency cone.  Everything the sorry gate protects hangs off it.
ROOT_DECL = "fermat_last_theorem"

# `Fermat/SorryGate.lean` contains the token `sorry` inside a STRING LITERAL in
# its `elab`; any scan that does not exclude it is off by one.
SKIP_FILES = {"SorryGate.lean"}

DECL_HEAD = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|public\s+)*"
    r"(theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s({\[:]+)"
)
SORRY_TOKEN = re.compile(r"(?<![A-Za-z_])sorry(?![A-Za-z_])")


def strip_comments(text):
    """Blank out line and NESTED block comments, preserving line numbering."""
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        if depth == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            if j < 0:
                break
            out.append("\n")
            i = j + 1
            continue
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if text.startswith("-/", i):
            if depth > 0:
                depth -= 1
            i += 2
            continue
        if depth == 0:
            out.append(text[i])
        elif text[i] == "\n":
            out.append("\n")
        i += 1
    return "".join(out)


def tokenise(text):
    """Unicode-safe identifier split.

    Do NOT use a character class such as `À-￿`: it swallows the bracket
    characters `⟨⟩←▸`, so every name inside an anonymous constructor is lost.
    Splitting on "not isalnum and not one of _ ' ." keeps `ι`, `Ψ`, `₁`.
    """
    cur, out = "", []
    for ch in text:
        if ch.isalnum() or ch in "_'.":
            cur += ch
        else:
            if cur:
                out.append(cur)
                cur = ""
    if cur:
        out.append(cur)
    return out


def scan(root):
    """-> (uses, where, sorried); every declaration keyed by LAST dotted component."""
    uses, where, sorried = {}, {}, set()
    base = os.path.join(root, "Fermat")
    for dirpath, _dirnames, filenames in os.walk(base):
        for fn in sorted(filenames):
            if not fn.endswith(".lean") or fn in SKIP_FILES:
                continue
            path = os.path.join(dirpath, fn)
            rel = os.path.relpath(path, root)
            src = strip_comments(open(path, encoding="utf-8").read()).split("\n")
            heads = [
                (k, m.group(2))
                for k, line in enumerate(src, 1)
                if (m := DECL_HEAD.match(line))
            ]
            for idx, (k, name) in enumerate(heads):
                end = heads[idx + 1][0] - 1 if idx + 1 < len(heads) else len(src)
                short = name.split(".")[-1]
                body = "\n".join(src[k - 1 : end])
                uses.setdefault(short, set()).update(
                    t.split(".")[-1] for t in tokenise(body)
                )
                where.setdefault(short, (rel, k))
                if SORRY_TOKEN.search(body):
                    sorried.add(short)
    return uses, where, sorried


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", default=None,
                    help="repository root (default: the repo this script lives in)")
    ap.add_argument("--pending", action="store_true",
                    help="also list PENDING leaves (out of cone, chain reaches a sorry)")
    args = ap.parse_args()

    # Never hardcode an absolute root: a tool rooted at somebody else's worktree
    # silently reports THEIR tree and looks like an answer about yours.
    root = args.root or os.path.dirname(os.path.dirname(os.path.dirname(
        os.path.abspath(__file__))))
    if not os.path.isdir(os.path.join(root, "Fermat")):
        sys.exit(f"no Fermat/ under {root}")

    uses, where, sorried = scan(root)
    users = {}
    for name, toks in uses.items():
        for t in toks:
            if t != name:
                users.setdefault(t, set()).add(name)

    if ROOT_DECL not in uses:
        sys.exit(f"root declaration {ROOT_DECL} not found under {root}/Fermat")

    cone, stack = {ROOT_DECL}, [ROOT_DECL]
    while stack:
        for u in uses.get(stack.pop(), ()):
            if u not in cone and u in uses:
                cone.add(u)
                stack.append(u)

    leaves = sorted(l for l in sorried if l in uses)
    dead, pending = [], []
    for leaf in leaves:
        if leaf in cone:
            continue
        up, stack = {leaf}, [leaf]
        while stack:
            for u in users.get(stack.pop(), ()):
                if u not in up:
                    up.add(u)
                    stack.append(u)
        if up & cone:
            continue
        # MAXIMAL means consumed by nothing at all -- not merely "every consumer is
        # inside the island", which in a chain `leaf <- mid <- top` is also true of
        # the leaf and would misclassify every island as PENDING.
        tops = [n for n in up if not users.get(n, set())]
        if tops and all(t not in sorried for t in tops):
            dead.append((leaf, up, tops))
        else:
            pending.append((leaf, up))

    print(f"root cone: {len(cone)} declarations")
    print(f"open leaves: {len(leaves)}   outside the cone: {len(dead) + len(pending)}")
    print(f"  PENDING (normal bottom-up work, leave alone): {len(pending)}")
    print(f"  CANDIDATES (review, do NOT delete blind):      {len(dead)}")
    for leaf, up, tops in dead:
        rel, line = where[leaf]
        print(f"\nCANDIDATE {rel}:{line}  {leaf}")
        print(f"     island of {len(up)} declarations; maximal elements, all PROVEN "
              f"and consumed by nothing:")
        for t in sorted(tops):
            trel, tline = where[t]
            print(f"       {t}  [{trel}:{tline}]")
    if args.pending:
        for leaf, up in pending:
            rel, line = where[leaf]
            print(f"pending {rel}:{line}  {leaf}  (island {len(up)})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
