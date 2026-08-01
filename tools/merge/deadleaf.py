#!/usr/bin/env python3
"""Report OPEN LEAVES THAT NOTHING CONSUMES.

A leaf can be open, compile, emit an honest `declaration uses 'sorry'` warning,
pass every ownership test -- and still be worth nothing to close, because no
proof term reachable from the root ever mentions it.  Closing such a leaf moves
the frontier count and does not move the project; worse, it keeps drawing
dispatches for ever.  CLAUDE.md calls this the seventh invisibility class.

The three ways a leaf ends up dead, all seen in this tree:

  * DELETE x REFACTOR -- one branch deletes a leaf's only consumer while another
    refactors the leaf; both merge cleanly and the leaf is orphaned;
  * A RIVAL CUT LANDS -- two agents cut one node two ways, the merge keeps both,
    the parent's proof picks one, and the loser's halves are stranded;
  * A HOIST CARRIES THE LEAF AND NOT THE CUT -- a leaf hoisted upstream (to break
    an import cycle, say) leaves the halves it was cut into behind, DOWNSTREAM of
    itself, where declaration order makes them uncitable.  That is
    `flt-lean-378`, 2026-08-01, and it is why this script exists.

None of the three is visible to any other instrument: nothing is duplicated,
nothing is renamed, no name is missing, no comment is unbalanced, every module
builds, and every sorry warning is truthful.  The ONLY trace is the missing
consumer.

WHAT A HIT MEANS, precisely.  The leaf's short name (last dotted component) does
not occur ANYWHERE in the comment-stripped source of `Fermat/` outside its own
declaration.  That is a strong signal and it is not a proof of deadness: the leaf
could still be reached through an `open`ed abbreviation this scan does not model.
It is, however, sound in the useful direction -- a leaf that is NOT flagged
certainly has an occurrence, so the flagged set is an over-approximation of the
live set's complement and every hit is worth one grep.

WHAT TO DO WITH A HIT, and it is NOT automatically "delete":

  * find the declaration the leaf was cut out of, and check whether that parent is
    proven by a RIVAL route.  If so the leaf is the loser of a duplicated cut --
    prefer deriving it from the winner (one line) to deleting it, unless it has no
    prospect of a consumer at all;
  * check whether the leaf and its siblings were separated by a RELOCATION.  If the
    cut is merely on the wrong side of an import edge, the repair is to move it
    back, not to delete anything -- that is a strict frontier win with no
    mathematics done;
  * only when neither applies is the leaf garbage.  Delete it and say in the
    section docstring where to recover it from.

Do NOT delete a leaf that has a live owner in `~/.flt-loop/jobs`; tidiness is not
worth destroying another agent's in-flight target.

Usage:
    python3 tools/merge/deadleaf.py [--root DIR] [--quiet]

`--root` defaults to the repository this file lives in, so it is safe to run from
a worktree.  (Several scanners in this directory used to hardcode the merge
worker's staging tree and silently report ITS frontier; see CLAUDE.md.)
"""

import collections
import pathlib
import re
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve()
ROOT = HERE.parents[2]
if "--root" in sys.argv:
    ROOT = pathlib.Path(sys.argv[sys.argv.index("--root") + 1]).resolve()
QUIET = "--quiet" in sys.argv

# `Fermat/SorryGate.lean` contains the token `sorry` twice inside a STRING LITERAL
# in its `elab`; every scan in this tree has to exclude it or be off by two.
SKIP = {"Fermat/SorryGate.lean"}


def strip_comments(text: str) -> str:
    """Remove Lean line and (nesting) block comments, keeping everything else."""
    out = []
    depth = 0
    i = 0
    n = len(text)
    while i < n:
        if depth == 0 and text.startswith("--", i) and not text.startswith("-/", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
            continue
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if text.startswith("-/", i) and depth > 0:
            depth -= 1
            i += 2
            continue
        if depth == 0:
            out.append(text[i])
        i += 1
    return "".join(out)


def open_leaves():
    """(file, line, fully-qualified name) for every direct sorry, via frontier.py."""
    fr = HERE.parent / "frontier.py"
    res = subprocess.run(
        [sys.executable, str(fr), "--root", str(ROOT)],
        capture_output=True, text=True,
    )
    if res.returncode != 0:
        sys.stderr.write(res.stderr)
        raise SystemExit("frontier.py failed")
    leaves = []
    for line in res.stdout.splitlines():
        parts = line.split("\t")
        if len(parts) < 3:
            continue
        f, ln, name = parts[0], parts[1], parts[-1]
        if f in SKIP or name.startswith("<"):
            continue
        leaves.append((f, ln, name))
    return leaves


def token_counts():
    """How often each identifier piece occurs in comment-stripped `Fermat/`.

    Both the full dotted name and each dotted piece are counted, so a leaf reached
    by dot notation (`h.foo`) is correctly seen as CONSUMED and not reported.
    """
    counts = collections.Counter()
    for p in sorted(ROOT.glob("Fermat/**/*.lean")):
        if str(p.relative_to(ROOT)) in SKIP:
            continue
        src = strip_comments(p.read_text(encoding="utf-8", errors="replace"))
        # Split on anything that cannot appear in a Lean identifier.  Do NOT use a
        # unicode range such as `À-` here: it swallows `⟨⟩←▸` and silently merges
        # every name inside an anonymous constructor with its neighbours.
        for word in re.split(r"[^A-Za-z0-9_'.]+", src):
            if not word:
                continue
            counts[word] += 1
            if "." in word:
                for piece in word.split("."):
                    if piece:
                        counts[piece] += 1
    return counts


def main() -> int:
    leaves = open_leaves()
    counts = token_counts()
    dead = []
    for f, ln, name in leaves:
        # A frontier row for a declaration carrying explicit universe parameters
        # ends in a dot, and a naive `split('.')[-1]` is then the empty string,
        # which matches nothing and reports every such leaf as dead.
        short = name.rstrip(".").split(".")[-1]
        if not short:
            continue
        if counts[short] <= 1:
            dead.append((f, int(ln), name))
    dead.sort()
    if not QUIET:
        for f, ln, name in dead:
            print(f"DEADLEAF {f}:{ln}  {name}")
    print(f"{len(dead)} consumerless open leaf/leaves out of {len(leaves)}")
    return 1 if dead else 0


if __name__ == "__main__":
    raise SystemExit(main())
