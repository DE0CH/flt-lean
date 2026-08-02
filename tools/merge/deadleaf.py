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
"""Report sorried declarations that NOTHING IN THE TREE CONSUMES.
A leaf with no consumer is worth nothing to close: proving it moves the frontier
count and moves the project not at all.  Worse, it keeps drawing dispatches --
every such leaf is a phantom task waiting to be issued, and one of them issued
the task that produced this script (`exists_chartAtInfinity_of_finite_toAffineLine`,
deleted 2026-08-01; see CLAUDE.md, "WHEN BOTH RIVAL ROOTS ARE STILL OPEN").
NO OTHER INSTRUMENT SEES THIS.  The declaration is open, so `lake build` emits its
`declaration uses 'sorry'` warning truthfully; a source scan finds the token; the
frontier scans count it; `own.py` and `leafstat.py` correctly report it unowned.
Every one of them answers "is this leaf open", and none answers "does anything
reach it".
## Usage
    python3 tools/merge/deadleaf.py                # whole tree, repo-relative
    python3 tools/merge/deadleaf.py --root DIR     # another checkout
    python3 tools/merge/deadleaf.py --verbose      # also print live leaves' hit counts
ROOT defaults to the repository this script lives in -- NOT to a hardcoded
staging path.  (Three scanners in this repo have shipped with `ROOT` pinned to
`/home/chend/flt-staging`, which silently reports the merge worker's tree with
its line numbers; see CLAUDE.md.  Do not reintroduce that.)
## How it decides
Comment-strip every `.lean` file under `Fermat/` (nested block comments and line
comments, blanked out so line numbers are preserved), attribute each surviving
`sorry` token to the nearest declaration header ABOVE it, then search the whole
stripped tree for the declaration's LAST NAME COMPONENT, preceded by anything
that is not an identifier character (so `Foo.bar`, `h.bar` and bare `bar` all
count) and followed by a non-identifier character.  Its own declaration line is
excluded.  Zero hits => reported.
## Reading the output -- three things it is NOT
* **"No consumer" is not "delete it".**  A cut that lands before its parent is
  rewired legitimately has no consumer for a while, and a leaf at the top of its
  own subtree may be waiting for glue somebody is writing.  The report is a list
  of things to CHECK, not a work order.  Check the parent's proof body first:
  if the parent is PROVEN and its body names a DIFFERENT leaf, you have a rival
  cut and this leaf lost it.
* **When it IS a rival-cut orphan, deletion is not automatic either.**  Compare
  the two roots: keep the arrangement whose root is IMPLIED by the rival's root,
  so the tree owes the weaker obligation.  If the loser is strictly stronger and
  the winner is itself open, it cannot be demoted to a proven corollary and
  deletion is right; salvage its docstring analysis onto the survivor first.
* **It UNDER-reports, deliberately.**  Matching is by last name component, so a
  dead `Foo.bar` is called live if any unrelated `Bar.bar` is used anywhere.
  That is the safe direction: a false "live" costs nothing, a false "dead"
  invites a wrong deletion.
## Calibration (2026-08-01, at the release-33 tree)
378 sorried declarations, **36** with zero code consumers.  The run independently
rediscovers two orphans CLAUDE.md documents from earlier tasks --
`map_add_relPointWeierstrassEquiv` (`ModularCurve/X1.lean`, the semantic-merge
orphan of `flt-lean-113`) and `exists_pow_Pz_mul_mem_idl`
(`Mathlib/.../ProjectiveEquationAdd2.lean`, the duplicated-cut pair) -- which is
the check that it works.  **Re-run this calibration whenever you touch the
script**; a scanner that reports nothing is indistinguishable from a scanner that
is broken.
import subprocess
DECL = re.compile(
    r'^(?:@\[[^\]]*\]\s*)?'
    r'(?:private\s+|protected\s+|noncomputable\s+|public\s+|scoped\s+|partial\s+|unsafe\s+)*'
    r'(theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s\(\{\[:]+)'
SORRY = re.compile(r"(^|[^A-Za-z0-9_.'])sorry([^A-Za-z0-9_']|$)")
def strip_comments(text: str) -> str:
    """Blank out Lean comments, preserving every newline so line numbers survive.
    Block comments NEST in Lean, so this tracks depth rather than scanning for the
    first terminator; a line comment only starts a comment at depth 0.
    out = []
    i, n, depth = 0, len(text), 0
        if depth == 0 and text.startswith('--', i):
            j = text.find('\n', i)
            j = n if j < 0 else j
            out.append(' ' * (j - i))
            i = j
        if text.startswith('/-', i):
            out.append('  ')
        if text.startswith('-/', i) and depth > 0:
            depth -= 1
            out.append('  ')
        c = text[i]
        out.append(' ' if (depth > 0 and c != '\n') else c)
    return ''.join(out)
def repo_root() -> str:
    here = os.path.dirname(os.path.abspath(__file__))
    try:
        return subprocess.run(['git', '-C', here, 'rev-parse', '--show-toplevel'],
                              capture_output=True, text=True, check=True).stdout.strip()
    except Exception:
        return os.path.abspath(os.path.join(here, '..', '..'))
def main() -> int:
    ap.add_argument('--root', default=None, help='repository root (default: this script\'s repo)')
    ap.add_argument('--verbose', action='store_true', help='also print consumer counts for live leaves')
    root = args.root or repo_root()
    base = os.path.join(root, 'Fermat')
    if not os.path.isdir(base):
        print(f'deadleaf: no Fermat/ under {root}', file=sys.stderr)
        return 2
    files = []
    for d, _, fs in os.walk(base):
        for f in fs:
            if f.endswith('.lean'):
                files.append(os.path.relpath(os.path.join(d, f), root))
    files.sort()
    stripped = {}
    for f in files:
        with open(os.path.join(root, f), encoding='utf-8') as fh:
            stripped[f] = strip_comments(fh.read()).split('\n')
    # (file, 1-indexed line, name) for each declaration whose body contains a sorry
    leaves, seen = [], set()
    for f in files:
        lines = stripped[f]
        decls = []
        for i, line in enumerate(lines):
            m = DECL.match(line)
            if m and m.group(2):
                decls.append((i, m.group(2)))
        for i, line in enumerate(lines):
            if not SORRY.search(line):
            owner = [d for d in decls if d[0] <= i]
            if not owner:
            name = owner[-1][1]
            if name in seen:
            seen.add(name)
            leaves.append((f, owner[-1][0] + 1, name))
    dead = []
    for (f, ln, name) in leaves:
        short = name.split('.')[-1]
        if len(short) < 4:      # too short to match reliably; treat as live
        pat = re.compile(r"(^|[^A-Za-z0-9_'])" + re.escape(short) + r"([^A-Za-z0-9_']|$)")
        hits = 0
        for g in files:
            for j, line in enumerate(stripped[g], 1):
                if g == f and j == ln:
                    continue
                if pat.search(line):
                    hits += 1
        if hits == 0:
            dead.append((f, ln, name))
        elif args.verbose:
            print(f'live {hits:5d}  {f}:{ln}  {name}')
    print(f'sorried declarations: {len(leaves)}')
    print(f'\n=== SORRIED DECLARATIONS WITH ZERO CODE CONSUMERS ({len(dead)}) ===')
    for f, ln, name in dead:
        print(f'{f}:{ln}  {name}')
    print('\nEach is a leaf whose closure would move the count and not the project.'
          '\nCheck the parent\'s PROOF BODY before acting: a proven parent naming a'
          '\ndifferent leaf means a rival cut landed and this one lost.')
if __name__ == '__main__':
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
    python3 tools/merge/deadleaf.py [--root DIR] [--quiet]
`--root` defaults to the repository this file lives in, so it is safe to run from
a worktree.  (Several scanners in this directory used to hardcode the merge
worker's staging tree and silently report ITS frontier; see CLAUDE.md.)
import collections
import pathlib
HERE = pathlib.Path(__file__).resolve()
ROOT = HERE.parents[2]
if "--root" in sys.argv:
    ROOT = pathlib.Path(sys.argv[sys.argv.index("--root") + 1]).resolve()
QUIET = "--quiet" in sys.argv
# `Fermat/SorryGate.lean` contains the token `sorry` twice inside a STRING LITERAL
# in its `elab`; every scan in this tree has to exclude it or be off by two.
SKIP = {"Fermat/SorryGate.lean"}
    """Remove Lean line and (nesting) block comments, keeping everything else."""
    depth = 0
    i = 0
    n = len(text)
        if depth == 0 and text.startswith("--", i) and not text.startswith("-/", i):
            i = n if j < 0 else j
        if text.startswith("-/", i) and depth > 0:
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
        f, ln, name = parts[0], parts[1], parts[-1]
        if f in SKIP or name.startswith("<"):
        leaves.append((f, ln, name))
    return leaves
def token_counts():
    """How often each identifier piece occurs in comment-stripped `Fermat/`.
    Both the full dotted name and each dotted piece are counted, so a leaf reached
    by dot notation (`h.foo`) is correctly seen as CONSUMED and not reported.
    counts = collections.Counter()
    for p in sorted(ROOT.glob("Fermat/**/*.lean")):
        if str(p.relative_to(ROOT)) in SKIP:
        src = strip_comments(p.read_text(encoding="utf-8", errors="replace"))
        # Split on anything that cannot appear in a Lean identifier.  Do NOT use a
        # unicode range such as `À-` here: it swallows `⟨⟩←▸` and silently merges
        # every name inside an anonymous constructor with its neighbours.
        for word in re.split(r"[^A-Za-z0-9_'.]+", src):
            if not word:
            counts[word] += 1
            if "." in word:
                for piece in word.split("."):
                    if piece:
                        counts[piece] += 1
    return counts
    leaves = open_leaves()
    counts = token_counts()
    for f, ln, name in leaves:
        # A frontier row for a declaration carrying explicit universe parameters
        # ends in a dot, and a naive `split('.')[-1]` is then the empty string,
        # which matches nothing and reports every such leaf as dead.
        short = name.rstrip(".").split(".")[-1]
        if not short:
        if counts[short] <= 1:
            dead.append((f, int(ln), name))
    dead.sort()
    if not QUIET:
        for f, ln, name in dead:
            print(f"DEADLEAF {f}:{ln}  {name}")
    print(f"{len(dead)} consumerless open leaf/leaves out of {len(leaves)}")
    return 1 if dead else 0
    raise SystemExit(main())
