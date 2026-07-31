# Merge-worker tooling (written at release 26)

These are the scripts that merged release 26's 24 conflicting branches. They are
committed here rather than left in `/tmp` because every merge worker so far has
rewritten them from scratch, and two of the bugs below cost a build round each.

Run them from the staging worktree, on the working tree, mid-merge.

| script | question it answers |
|---|---|
| `semmerge.py <branch> <file>` | resolve a conflicted Lean file at DECLARATION granularity |
| `scopecheck.py <files…>` | is any `namespace`/`section` unbalanced? |
| `checks.py check-dup / check-comment / check-branch / check-binder` | duplicates, comment nesting, payload presence, underscored binders |
| `verify_added.py <branches…>` | did every branch-ADDED declaration land somewhere in the tree? |
| `domerge.sh <branches…>` | driver: merge, resolve, check, commit, one branch at a time |

## Why declaration granularity

Release 24's textual union policy DROPS PAYLOAD when both sides edit adjacent
lines: `difflib` reports one `replace` opcode and the "keep theirs' pure
insertions" rule keeps nothing. Measured at release 26: five branch-added
declarations silently lost from one file.

`semmerge.py` splits BASE/OURS/THEIRS into declaration blocks keyed by
namespace-qualified name and decides per name. It prints every decision that is
not a pure addition; **read that output**, especially `BOTH-CHANGED, kept ours`,
which is the only case needing judgement (nine of them across 24 branches).

## The three things that are easy to get wrong

1. **Decide on CODE, merge docstrings separately.** Otherwise a docstring edit on
   merger's side makes every code take-theirs look like a conflict — and splitting
   a multi-site interface repair across sides is the class-7 failure.
2. **A block that CONSUMES one of theirs' new declarations must come from theirs**,
   or the new leaf lands orphaned. Guarded so it cannot resurrect a `sorry`.
3. **SCOPE LINES ARE NOT DECLARATIONS.** `namespace`, `section`, `variable` sit in
   the glue between blocks, and a block's extent runs to the next block's start —
   so replacing a block deletes the glue after it. Four scopes were lost this way
   in one release. `scopecheck.py` is the whole defence; run it on the result and
   difference against pre-merge `main`, because this tree has legitimate patterns
   that the naive check flags.

## What `semmerge.py` still does NOT do

It does not reorder. If merger's declaration order differs from the branch's, an
added helper can land BELOW its consumer, and Lean's linear order is a dependency
edge: the symptom is `Unknown identifier` on a name that `grep` finds. Three
relocations were needed at release 26. Move code DOWN (it cannot break the moved
code's own dependencies), and verify the move is byte-exact by sorting the whole
file before and after and diffing the multiset.

## `scopecheck.py` over-reports, and that is deliberate

Lean allows a bare `end` to close a *named* `section`, and this tree interleaves
`section`/`namespace` freely, so a strict stack model flags a dozen files that
compile perfectly. Two consequences:

* **Always difference against pre-merge `main`.** Only the NEW reports are yours.
  Release 26: seven reports on `X0.lean`, three of them pre-existing.
* **Run it over EVERY file under `Fermat/`, not just the ones your batch touched.**
  The unclosed `section HalfAColimit` in `AbelianSchemeIsogeny.lean` — a
  pre-existing wound that blocked most of the tree — was found by build round 5
  and would have been found before round 1 by a tree-wide run.

Do not tune the false positives away by weakening the model; tune them away by
subtracting the baseline. A checker that reports nothing is the one that missed
the four wounds this release had to find with the compiler.
