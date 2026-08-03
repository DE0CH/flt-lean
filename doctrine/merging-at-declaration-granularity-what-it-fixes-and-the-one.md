## MERGING AT DECLARATION GRANULARITY: what it fixes, and the ONE thing it silently breaks

(2026-07-31, release 26 — 24 conflicting branches over files both sides had rewritten
heavily.) Release 24's textual union policy (hunk-level, "base empty ⇒ ours+theirs;
base non-empty ⇒ ours + theirs' pure insertions") **dropped real payload here**: five
branch-added declarations vanished from `MoretBailly.lean` alone, silently, and the
declaration-presence check is the only reason anyone noticed. The reason is structural
— when both sides edit adjacent lines, `difflib` reports one `replace` opcode and the
"pure insertions" rule keeps nothing.

**What worked instead: merge at DECLARATION granularity.** Split BASE / OURS / THEIRS
into blocks (leading docstring+attributes, then the declaration), key them by
namespace-qualified name, and decide per name:

* theirs ADDED it (not in base, not in ours) → splice it in, anchored after the
  theirs-predecessor that exists in ours;
* theirs changed its CODE while ours left the code equal to base → take theirs;
* both changed the code → keep ours and REPORT, with the `sorry`-status of each side
  printed, because that is the only case a human has to look at. Twenty-four branches
  produced **nine** such reports.

Three refinements, each of which was a bug before it was a rule:

1. **Decide on CODE, merge DOCSTRINGS separately.** Comparing whole blocks makes every
   docstring edit look like a code conflict. `flt-lean-88`'s five-site arity repair was
   reported as "both changed, kept ours" purely because merger had appended a paragraph
   to one docstring — and keeping ours on two of the five sites is exactly the class-7
   split that does not compile.
2. **A block that CONSUMES one of theirs' new declarations must come from theirs.**
   Otherwise the new leaf lands orphaned and the parent stays sorried: one closed leaf
   traded for two open ones plus free-floating code. Guard it with "unless ours' body is
   sorry-free and theirs' is not", so the rule cannot resurrect a `sorry`.
3. **Widen the identifier class before you trust any of it.** The stock
   `[A-Za-z0-9_À-ɏͰ-Ͽ℀-⅏.'!?₀-₉]` stops at U+2089, so `mulVecRightₗ` (U+2097) and
   `mulVecRightₗ_apply` both truncate to `mulVecRight` and are reported as a duplicate
   pair that does not exist. Use `₀-ₜ` and `ᴀ-ᵿ`; still avoid `À-￿`, which swallows
   `⟨⟩←▸` (see [[lean-identifier-regex-swallows-brackets]]).

**AND THE ONE THING IT BREAKS, which no check in this file previously covered: SCOPE
LINES.** `namespace X`, `section X`, `variable`, `open … in` live in the glue BETWEEN
declarations, and a block's extent runs to the next block's start — so trailing glue
belongs to the preceding block, and replacing that block with theirs DELETES it. Four
scopes were lost in one release. The symptom is never "missing namespace": it is
`Invalid field 'foo': the environment does not contain X.foo` at every use site
(RelativePicard: 75 errors from one dropped `namespace IsRelPicOf`), or
`Unexpected name X after end: the current section is unnamed`.

The check is ten lines and belongs in every merge:

    walk the file, comment-masked; push on `namespace`/`section`, pop on `end`;
    report an `end X` with nothing (or the wrong thing) open, and any scope left
    open at EOF.

**Run it on the RESULT and difference against PRE-MERGE `main`.** This tree has many
legitimate `section Foo … end` + `end Foo` patterns that the naive check flags; only the
NEW reports are yours. Three of the seven X0 reports were pre-existing and compile fine.

**When you insert the recovered opener, put it where the GAP is, not where the branch's
copy sits.** I inserted `namespace IsRelPicOf` immediately before an existing opener and
gave a whole block the doubled name `Fermat.IsRelPicOf.IsRelPicOf.zeroPoint` — same 75
errors, new cause. **Lean's `linter.dupNamespace` warning named it exactly**, and it was
sitting three lines above the first error in the same log. Read the warnings before the
errors when a merge goes red; they are about causes and the errors are about symptoms.

### The four post-merge checks, in the order they pay off

1. **Scope balance** (above) — seconds, catches whole-module failures.
2. **Every branch-ADDED declaration present in the tree.** Compute "added" as
   branch-decls minus MERGE-BASE-decls, and match on the LAST COMPONENT against the
   whole tree — not the qualified name in the one file, or every relocation and every
   re-nesting reads as a dropped payload. With last-component matching, 23 branches
   reported **zero** missing; with qualified matching the same tree reported eight
   false positives and I chased two of them.
3. **Duplicate declaration names**, namespace-qualified, differenced against pre-merge.
4. **Block-comment nesting depth zero** in every file.

Then the build, three rounds minimum — the errors are serialised behind each other by
the import graph, so round *n* only reveals what round *n−1* was hiding.

