---
name: flt-runaway-doc-comment
description: A doc comment that lost its terminator silently deletes hundreds of declarations while the file still PARSES; the symptom appears hundreds of lines away as "X is a local variable"
metadata:
  type: project
---

A `/--` whose closing terminator a declaration-level merge drops does **not**
produce a parse error. Some later stray terminator closes it, the file parses,
and every declaration in between is silently a comment. Found 2026-07-31 in
`Fermat/FLT/Modularity/Patching.lean` at release 27: one such wound swallowed
**~1980 lines** including `IsCohenCoefficients`,
`existsUnique_ringHom_wittVector_of_isNilpotent`, `taylorWilesCoordModel` and
~50 other declarations.

**Why:** Lean block comments NEST, so an unterminated one is absorbed by the
next terminator rather than reported where it opened. Nothing in the build
output points at the opening line.

**How to apply:** the tell is a cluster of `Unknown identifier X`,
`Function expected at`, and above all
`invalid use of explicit universe parameters, X is a local variable` — that
last one is what a *swallowed* name becomes once `autoImplicit` binds it, and
it is unmistakable, because a genuinely missing name is never written `X.{u,v}`
by an author. When you see it, do NOT hunt for a missing import: scan the file
for comment-depth balance (walk the text counting `/-` and `-/`, skipping `--`
lines at depth 0) and report every top-level block longer than ~400 lines. The
repair is to close the runaway; demote it to an ordinary block comment if the
declaration it documented already has its own docstring.

Two traps while writing the repair note itself: (1) a comment-open or
comment-close token spelled inside block-comment PROSE still nests, so
describing the wound in the comment you are fixing reopens it — check the depth
scan again after editing; (2) the same merge often leaves the *matching* stray
terminator further down attached to an orphaned rival declaration, so fixing
only the opener flips the whole rest of the file into a comment.

Related: [[flt-hidden-sorries-scans-main-repo]], [[flt-see-the-merge-before-the-merger]].
