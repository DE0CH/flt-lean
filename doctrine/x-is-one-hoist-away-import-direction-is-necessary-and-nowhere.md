## "X is one HOIST away" — import direction is necessary and nowhere near sufficient

(2026-07-31.) Three leaves in `ModularCurve/X0.lean` — the
`mem_isolatedJInvariants_of_stable_*` group, Mazur's Theorem 1 — each carried the
sentence *"this leaf is therefore one hoist away from three lines; a successor should
hoist rather than reprove"*, pointing at proven counterparts in
`FreyCurve/MazurTorsion.lean`. The claim had been re-checked once, by exactly the check
the docstring names: **is the import direction still what I think it is?** It was. The
advice was still wrong, and had been sending successors at an impossible operation.

Three things must ALL be true for a hoist to be the repair, and only the first is about
imports:

1. **Import direction** — the standard check, and the only one anybody ran.
2. **DECLARATION ORDER IN THE DESTINATION FILE.** Every declaration the hoisted block
   consumes must end up above it. Here `IsJMapOn` (24058), `exists_jMap` (27456),
   `HasRankZeroJacobian` (30385) and `card_le_of_rankZeroJacobian` (63677) all sit
   *below* the three leaves at 18592–18684 — so the hoist's real precondition is
   relocating the leaves and their whole cluster past line 63677, in a file of 81 530
   lines. Lean's linear order is a dependency edge exactly as much as an import is.
3. **THE LEAF COUNT ON THE OTHER SIDE.** "PROVEN there" almost never means sorry-free.
   The two namespaces to be hoisted carry **18** open leaves between them; the trade is
   3 leaves here for 19 there. A hoist that raises the frontier may still be right —
   it is disclosure, not regression — but "hoist and these close" is a different claim
   and it was the one being made.

And **re-measure the SIZE, every time**: the section was recorded as `3 500` lines when
the note was written and is `13 000` now. These sections grow while the note does not.
`grep -n 'namespace X' file | ...` is two seconds.

The measurement that made this actionable rather than merely negative is worth copying:
take every top-level declaration name in the block to be moved, strip comments, tokenise
with `isalnum` (**not** a unicode identifier regex — `À-￿` swallows `⟨⟩←▸`, see
[[lean-identifier-regex-swallows-brackets]]), and grep the whole file for those names
*outside* the block. Here 132 declarations produced exactly **four** external hits, one
of which was the single declaration that cannot travel with the rest. That turns
"integrator-level refactor, two files, concurrent owners" into "move 131 declarations,
leave one behind" — a claim someone can act on.

Corollary, same finding: **all six leaf names those three docstrings cited as "the open
residue" had since been PROVEN.** A docstring leaf list is a snapshot with no
maintainer. Cite the section, never the leaves; and if you do cite leaves, stamp the
commit — as with every other frontier number in this file, regenerate rather than quote.

