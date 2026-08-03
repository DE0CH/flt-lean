## A PURE MOVE IS A LINE-MULTISET PERMUTATION — verify it that way, not by reading the diff
(2026-07-31, the `MoretBailly.lean` Stepanov hoist: 539 lines moved up ~1800 in a 51 761-line
file.) A hoist has an exact, machine-checkable definition of correctness that costs milliseconds,
and the two 25-minute elaborations the obvious recipe asks for are mostly avoidable.
**1. Byte-identity is `Counter(before) == Counter(after)`.** If the move changed no line, the two
files are permutations of each other as multisets of lines. This is strictly stronger than reading
the diff and it is instant. Do NOT read `git diff --stat` as evidence: git realigned this move as
`789 insertions(+), 789 deletions(-)` against 539 lines actually moved, because its LCS picked a
different alignment. The stat is noise; the multiset equality is the proof.
**2. The scope check is mechanical, and it is what makes the `#check` diff a formality.** Walk
`namespace`/`section`/`end` and record the ACTIVE `variable`/`open` at the SOURCE and DESTINATION
lines. Identical stacks + byte-identical text ⟹ identical signatures, necessarily. Here both
positions were bare `namespace GaloisRepresentation.Modularity` with **no** active `variable`
binders (every moved declaration carried its own `{R : Type*} [CommRing R]`), so the class-7
"landed inside a section with different binders" hazard was excluded before any Lean ran.
**3. The dependency check is a SUFFIX-RESOLUTION TABLE, not a grep.** Index every declaration in
the file by every suffix of its fully-qualified name (`…StepanovFilt.mem_det` also under
`mem_det`), tokenise the comment-stripped moved text, and flag any used name whose definition
sites ALL lie between the two positions. Tokenise with `isalnum() or c in "_'."` — never a Unicode
range: `À-￿` contains `⟨⟩←▸` and silently swallows every name inside an anonymous constructor.
Expect exactly two false positives and do not chase them: **`zero` and `succ`**, which are
`induction … with | zero | succ` CASE LABELS, not constants.
**4. Two things a hoist can break while still compiling, both invisible to the leaf you moved.**
Moving UP is not automatically safe for the code you moved PAST:
* *resolution*: a moved declaration using an in-file name defined BETWEEN the two positions
  re-resolves, at the new position, to whatever else answers to that suffix — typically a mathlib
  lemma of the same last component. Green build, different theorem. Check 3 is what excludes this;
* *simp sets*: a moved `@[simp]` lemma enters the default simp set EARLIER, so proofs strictly
  between the two positions can change behaviour. **Grep the moved region for `@[` and for
  `attribute` commands naming the moved declarations** before assuming a move is inert. (Here:
  none, so the move is inert by construction.)
**5. The before/after `#check` costs 36 SECONDS, not 25 minutes — run it against the OLEAN.** A
scratch module that only `import`s the target and `#check @Name`s the moved declarations reads the
built `.olean`; it never elaborates the 51k-line source. And the "before" olean you want is
already on disk: `~/.flt-release-lake/build` is the clean build of `main`, i.e. of your base. So
the sequence is *snapshot signatures (36 s) → move → `lake build` once → snapshot again → diff*,
and only the middle step is expensive.
The whole check took under two minutes of thinking-time tooling against one unavoidable build.
