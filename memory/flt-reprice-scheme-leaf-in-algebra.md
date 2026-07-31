---
name: flt-reprice-scheme-leaf-in-algebra
description: An audit that prices a leaf by a missing SCHEME-theory lemma is often cheap once the same fact is stated about ALGEBRAS, where mathlib has it
metadata:
  type: project
---

`redX_base_ne_of_isCusp` (MazurTorsion.lean) carried a correct derivability audit
naming the missing step as *"a section of a separated étale morphism is an
isomorphism onto an open-and-closed subscheme, and over a LOCAL base two such
images sharing their closed point coincide"*. Mathlib has no such lemma, so the
leaf read as a chapter of scheme theory. The same fact about ALGEBRAS is
`Algebra.FormallyUnramified.ext_of_iInf`, which mathlib does have, and the whole
non-classical content then fits in ~40 lines (2026-07-31).

**Why:** this development is affine-over-affine wherever it matters — a cuspidal
locus is finite over the base, hence affine — so the scheme statement almost
always has a ring-level twin, and the audit's price is a price for the *phrasing*,
not for the mathematics.

**How to apply:** before accepting an audit's cost estimate, restate its missing
lemma about rings/algebras and grep mathlib again. Carry any new object as an
ALGEBRA plus a mono into the ambient scheme plus a `range ι.base = …` clause,
which is the idiom `IsX0Compactification.CuspLocus` already uses. Watch for two
traps met here: `IsReductionBase` deliberately carries no `IsNoetherianRing`, so
Krull's `⨅ 𝔪ⁱ = ⊥` must be proven by hand through `padicValRat`; and a
functor-of-points datum such as `IsX0JNeronDatum` LOOKS like it carries no map of
underlying spaces `X' → XZ` (only `RelPoint` equivalences), which is false —
instantiate the universally quantified `T` at `X'` and feed it `𝟙 X'`, and
naturality makes the result a base change of a closed immersion. Run Yoneda by
hand before concluding a functor-of-points structure cannot express something.

See also [[flt-leaf-cost-estimates-are-hypotheses]],
[[flt-inventory-audits-understate-what-exists]],
[[audit-searched-production-not-invariant]].
