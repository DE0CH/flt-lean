---
name: flt-escape-hypothesis-and-price-both-overpriced
description: "A leaf's \"cheaper escape, add hypothesis H at the price of threading it through A,B,C\" over-prices BOTH halves; check what the objects already are, and read the consumer's binder list"
metadata: 
  node_type: memory
  type: project
  originSessionId: 3eb58e3b-bdbb-4ee1-bc01-5d8b34ad4b88
  modified: 2026-08-02T02:28:54.783Z
---

A mature leaf priced at a named hard theorem often carries *"a successor may add
hypothesis `H`, which discharges this cheaply — at the price of threading `H`
through `A`, `B`, `C`."* Both halves are estimates written before anyone tried,
and both are routinely too big. Measured 2026-08-02 on
`projective_of_projective_tensorProduct_of_faithfullyFlat`
(`Fermat/FLT/Mathlib/AlgebraicGeometry/SmoothLocusDescent.lean`), priced as
Raynaud–Gruson / Stacks `058B` and **closed in three lines**.

**Why:** the leaf's author reasons about the STATEMENT in the generality it is
written in. What the objects turn out to be at the point of use, and what the
consumer already requires, live in other declarations — often other files — so
nothing prompts the join.

**How to apply:** two commands before writing any Lean.

1. *Is `H` too strong?* Ask what the objects at the point of use ALREADY are —
   local ring, noetherian, a field, a stalk. A weaker lemma often applies there.
   Here the note named `[Module.FinitePresentation S M]` (what
   `Module.Flat.projective_of_finitePresentation` needs over an arbitrary ring),
   but `S` is always a STALK hence LOCAL, and `Module.free_of_flat_of_isLocalRing`
   (Stacks `00NZ`) needs only `Module.Finite`.
2. *Is the price real?* `grep -n 'theorem <the consumer>' -A8` and read its binder
   list in full. Here `mem_smoothLocus_of_comp_of_smooth` already required
   `[LocallyOfFinitePresentation f]`, which yields `LocallyOfFiniteType f` →
   `AlgebraicGeometry.LocallyOfFiniteType.stalkMap` → `Algebra.EssFiniteType R S`
   → `Module.Finite S Ω[S⁄R]` by the instance `KaehlerDifferential.finite`. **No
   signature outside the file moved**; the costed `X0.lean` interface change was
   zero.

Then CLOSE the leaf under the stronger hypotheses rather than keeping the general
form open — nothing consumed the general form, and a leaf priced at a multi-month
formalisation draws dispatches for ever. Say in the docstring what would put it
back (here: a non-local `S`, or a non-finite module), so it is reversible.

Same family as [[flt-leaf-hypotheses-are-a-superset]],
[[flt-consumer-supplies-the-missing-stability]] and
[[flt-leaf-cost-estimates-are-hypotheses]]; the twist is that the docstring had
already done the mathematics and merely over-priced it.
