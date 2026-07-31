---
name: flt-price-the-consumers-input
description: A task's named "missing theory" is often not the gate; read what the already-proven downstream bridge actually CONSUMES, which is usually weaker
metadata:
  type: feedback
---

Before building the classical theorem a leaf's docstring names as missing, read the
signature of the PROVEN theorem that will consume your output. It often takes a strictly
weaker input than the classical statement, because some other theorem in the chain does
the upgrading.

Concretely (2026-07-31, `flt-lean-371`): the task was "build the divisor/degree layer;
deliverable 1 is `deg (div f) = 0`, the one identity everything else rests on", gating
three `X0.lean` leaves. But `Fermat/FLT/Mathlib/AlgebraicGeometry/BirationalFunctionField.lean`
already proves `exists_iso_specRatFunc_specFunctionField_of_hom`, which takes a mere
**`K`-algebra MAP `K(X) ⟶ K(t)`** and applies `Mathlib`'s Lüroth (`RatFunc.Luroth.algEquiv`)
to upgrade it to an isomorphism, and `birationalOver_of_iso_specFunctionField`, which turns
that into `Scheme.BirationalOver`. So the whole gap between the divisor hypothesis and the
geometric conclusion is ONE EMBEDDING, not a degree calculus — and `deg (div f) = 0` is a
corollary of the sharp statement (`[K(X):K(f)] = deg (f)_∞`, Stichtenoth I.4.11) rather
than a step towards it.

**Why:** a docstring's "what it still needs" survey is written by someone reasoning
FORWARDS from the mathematics, so it names the classical theorem. The bridge on the other
side was written later, by someone reasoning backwards from what was cheap, and its
hypotheses are what actually bind. Nobody re-reads the survey when the bridge lands. This
is the same failure family as [[audit-searched-production-not-invariant]] and
[[flt-inventory-audits-understate-what-exists]], in the direction of the CONSUMER rather
than the producer.

**How to apply:** on any "build the missing theory X" task, before writing a line, grep the
tree for the theorem that will consume X and read its hypotheses. Two minutes. Then state
your leaf at the weakest form the consumer accepts, and say IN THE LEAF'S DOCSTRING that a
prover need not produce the stronger object — otherwise the next agent proves the classical
theorem anyway. See also [[flt-leaf-cost-estimates-are-hypotheses]].

Corollary that cost nothing here and would have cost a rewrite: `Mathlib`'s
`Scheme.ord f z` is `0` unless `coheight z = 1`, so `ord f x = 1` already FORCES
codimension `1`; and an indicator-shaped divisor hypothesis `∀ z, ord f z = [z=x] − [z=y]`
does not typecheck, because no scheme carries `DecidableEq`. Write the three-clause form.
