---
name: flt-specialize-symmetry-at-its-fixed-point
description: When a leaf's hypothesis is a symmetry, specialize it at the symmetry's fixed point before believing its MISSING MACHINERY note — and measure before restating into the no-cancellation shape
metadata:
  type: feedback
---

A leaf whose hypothesis is a functional equation holding for **all** arguments
carries a free consequence at the symmetry's **fixed locus**, and that
consequence is often the entire content of the leaf.

`frickeSign_eq_neg_one_of_isNewEigenformAt` (`ModularCurve/X0.lean`) had
`hFE : ∀ y > 0, F(1/y) = -ε·y²·F(y)` and concluded `ε = -1`. Its docstring
named the missing theory as "the Atkin–Lehner pseudo-eigenvalue, i.e. `W_M`
acting on `S₂(Γ₀(M))^new` with a certified basis". But `y = 1` is the only
fixed point of `y ↦ 1/y`, and there `hFE` reads `(1 + ε)·F(1) = 0`. So the
leaf **is** the non-vanishing `F(1) ≠ 0`, and `ε = -1` is a six-line proof
over it — no operator, no involution, no basis. (Applying `hFE` twice also
makes the `ε = ±1` hypothesis redundant: `(ε² − 1)·F(y) = 0`.)

**Why:** a `MISSING MACHINERY` note records the route its author had in mind,
not the cheapest route. It is a hypothesis to check, exactly like a "still
open, owned elsewhere" claim. Checking it costs one specialization of the
leaf's own hypotheses and can convert "build a theory" into "evaluate a
series".

**How to apply:** before dispatching effort at a hard leaf, specialize every
universally quantified hypothesis at its distinguished points — the fixed
point of an involution, `n = 1`, the identity, the trivial character. Then
re-read the MISSING MACHINERY note against what survives.

**Second half, learned the same day and equally load-bearing: MEASURE before
restating a leaf into the file's established shape.** `X0.lean`'s idiom for
numerical leaves is `tail < head` — an inequality between reals with **no
cancellation**, chosen because it is reachable from norm bounds. The obvious
move was to state the new leaf that way. PARI/GP says that shape is **FALSE**
here at 6 of the 28 newform/embedding pairs (`tail/head` up to `1.527` at
`M = 75`), because the sibling's `1/n` factor is what buys it the room and it
is absent. The true statement needs the head to cancel against the tail. An
idiom that is correct for one numerical leaf can be false for its sibling;
the five minutes of `gp` is what separates a recut from a manufactured false
leaf. See [[flt-cleaner-statement-harder-proof]] and
[[audit-searched-production-not-invariant]].
