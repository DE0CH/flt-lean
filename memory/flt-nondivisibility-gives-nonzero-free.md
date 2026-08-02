---
name: flt-nondivisibility-gives-nonzero-free
description: "A leaf needing `0 < N` often already carries `¬ ℓ ∣ N` two binders away — everything divides 0, so it is three lines; check the binder list before citing or building a positivity theorem."
metadata: 
  node_type: memory
  type: project
  originSessionId: fb3b2d63-2419-4029-a3c8-5d2970070590
  modified: 2026-08-01T16:26:00.958Z
---

(2026-08-01, `flt-lean-3`, `ModularCurve/X1.lean`.) A leaf that needs a numeric
non-degeneracy — `0 < N`, `n ≠ 0`, "the level has objects" — routinely acquires a
whole hypothesis, and sometimes a whole PROVEN theorem, to supply it. Read the OTHER
binders first. **Everything divides `0`**, so a non-divisibility hypothesis gives it:

```lean
have hN : 0 < N := by
  rcases Nat.eq_zero_or_pos N with rfl | h
  exacts [absurd (dvd_zero ℓ) hℓN, h]
```

`X0.lean`'s `exists_x0IntegralCompactifiedModel` carries BOTH `_hℓN : ¬ ℓ ∣ N` and a
rational compactification `_hX`, and spends the PROVEN `pos_of_isX0Compactification`
on `_hX` — while `_hℓN` gives it in three lines. Every docstring in that cluster says
`_hX` "is load-bearing and is what rules out the degenerate level", repeated verbatim
onto the `Γ₁` twin, where it is equally unnecessary. Taking the free route made `_hX`
UNUSED in the target and absent from all three residual leaves, so none of them
mentions a rational model — which is what the `Γ₀` docstring says it wants and pays a
theorem for.

Watch for: `¬ p ∣ n` (⟹ `n ≠ 0`), `p.Prime` on a modulus, `IsUnit (n : R)` in a
nonzero ring, a `Fintype`/`Nonempty` clause on something indexed by the quantity.

**How it survives review**: "which hypothesis supplies `0 < N`" is not a question a
cut has to answer, so the route note never asks it, and the answer is then copied
between twins. Same family as [[flt-leaf-cost-estimates-are-hypotheses]] and
[[flt-decomposition-drops-a-hypothesis]].

Corollary: a PROVEN theorem existing only to supply such a fact may have no call site
that needs it. Do not delete on that evidence alone — other consumers, other file —
but say so in `to_merger`.
