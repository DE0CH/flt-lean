---
name: flt-obstruction-names-wrong-thing
description: "'We lack a predicate for X' blocks a route that needs one INSTANCE of X, not a quantifier over it; and Spec of a ℤ-epimorphic ring is subterminal, which is what lets a fine-moduli structure change base"
metadata:
  type: project
---

A docstring in `X0.lean` blocked merging two Katz–Mazur citation leaves on
"this project has no predicate for `n` is invertible on `S`". The repair
needed no predicate: a base change consumes a **morphism**
`Spec 𝔽_ℓ ⟶ Spec ℤ[1/n]`, whose existence *is* the invertibility, delivered
by `IsLocalization.Away.lift`.

**Why:** an abstraction quantifies over instances of a fact; a single call
site needs one instance. A confident, mathematically-informed "we lack X"
is a hypothesis about the *shape* of the missing input, and it is wrong
whenever the route needs X at one point rather than uniformly.

**How to apply:** when a route note blocks on a missing abstraction, write
the proof obligation the abstraction was to discharge and grep the pin for
something that discharges *that*. Related: [[flt-leaf-cost-estimates-are-hypotheses]],
[[flt-a-theory-name-is-a-mathlib-query]], [[flt-recommended-route-may-be-expensive]].

Second half, reusable on its own: **`Spec R` is subterminal (at most one
morphism in, from any scheme) exactly when `ℤ →+* R` is a ring epimorphism**,
since `Spec ℤ` is terminal — so `Spec 𝔽_ℓ`, `Spec ℤ[1/n]` and `Spec ℚ` all
are, two lines each over `AlgebraicGeometry.ext_to_Spec` +
`RingHom.ext_zmod` / `IsLocalization.ringHom_ext`. This project's fine-moduli
structures bind `(_g : T ⟶ S)` and never inspect it, so nothing relates a
classifying map to the base; descending along `S' ⟶ S` needs
`m₀ ≫ strM = g ≫ s`, which subterminality of `S` gives free, and uniqueness
of the lift, which subterminality of `S'` gives free.
