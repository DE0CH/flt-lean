---
name: flt-implication-leaf-needs-half-a-citation
description: "A leaf whose conclusion is an IMPLICATION consumes one inclusion of the equivalence its docstring cites — usually not the half the theorem is named after; price the direction, not the theorem"
metadata: 
  node_type: memory
  type: project
  originSessionId: d28e21f0-d194-4b0d-857d-0e68cd9ba1c2
  modified: 2026-08-02T04:06:59.511Z
---

(2026-08-02, `flt-lean-207`, `exists_narrowRayArtin_of_sup_eq_top` in
`Modularity/KhareWintenberger.lean`.) The leaf's ROUTE cited *the existence theorem
of class field theory PLUS Artin reciprocity* `ker Art = P_𝔪`. Its conclusion is
`Frob_w = τ ⟹ w ∼_𝔪 (a)`, i.e. `Art(w) = Art((a)) ⟹ w ∼ (a)` — exactly
`ker Art ⊆ P_𝔪`. The other inclusion, reciprocity proper and the half every
textbook proof spends its effort on, is **never used**. And the Artin map itself is
free: `exists_idealSymbolMonoidHom` (`NumberField/CyclotomicIdealSymbol.lean`,
PROVEN, pure Dedekind-domain theory) extends any function on height-one primes to a
monoid hom on `(Ideal R)⁰`.

**Why:** a docstring names the classical theorem it has in mind, and an equivalence
is the natural way to name it. Pricing the whole equivalence can double or triple
the estimate and can point the next owner at a chapter they do not need.

**How to apply:** write the leaf's conclusion as an implication between the two
sides of the cited equivalence and read off which arrow is needed. Record the
narrowing in the docstring — "one inclusion of theorem X" is a real reduction that
no leaf count shows.

Riders from the same run:

* **A totally positive representative of a residue class is ARITHMETIC.** For
  `x + 𝔣` the reflex is a lattice-point/Minkowski argument; instead take a nonzero
  RATIONAL integer `N ∈ 𝔣` (`Ideal.absNorm_mem`) and `x + N·m` for large `m : ℕ`.
  A rational integer shifts every real embedding by the same amount, so one `m`
  serves all of them; only `Finite.exists_le` is used and a totally imaginary `F`
  costs nothing.
* **Grep your intended NAME before writing a helper, not only the concept.**
  `exists_totallyPositive_sub_mem_ray_class` was already proven in
  `HardlyRamified/ModThree.lean`; no concept grep found it, because that file
  suffixes ~30 unrelated support lemmas with `_ray_class`. The routine
  name-collision check is what saw it.
* **Measure a giant module's elaboration before planning around it.**
  `KhareWintenberger.lean` (28 k lines) is `lake env lean`-clean in **176 s** with
  oleans seeded from `~/.flt-release-lake`, not the half-hour the scratch-module
  doctrine assumes.

Related: [[flt-leaf-cost-estimates-are-hypotheses]],
[[flt-inventory-audits-understate-what-exists]], [[flt-cut-so-each-half-is-a-consequence]].
