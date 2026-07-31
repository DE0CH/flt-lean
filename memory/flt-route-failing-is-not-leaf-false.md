---
name: flt-route-failing-is-not-leaf-false
description: "A ROUTE that stops closing at a boundary case is evidence about the route, not about the statement; go hunt the counterexample or find the second route"
metadata:
  node_type: memory
  type: project
---

**A docstring saying "the count no longer closes at `p = 3`, so this leaf may be
FALSE AS STATED" is a claim about the ROUTE, not about the LEAF.** The two get
conflated because the audit is written by whoever just watched their own argument
die, and from inside that argument the boundary looks like the edge of the truth.

Instance, 2026-07-31, `not_index_two_commutative_of_isHardlyRamified`
(`Modularity/Patching.lean`). Its route ruled out a dihedral hardly ramified
`ρbar` by an inertia ORDER COUNT at `p`: `χ_cyc|_{I_p}` has order `p − 1` while
`ε_{F_p}|_{I_p}` has order `2`, so `p = 3`. At `p = 3` those orders coincide, the
count is vacuous, and the leaf carried a warning that it was probably false there
and needed `5 ≤ p` threaded through four consumers that do not carry it.

**It is true at `p = 3`, by an argument the audit never looked at**, because the
audit kept staring at the step that broke. `F` is forced to `ℚ(√-3)`, and `χ` has
order PRIME TO `p` (it lands in `k̄ˣ`, characteristic `p`) — so its conductor
cannot reach past `𝔭₃`, and every ray class group `Cl_{𝔭₃ⁿ}(ℚ(√-3))` has trivial
prime-to-`3` part (`(1+𝔭₃)/(1+𝔭₃ⁿ)` is a `3`-group, `h = 1`, and `−1` already
surjects onto `𝔽₃ˣ`). So `χ = 1`, `ρbar = 1 ⊕ ε_F` is reducible, done — and
**that branch spends no flatness at all**, i.e. it is cheaper than the route that
failed, not harder.

Two operational rules:

- **Refuting a leaf means EXHIBITING a counterexample.** "The argument stopped
  working" is not a refutation and must never be recorded as one. The task prompt
  here was right to say *look for the counterexample first*; the trap is
  concluding falsity from the search being hard rather than from the search
  succeeding. `gp`'s `bnrinit` settled this one in seconds — one command against
  the object the counterexample would have had to live in.
- **When a route dies at a boundary, ask what is SPECIAL about the boundary
  besides the failing step.** Here `p = 3` makes `F = ℚ(ζ_p)` and `h(F) = 1`,
  which is exactly why the class-field argument closes there and nowhere else.
  Boundary cases are usually small, and small is usually easier.

Related: a leaf really can be false ([[flt-cleaner-statement-harder-proof]] is
about the sibling judgement), and an audit certifies only the statement it was
written against.
