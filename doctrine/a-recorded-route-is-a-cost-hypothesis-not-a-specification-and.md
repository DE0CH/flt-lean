## A RECORDED ROUTE IS A COST HYPOTHESIS, NOT A SPECIFICATION — and an `∃` licenses a cruder witness

(2026-07-31, measured on `exists_badPrimes_localInertiaGroup_le_of_isOpen_ray_class`.)
Docstrings in this development often carry a fully worked-out route. That route is
evidence the leaf is TRUE; it is not a statement of what must be formalized. When the
conclusion is `∃ T : Finset _, …` — or `∃` a bound, a modulus, a constant — **any
admissible witness discharges it, and the canonical invariant the route names is
usually the most expensive object that would work.**

That leaf's route prescribed a primitive element `α` of `L = fixedField N` and
`Δ := ∏_{β≠γ}(β−γ)` over the roots of `minpoly ℤ α`, with `T :=` the primes dividing
`Δ`. Two substitutions deleted most of the formal cost and no mathematics:

- **A `ℚ`-SPANNING SET beats a primitive element.** An automorphism fixing a spanning
  set of `L` fixes all of `L` by `Submodule.span_induction` — plain linearity, and
  `(⊤ : Submodule ℚ L).FG` supplies the set from `FiniteDimensional`. The primitive
  element theorem only makes that set a *singleton*, which the argument never needs,
  and it costs the `IntermediateField.lift` bookkeeping to move `ℚ⟮α⟯` from inside `L`
  up to an intermediate field of `ℚᵃˡᵍ`.
- **ANY DIVISOR beats the discriminant.** `x − β` is a nonzero algebraic integer for
  every root `β ≠ x` of **any** monic integral witness `g ∈ ℤ[X]` of `x` — *not*
  `minpoly`; any monic `g` with `g(x) = 0` works, because roots of a monic integer
  polynomial are again algebraic integers. Each such difference divides SOME nonzero
  rational integer, and the union of those integers' prime factors is a legitimate
  `T`. No Vieta, no `derivative`, no separability, no Bézout.

So the discipline is: **before formalizing a named classical invariant, ask which
property of it the proof actually uses.** If the answer is "it is nonzero and
everything bad divides it", build the crude divisor instead. Then state in the commit
which reading of the route you took and what would change your mind — here, a consumer
needing `T` to be *exactly* the ramified primes; none of the three named customers
(`finite_hilbertInertiaOutsideSubgroups`, `exists_finset_isUnramifiedAt_hilbert_of_notMem`,
`exists_finset_isUnramifiedAt_of_notMem`) does.

Corollary, general: **`minpoly` is rarely what you need** when a plain `IsIntegral`
witness will do — it drags in irreducibility and the `ℤ`-vs-`ℚ` integrally-closed
bridge for nothing.

