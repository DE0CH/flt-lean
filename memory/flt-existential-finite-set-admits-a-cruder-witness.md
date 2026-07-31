---
name: flt-existential-finite-set-admits-a-cruder-witness
description: A docstring's recorded ROUTE is a cost hypothesis, not a spec — when the leaf is ∃ (a finite set / a bound), any superset works, so replace the canonical invariant with a crude divisor
metadata:
  type: project
---

A leaf whose conclusion is `∃ T : Finset _, …` (or `∃` a bound, a modulus, a
constant) is discharged by ANY admissible witness, so the canonical invariant
the docstring names is usually the most expensive thing that would work. Check
whether a cruder object discharges the same existential before formalizing the
canonical one.

**Measured, 2026-07-31, on `exists_badPrimes_localInertiaGroup_le_of_isOpen_ray_class`**
(`Fermat/FLT/GaloisRepresentation/HardlyRamified/ModThree.lean`). The docstring
prescribed: primitive element `α` of `L = fixedField N`, `Δ := ∏_{β≠γ}(β−γ)`
over the roots of `minpoly ℤ α`, `T :=` the primes dividing `Δ`. Two
substitutions removed most of the formal cost and no mathematics:

- **Spanning set instead of primitive element.** A `ℚ`-algebra automorphism
  that fixes a `ℚ`-SPANNING set of `L` fixes all of `L` by
  `Submodule.span_induction` — plain linearity. `(⊤ : Submodule ℚ L).FG` gives
  the set from `FiniteDimensional`. The primitive element theorem only makes
  the set a *singleton*, which the argument never needs, and it would have cost
  the `IntermediateField.lift` bookkeeping to move `ℚ⟮α⟯` from inside `L` up to
  an intermediate field of `ℚᵃˡᵍ`.
- **Any divisor instead of the discriminant.** For each root `β ≠ x` of ANY
  monic *integral witness* of `x` (not `minpoly` — any monic `g ∈ ℤ[X]` with
  `g(x) = 0` works, since roots of a monic integer polynomial are again
  algebraic integers), `x − β` is a nonzero algebraic integer and therefore
  divides SOME nonzero rational integer. The union of those integers' prime
  factors is a legitimate `T`. It is a divisor-multiple of the discriminant,
  which is all the `∃` asks for, and it needs no Vieta, no `derivative`, no
  separability and no Bézout.

**Why:** the existential quantifier is the licence. A finite set that is merely
a SUPERSET of the genuinely-bad primes is as good as the exact one, and the
"exact" one is exactly where the expensive classical invariants live.

**How to apply:** before formalizing a named invariant a docstring prescribes,
ask what property of it the proof actually uses. If the answer is "it is
nonzero and everything bad divides it", build the crude divisor. Then say in
the commit which reading of the recorded route you took and what would change
your mind — here, a consumer needing `T` to be *exactly* the ramified primes;
none of the three named customers does.

Two corollaries worth remembering separately: **`minpoly` is rarely what you
need** when a plain integrality witness will do (it drags in irreducibility and
the `ℤ`-vs-`ℚ` integrally-closed bridge); and **`IsIntegral ℤ δ`, `δ ≠ 0` ⟹
`δ ∣ n` for some `n : ℕ`, `n ≠ 0`, with integral cofactor** is a ~35-line
self-contained lemma (strip factors of `X` off the witness polynomial by
induction on `natDegree`, then `Polynomial.X_mul_divX_add`), now available as
`exists_natCast_eq_mul_of_isIntegral_int` in that file.

Related: [[audit-searched-production-not-invariant]],
[[flt-cleaner-statement-harder-proof]].
