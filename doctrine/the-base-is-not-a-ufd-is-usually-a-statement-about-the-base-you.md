## "The base is not a UFD" is usually a statement about the base you happened to pick

(2026-07-31, `Universal.idl_isPrime` in `ProjectiveEquationAdd2.lean`.) That leaf carried a
carefully-written docstring laying out a two-step tower `Poly ⧸ idl ≅ (B[Px] ⧸ (f₁))[Qx] ⧸ (f₂)`,
proving step 1 by primitivity, and stopping at step 2 with a named obstruction:

> `f₂` is irreducible over the domain `C = B[Px] ⧸ (f₁)`. This half is the real work: **`C` need
> not be a UFD, so the primitivity argument is unavailable.**

The obstruction is real and the sentence is true. It is also **removable by inverting one
variable**, and nothing in the docstring's own data hid that: `f₁` has degree `1` in `a₆` with
coefficient `Pz ^ 3` — the very fact step 1 used to prove `f₁` primitive. Degree one in `a₆` means
that once `Pz` is inverted the relation *solves* for `a₆`, so `C[1/Pz]` collapses back to a
localised polynomial ring, i.e. **a UFD**, and step 2 becomes the same easy primitivity argument as
step 1. The leaf then splits into "prime after inverting `Pz`" plus "`Pz` is a non-zerodivisor mod
the ideal", the second of which needs no primality at all — only uniqueness of division by a monic
polynomial, twice.

The general shape, and why it is worth a standing note: **a quotient by a relation that is degree
`1` in some variable is a graph, not a hypersurface, on the locus where that variable's coefficient
is invertible.** So before accepting "not a UFD / needs new theory" about `R[x]/(f)`:

1. find a variable in which `f` has degree `1`;
2. invert its leading coefficient — the quotient becomes a localisation of a polynomial ring;
3. prove the statement there, and contract back with a non-zerodivisor (saturation) lemma, which is
   normally the *easy* half because the generators are monic in disjoint variables.

Two smaller findings from the same leaf, both worth reusing:

* **Degree-one primitivity is already in mathlib and does not need Gauss's lemma.**
  `Polynomial.irreducible_C_mul_X_add_C : a ≠ 0 → IsRelPrime a b → Irreducible (C a * X + C b)`
  (`Mathlib/Algebra/Polynomial/RingDivision.lean`). `IsRelPrime` *is* the primitivity check.
* **The cost of these leaves is bookkeeping, not mathematics.** All of it sat in viewing
  `MvPolynomial (Fin 11) ℤ` as `B[Px][Qx]` through `renameEquiv`/`finSuccEquiv`. When that fight
  starts, the move is to re-present the universal ring as `B[Px][Qx]` **by construction** rather
  than to win the fight — the surrounding development only ever uses `spec`, so how the ring is
  presented is free to change.

