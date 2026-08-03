## A CUT'S "WHAT IT NEEDS" CAN NAME A CALCULUS WHERE A MULTISET WILL DO — and the injectivity is usually free
(2026-08-02, `flt-lean-362`, closing ALL THREE Dirichlet-series leaves of
`NumberField/Density.lean` in one run, so that `finrank_eq_one_of_forall_inertiaDeg_eq_one`
and with it `closure_frobAt_eq_top` — CHEBOTAREV — became axiom-clean.)
All three leaves carried a careful **What it needs** paragraph, and all three named the same
machine: the `IsDedekindDomain.HeightOneSpectrum` / `FractionalIdeal.count` factorisation
calculus (`finprod_heightOneSpectrum_factorization'`, `∏ᶠ` over height-one primes,
`ℤ`-valued `count`, a fraction field to state it over). None of the three proofs uses one
line of it. What they use is:
* **`UniqueFactorizationMonoid.normalizedFactors` as a MULTISET.** `Ideal.prod_normalizedFactors_eq_self`
  turns the multiset back into the ideal; `normalizedFactors_prod_of_prime` turns a product
  of primes back into the multiset (`Ideal.uniqueUnits` supplies the `Subsingleton αˣ`
  instance it wants); `map_multiset_prod` pushes the `MonoidHom` `Ideal.absNorm` through a
  product. Between them, "the ideal monoid is free on the primes" is available without ever
  naming an exponent.
* **`Equiv.sigmaFiberEquiv` to group a sum over ideals by their norm**, with
  `Ideal.finite_setOf_absNorm_eq` for the fibres and `tsum_const` for each fibre's sum.
**And the payoff that is easiest to miss: an injection built this way needs NO injectivity
lemma, because the inverse is explicit.** To show `(𝔞, 𝔟) ↦ (map q₁ (nf 𝔞) + map q₂ (nf 𝔟)).prod`
is injective, do not try to prove `q₁` injective and lift it through `Multiset.map`. Recover
`nf 𝔞` from the value: `Multiset.filter (· ∈ range q₁)` splits the factorisation back into
its two halves (the two ranges are disjoint), and then `Multiset.map (Ideal.under R)` undoes
`q₁` POINTWISE because `under (q₁ 𝔭) = 𝔭` is a hypothesis you already hold. Same shape in
the third leaf: `I ↦ (e, J)` with `I = 𝔭 ^ e * J` is injective because the product recovers
`I`, with nothing to prove at all.
**So when a leaf's route names a calculus, ask what the calculus is being used FOR.** Here it
was for three things — "the factorisation exists", "it is unique", "it is multiplicative" —
and a multiset of primes with a `prod` has all three definitionally.
### Three analytic moves that made the leaves smaller, all reusable
* **In an inequality between `tsum`s of NON-NEGATIVE terms, summability of the SOURCE is
  free.** `by_cases hfsum : Summable f`; in the negative branch `tsum_eq_zero_of_not_summable`
  makes the left side `0` and the goal is `0 ≤ ∑' g`. That deleted the hardest-looking
  hypothesis of leaf 2 (nobody has to prove the `k`-side series converges).
* **A `n = 0` term that disagrees on the two sides is usually harmless** — `(0 : ℝ) ^ (-s) = 0`
  for `s > 0` kills it. Leaf 1's two `n = 0` fibres genuinely differ (empty on the ideal side,
  `{⊥}` on the `ℕ` side) and the proof does not care.
* **Do not sum a geometric series if an inequality can absorb the recursion.** Leaf 3's route
  asked for `∏_𝔭 (1 - N𝔭^{-s})^{-1}`. Removing ONE Euler factor and splitting the `T`-avoiding
  ideals by whether `𝔭` divides them gives `Z_T ≤ Z_{insert 𝔭 T} + ½ Z_T` — i.e.
  `Z_T ≤ 2 Z_{insert 𝔭 T}` — with `Summable.tsum_add_tsum_compl` for the split and one
  application of `Summable.tsum_le_tsum_of_inj` for the half. Then `Set.Finite.induction_on`.
  No geometric series, no product of two `tsum`s, and the constant `2 ^ #T` comes out uniform
  in `s` for free, which is what the endgame needs.
### Four Lean traps, each of which cost a round and none of which prints a useful message
* **`set f := <a function> with hf` makes `f` a LET-BOUND local, and every later `isDefEq`
  zeta-unfolds it.** A `simp only [hf]` or an `exact` on a goal mentioning `f p` then dies
  with `(deterministic) timeout at isDefEq/whnf, 200000 heartbeats` on a line that looks
  trivial. The cure is to make the function OPAQUE and carry only the equation you need:
      obtain ⟨e, he⟩ : ∃ e : A → B, ∀ p, (e p : Carrier) = <the value> :=
        ⟨fun p => ⟨<the value>, <proofs>⟩, fun _ => rfl⟩
  This is the standing "`have` on data destroys defeq / `let` is expensive" rule, in the
  direction where you WANT the opacity: state the defining equation on the one COMPONENT the
  proof reads, and every later step is a `rw` instead of an unfolding.
* **`Equiv.tsum_eq` with the equiv left as `?_` is a non-pattern higher-order unification**
  (`?f (?e c) ≡ <the summand>`) and times out. Supply the equiv as an explicit term — an
  anonymous constructor with a type ascription, inline in the `exact` — so that `e` and `f`
  are both given.
* **`summable_mul_of_summable_norm` timed out where `Summable.mul_of_nonneg` was instant.**
  The first goes through `NormedRing`/`CompleteSpace`; for a goal about `ℝ` use the
  real-specific lemma. Same for `tsum_mul_tsum_of_summable_norm`, which is fine — it is the
  SUMMABILITY companion that is worth swapping.
* **`rw` on a `zetaAvoiding`-style project `def` inside a big goal**: state the unfolding as a
  `have ... := rfl` FIRST and `rw` it, rather than letting a later tactic unify through the
  definition. `have hz : zetaAvoiding k T s = ∑' I : {...}, ... := rfl` costs nothing and
  makes every subsequent step syntactic.
Minor pin facts met on the way: `Ideal.prod_normalizedFactors_eq_self` and
`Ideal.isPrime_of_prime` already exist (in `Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean`)
— check that file before writing a Dedekind-domain factorisation helper; `inv_le_inv_of_le` is
gone, use `one_div_le_one_div_of_le`; and `Summable.tsum_le_tsum_of_inj` /
`Summable.tsum_add_tsum_compl` are `to_additive`-generated from the `Multipliable` versions, so
`grep` for the multiplicative name when the additive one appears only at use sites.
