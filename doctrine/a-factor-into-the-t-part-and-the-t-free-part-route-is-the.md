## A "FACTOR INTO THE `T`-PART AND THE `T`-FREE PART" ROUTE IS THE EXPENSIVE ONE — REMOVE ONE PRIME AT A TIME
(2026-08-02, `flt-lean-37`, closing `exists_zetaAvoiding_empty_le` in
`NumberField/Density.lean`.)  That leaf's recorded route was the classical one: every
nonzero ideal factors uniquely as `𝔟 · 𝔠` with `𝔟` supported on the finite set `T` and `𝔠`
avoiding it, so `ζ_K(s) = (∑_{T-supported} N𝔟^{-s}) · zetaAvoiding K T s`.  Its **what it
needs** paragraph priced that at *"`Ideal.factorization` over `HeightOneSpectrum`, or
`UniqueFactorizationMonoid` `Finsupp` support splitting"*.  Both are real developments and
**neither is needed**.
**Induct on the finite set, one prime at a time.**  For a SINGLE maximal `𝔮 ∉ U` the
decomposition is `I = 𝔮 ^ n · J` with `𝔮 ∤ J`, and that is off the shelf:
* `FiniteMultiplicity.of_not_isUnit` (in `RingTheory/UniqueFactorizationDomain/Multiplicity.lean`)
  gives finiteness from `𝔮 ≠ ⊤` and `I ≠ ⊥` — for `Ideal (𝓞 K)`, which is a
  `CancelCommMonoidWithZero` and a `UniqueFactorizationMonoid` at this pin
  (`Ideal.uniqueFactorizationMonoid`);
* `FiniteMultiplicity.exists_eq_pow_mul_and_not_dvd` is the surjection;
* injectivity is `multiplicity 𝔮 (𝔮 ^ n · J) = n` (three lines from
  `FiniteMultiplicity.multiplicity_eq_iff` + `mul_dvd_mul_iff_left`) plus one
  `mul_left_cancel₀`.
That produces an honest `Equiv (ℕ × B) A` rather than a `Finsupp`, each induction step
costs one geometric factor `(1 − N𝔮^{-s})⁻¹ ≤ 2`, and the whole leaf is ~150 lines with no
`Finsupp`, no `HeightOneSpectrum` and no `Ideal.factorization` anywhere.
**The generalisable form: a decomposition indexed by a FINITE SET is an INDUCTION, and the
single-element case is usually one mathlib lemma while the whole-set case is a
development.**  Ask which one the statement needs before pricing the route — the route was
written by whoever cut the leaf, from the argument a textbook states, and a textbook states
the whole-set version because for a human it is the same sentence.
Two riders that made this one cheap, both reusable.
### A `tsum` INEQUALITY OVER `ℝ` NEEDS NO SUMMABILITY HYPOTHESIS — the `∑' = 0` convention pays
`∑' f ≤ C · ∑' g` with `g ≥ 0` is TRIVIALLY TRUE when `f` is not summable, because mathlib
defines `∑'` to be `0` there.  So the shape is
    by_cases hfs : Summable f
    case neg => rw [tsum_eq_zero_of_not_summable hfs]; exact mul_nonneg … (tsum_nonneg …)
and the positive branch has `Summable f` in hand for free.  Better still: when the index of
`f` is `ℕ × β` up to an equivalence, **summability of `g` is RECOVERED from summability of
`f`** by restricting the product index to `{0} × β` (`Summable.comp_injective` along
`fun b => (0, b)`, then `pow_zero`/`one_mul`).  So the analytic lemma carries NO convergence
hypothesis at all and none has to be threaded through the induction — which is what the
leaf's docstring had expected to cost (*"nothing analytic beyond `Summable.mul_of_nonneg`"*
was already an over-estimate).
The named pieces: `summable_geometric_of_lt_one`, `tsum_geometric_of_lt_one`,
`tsum_mul_tsum_of_summable_norm` (`Mathlib/Analysis/Normed/Ring/InfiniteSum.lean`; feed it
`Summable ‖·‖`, which for a nonnegative family is `simpa [Real.norm_of_nonneg …]`), and
`Equiv.tsum_eq` / `Equiv.summable_iff` (the additive versions of `Equiv.tprod_eq` /
`Equiv.multipliable_iff`, so they do not appear under those names in a source grep).
### `set` ON A SUBTYPE IS A `whnf` TIMEOUT — HOIST THE ANALYSIS INTO A TYPE-POLYMORPHIC LEMMA
The first attempt named the two index types with
`set A := {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ ∀ 𝔭 ∈ U, 𝔭.IsMaximal → ¬ 𝔭 ∣ I} with hA_def`, so that
the six places they occur would read tolerably.  It died with **`(deterministic) timeout at
whnf`, 200 000 heartbeats**, reported at the `theorem` line and naming nothing.  `set`
introduces a let-bound local, and every subsequent `Summable`/`TopologicalSpace`/coercion
elaboration on that type then has to zeta-reduce through it.
**The fix is not `set_option maxHeartbeats`.  It is to state the analysis as a lemma over
ABSTRACT types `{α β : Type*}` and let unification fill them in at the call site.**  Here
that is
    theorem tsum_le_two_mul_geom {α β : Type*} (f : α → ℝ) (g : β → ℝ) (r : ℝ)
        (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2) (hg0 : ∀ b, 0 ≤ g b)
        (e : ℕ × β ≃ α) (he : ∀ p, f (e p) = r ^ p.1 * g p.2) :
        ∑' a, f a ≤ 2 * ∑' b, g b
— it mentions no ideal, and after `unfold zetaAvoiding` the arithmetic proof is one
`refine tsum_le_two_mul_geom _ _ … (Equiv.ofBijective (fun p : ℕ × {…} => …) ⟨?_, ?_⟩) ?_`
in which each subtype is written exactly ONCE.  Elaboration went from a 200 000-heartbeat
timeout to **5 seconds**.  Same family as the standing "an abstract `example` proves the
glue is glue" rule, with a performance reason on top of the design one.
Two smaller notes from the same proof.  `unfold zetaAvoiding` is needed before any
`Equiv.tsum_eq`-shaped `exact` — a `noncomputable def` will not unify with its own body
under a metavariable-headed `∑'`, and the error is a `TopologicalSpace ?m` instance-stuck
message rather than anything about unfolding.  And `rw [hc]` where
`hc : I = 𝔮 ^ multiplicity 𝔮 I * c` rewrites `I` INSIDE `multiplicity 𝔮 I` too, leaving an
unprovable goal; state the `Dvd` witness with `refine ⟨_, ?_⟩; rw [mul_comm]; exact hc`
instead of letting `rw` at the occurrence you meant.
