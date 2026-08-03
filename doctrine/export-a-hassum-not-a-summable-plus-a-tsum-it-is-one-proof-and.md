## EXPORT A `HasSum`, NOT A `Summable` PLUS A `tsum` — it is one proof and it cannot float
(2026-08-02, `flt-lean-36`, closing `dedekindZeta_re_eq_zetaAvoiding_empty` in
`NumberField/Density.lean`.)  A convergence leaf routinely has two customers wanting two
different halves of it: one needs *the series converges*, the other needs *its value*.  The
reflex is two theorems, `summable_foo` and `tsum_foo_eq`.  That is a trap in this project,
because **the `Summable` half is then usually consumed by nobody in the cone** — the target
needs only the value — so it is FREE-FLOATING CODE, which is banned, and the next agent
either deletes it or re-derives it.
State it once as `HasSum f v`.  A `HasSum` carries both halves, so
`(h …).summable` and `(h …).tsum_eq` serve both customers off ONE declaration that the
target genuinely consumes.  The proof shape is unchanged:
    have hsummable : Summable f := …
    have hval : ∑' b, f b = v := …
    exact hval ▸ hsummable.hasSum
Here the three residual leaves of that file share one analytic input — absolute convergence
of `∑ (N I)^{-s}` over the ideals — and only leaf 1 needed its VALUE.  Exporting
`hasSum_absNorm_rpow` gave leaves 2 and 3 their convergence for free with no floating
declaration and no second proof.  **Say in the docstring which sibling leaf takes which
half**; that sentence is the whole reason the shape was chosen and it is invisible from the
statement.
### `Equiv.summable_iff` wants `f ∘ e`; `summable_sigma_of_nonneg` wants `fun p => …`
Both are `Iff`s, both look `rw`-able, and **neither `rw` fires against the other's output** —
the mismatch is composition-vs-lambda and the error prints the pattern and the target as
visibly the same sum:
    rewrite failed: Did not find an occurrence of the pattern
      Summable (?f ∘ ⇑(Equiv.sigmaFiberEquiv fun I => Ideal.absNorm I))
    in the target expression
      Summable fun p => ↑(Ideal.absNorm ((Equiv.sigmaFiberEquiv fun I => Ideal.absNorm I) p)) ^ (-s)
Do not chase it with `Function.comp_def` rewrites.  **State every intermediate fact in the
clean `fun p => … p.1 … p.2.1 …` form and bridge with `Summable.congr` / `tsum_congr`,
which check up to DEFEQ:**
    (Equiv.summable_iff (Equiv.sigmaFiberEquiv g)).mp (hsigma.congr fun p => (hval p).symm)
`Equiv.sigmaFiberEquiv g` sends `⟨n, x⟩ ↦ x.1` definitionally, so the bridging equations are
`rfl` up to the fibre's defining equation, and `rintro ⟨n, I, rfl⟩; rfl` discharges the whole
family.  Same family as the standing "printed pattern equals printed target ⟹ switch to a
defeq-checking tactic" rule, with `Equiv`-coercion as the new cause.
### Do NOT case-split on `n = 0` in an `LSeries` computation
The docstring for this leaf (correctly) observed that `LSeries.term` vanishes at `n = 0`
while `absNorm ⊥ = 0`, and priced a case split for it.  None is needed, twice over:
* **`LSeries.term_of_ne_zero'` removes the `if` outright given `s ≠ 0`**, because
  `(0 : ℂ) ^ s = 0` and division by `0` is `0`.  Then `Real.rpow_neg` and `div_eq_mul_inv`
  are identities that hold at `n = 0` as well, so the term computation is one `rw` chain with
  no branches — and it needs only `s ≠ 0`, not the convergence threshold, so state it that way.
* **The `⊥` ideal is dropped at the very END, by support**, not by a branch:
  `tsum_subtype_eq_of_support_subset` (the `to_additive` image of
  `tprod_subtype_eq_of_mulSupport_subset`, so `grep` for the multiplicative name or `exact?`
  will find it) turns `∑' I : {I // I ≠ ⊥}, f I` into `∑' I, f I` from
  `Ideal.absNorm_bot` plus `Real.zero_rpow`.  Everything upstream may then quantify over ALL
  ideals, which is what makes the fibres of `absNorm` match `Nat.card {I // absNorm I = n}`
  on the nose at every `n` including `0`.
Pin note: `tsum_sigma'` does not exist at this pin under that name — it is
`Summable.tsum_sigma'`, and dot notation puts the `Summable f` argument first even though it
is the SECOND explicit argument (the fibrewise hypothesis is a `∀`, whose head is not
`Summable`).  `Summable.tsum_fiberwise`, which the route note also named, does not exist at all.
