## AN ITERATED OPERATOR IN A ROUTE NOTE IS A COST ESTIMATE — TRY ONE APPLICATION AT A TIME
(2026-07-31, `flt-lean-130`, proving `MvPowerSeries.span_insert_setOf_forall_pderiv_mem_eq`,
the KEY LEMMA of Fontaine's step 3.)  That leaf's recorded proof, and **three** successive
route notes built on it — its own docstring, its parent's, and a dated MACHINERY
RECONNAISSANCE — all priced the same missing input: a multivariate HASSE-DERIVATIVE API,
which this pin has only for univariate `Polynomial`.  The reason was the shape of step 2:
extract the maximal box term by applying the iterated operator `T^(b) = ∏_j (∂/∂X_j)^{b_j}`
and then divide by `∏_j b_j!`.
**No iterated derivative is needed, and the factorials never appear.**  Induct on the TOTAL
DEGREE of `b`, peeling ONE derivative at a time: writing `b = b' + e_j`, the `b'`-th slice of
`∂f/∂X_j` is `b_j` times the `b`-th slice of `f` modulo `p`.  A single derivative lowers the
degree by one and multiplies the slice by the SINGLE factor `b_j`, so only `b_j` has to be
inverted mod `p` — one `Nat.Coprime` plus Bézout, where the recorded route wanted a product
of factorials to be invertible.  ~350 lines, no new theory.
**The generalisable check, and it is one question: does the route apply an ITERATED operator
`T^n` (or a product over an index set) and then divide by the constant that operator
produces?**  If so, ask whether an induction that applies `T` ONCE per step works. The
iterated form needs the whole algebra of `T^n` — a Leibniz expansion, a commutation rule, the
constant's arithmetic — while the one-step form needs only `T` itself plus a decreasing
measure, and the constant it produces is a single factor rather than a product. This is the
same family as *ASK WHAT THE CRUDE BOUND ALREADY GIVES* above, at the level of the OPERATOR
rather than of the estimate; and note it fired on a leaf whose route had already been
re-examined three times, because each re-examination was pricing the recorded shape rather
than questioning it.
Three riders from the same run, each worth its own reflex:
* **A GUARDED HYPOTHESIS THE COMPILER CALLS UNUSED MEANS THE LEMMA IS UNCONDITIONAL.**
  `part_pderiv_sub_nsmul_mem` was written with `a j + 1 < p`, copying the guard from the
  context that motivated it; `unusedVariables` flagged it immediately, because the error term
  is literally `(p·q_j)·x` and no hypothesis on `a j` is involved. The guard belongs at the
  CALL SITE (where `a + e_j` must stay inside the box), not in the lemma. Read the linter on a
  freshly written helper before moving on — it is the cheapest strengthening available, and
  here it removed a case split from every consumer.
* **DO NOT IMPORT A HEAVY GENERAL DEFINITION FOR TWO OF ITS PROPERTIES.**  The pin HAS the
  object this proof wanted (`MvPowerSeries.expand`, with exactly the two coefficient lemmas
  needed), and using it would have been wrong: it is built on `MvPowerSeries.Substitution`, so
  it drags a topology cone into the target file and into everything below it — and the leaf's
  own docstring says a TINY IMPORT CONE is the reason the statement is phrased in the
  `p`-divisibility form at all. A ten-line local definition with the two properties added no
  import. **When a recon note says "the ambient object already exists in the pin", check what
  its module imports before treating that as good news.**
* **`(a + Finsupp.single j 1) k` fails to elaborate as an ARGUMENT position** with
  `Function expected at … but this term has type ?m  k` — the Finsupp's type is still a
  metavariable when the coercion is needed. It is not a missing instance and not a parse
  error: ascribe the type, `(a + Finsupp.single j 1 : σ →₀ ℕ) k`. Same for `(p • d) j`. This
  cost three round trips and the message names neither the cause nor the fix.
