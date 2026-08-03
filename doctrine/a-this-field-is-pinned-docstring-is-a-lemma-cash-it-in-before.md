## A "this field is PINNED" docstring is a LEMMA — cash it in before cutting

(2026-07-31, `flt-lean-370`, `HyperellipticJacobian.lean`.) Structures in this development
are routinely defended against vacuity in prose: `GeomPic`'s section docstring argued at
length that `fieldAct σ` is *determined* by its two axioms, hence that the leaves quantified
over `gp` are model-independent. That argument was never written in Lean, and the cost was
invisible: the derived facts it implies were unavailable, so nobody could use them.

Proving it is usually cheap and pays immediately. `fieldAct_eq_of` — any ring map that is
`σ` on constants and fixes the two coordinates IS `fieldAct σ` — is 30 lines over the
structure's own `gen` field plus `transcendental_xx`, and it yields `fieldAct_mul`,
`placeAct_mul`, `divAct_mul` and finally **`act_mul`: the Galois action on `Pic⁰` is a group
action**. None of that is an axiom, and none of it can be added as one without making
`exists_geomPic` harder.

That mattered concretely: a Kummer cochain `σ ↦ act σ Q − Q` has NO coset structure until
`act` is known to be multiplicative, so "the cochain factors through a finite quotient of
`Γ`" cannot even be *stated*. With `act_mul` in hand, `finite_kummerCochains_pic` — a leaf
carrying the whole arithmetic of weak Mordell–Weil — became a PROOF over two smaller inputs.

So when a structure's docstring says a field is pinned, forced, or determined: **write that
lemma first.** It is the one piece of the development guaranteed to be provable from the
axioms as they stand, and it is what the interesting proofs turn out to need.

**Same day, same file, the sibling lesson: compare a leaf to its CALL SITE before proving
it.** `geomPic_divisible` asked for `∀ n ≠ 0, ∀ y, ∃ z, n • z = y` — divisibility of the
entire geometric Picard group, i.e. surjectivity of an isogeny on the points of an abelian
surface. Its single consumer used it as `fun P => geomPic_divisible gp p hp.ne_zero (bc P)`:
one prime, and only on the image of `bc`. The leaf was DELETED and its content folded into a
statement matching the call site. A leaf quantified more widely than anything consumes it is
a harder theorem that nobody asked for, and the over-quantification is invisible unless you
go and read the consumer.

