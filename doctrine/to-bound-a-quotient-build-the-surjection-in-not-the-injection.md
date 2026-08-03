## TO BOUND A QUOTIENT, BUILD THE SURJECTION *IN* — NOT THE INJECTION *OUT*

(2026-07-31, `flt-lean-282`, peeling `card_sha1Twist_le_card_dualNumberPoints` in
`HardlyRamified/Deformation.lean`.)

A cut that inserts a quotient in the middle — `#Ш ≤ #(A/∼) ≤ #B` — asks for a
cardinality bound on `A/∼`, and the reflex, which the task prompt for this leaf
also recommended, is to build an INJECTION `A/∼ ↪ B`. That is the expensive
direction and it is expensive for a reason nobody writes down: **an injection out
of a quotient must first DESCEND, and the descent obligation is usually the whole
mathematical content of the cut.** Here the map was `⟦X⟧ ↦ X.pt ∘ fₓ`, injectivity
was three lines, and well-definedness was *"equal Frobenius charpolys ⟹ equal ring
homomorphism"* — i.e. Carayol / trace generation, exactly the theory the cut
existed to avoid.

**Run it the other way and nothing is owed.** A SURJECTION `B ↠ A/∼` gives the same
bound (`Nat.card_le_card_of_surjective`, needing only `Finite B`), and its source is
not a quotient, so there is no well-definedness check at all. The surjection here
was `f ↦ ⟦⟨D, f⟩⟧`, and its surjectivity is the *same one-line charpoly computation*
that would have proved injectivity of the other map. Same computation, no theory.

So: **when you must bound `#(A/∼)`, look for a map INTO the quotient before you look
for one out of it.** The tell that the surjection exists is that `B` embeds in `A`
in some cheap way (here every `k[ε]`-point `f` of the universal ring *is* a point of
the functor, namely `⟨D, f⟩`), and then surjectivity is the statement that every
class is hit — which is the universal property you were going to use anyway. The
finiteness side condition is normally already proven: here
`card_dualNumberPoints_eq_pow_cotangentFinrankModL` gives the cardinality outright,
and `Nat.finite_of_card_ne_zero` converts it.

**Second lever from the same cut, and it deleted an entire instance-building task:
DO NOT ask for objects over a CONCRETE ring — ask for objects over ANY ring plus a
map to it.** The classical middle object is "hardly ramified deformations to
`DualNumber k`", which in Lean means supplying `TopologicalSpace`,
`IsTopologicalRing`, `IsLocalRing`, `Algebra ℤ_[ℓ]`, `IsNoetherianRing`, `IsAdic`
and `IsAdicComplete` instances for `DualNumber k` — none deep, all work. The pair
`(D, e : D.R →+* k[ε] compatible)` carries the same information whenever the
property is stable under push-forward (`isHardlyRamified_pushforwardFrame` here, and
`(D, id)` recovers the concrete case), and it needs **no instances at all**, because
the ring comes bundled with its own inside `D`. Record the translation in the
docstring rather than proving it; nothing downstream needs it, and the leaf is
stated in the vocabulary the citation uses either way.

**And say out loud that the residual leaf is a priori STRONGER.** Cutting `a ≤ c`
as `a ≤ b ≤ c` always is, whenever `b ≤ c` is not known to be an equality — that is
inherent, not a defect, but the project rule is that a restatement voids the earlier
audit, so the new leaf owes a fresh one that (i) names the gap (here: injectivity of
the same surjection, i.e. trace generation) and (ii) checks the middle object is a
genuine count. **A junk `Nat.card = 0` on the RIGHT of a `≤` is fatal in a way a junk
`0` on the left is not**: the left is a submodule and is `≥ 1`, so a zero on the
right makes the leaf FALSE rather than vacuous. The finiteness of the middle object
is therefore load-bearing for TRUTH, and in this instance it is the only thing the
universal datum `D`/`hu` is still doing in the leaf's hypothesis list — which is
worth saying in the docstring, because otherwise the next reader will think they
have to use it.

