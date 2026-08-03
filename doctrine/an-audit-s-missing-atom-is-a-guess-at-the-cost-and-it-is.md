## AN AUDIT'S "MISSING ATOM" IS A GUESS AT THE COST, AND IT IS USUALLY TOO BIG

(2026-07-31, `HasseBound.lean`.) Two independent audits in that file, months apart,
ended at the same sentence — *"separable and non-constant ⟹ `#ker = deg > 1`"* — and
both priced it the same way: "a fibre-counting statement for a separable rational map
of curves, which is a real piece of work", i.e. blocked on a degree theory this tree
does not have and, in characteristic `p`, cannot cheaply get (`Isogeny.lean`
machine-REFUTES the characteristic-`p` dual isogeny). On that basis the leaf it gated,
the ordinary criterion `exists_ne_zero_qTorsion`, was left open for three days with two
expensive routes written out beside it (Deuring by character sums; the Verschiebung).

**No fibre is ever counted, and the proof is 90 lines.** The audits asked for the
CARDINALITY of a fibre; what the argument needs is only that an injective map has
SINGLETON fibres — which is the hypothesis, not a theorem. Concretely: `φ` injective
with `x`-witness `A/B` in lowest terms, so for each slope `ξ` the polynomial
`A − ξ·B` has exactly ONE distinct root; if its degree is `≥ 2` that root is a
MULTIPLE root, and there the Wronskian `A′B − AB′` vanishes. Distinct slopes give
distinct roots, there are infinitely many slopes, so the Wronskian vanishes
identically — and a vanishing Wronskian is exactly `λ(φ) = 0`, inseparability.

The general lesson, and it is about how to READ the audits this project is full of:

* **An audit's "missing atom" is the cheapest thing its author could see, not the
  cheapest thing there is.** It is a hypothesis about cost, in the same way a
  docstring's "this needs lemma X" is (see *Leaf cost estimates are hypotheses*).
  Both audits here named the right OBJECTS — "the `x`-witness `A/B` and its Wronskian
  `A′B − AB′`, both already handled in that file" — and overestimated what has to be
  done with them. When an audit names the objects and then prices the step high, try
  the objects.
* **A quantitative statement blocking a leaf is often needed only qualitatively.**
  `#ker = deg` was demanded; `#ker > 1` was used. Check which one the consumer
  actually calls before accepting the blockage.
* **The Wronskian is this tree's separability oracle**, and it is cheap:
  `DifferentialCharacter.lean`'s `IsDiffCharCert` says `λ·(…) = (A′B − AB′)·(…)`, so
  `A′B − AB′ = 0` gives `λ = 0` with no side conditions, and `λ(F) = 0` for the
  `q`-power Frobenius is literally `derivative (X^q) = 0`. Reach for it before
  reaching for degree theory, the Cartier operator, or `E[p^∞]` structure theory.

One mechanical trap met on the way, worth knowing before it costs a cycle:
`IsRationalMap` hands you witnesses `A, B` that need NOT be coprime, and the fibre
argument needs coprimality. Dividing by `gcd A B` loses the witness identity exactly
on the (finite) zero set of the gcd, and there is no cheap way to recover it there —
no continuity argument is available for `x(φP)`, which is not a polynomial in `x(P)`.
So carry the gcd as an explicit third polynomial `G` and state every downstream lemma
"for all `P` with `G(x P) ≠ 0`"; then absorb `G` by excluding the finitely many slopes
it is attained at. Do not try to prove the reduced identity holds everywhere.

