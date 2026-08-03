## "THESE TWO HALVES MAY NOT BE SEPARATED" IS A CLAIM ABOUT THE SPLIT'S *HYPOTHESIS* — PIN THE OBJECT AND PROVE A UNIQUENESS LEMMA
(2026-07-31, `flt-lean-109`, cutting `exists_end_of_isWeierstrassModel_of_isAdditiveOn`
in `FreyCurve/MazurTorsion.lean`.)
A mature leaf whose conclusion bundles an OBJECT and a PROPERTY OF IT routinely
carries a paragraph forbidding the obvious split, with a real witness. This one
said: splitting "an additive equivalence `e : W(ℚ̄) ≃+ RelPoint` exists" from "any
such `e` transports `Φ` into `End W`" makes the SECOND HALF FALSE, because
`W(ℚ̄) ≅ (ℚ/ℤ)² ⊕ ⊕ℚ` has wild automorphisms, so composing a geometric `e` with one
gives another `≃+` whose transported endomorphism is algebraic for no reason. The
witness is correct and the leaf must not be split that way.
**It is a statement about splitting along an UNPINNED object, and says nothing
about splitting along a PINNED one.** The `≃+` type does not record where `e` came
from; an EQUATION can. Here the chart of `IsWeierstrassModel` gives, for each
affine solution `(x, y)` of `W`, a canonical relative point (`Spec` of evaluation
at `(x, y)`, composed with the chart), and the second half receives
`e (some x y h) = chartRelPoint … x y h` alongside `e`. The wild automorphism is
then not an admissible witness, and the split goes through.
**The receipt is a UNIQUENESS LEMMA, and it must be written in Lean or the cut is
just an assertion.** `eq_of_chartPinned` — two maps agreeing at `0` and at every
`some x y h` are equal — is *four lines* (`Affine.Point` has two constructors), and
it is what converts "pinned" from one property among many into a complete
determination of `e`. Without it a reviewer cannot tell the new split from the
refuted one; with it the difference is mechanical.
**So the standing move when a docstring forbids a split: ask what EQUATION would
record the construction the type forgets, check the equation determines the object,
and split along that.** In this development the equation is almost always
"agrees with the chart / the section / the tautological point", and the uniqueness
proof is a case split on a two-constructor inductive or a Yoneda evaluation. Say in
the amended docstring WHY the recorded witness does not apply — leave the old
paragraph standing, it is correct about what it describes — or the next reader will
believe the cut is the one that was refuted. (`X0.lean`'s
`exists_weierstrassQ_autStable_of_weierstrassAlgClos` records the same trap and
prescribes the same repair in the words "hypothesise it together with its
semilinearity"; chart-pinning is that repair with a different invariance.)
### A BUNDLED MEMBERSHIP CAN COLLAPSE TO ONE FIELD UNDER A HYPOTHESIS YOU ALREADY HAVE
Same leaf, and it halved the residual. `WeierstrassCurve.End W` is
`↥(endSubring W)` and membership is `IsIsogeny`, a THREE-field structure:
`IsRationalMap`, surjectivity of a nonzero map, finiteness of its kernel. The
leaf's docstring listed all three as its content ("All three come from `Φ` being a
MORPHISM: … surjectivity and finite kernel are then properness of `Φ` and
dimension"). Two of them are FREE:
`WeierstrassCurve.IsRationalMap.isIsogeny` (`EllipticCurve/Isogeny.lean`, PROVEN,
axiom-clean) derives both over an ALGEBRAICALLY CLOSED field, and this leaf lives
over `AlgebraicClosure ℚ`. So the residual leaf is `IsRationalMap` and nothing else.
**Before costing the fields of a bundled predicate separately, grep its OWN file
for a constructor-from-one-field theorem** — `foo.isBar`, `isBar_of_foo`,
`mk_of_…` — and read what hypotheses it carries. A file that has been through a
falsity audit usually has one, because the audit is what forced the strong
hypothesis into the statement in the first place; here the `[IsAlgClosed F]` on
`IsIsogeny.add` and the `isIsogeny` shortcut come from the same 2026-07-26
refutation, and the docstring that costed the three fields predates it.
### Two Lean traps, both about a `def`-wrapped object being defeq-but-not-syntactic
* **State a helper with the UNFOLDED spelling and let APPLICATION do the folding.**
  `IsWeierstrassModel` hands over `ι : weierstrassAffine W ⟶ A`, and
  `weierstrassAffine W` is a plain `def` for `Spec (CommRingCat.of W.toAffine.CoordinateRing)`.
  Writing a helper with `ι : weierstrassAffine W ⟶ A` makes `rw [hcomm]` fail inside
  a composite — *"the target expression is not type-correct under the `instances`
  transparency level"*, with an `Application type mismatch` naming the two spellings
  — because `rw` needs a syntactic match. Stating the helper with
  `ι : Spec (CommRingCat.of W.toAffine.CoordinateRing) ⟶ A` fixes it and costs
  nothing at the call site: `obtain`ing `ι` from `IsWeierstrassModel` and passing it
  in is checked up to defeq. Same rule as the standing "pass a factorisation equation
  as an EXPLICIT argument across a type synonym", in the direction of a `def`.
* **`Spec.map_injective` needs its two rings explicitly and still costs heartbeats.**
  `Spec.map_injective h` on `CommRingCat.of R`/`CommRingCat.of k` timed out at `whnf`
  at the default budget; `(R := CommRingCat.of …) (S := CommRingCat.of k)` plus
  `set_option maxHeartbeats 1000000 in` is what elaborates. Note the `set_option … in`
  goes ABOVE the doc comment — between docstring and `theorem` it is
  `unexpected token 'set_option'; expected 'lemma'`, reported at the END of the
  docstring, which reads like a problem with the comment.
