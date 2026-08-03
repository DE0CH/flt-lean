## A LEAF CUT OUT OF A CONSUMER THAT IS RE-PROVEN THE SAME DAY IS ORPHANED AT BIRTH — and its docstring says the opposite
(2026-08-02, `flt-lean-76`, `det ρ_{E,n} = χ_n`.) The delete×refactor orphan classes above
all need two branches. This one needs none: **one file, one day, two cuts of one consumer.**
`MoretBailly.det_nTorsion_eq_cyclotomicExponent` was cut on 2026-07-30 out of
`exists_weilPairing_mu_charZero`, whose docstring accordingly reads *"which is now PROVEN
over it"*. On the SAME DAY that consumer was re-proven over a DIFFERENT leaf
(`exists_weilPairing_mu_nondeg_of_natCast_ne_zero`), which on 2026-07-31 was delegated to a
new upstream module. So the first leaf lost its only consumer within hours of being written,
and a comment-stripped scan of every `.lean` under `Fermat/` found **exactly one** occurrence
of its name: its own declaration. It sat there for three days carrying the sentence *"This is
the ONE genuinely missing piece of mathematics in the whole archimedean cluster"* — true when
written, false the same afternoon — and a second docstring 130 lines below still said the
cluster "bottoms out" there.
**Every instrument agrees it is ordinary open work.** It emits `declaration uses 'sorry'`; a
source scan finds the token; `own.py`/`leafstat.py` correctly report it unowned; and it is a
real, true, carefully-audited statement. Nothing distinguishes it from a live leaf except
the consumer count.
**The tell is a docstring sentence of the form "X below is now PROVEN over this".** That is a
claim about `X`'s PROOF BODY, and it is exactly the claim a rival cut falsifies without
touching a character of it. So, before working any leaf:
    grep -n '<the consumer named in your leaf.s docstring>' <the file>   # find its `by` block
    # then read the proof and check YOUR leaf's name is in it
and, independently, the consumer count for the leaf itself — hits that are its own
declaration plus prose mean it is dead. Both are seconds and either one settles it.
**The repair when the orphan is a SPECIAL CASE of a live leaf: prove it, do not delete it
first.** Here the orphan is the characteristic-zero case of the live leaf with the cyclotomic
exponent named as `c` instead of read off as `(det …).val`; the derivation is ~12 lines and
took the file from 20 to 19 direct sorries with no mathematics done. Deleting instead is
defensible (a consumerless PROVEN theorem is free-floating) and is the wrong FIRST move in a
57 000-line file with many concurrent editors: proving is a one-hunk edit that conflicts with
nobody, deleting is not, and the deletion stays available to anyone afterwards while
un-deleting does not. Queue the deletion; say in the docstring that it is a duplicate, and
correct the stale claim IN PLACE rather than over it.
### The count did not move on the leaf itself, and that is the honest report
The same run RECUT the live leaf `∀ ζ primitive → …` to `∃ ζ primitive, …` — `1 → 1`. What
left is a quantifier the leaf's OWN docstring had already priced at zero (*"a prover may
prove it at a single convenient `ζ` and transport"*) and never paid. **A docstring sentence
of that shape is an unpaid formal debt in the same sense as a "why the `∀` is legitimate"
paragraph**, and here it was five lines (`IsPrimitiveRoot.eq_pow_of_pow_eq_one`, then
`map_pow` and two `pow_mul`s). Paying it is worth doing even at a flat count, because the
`∃` form is what every construction of the Weil pairing actually produces — the pairing's
value at a basis IS one specific primitive root, and nothing hands a prover an arbitrary one.
Two riders: keep the old statement under its old name as a one-line corollary so no
consumer's signature moves; and say explicitly that a recut which only WEAKENS the leaf
INHERITS its faithfulness audit (every counterexample to the weaker form refutes the
stronger), since the standing rule that a restatement VOIDS the audit does not bite in that
direction and the next reader should not have to re-derive that.
### Size a port by the declarations whose STATEMENT is base-specific, not by lines
The route note for this leaf priced the port of the finite-field Weil pairing at "8 500
lines, re-run the 94 assembly steps". That is unactionable. The measurement that is: strip
comments, list top-level declarations, take each one's text up to its first `:=`, and grep
THAT for the base-specific vocabulary. Here: **21 of 49** declarations in
`EllipticCurve/WeilPairing.lean` mention `ZMod q`, `frobFixed`, `frobPeriod`, `frobAlgHom`,
`frobeniusTorsionEnd` or `Fact q.Prime` in their STATEMENT — including `weilValueProp`, whose
very type is `WeierstrassCurve (ZMod q) → …`, so no instantiation reaches it. That confirms
the audit's verdict AND gives the next owner a work list.
**And it relocated the obstruction, which is the part that changes what a successor does.**
The audit blamed the finite-subfield genericity device wholesale. Splitting its roles: the
CARDINALITY role ("pick a point whose abscissa avoids `F`") survives over any algebraically
closed base with `F` finitely generated, because an algebraically closed field is never
finitely generated over its prime field. What has no analogue is the STABILITY role — the
`frobFixed q (…) ≤ F` clause asking that `F` be Frobenius-stable — because the auxiliary
generic points are not algebraic over the base, so their `σ`-orbits need not lie in a
finitely generated field. **When an audit condemns an avoidance device, separate its
cardinality role from its stability role; they generalise differently and only one of them
is the wall.**
