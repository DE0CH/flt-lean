## A LEAF'S PRESCRIBED ROUTE CAN BE UNSTATABLE AT THE LEAF'S OWN LINE — check the VOCABULARY's declaration order, not the theorems'
(2026-08-02, `flt-lean-50`, `exists_nonConstantClassify_gamma0Datum_fractionRingPowerSeries`
in `ModularCurve/X0.lean`.) The declaration-order sections above are about a THEOREM
declared below its consumer. There is a cheaper and much better-hidden variant: the
**noun** the route needs is below you. That leaf's docstring prescribed, correctly, *"if
the classifying point factored through `SpecQ` the datum's `j`-invariant would be a
rational constant"* — and `IsWeierstrassModel`, the file's only vocabulary for *"`W` is
the Weierstrass model of this elliptic scheme"*, was declared **2000 lines below it**. So
the route could not be written down at all, and every attempt to cut the leaf along it
ends in inlining a copy of that definition, which is a duplicate cut in all but name.
**The check is one `grep -n` per NOUN in the route, not per theorem**, and it belongs
before any mathematics: list the objects the docstring's argument mentions (`j`-invariant,
Weierstrass model, coarse ring, `IsJElt`, …), find each one's declaration line, and
compare with your own. Here two of the four were below.
**The repair is to hoist the DEFINITION, which is small, not the theory, which is not.**
`weierstrassAffine` / `weierstrassAffineStr` / `IsWeierstrassModel` are 51 lines with three
dependencies, all imported; the `IsJElt` layer that sits with them is thousands of lines and
did not have to move. Moving UP was chosen over moving the leaf DOWN because the leaf's
consumer chain was ~500 lines and would have travelled with it. Receipt for the move:
`Counter(lines before) == Counter(lines after)`, plus the three checks the hoist note above
prescribes — and note the third one fires falsely here, because five lines in the jumped
range begin with the word `section` **inside docstring prose** (`section comment above …`).
