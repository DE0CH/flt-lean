## "NOT IN MATHLIB, NOT IN `~/cs/FLT`, **AND NOT HERE**" IS THREE CLAIMS WITH THREE DIFFERENT DECAY RATES
(2026-08-01, `flt-lean-220`, the degree-`1` Riemann–Roch cluster of `X0.lean`.)
Three sibling leaves — `relPicEquiv_sectionIdeal_of_rationalProperCurve`,
`birationalOver_affineLine_of_relPicEquiv_sectionIdeal` and
`exists_birationalOver_affineLine_of_relPicEquiv_sectionIdeal_of_sqZero` — each carried,
in near-identical words, the survey *"no Riemann–Roch, no genus and no degree of a
divisor exists in `Mathlib`, in `~/cs/FLT` **or here**"*, dated and re-checked twice. The
task prompt built from them repeated it and told me to re-run the grep.
The first two clauses were true. **The third had been false for a day**: the divisor layer
had been built on 2026-07-31, TWICE, in
`Fermat/FLT/Mathlib/AlgebraicGeometry/PrincipalDivisorDegree.lean` and
`…/CurveDivisorDegree.lean` — `divSupport`, `divCoeff`, `divDegree`, the zero/pole split,
`divDegree_eq_zero`, `residueDegree_eq_one_of_section`, and a PROVEN
`birationalOver_affineLine_of_ord_eq_sub` that is the second half of the leaf verbatim. A
genus existed too (`…/CurveGenus.lean`, with a uniqueness proof). One of the three leaves
closed the same afternoon over a single new Abel leaf.
**The compound form of the claim is what made it survive.** Bundled into one sentence, the
two durable clauses lend their authority to the perishable one, and the reader who
re-checks — as three agents did — re-checks the mathlib grep, which passes. Then the
sentence was COPIED onto three siblings, so one stale clause read as three independent
confirmations. So:
* **Split the claim when you write it.** A pin and a frozen reference repo do not move; the
  tree moves in HOURS. Write the third clause separately, with its own date and its own
  command, or do not write it.
* **Split it when you read it.** `grep -rn '<the concept>' Fermat/` is the only part worth
  re-running, and it is the part nobody runs — see the four earlier entries in this file on
  the same failure (`flt-inventory-audits-understate-what-exists`, the `Fermat/FLT/Mathlib/`
  entry below, the `jInvariant`-in-`BinaryQuadraticForm` entry, and the
  `smoothOfRelativeDimension_finrank_cuspForm` entry). This is the fifth. **The recurrence
  is the finding**: absence claims about this tree should be assumed stale by default.
### THE LAYER WAS THERE AND UNREACHABLE, AND THAT IS A SEPARATE, WORSE FAILURE
`CurveDivisorDegree.lean` was **not imported by anything**. Two branches had built rival
layers the same day; they collided on `AlgebraicGeometry.Scheme.ord_one` and
`Scheme.ord_inv`; `X0.lean` is the only module that would import either and could not
import both, so it carried a 16-line comment DELIBERATELY NOT importing the one that had
the theorem the leaf needed. Everything downstream then behaved exactly as if the file did
not exist — including three docstring surveys that said so.
**The reconciliation is small and it deleted TWO SORRY LEAVES for free.** Only two
QUALIFIED names collided (the `divDegree*` overlaps were last-component-only, in different
namespaces). Making the unimported file `public import` the imported one and deleting its
two duplicates is the whole edit. And once both were in scope, two of the three leaves in
the newly-imported file turned out to be **definitionally the same propositions** as
already-present ones:
    example … : (Function.support (Scheme.ord f)).Finite = (Scheme.divSupport f).Finite := rfl
    example … : divDegree strX f = strX.divDegree f := rfl        -- both `∑ᶠ z, ord · residueDegree`
**No name-based scan can see that pair**, because the two names share no component
(`finite_support_ord` / `finite_divSupport`, `divDegree_eq_zero_curve` /
`divDegree_eq_zero_of_ne_zero`), and `tools/merge/dupstmt.py` does not either, because the
statements differ in binder names and in which of `divSupport`/`Function.support` they are
phrased over. **What finds it is elaborating `example : <A> = <B> := rfl` in a scratch** —
four seconds, and it is the check to run on ANY pair of rival modules before choosing which
to keep. Choosing on the strength of "this one's theorem is PROVEN and that one's is a
`sorry`" — which is what the X0 note did, correctly and uselessly — keeps a duplicate leaf
on the frontier for as long as the modules stay apart.
### PUT "THE TWO POINTS ARE DISTINCT" ON THE **CONCLUSION** SIDE OF A LEAF
A small design lever that deleted a whole sub-development. The consumer needed
`px ≠ py` for two `K`-rational points arising as the images of two distinct sections, and
the honest lemma — *a section of a scheme over `Spec K` is determined by its image point*
— is real work (`SpecToEquivOfField`, surjectivity of the residue-field map, and the
`residueFieldCongr` transport that `residueDegree_eq_one_of_section` needed a
generalisation trick to survive). Nothing in this tree has it.
It is unnecessary if the leaf's CONCLUSION already says `ord f px = 1` and `ord f py = -1`:
those cannot both hold at one point, so the consumer gets `px ≠ py` by `rw` plus `omega`.
The leaf keeps `σ ≠ τ` as its hypothesis, which is the classical statement, and the
distinctness of the images comes out as a consequence — which is true, and is exactly the
fact the missing lemma would have supplied.
**Generalisable: when a consumer needs a formal separation fact about objects a leaf
produces, check whether the leaf's numeric conclusion already forces it.** A conclusion that
pins two different VALUES at two points is a conclusion that the points differ, and reading
it that way is free where proving it directly is a development.
