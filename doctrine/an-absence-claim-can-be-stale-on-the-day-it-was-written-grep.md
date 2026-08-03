## AN ABSENCE CLAIM CAN BE STALE ON THE DAY IT WAS WRITTEN — GREP YOUR OWN IMPORT LIST, NEWEST FIRST
(2026-08-02, `flt-lean-342`, `exists_abelianQuotient_of_range_ne_univ` in
`Modularity/TateModule.lean`.)  The standing rule is that the PROJECT half of an
absence claim expires fast, so re-grep it.  This run found the sharper form:
**it can be false already when the ink dries, and no amount of re-grepping
LATER identifies it as stale, because it was never fresh.**
That leaf's docstring, dated 2026-07-31, ends:
> So a prover must either build the fppf quotient here or first build the
> `AbelianSchemeStruct ↔ GrpObj` translation and then the quotient on the
> mathlib side.
`Modularity/AbelianSchemeGrpObj.lean` builds exactly that translation, is a
`public import` OF THE SAME FILE, and was added **the same day** — its own
header says "found 2026-07-31".  Two agents worked one morning and neither
could see the other.  The half of the claim about MATHLIB (no fppf quotient,
`Group/` is exactly `Abelian.lean` + `Smooth.lean`) re-checked out exactly, so
the paragraph reads as verified and the false clause rides along with it.
**The check is not a grep for the concept — it is a read of your own module's
import list against the leaf's date:**
    grep -nE '^\s*(public )?import Fermat' <your module>     # newest entries first
    git log --diff-filter=A --format='%ad %h %s' --date=short -15 -- Fermat/FLT/<its dir>/
A module whose NAME matches the thing the docstring calls missing, sitting in
your own import list, is the commonest way this fires — here
`AbelianSchemeGrpObj` against a claim about `AbelianSchemeStruct ↔ GrpObj`.
Both halves of a two-clause absence claim must be checked separately; one of
them being re-verifiable is what makes the other survive.
**And the payoff is a RECUT, not merely a corrected paragraph.**  Once the
bridge is known present, the leaf must stop demanding what the bridge
produces.  `AbelianSchemeStruct` (ten functor-of-points fields) became
`GrpObj + IsProper + GeometricallyIntegral`, with SMOOTHNESS and COMMUTATIVITY
free from `AlgebraicGeometry.smooth_of_grpObj` and
`isCommMonObj_of_isProper_of_geometricallyIntegral` — the two hardest fields,
and the current statement was BLOCKING both.  That is this file's own "never
ask a geometry leaf to produce a bundled algebraic structure" rule; a bridge in
your import list is what makes it available, and nothing announces it.
### `Mult` IS A FAMILY OF MORPHISMS — `Mult.ofPostComp` is the converse of `mulByElt`
Same run.  `TateModule.lean` already carried the Yoneda layer in ONE direction:
`Mult.mulByElt m a : A ⟶ A` (the action read off the tautological point
`RelPoint.self f`) and `Mult.act_val : (m.act a y).1 = y.1 ≫ m.mulByElt a`.  The
CONVERSE was absent and is ~35 lines: given `γ : R → (A ⟶ A)` with `γ a ≫ f = f`,
`γ 1 = 𝟙`, `γ (a*b) = γ b ≫ γ a`, `γ (a+b) = γ a + γ b` **as an equation in
`RelPoint f f`**, and each `γ a` additive, `act a := RelPoint.postComp (γ a)` is
a `Mult`.
* **`pre_act` is FREE** — precomposition and postcomposition commute, so
  naturality in the test object is `Category.assoc` with no hypothesis at all;
* **`act_add` is the only step with content**, and it is the Yoneda transport of
  the `RelPoint f f` equation along `ab.pre_add` — the same move `act_val`
  makes, in the other direction.
So a leaf demanding a `Mult` is demanding six functorial axioms for what is
three equations of MORPHISMS plus one additivity clause.  Ask this of any
geometry leaf whose conclusion carries a `Mult`, an `AbelianSchemeStruct`, or
any other functor-of-points structure: which fields would the producer have to
invent, and which are transport of something it already has?
### `open scoped CategoryTheory.MonObj` MAKES `ι` A RESERVED TOKEN
Same run, and at file level it would have broken a 27 000-line module.  Adding
that line to reach mathlib's group-object notation turns `ι` into a TOKEN, so
every binder named `ι` — and this development names closed immersions `ι`
everywhere — dies with
    unexpected token 'ι'; expected '_' or identifier
reported AT THE BINDER, which reads as a typo in your own signature rather than
as a notation clash.  The `GrpObj` class itself needs only `open CategoryTheory`;
the scoped `MonObj` notation is wanted only inside proofs that write `*` and `1`
for the group object (which is why `AbelianSchemeGrpObj.lean` opens it inside a
`section`).  Scope it with `open scoped CategoryTheory.MonObj in` on the one
declaration, never at file level — and note that a scratch module which opens it
does NOT reproduce the target file's scope, so a statement that parses in your
scratch can fail in the file and vice versa.
