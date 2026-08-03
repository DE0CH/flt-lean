## AN UNCITABLE HIT IS STILL THE PROOF — grep the whole tree for the CONCLUSION, including layers you cannot import
(2026-08-02, `flt-lean-332`, `exists_residueField_ringHom_of_valuationSubring` in
`Modularity/TateModule.lean` — open since it was cut, closed in one run.)
That leaf carried a dated MATHLIB STATUS paragraph, and every word of it was true:
> there is no `IsAlgClosed` instance for the residue field of a valuation ring
> (`grep` over `Mathlib/` for `IsAlgClosed.*ResidueField` is empty) … **Both
> halves have to be written.**
`grep -rn "IsAlgClosed" --include=*.lean Fermat/ | grep -i "residue\|valuation"` returns
**four** hits, and one of them —
`GaloisRepresentation.exists_resIso_of_comap_toSubring_eq_range` in
`FreyCurve/IsogenySignature.lean` — is the same theorem for `ℚ`, PROVEN, with both halves
written out and a docstring describing the argument step by step. The leaf's proof is that
proof with `AlgebraicClosure ℚ ↝ AlgebraicClosure F`; it compiled **first try**, and the
whole run was 15 seconds of elaboration.
**The new part, and it is why the standard "grep `Fermat/` too" rule did not fire:** the
hit is in a layer this module CANNOT IMPORT (`FreyCurve`/`EllipticCurve` sit downstream of
`Modularity`). So the question an agent naturally asks — *is there something I can call?* —
correctly answers NO, and the audit stops there. **That is the wrong question.** A hit you
cannot cite still hands you the route, the lemma names, and the tactic script, which is
95% of the work. Ask *does this tree contain a PROOF of this shape*, not *does this tree
contain a usable declaration*.
So the check, and it is one command:
    grep -rn '<the CONCLUSION, 2-3 spellings>' --include=*.lean Fermat/
Grep for the mathematical content, never for what you would name it, and **do not filter
by your import cone**. Then decide separately whether the hit is a call or a transcription.
Both outcomes are cheap; only "not in the tree" is expensive, and it was false here.
Corollary for whoever WRITES such a paragraph: say which trees you searched, and quote the
command. "`grep` over `Mathlib/` is empty" is a true and complete sentence that reads as a
claim about the project. This is the fourth recorded instance of the same failure and the
first where the answer was in an unimportable layer.
### The technique that made the transcription cheaper than the leaf's own route
The docstring prescribed proving `κ(V)` algebraic over **`κ(w)`** — "the residue extension
of an algebraic extension of valued fields is algebraic", a real chapter of valuation
theory. **Compare the two algebraically closed fields over the PRIME FIELD `ZMod p`
instead.** It is legal exactly when no compatibility is asked of the isomorphism (which the
leaf's own docstring already argues at length), and it deletes the chapter:
* `κ(V)` is algebraic over `𝔽_p` because every `a : V` is algebraic over `ℤ`, and the
  **PRIMITIVE PART** `g` of an integral equation still kills `a` while `g mod p ≠ 0`
  precisely because `g` is primitive (`C p ∣ g` would make `p` a unit of `ℤ`). Ring maps
  out of `ℤ` are unique, so no compatibility has to be checked — `RingHom.ext_int`;
* the other side is `AlgebraicClosure κ(w)` with `κ(w)` FINITE, so `Module.Finite.of_finite`
  plus `Algebra.IsAlgebraic.trans` is the whole of it;
* `IsAlgClosure.equiv (ZMod p) _ _` produces the isomorphism.
**Generalisable: when a leaf asks for an isomorphism of two algebraic closures and pins it
by nothing, compare them over the prime field.** The intended base field is usually where
all the difficulty is, and it is usually not needed.
### The one Lean error in the run: do NOT hand-install `Algebra R (AlgebraicClosure k)`
`AlgebraicClosure.instAlgebra {R} [CommSemiring R] [Algebra R k] : Algebra R (AlgebraicClosure k)`
is an instance, and so are `IsScalarTower R S (AlgebraicClosure k)` and
`CharP (AlgebraicClosure k) p`. Supplying `Algebra R k` is therefore enough and a
`letI : Algebra R (AlgebraicClosure k) := (ZMod.castHom …).toAlgebra` is actively harmful:
it is a second, non-defeq `SMul`, and `IsScalarTower.of_algebraMap_eq'` then fails with
    has type  @IsScalarTower (ZMod ?) ? ? Algebra.toSMul Algebra.toSMul Algebra.toSMul
    but is expected to have type
      @IsScalarTower (ZMod p) κ(w) (AlgebraicClosure κ(w)) this✝.toSMul
        (AlgebraicClosure.instSMulOfIsScalarTower κ(w)) (AlgebraicClosure.instSMulOfIsScalarTower κ(w))
which reads as a universe or elaboration problem and is neither. **Deleting three `haveI`s
fixed it.** The general shape: `AlgebraicClosure k` derives its scalar structure from `k`'s,
so give it `k`'s and stop.
