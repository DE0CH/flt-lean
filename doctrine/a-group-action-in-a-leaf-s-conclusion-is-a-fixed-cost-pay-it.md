## A GROUP ACTION IN A LEAF'S CONCLUSION IS A FIXED COST — PAY IT ONCE, OFF THE SUBJECT MATTER
(2026-08-01, `flt-lean-330`, `exists_geometricCuspEquiv_x1_finiteField` in
`ModularCurve/X1.lean`.) A leaf whose conclusion is an EQUIVARIANT bijection carries two
independent things: the mathematics, and the structure of the group action. The second is
almost never about your subject, and if it is not, it can be proven separately over mathlib
and deleted from the leaf for good.
Here the leaf asked for `Σ c ∈ X∖Y, Hom(κ(c), 𝔽̄_ℓ) ≃ {primitive cusp symbols}` matching the
arithmetic Frobenius against `cuspFrobX1 N ℓ` — Deligne–Rapoport VI.5, a real theory build.
But *"the geometric points above a point of residue degree `d` are a `ZMod d`-torsor under
Frobenius"* is not modular, not cuspidal and not even about a scheme. Proving it (~180 lines)
lets the leaf be restated over `ZMod (residueFDegree strX c)`, where the action is literally
`+1`, so the residue mentions **no `AlgebraicClosure`, no `→+*` and no Frobenius** and reads
as the sentence the literature states: *the cusps, indexed by their residue degrees, are the
`cuspFrob`-orbits on the symbols.*
**The mathlib toolkit, because none of it had been used in this tree and it is the whole
reason the cut is cheap:**
* `FiniteField.orderOf_frobeniusAlgHom` — the order of Frobenius on a finite extension **is**
  its degree. That is the FREENESS of the torsor, and it makes every subfield / cyclic-group /
  `a^d − 1 ∣ a^k − 1` argument unnecessary;
* `AlgHom.card` — an algebraically closed target receives exactly `finrank` embeddings. That
  is TRANSITIVITY, obtained **by cardinality**: an injective map between finite sets of equal
  size is bijective, so no Galois theory of finite fields appears anywhere;
* `FiniteField.pow_card` for the periodicity `Frob^[d] = id`;
* `RingHom.ext_zmod` to state the whole thing about BARE ring maps rather than `𝔽_ℓ`-algebra
  maps — which is what keeps the `letI`-only `residueFAlgebra` out of the statement.
**The generalisable question, and it costs one read of the conclusion: is the group acting on
one side of your bijection acting the same way on EVERY instance of the problem?** Frobenius
on `Hom(κ(x), 𝔽̄_ℓ)`, `Gal(K̄/K)` on embeddings, `μ_n` on a torsor, deck transformations on a
cover — all yes. If so its orbit structure is a lemma about the group, not about your leaf,
and it belongs outside.
**Report it as a RECUT and give the receipt, because the delta cannot show it.** Count
unchanged, `24 → 24` in the file and `191 → 191` in the build, and
`git diff | grep -E '^[+-] *sorry *$'` exactly one `+` and one `-`. No mathematics was proven;
what changed is what is LEFT in the leaf.
Two riders from the same run:
* **The positivity conjunct (`0 < residueFDegree`) is carried, not derived, on purpose.** It
  says the cusps are closed points — true, and a separate piece of scheme theory (closedness
  of the points of a finite complement in a proper curve, plus Jacobson-ness) that the moduli
  owner should not have to do. When a torsor cut needs a finiteness side condition, put it in
  the leaf's conclusion and say in the docstring both why it is true and how to avoid it;
  making it a fourth leaf would be the expensive kind of `1 → 2`.
* **Prototype the group-theoretic half in a MATHLIB-ONLY scratch.** It mentions none of the
  project, so iterations are seconds; then re-verify the same text in a scratch that
  `public import`s the target module (7 s here) to catch the namespace and `open` problems —
  the first such run failed with *"invalid use of explicit universe parameters, `Scheme` is a
  local variable"*, which is the standing autoImplicit tell for a missing
  `open CategoryTheory AlgebraicGeometry` and nothing to do with universes.
