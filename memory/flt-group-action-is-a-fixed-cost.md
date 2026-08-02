---
name: flt-group-action-is-a-fixed-cost
description: An equivariant-bijection leaf splits into the mathematics and the orbit structure of the group; the second is mathlib and belongs outside the leaf.
metadata: 
  node_type: memory
  type: project
  originSessionId: 24422c2d-a2ea-4f18-ac34-e3753aff7ccc
  modified: 2026-08-01T17:56:10.454Z
---

(2026-08-01, `flt-lean-330`, `exists_geometricCuspEquiv_x1_finiteField` in
`ModularCurve/X1.lean`.) A leaf whose conclusion is a GALOIS-EQUIVARIANT bijection
carries two independent things: the subject-matter theorem, and the orbit structure
of the acting group. Ask whether the group acts the SAME WAY on every instance of the
problem — Frobenius on `Hom(κ(x), 𝔽̄_ℓ)`, `Gal(K̄/K)` on embeddings, `μ_n` on a torsor.
If so, that half is a lemma about the group, provable over mathlib alone, and it
should leave the leaf permanently.

Here: `Hom(κ(x), 𝔽̄_ℓ)` is a `ZMod (deg x)`-TORSOR under the arithmetic Frobenius.
Proving it (~180 lines) let the Deligne–Rapoport cusp leaf be restated over
`ZMod (residueFDegree strX c)` with the action as `+1`, so the residue mentions no
`AlgebraicClosure`, no `→+*` and no Frobenius.

The mathlib toolkit, none of it previously used in this tree:
* `FiniteField.orderOf_frobeniusAlgHom` — order of Frobenius = degree. This is
  FREENESS, and it replaces every subfield / cyclic-group / `a^d−1 ∣ a^k−1` argument;
* `AlgHom.card` — an algebraically closed target receives exactly `finrank`
  embeddings. This gives TRANSITIVITY **by cardinality** (injective + equal finite
  cardinality ⟹ bijective), so no Galois theory of finite fields is needed;
* `FiniteField.pow_card` for periodicity; `RingHom.ext_zmod` to keep the statement
  about bare ring maps rather than `𝔽_ℓ`-algebra maps.

Report it as a RECUT with the receipt — count unchanged, and
`git diff | grep -E '^[+-] *sorry *$'` exactly one `+` and one `-`. No mathematics is
proven; what changes is what is LEFT in the leaf.

Prototype the group half in a MATHLIB-ONLY scratch (seconds per round), then re-verify
in a scratch that `public import`s the target (7 s) for namespace/`open` problems. See
[[flt-audit-consumer-claim-is-refutable-by-compile]] for the companion check, and
[[flt-leaf-cost-estimates-are-hypotheses]].
