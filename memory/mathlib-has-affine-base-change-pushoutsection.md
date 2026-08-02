---
name: mathlib-has-affine-base-change-pushoutsection
description: "Mathlib's degree-0 base change of sections lives in Morphisms/Flat.lean as `pushoutSection`, invisible to any grep for cohomology"
metadata: 
  node_type: memory
  type: reference
  originSessionId: d2d70877-dfb7-4b35-946b-92222d11a4b2
  modified: 2026-08-01T17:55:49.798Z
---

`Mathlib/AlgebraicGeometry/Morphisms/Flat.lean` has a 250-line section
*"Sections of fibered products"* defining

    pushoutSection : Γ(X, Uₓ) ⊗_{Γ(S, Uₛ)} Γ(T, Uₜ) ⟶ Γ(X ×_S T, pr₁⁻¹Uₓ ⊓ pr₂⁻¹Uₜ)

and proving it is an isomorphism in five packages. The one that is FREE —
no flatness, no finiteness — is `isIso_pushoutSection_of_isAffineOpen`
(all three opens affine). That is exactly the term-by-term base change a
Čech argument needs. The others: `…_of_isQuasiSeparated_of_flat_right`,
`…_of_isQuasiSeparated_of_flat_left` (note: still needs `U_X` AFFINE),
and two `_of_ringHomFlat` variants.

**Why nobody finds it:** it is in the file about FLATNESS, under a header
about FIBRED PRODUCTS, and its name contains neither "base change" nor
"sections". `ProperPushforward.lean` carries four dated pin re-audits
saying "no cohomology of `𝒪_X` under `Mathlib/AlgebraicGeometry/`" — all
true, and all silent about this.

Read the hypothesis lists before hoping: a variant with `U_X` merely qcqs
would be degree-0 cohomology-and-base-change, FALSE without a fibrewise
hypothesis (that is semicontinuity). The pin's hypotheses are the fastest
way to see which half of a classical theorem is free.

Same family as [[flt-pin-has-dedekind-zeta]] and
[[audit-lacks-x-is-about-x]]: grep for the OBJECT the proof consumes, in
the files about the hypotheses you hold, not for the THEORY you are
quoting.
