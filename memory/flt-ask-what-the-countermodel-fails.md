---
name: flt-ask-what-the-countermodel-fails
description: An audit's counter-model names the missing atom — the property the model FAILS is the thing to prove, and the audit's "no route" verdict is scoped to the axis it searched
metadata:
  type: feedback
---

When a leaf carries a FALSITY/IRREDUCIBILITY audit built on an explicit
counter-model `A` ("every identity in this file holds in `A`, and the leaf is
false there"), do not read it as "no route". Read it as a **specification of the
missing atom**: check whether `A` still satisfies your new tool, and if it does,
ask *which property `A` fails*. That property, stated as a lemma, is a route the
audit does not refute — by construction.

Worked instance, `HasseBound.lean` 2026-07-31. Its audit of
`natCard_ker_degreeFormEnd_le` says "no rearrangement of the `ℤ[F]` material, and
no `ℓ`-adic / Tate-module or Weil-pairing computation, can close this leaf",
over `A = ⨁_{ℓ≠q}(ℚ_ℓ/ℤ_ℓ)²` with `F` the companion matrix of `X²−cX+q` at
`q=5, c=7`. Both clauses steered wrongly at the margin:

* the Weil-pairing determinant **did** decide something the counting facts could
  not — that `F` is not multiplication by an integer (`det F = q` vs `det[r] =
  r²` for every prime `p ≠ q`). The audit's true claim is that a determinant
  cannot see a SIGN; "cannot see anything" is a wider claim it never made.
* `A` survives that (its `F` is not a scalar). The property `A` **fails** is that
  its unit group is infinite — the companion matrix generates infinitely many
  invertible endomorphisms. So "an isogeny invertible in `End` has finite
  multiplicative order" is an atom no `A`-style model can refute, and Pell on the
  discriminant turns it into Hasse's bound.

Corollary for writing audits: state which axis the model was built to kill, and
list what the model DOES satisfy. Also: a sketch offered as "elementary, just a
second piece of work" deserves the same suspicion as a leaf — the one here
(`(F∓1)(F∓q) = 0` "with both factors of finite kernel") had its load-bearing
step, `F ≠ [q]`, entirely unaddressed. See [[audit-searched-production-not-invariant]]
and [[flt-dispatch-consumer-lists-are-unverified]].
