---
name: flt-reduce-to-an-open-leaf-not-a-proof
description: "An absence audit asks \"is it PROVEN\" and so misses an open sorry LEAF stating the same theorem — reducing two theory gates to one is progress even though nothing is proven"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 774353e4-c0c9-4425-a952-d1ff8acda96d
  modified: 2026-07-31T07:03:50.095Z
---

`X0.lean`'s `exists_heckeCorrespondenceFamily` carried a careful 2026-07-28
diagnosis: `IsGamma0Isogeny` inhabitation is blocked because Vélu yields a map of
POINT GROUPS while the field wants a morphism of SCHEMES, and "nothing in this
development turns a homomorphism of geometric point groups into a morphism of
abelian schemes". Every clause true. The verdict wrong: `exists_isNIsogenyPair`,
22 600 lines below in the same file, ASSERTS the scheme-level quotient of an
elliptic scheme by a finite flat cyclic subgroup over a `ℚ`-scheme, with the
kernel condition quantified over every test scheme — the exact obligation the
diagnosis called uncheckable — and its whole universal-property layer is proven.
At a subgroup of order `ℓ` it supplies six of `IsGamma0Isogeny`'s seven fields.

**Why:** the audit searched for something to *use*, i.e. something PROVEN. An
open `sorry` leaf answers "is this proven?" with no and "is this available as a
reduction target?" with yes, and those are different questions. Reducing a second
theory gate onto an existing leaf is real progress — it halves what a prover must
build and it settles the vacuity hedges that hang off the unknown gate — even
though the leaf count does not move.

**How to apply:** when an audit says a theorem is missing, grep the file's own
`sorry` leaves for the CONCLUSION as well as the libraries for a proof. Then
check declaration ORDER: here the reusable statement had to be phrased in
`Gamma0Datum`/`CyclicSubgroupOfOrder` (both near line 1000) to sit above both
consumers, because `IsNIsogenyPair` is defined below one of them — that
constraint, not the mathematics, is what decides whether the merge is cheap.
Related: [[flt-inventory-audits-understate-what-exists]],
[[audit-searched-production-not-invariant]],
[[flt-missing-machinery-may-be-downstream]].
