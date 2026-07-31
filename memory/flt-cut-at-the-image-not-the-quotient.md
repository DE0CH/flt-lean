---
name: flt-cut-at-the-image-not-the-quotient
description: When a leaf is blocked on constructing a quotient object, try cutting at the IMAGE of a map instead — and move nontriviality from the object to the morphism
metadata:
  type: project
---

A leaf that says "produce an object `A` with properties P, Q, nontrivial" is
often blocked on machinery for BUILDING `A` (quotients of abelian schemes, in
the case that produced this note: `exists_isotypicQuotient_of_isIntegral`,
X0/X1.lean, cut 2026-07-31). Two moves turn that into a much cheaper pair of
leaves, and they compose:

1. **Cut at the IMAGE, not the quotient.** `A := im(v)` for a map `v : J ⟶ B`
   needs only an image factorisation, which is strictly less theory than a
   quotient by a subobject — and for abelian varieties over a field it is a
   textbook fact (Milne, *AV* 5.31) rather than a construction.
2. **Move nontriviality from the OBJECT to the MORPHISM.** `A ≠ 0` becomes
   `v ≠ 0`. Mathematically the same (a nonzero hom has nontrivial image), but
   the producer of the modular half no longer has to exhibit the object whose
   nontriviality is being asserted — it only has to exhibit a nonzero map.

**The third move is what actually paid.** State the property demanded of the
target on the IMAGE of `v` rather than on all of `B`. That single weakening
makes `B := J`, `v := ` an endomorphism, `S := T` an admissible witness — i.e.
the hard half collapses to a statement inside `End(J)` with no new objects at
all. Stating it on `B` would have left `A_f` as the only witness and the cut
would have bought nothing. The cost is one epimorphism argument (`J ↠ im(v)` is
epi onto a reduced separated scheme), paid once in the shape-free leaf instead
of by every producer.

**Audit the NONTRIVIALITY half before stating the shape-free half.** The
shape-free leaf is usually unconditionally true and boring to audit; the
refutable one is the other. Here both `hmod` and `hf` are load-bearing purely
because `v ≠ 0` is falsifiable — drop either and an explicit witness (`T ≡ 𝟙`;
`a ≡ 0`) forces `v = 0` through `Hom` being torsion-free. Related:
[[flt-cleaner-statement-harder-proof]], [[flt-two-leaves-may-be-one]].

Corollary for two-file twins: when a structure is stated once and reused
verbatim by a sibling file, the shape-free half of a cut is not a "twin" to be
duplicated — it is the SAME declaration, called by both. That is the cheapest
possible way to obey the "do not cut only one side" rule.
