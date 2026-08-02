---
name: flt-partial-structure-on-test-schemes
description: "To state a partial/rational algebraic structure (birational group law) in Lean, carry the partial morphism as data and state its axioms on test schemes — no equivalence classes, no triple fibre products, no scheme-theoretic fibres."
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 3f5429dc-f18a-4f7d-9d07-d71bf2898ca5
  modified: 2026-08-01T18:27:06.672Z
---

A leaf whose interface is a PARTIAL structure — an `S`-birational group law (BLR
5.1/1), a rational map, a partially-defined action — looks like it needs the whole
rational-map apparatus (equivalence classes of morphisms on dense opens, domains of
definition, graphs, schematic images). It does not, if the structure is PRODUCED by
one leaf and CONSUMED by the next.

**Why:** equivalence classes are only needed where a statement quantifies over all
representatives. A producer/consumer pair never does.

**How to apply** (measured on `flt-lean-350`, ~180 lines compiling in 6 s where a
faithful §2.5 build would have been a module):

* carry the partial morphism as DATA: `(domain : X.Opens, mul : ↑domain ⟶ X)`;
* state fibrewise density TOPOLOGICALLY —
  `∀ s, f.base ⁻¹' {s} ⊆ closure (A ∩ f.base ⁻¹' {s})` — instead of building
  `X ×_S Spec κ(s)`. Justify it in the docstring: closure-in-`X` met with the fibre
  is closure in the fibre's subspace topology, and `X ×_S Spec κ(s) ⟶ X` is a
  homeomorphism onto the set-theoretic fibre;
* state associativity ON TEST SCHEMES: quantify over `a b c d : T ⟶ ↑domain` with
  equations pinning them as `(x,y), (y,z), (xy,z), (x,yz)`, conclude
  `c ≫ mul = d ≫ mul`. This avoids `X ×_S X ×_S X` entirely and is the
  functor-of-points idiom this tree already uses;
* take the SHRUNK representative (ask that the universal translations be open
  immersions on `domain` itself, not on some `S`-dense open of it) — one fewer
  existential per clause — and write the equivalence-up-to-representative paragraph
  into the docstring, or the definition reads as an unmeetable strengthening.

Related: [[flt-cut-at-the-missing-object-but-quantify-it]],
[[flt-cut-so-each-half-is-a-consequence]].
