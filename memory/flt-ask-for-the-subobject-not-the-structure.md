---
name: flt-ask-for-the-subobject-not-the-structure
description: Never ask a geometry leaf to produce a big algebraic structure; ask for the object plus CLOSURE clauses and transport the algebra along the injection
metadata:
  type: project
---

`exists_relPicZeroSubgroup` asked a leaf to produce an `AbelianSchemeStruct` on
`Pic⁰` — twelve fields, nine of them group axioms and two naturality. None of
those nine is about the identity component: they are the group axioms of `Pic`,
restricted. So an owner of the geometry had to reprove them from scratch, and
the leaf looked far bigger than its mathematics.

The cut (2026-07-31) replaces the structure with three CLOSURE clauses — the
image of `incl` contains `zeroPoint`, and is closed under `addPoint` and
`negPoint` — each a bare existential with no equation to verify. The group
structure is then transported along `incl`: `ab.add p q` is the unique preimage
(existence from closure, uniqueness from injectivity), and every axiom is
`hinj` applied to a rewrite chain ending in the corresponding law upstream.

Two things made it cheap, and both are worth expecting:

* the upstream group axioms (`IsRelPicOf.addPoint_assoc`, `addPoint_comm`,
  `zeroPoint_addPoint`, `negPoint_addPoint`, `pre_addPoint`, `pre_zeroPoint`)
  did not exist and had to be proven first — but each is `inj` applied to a
  chain of `RelPicEquiv`s, i.e. the unitor / associator / braiding / inverse of
  the tensor calculus, and all six went through on the first elaboration;
* the transport itself is `choose` on the three closure clauses plus nine
  one-line `rw` chains.

**How to apply:** whenever a leaf's conclusion contains a bundled algebraic
structure, check which of its fields are inherited rather than constructed.
Inherited fields belong in an assembly, not in the leaf. State the leaf as
"the object, plus closure of its image under the operations it inherits".
