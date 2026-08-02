---
name: flt-peel-the-record-not-the-datum
description: A leaf whose conclusion is a bundled record splits into "produce the datum" (the leaf) and "package it" (provable now); the packaging predicate must be a top-level def taking instances as ordinary arguments.
metadata:
  type: project
---

(2026-08-02, `exists_obstructionCocycle_smallExtension_deformation_of_section`,
`HardlyRamified/Deformation.lean`.) A leaf concluding `∃ D' : <bundled record>, <D' lies
over D>` is two obligations glued: **produce the mathematical datum** and **package it as
a record**. The second half is normally pure commutative algebra with no content from the
leaf's subject at all, and it is provable today. Peel it — the trade is 1 leaf → 1 leaf
and what leaves the frontier is every instance the record demands.

Here the record was `HardlyRamifiedDeformation` (topology, `IsTopologicalRing`,
`IsLocalRing`, `Algebra ℤ_[ℓ]`, `IsNoetherianRing`, `IsAdic`, `IsAdicComplete`, the rep,
the reduction map, its surjectivity, Frobenius charpolys) plus the `≃+*` of
`IsDeformationStructureOn`. All of it is now
`exists_deformationStructureOn_of_hasFramedLiftOn`, PROVEN; the residue asks for a framed
representation and nothing else.

**The three facts that make such a packaging cheap, and they generalise:**

* **the TOPOLOGY is never a choice.** Take `(IsLocalRing.maximalIdeal T).adicTopology`;
  then `IsAdic (maximalIdeal T)` is **`rfl`** (mathlib defines `IsAdic J := inst =
  J.adicTopology`) and `IsTopologicalRing T` is
  `(Ideal.nonarchimedean _).toIsTopologicalRing`. Do NOT reach for a quotient topology
  inherited from the presenting ring — it is not the adic one;
* **the `≃+*` a "structure on `T`" predicate asks for is `RingEquiv.refl T`**, because the
  record you build is carried by `T` itself. Every clause that mentions `e` is then `rfl`;
* **charpoly compatibility of the new record is `Polynomial.map_map` plus the OLD record's
  own field** — `(ρ'.charFrob).map (π ∘ q) = ((ρ'.charFrob).map q).map π`.

**HOW TO STATE THE RESIDUE UNDER A HAZARDOUS BINDER.** The leaf's conclusion sits inside an
`∃ oc : … →ₗ[k] …` binder whose instance context makes any new clause fail with the internal
error `unknown free variable`. The recipe that works, copied from `IsDeformationStructureOn`
in the same file:

* make it a **top-level `def … : Prop`**, never an inline conjunct;
* take the target ring's instances (`CommRing`, `IsLocalRing`, `Algebra`) as **ordinary
  explicit arguments**, and put them plus the source's instances in a `letI` block in the
  BODY, so the signature needs no instance search at all;
* take the comparison map as a **bare function** `q : T → D.R` and bundle its ring-hom-ness
  existentially inside (`∃ p : T →+* D.R, (∀ x, p x = q x) ∧ …`).

At the use site the whole clause is then one constant applied to `inferInstance`s, which is
exactly what the surrounding binder can elaborate.

**A `rw` on a variable occurring inside a structure literal fails with "motive is not type
correct" — use `subst`.** `rw [hpe]` for `hpe : p = q` failed because `p` appears in the
`π := D.π.comp p` field of a `HardlyRamifiedDeformation` literal, and later fields' types
depend on it. `subst hpe` (both sides are local variables) removes the problem entirely and
the goals close by `exact`.

See [[flt-take-the-arithmetic-out-of-the-leaf]] and
[[flt-ask-for-the-subobject-not-the-structure]] for the same move on other records, and
note the bookkeeping obligation: a recut RENAMES the open leaf, so the old name survives as
a PROVEN theorem and every queue entry keyed on it becomes a phantom
([[flt-frozen-main-rots-the-queue]] has the release-side version).
