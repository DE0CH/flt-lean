## A LEAF THAT CONCLUDES `∃ <BUNDLED RECORD>` IS TWO OBLIGATIONS — AND THE PACKAGING HALF IS PROVABLE TODAY
(2026-08-02, `flt-lean-236`, on
`exists_obstructionCocycle_smallExtension_deformation_of_section` in
`HardlyRamified/Deformation.lean`.) The rule "never ask a geometry leaf to produce a
bundled algebraic structure" already stands above. This is its commonest shape in this
tree and the recipe for executing it, because the obstacle is never the mathematics — it
is that the residue cannot be STATED where the leaf lives.
The leaf concluded `∃ D' : HardlyRamifiedDeformation …, IsDeformationStructureOn D D' (S ⧸ K) _ q`.
`HardlyRamifiedDeformation` bundles a topology, `IsTopologicalRing`, `IsLocalRing`,
`Algebra ℤ_[ℓ]`, `IsNoetherianRing`, `IsAdic`, `IsAdicComplete`, the representation, the
reduction map, its surjectivity and the Frobenius charpolys — of which **exactly one**
(the representation) is what obstruction theory produces. Everything else is commutative
algebra with no Galois input, and it is now `exists_deformationStructureOn_of_hasFramedLiftOn`,
PROVEN. **Count unchanged, 1 → 1; what left the frontier is the whole record.**
**The three facts that make such a packaging cheap, and none of them is obvious:**
* **the TOPOLOGY is not a choice.** `(IsLocalRing.maximalIdeal T).adicTopology` makes
  `IsAdic (IsLocalRing.maximalIdeal T)` literally **`rfl`** — mathlib defines
  `IsAdic J := inst = J.adicTopology` — and `IsTopologicalRing T` is
  `(Ideal.nonarchimedean _).toIsTopologicalRing`, `NonarchimedeanRing` extending it. Do
  NOT use a quotient topology inherited from the presenting ring; it is not the adic one;
* **the `≃+*` that a "structure ON `T`" predicate asks for is `RingEquiv.refl T`**, since
  the record you are building is carried by `T` itself. Every clause mentioning it is `rfl`;
* **charpoly compatibility of the new record is `Polynomial.map_map` plus the old record's
  own field**: `(ρ'.charFrob).map (π ∘ q) = ((ρ'.charFrob).map q).map π = ρbar.charFrob`.
**HOW TO STATE THE RESIDUE WHEN THE BINDER IS HAZARDOUS — this is the part that decides
whether the cut is possible at all.** That leaf's conclusion sits under an
`∃ oc : … →ₗ[k] …` binder whose instance context makes a new clause fail with the internal
error `unknown free variable` (the file records four separate measurements of it). The
recipe, copied from `IsDeformationStructureOn` in the same file:
* make the residue a **top-level `def … : Prop`**, never an inline conjunct;
* take the target ring's instances (`CommRing`, `IsLocalRing`, `Algebra`) as **ordinary
  explicit arguments**, and put them — with the source's — in a `letI` block in the BODY,
  so the signature performs no instance search;
* take the comparison map as a **bare function** `q : T → D.R`, bundling its ring-hom-ness
  existentially inside as `∃ p : T →+* D.R, (∀ x, p x = q x) ∧ …`.
At the use site the clause is then one constant applied to `inferInstance`s, which the
surrounding binder elaborates without complaint. Both new declarations went green first
try in a 12-second scratch that `public import`s the module's own (freshly built) olean.
Two riders. **`rw` on a variable that occurs inside a structure literal fails with
"motive is not type correct" — use `subst`.** `rw [hpe]` for `hpe : p = q` failed because
`p` sits in the `π := D.π.comp p` field and later fields' types depend on it; `subst hpe`
(both sides local variables) deletes the problem and every goal closes by `exact`. And
**say RECUT in the commit**: the open leaf is renamed (`…_of_section_framed` here), the old
name survives as a PROVEN theorem, so any queue entry keyed on the old name passes every
existence check and finds nothing to prove.
