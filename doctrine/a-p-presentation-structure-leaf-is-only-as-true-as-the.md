## A `∀ P : <presentation structure>` LEAF IS ONLY AS TRUE AS THE STRUCTURE PINS ITS OBJECT

(2026-07-31, generalising a refutation found 2026-07-30.) `X1.lean` and `X0.lean` state most
of their geometry as `∀ P : Gamma1GITPresentation N (Spec K), <property of P.A>`. That shape
is only sound for properties the FIELDS force. `Gamma1GITPresentation.classify_dM` pins the
coarse ring `B = A^G` — it says `Spec (algebraMap B A)` IS the classifying map of the
universal family — and pins `A` **not at all**. `smoothCurve_A_of_gamma1GITPresentation` was
refuted on exactly that gap, by an explicit inhabitant nobody had looked for.

**The test is cheap and mechanical: PINCH the honest presentation.** Given any inhabitant `P₀`
with ring `A₀`, group `G₀`, invariants `B₀`, and a `G₀`-stable ideal `0 ≠ I ⊊ A₀`, set

    A := A₀ ×_{A₀ ⧸ I} A₀,   G := G₀ × ℤ⧸2   (G₀ diagonal, the generator swapping),
    dM := (Spec Δ)^* dM₀     for Δ : A₀ → A, a ↦ (a, a).

Every field survives — each datum is a pullback along an explicit ring map, `pr₁ ∘ Δ = id`
carries `cover`, and `A^G = B₀` keeps `classify_dM` — while `Spec A` is two copies of
`Spec A₀` glued along `V(I)`, i.e. nodal. **So no property that fails at a node is provable
from these axioms**, and any leaf asserting one is FALSE, not merely hard.

Two corollaries worth having in advance:

* **The swap is what keeps `B` pinned, and it is also why the pinch is not universal.**
  Dropping it (`G := G₀` alone) would break far more — the two components stop being
  exchanged — but then `A^{G₀} = B₀ ×_{B₀ ⧸ (I ∩ B₀)} B₀ ≠ B₀`, and `classify_dM` rejects it.
  So the pinch family only ever attacks properties destroyed by GLUING (regularity,
  smoothness, normality, being a domain), never properties preserved by it (reducedness,
  Krull dimension, transitivity of `G` on components). Check which side your leaf is on
  before assuming the refutation transfers: `transitiveMinimalPrimes_tensorProduct_of_`
  `gamma1GITPresentation` was audited against the pinch on 2026-07-31 and survives it.
* **The repair is to MOVE the citation, not to weaken the statement.** `Gamma1RigidifiedModuli`
  carries `universal`, a fine-moduli property WITH a uniqueness clause, so it pins `Spec A` up
  to unique isomorphism. State the citation there and carry it down as a structure FIELD
  (`smoothM : SmoothOfRelativeDimension 1 strM` is the worked example). Weakening the
  conclusion instead just makes a second universally-quantified guess of the kind that was
  just refuted.

**And a field added this way SHRINKS the class every other leaf in the file quantifies over.**
Once `smoothM` is a field the pinched `P` is not an inhabitant, so every route audit written
earlier was performed against a strictly larger class — those audits are not void, but they
are not evidence about the new class either. Re-run the ones that turned on a missing
regularity/normality precondition; that precondition is now free.

