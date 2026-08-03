## AN AUDIT THAT PRICES EACH CONJUNCT BY ITS OWN CLASSICAL PROOF PRICES THE LEAF AT THE MAX — ASK WHETHER ONE ROUTE COVERS BOTH
(2026-08-02, `flt-lean-121`, `isIntegral_of_smoothProperCurve` in `ModularCurve/X0.lean`,
PROVEN in ~5 scratch iterations of 10 s each after three days as a leaf.)
That leaf's docstring did the right thing and did it well: it split `IsIntegral` into its
three conjuncts and gave each its own short classical reason — *Nonempty* from
`GeometricallyConnected`, *Reduced* from "smooth over a regular base is regular, and regular
is reduced", *Irreducible* from "regular stalks are domains, so the components are disjoint,
and proper + flat with connected fibres over a connected base is connected". All three
reasons are correct. **Two of the three run through regularity of the total space over the
DVR, which is the one thing genuinely absent from the pin** — so the leaf was priced at a
mathlib-scale contribution.
**Neither conjunct needs it, and the SAME cheap route covers both: the GENERIC FIBRE.**
`𝒳` is flat over the domain `R`, and `Spec ℚ ⟶ Spec R` is an open immersion, so the generic
fibre is a dense open subscheme which is a smooth geometrically connected curve over a
FIELD — where every one of these properties is already available.
* *Reduced*: flat over a domain gives `A ↪ Frac R ⊗_R A` on each affine open, and the
  target is smooth over `Frac R`. One line.
* *Irreducible*: the generic fibre is INTEGRAL over the field, its image is an open hence
  preirreducible subset, and it is DENSE because a flat map is generalizing
  (`Flat.generalizingMap`) and the generic point of `Spec R` lies in the open. A space with
  a dense preirreducible subset is preirreducible (`IsPreirreducible.closure`).
Nothing over the DVR is shown regular; **and no connectedness of `𝒳` is needed either**,
which the audit's route also wanted.
**So the standing check, before accepting a conjunct-by-conjunct price: ask whether ONE
object makes several conjuncts true at once.** A conjunct-wise audit is by construction a
sum of independent classical proofs, and it will name the union of their inputs — but a
single well-chosen sub-object (a dense open, a generic fibre, a section, a chart) often
discharges several of them with shared machinery. The audit is right about each row and
wrong about the total.
**AND THE OTHER HALF OF WHY IT STOOD, which is the fourth recorded instance of the same
failure: the absence grep was of MATHLIB.** The audit said, correctly and with file and
line numbers, that the pin has no `Smooth ⟹ GeometricallyReduced`. Both
`AlgebraicGeometry.GeometricallyReduced.of_smooth` **and**
`AlgebraicGeometry.isReduced_of_smooth_over_domain` are PROVEN in
`Fermat/FLT/Mathlib/AlgebraicGeometry/Morphisms/SmoothReduced.lean` — which `X0.lean`
`public import`s, and whose domain-base theorem was added **the day before the audit was
written**. `Fermat/FLT/Mathlib/**` is where every agent's general-purpose commutative
algebra and mathlib-facing geometry lands, and a `Fermat/FLT/Mathlib/` module exists
PRECISELY BECAUSE its statement is missing from the pin — so "absent from mathlib" is
evidence that it is there, not evidence that it is missing. Grep `Fermat/` by CONCEPT
before writing any absence verdict, and say in the verdict which trees you searched.
**The cheap iteration loop that made this a one-session task**: `X0.lean` takes ~10 min to
build, but a scratch that `public import`s its CURRENT `.olean` loads in **13 seconds**.
Extract your finished declaration back OUT of the real file by line range into that scratch,
with the target's own `open`s reproduced (here `open CategoryTheory AlgebraicGeometry`, and
notably NOT `Limits`), and `#print axioms` it — that tests the exact characters you are
committing, including name resolution, and it is the one thing a hand-typed parallel copy
cannot do. Do the scratch first and the `lake build` last: `lake build` deletes the olean
the scratch is reading.
