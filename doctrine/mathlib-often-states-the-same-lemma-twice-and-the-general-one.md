## MATHLIB OFTEN STATES THE SAME LEMMA TWICE, AND THE GENERAL ONE IS INVISIBLE TO A GREP FOR THE SPECIAL ONE

(2026-07-31, `flt-lean-261`.) A task prompt priced the Galois transport of
`WeierstrassCurve.End` as "the work is the point-map: mathlib's addition formulas
(`baseChange_addX`, `baseChange_addY`, `baseChange_slope`, `baseChange_nonsingular`) are all
stated for ALGEBRA maps, so the `map_add'` obligation has to be re-derived, or those lemmas
generalised." **Every one of those has a plain RING-HOMOMORPHISM twin fifteen lines above it in
the same file** — `map_nonsingular` in `Affine/Basic.lean`, `map_negY`/`map_addX`/`map_addY`/
`map_slope` in `Affine/Formula.lean` — and the `baseChange_*` versions are one-line corollaries
of them (`rw [← RingHom.coe_coe, ← map_addX, map_baseChange]`). The "hard part" was mathlib's own
`Point.map` proof with `baseChange_*` textually replaced by `map_*`: about fifteen lines,
first try.

The failure mode is structural, not careless. **A grep for the name you know finds only the
consumer.** `baseChange_negY` is what appears at call sites, in docstrings and in every previous
agent's notes, so that is the name an audit searches for; the `map_negY` it is derived from is
never mentioned by anyone because nothing downstream uses it. So the audit correctly reports
"only the algebra-map version is used here" and then wrongly concludes "only the algebra-map
version exists".

**The check costs one command and belongs in every "mathlib only has X at generality G" verdict:
read the SECTION the lemma lives in, top to bottom.** Mathlib's convention is to prove the most
general form first and specialise downward in the same file, so the general version is a screenful
above the one you found — not in another module, not under another name, and invisible to any
search keyed on the specialisation. Concretely:

    sed -n '<start of the "Maps and base changes" section>,$p' <that file>

Related but distinct from the entries above about machinery living DOWNSTREAM or in another
module: here it is in the file you are already reading, which is why nobody looks.

