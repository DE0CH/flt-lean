## A LEAF AND ITS OWN FAITHFULNESS AUDIT CAN BE IN DIFFERENT LANGUAGES — and the bridge is an unwritten obligation
(2026-07-31, `flt-lean-105`, `exists_ratPoly_weberAlpha_pow_four` in
`Mathlib/NumberTheory/BinaryQuadraticForm.lean`.) That leaf asserted a MEMBERSHIP,
`α ∈ ℚ[α⁴]`. Its docstring's audit — three careful `PARI/GP` tables, offered as the evidence
that the leaf is true and as the recipe for refuting it — measured DEGREES, `deg α` against
`deg α⁴`. Those are equivalent only through `IntermediateField.eq_of_le_of_finrank_le` plus
`IsIntegral ℚ α`, about 25 lines that existed nowhere in the tree. **So the audit did not
support the statement it was attached to**, and a successor who refuted the table would not
have refuted the leaf (nor conversely).
Nothing flags this. Both halves are individually correct, the leaf compiles, the audit reads as
thorough, and the gap is invisible unless you ask *in what language is the conclusion, and in
what language is the evidence*. It is the same family as the "i.e." trap already recorded here —
a docstring linking two differently-shaped statements is asserting a lemma with no owner — but
one level up: the two shapes are the LEAF and its AUDIT rather than two clauses of one sentence.
**The check is one question per leaf and it costs a re-read: could the audit's measurement be
plugged into the statement verbatim?** If not, either write the bridge or restate the leaf in
the audit's language. Restating is usually right, because an audit is written in whatever the
CAS or the literature naturally produces, and that is the shape a prover will also produce.
### The corollary that makes it pay: if the SOLE CONSUMER opens by CONVERTING the leaf's conclusion, the leaf is stated in the wrong shape
Same leaf, and this is the mechanical tell. `natDegree_minpoly_weberAlpha_le` spent 20 of its 43
lines turning `∃ q, α = aeval (α⁴) q` into `α ∈ ℚ⟮α⁴⟯`, then `ℚ⟮α⟯ ≤ ℚ⟮α⁴⟯`, then a `finrank`
inequality — and pulled in `isIntegral_weberAlpha` (hence the class-number hypothesis `hcl`)
PURELY to make `ℚ⟮α⁴⟯` finite-dimensional for that conversion. Restating the leaf as the degree
inequality deleted all 20 lines, deleted the integrality import, and left `le_trans`.
So: **read the first few lines of a leaf's consumer before accepting the leaf's shape.** A
consumer that immediately translates is telling you the translation's TARGET is the honest
statement; the leaf's current form is an artefact of whoever cut it. Two riders:
* **count it honestly.** This is `1 → 1`; no mathematics was done and the frontier did not move.
  What changed is that the residual is smaller, matches its evidence, and no longer drags a
  hypothesis through a conversion. Say exactly that, or a `−1 +1` delta reads as a closure.
* **do NOT keep the old form as a proven corollary.** With the consumer taking the new shape
  directly, the old statement has no consumer and is free-floating, which this project forbids.
  Delete it, and put the bridge — which you should compile first, to prove nothing was lost —
  in the docstring with a pointer to the commit, not in the file.
### `lindep` RETURNING A HEIGHT-`1` RELATION MEANS A BASIS VECTOR UNDERFLOWED, NOT THAT THE CLAIM FAILED
Same run, and it nearly produced a false refutation report. Testing `α ∈ ℚ[α⁴]` directly by
`lindep([α, 1, α⁴, …, α^{4(d−1)}])` is far better conditioned than comparing two `algdep`
degrees — `algdep` on `α` is the badly conditioned half — and it proves the claim at a given `p`
the moment the coefficient of `α` comes back nonzero. But at two primes out of 34 the 300-digit
run returned coefficient `0` with height `1` and a tiny residual, which reads exactly like
independence. It is `lindep` reporting that one INPUT is numerically zero: `α ≈ 4 × 10⁻⁴` there,
so `α^{56}` underflows. At 700 digits both gave honest relations.
**A returned height of `1` is a precision verdict, never a mathematical one.** Whenever a
numeric witness search involves high powers of a small quantity, check the height of what comes
back before reading the answer, and record the diagnosis next to the row — an unexplained
degenerate row in a published table is exactly what the next agent will report as a refutation.
