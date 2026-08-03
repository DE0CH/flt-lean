## A DIMENSION-COUNT CUT CANNOT USE A RELAXED OBJECT — THE TWO HALVES SQUEEZE FROM OPPOSITE SIDES

(2026-07-31, `flt-lean-120`, on `exists_hilbertAuxCotangentSpanningFamily` in
`HardlyRamified/HilbertModularity.lean`.) The commonest cut this development makes on an
arithmetic leaf is *"define the object `X`, then split into (a) `thing = dim X` and (b)
`dim X = n`"*. It is the right cut when `X` is definable. **It is a FALSE-LEAF FACTORY when
`X` is only definable up to a choice, because (a) and (b) are monotone in `X` in OPPOSITE
directions and the safe-direction trick that works everywhere else does not exist here.**

Concretely: the leaf wanted `dim_k(cotangent of R_Q) ≤ q` cut through the Selmer group
`H¹_Q(F, ad⁰ρbar)`, whose local condition at the hardly ramified places is the FINITE-FLAT
condition in cohomological form — absent from the pin and from `Fermat/`. Two cheap
substitutes are available and BOTH produce a false leaf:

* **relax** at those places (no local condition — the literal untwisted transcription of the
  file's own `hilbertH1TwistUnramified`): `X` grows, so (a) survives and **(b) is false**, by
  exactly the local terms of the Euler-characteristic formula (`+[F_w : ℚ_ℓ]` at each `w ∣ ℓ`);
* **tighten** (full local triviality): `X` shrinks, (b) survives and **(a) is false**.

**The tell, and it generalises past Selmer groups: check the MONOTONICITY of each half in the
object before choosing its definition.** If the two halves are monotone the same way, a cheap
over- or under-approximation is safe and the cut is real; if they are opposed, the object must
be exactly right and the cut costs whatever defining it costs. The same file shows the contrast
one section away: on the DUAL side the clause is a VANISHING (`… = 0`), which is monotone in
one direction only, and the file's own section note correctly argues that relaxing there is
STRONGER hence safe. A vanishing tolerates slack; a dimension count does not.

**Two corollaries that decided what to do.**

* **A definition that cannot appear in a TRUE statement is not merely useless — it is
  FREE-FLOATING CODE, which this project forbids.** The dispatch that produced this had asked
  for ~80 lines of untwisted `ad⁰` vocabulary (the twisted definitions with the `det`-twist
  deleted; the underlying `HilbertAdZero.rep` was already in the file). Writing it would have
  compiled, looked like progress, and had no consumer it could ever legally acquire. **Before
  building vocabulary for a future leaf, write the leaf's STATEMENT first and check it is
  true.**
* **A "this cut was considered and REJECTED as unsafe" verdict is exactly as transferable
  between twins as a falsity audit, and just as reliably not transferred.**
  `Deformation.lean`'s section note above `adZeroCycloChar` had recorded this refutation at the
  `ℚ` level — naming `L_HR`, naming FLATNESS as its condition at `ℓ`, and adding that
  existentially quantifying the local-condition family does not rescue the split because *"an
  existential does not split into two leaves, which is the whole purpose of a cut"*. Every word
  of it applied at the `F` level and nobody had looked. **When a cut looks obvious and the file
  is a `ℚ`/`F` twin pair, grep the OTHER file for the same cut before taking it** — this file's
  existing rule about faithfulness repairs (immediately below) covers repairs and not
  rejections, and the rejection is the cheaper thing to find.

What was delivered instead is the cut that IS affordable and is the same one the `ℚ` level
took: peel the pure commutative algebra off the arithmetic. `hilbertRelCotangentFinrank` (the
relative cotangent space `𝔪/(𝔪²+J)` for an arbitrary `J`, the `F`-level twin of
`CotangentModL` with the hard-coded `J = (ℓ)` generalised) plus BOTH Nakayama directions makes
`∃ t : Fin q → R, 𝔪 = span(range t) ⊔ (𝔪² ⊔ J)` and `finrank ≤ q` provably EQUIVALENT — so the
restatement is not a strengthening and the leaf's existing falsity audits transfer with no
re-derivation, which is worth saying explicitly in the docstring. One leaf becomes one leaf;
what changed is that the arithmetic owner now sees an inequality between natural numbers with
no ideal in it. Judge it by what is LEFT in the leaf, not by the count.

