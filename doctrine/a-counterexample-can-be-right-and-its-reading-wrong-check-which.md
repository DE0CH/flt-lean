## A COUNTEREXAMPLE CAN BE RIGHT AND ITS READING WRONG — check which hypothesis it actually kills

(2026-07-31, `RelativePicard.lean`.) `surj_of_isRelPicOverAffines`'s audit named TWO load-bearing
hypotheses, a section `_o` and `f_*𝒪 = 𝒪` (`_hpush`), and backed both with one counterexample:
"for `X = S ⊔ S` — no section, and `f_*𝒪 = 𝒪 × 𝒪` — the sequence
`0 → Pic T → Pic X_T → P(T) → Br T` breaks". The example is correct and refutes the leaf. But
**`S ⊔ S ⟶ S` has a section** — either inclusion — so it says nothing whatever about `_o`, and
writing the proof showed `_o` is not needed at all: the local twists `Nᵢ` are canonically
`(f_*M)|_{Uᵢ}`, restrictions of ONE sheaf, so there is no cocycle to obstruct and no Brauer class
for a section to kill. `_hpush` alone does the work.

The failure mode is specific and worth naming, because it is invisible to every check this file
prescribes. An audit exhibits ONE object violating SEVERAL hypotheses at once and then reads it as
evidence for each of them separately. Nothing catches that: the leaf is genuinely false, the
witness is genuinely a witness, and a reviewer who checks "does this refute the statement?" gets
yes. **A counterexample licenses exactly one claim — that the statement is false as stated. To
attribute the failure to a particular hypothesis you need a witness satisfying all the OTHERS**,
and the discipline is to say out loud, per hypothesis, which one that is.

Two practical corollaries:

* **the cheapest place to find this is the proof.** Prove the parent over the leaf, then read off
  which hypotheses the route actually spent. Here the parent turned out to spend NONE of the five
  itself — all were forwarded — which is what made the over-attribution visible;
* **a hypothesis you cannot justify is still worth KEEPING in a new leaf's signature** when the
  caller already has it: it costs the prover nothing and cannot make the leaf false. Say in the
  docstring that it is retained defensively rather than needed. Deleting it is the move that can
  go wrong, and it buys almost nothing.

