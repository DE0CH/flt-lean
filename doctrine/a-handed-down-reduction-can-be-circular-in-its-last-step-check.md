## A HANDED-DOWN REDUCTION CAN BE CIRCULAR IN ITS LAST STEP — CHECK THE DIRECTION, THEN THE DECLARATION ORDER
(2026-07-31, `exists_unramifiedAbelian_card_classGroup_le_finrank`.) The task prompt carried a
reduction "worked out on paper, NOT verified in Lean" by an earlier agent. Its first half was
correct and its last step was not: it cited `finrank_le_index_relNormClassSubgroup` — which reads
`finrank ≤ index` — to conclude `finrank ≥ index`. Every intermediate step typechecked as prose,
and the error is invisible until you open the cited theorem and read its statement.
**Then it got worse, and this is the part worth keeping.** The inequality the reduction actually
needed *did* exist in the same file, under the obvious name `index_relNormClassSubgroup_le_finrank`
— PROVEN. But its proof ran through the very leaf being reduced, so citing it is a cycle, and
Lean's declaration order rejects it outright. So the reduction was not repairable by rearrangement:
what looked like a bookkeeping slip was a missing INPUT to the theory.
Two checks, both cheap, both skipped that day:
1. **Read the statement of every inequality a reduction cites, not its name.** `X_le_Y` and
   `Y_le_X` sit next to each other in files like this one, and the names are near-anagrams.
2. **Then check where it is DECLARED relative to your target.** A theorem proven *below* your leaf
   is not available to it, however true it is. `git grep -n` the two names and compare line numbers
   before believing a reduction closes.
The general shape: **a cluster can be rich in inequalities that all point the same way.** Here
everything upstream bounded `[L : K]` from ABOVE (the Artin map goes `Cl(𝓞 K) ↠ Gal(L/K)`), and
nothing bounded it from below — so no rearrangement of the existing material could produce a degree
lower bound, and the honest repair was a second leaf. Before adopting any reduction, ask which
DIRECTION its conclusion needs and whether anything upstream produces that direction at all.
**Corollary about what composes.** The same task turned up the reason the leaves must be phrased in
norm groups: `L ≤ M` gives `relNormClassSubgroup K M ≤ relNormClassSubgroup K L`
(`Ideal.relNorm_relNorm`), so norm groups shrink under composita and can be intersected; but a
compositum only gives `Gal(M/K) ↪ Gal(L₁/K) × Gal(L₂/K)`, an UPPER bound on the degree. So a leaf
carrying a degree — or an injection `Cl(𝓞 K) ↪ Gal(L/K)` — does not combine under composita at all,
and restating the leaf cannot dodge the missing input. **When a reduction combines objects, check
that the QUANTITY it tracks is monotone the right way under that combination**; that is usually
what decides how a statement must be phrased, and it is decided before any proof is attempted.
**And a small Lean lever found on the way**, useful whenever a single automorphism's fixed field is
wanted: take `IntermediateField.fixedField (Subgroup.closure {ρ})` and discharge membership with
`Subgroup.closure_le` into `MulAction.stabilizer _ y`. The stabiliser is already a subgroup, so the
single fact `ρ • y = y` covers every `ρ ^ n` in the closure and no `zpow` induction is needed;
`sup_le` then reduces "fixes `L₁ ⊔ L₂`" to "fixes `L₁`" and "fixes `L₂`".
