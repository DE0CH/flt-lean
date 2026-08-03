## A HOIST × A LEAF-MERGE STRANDS THE MERGED LEAF *BELOW* THE LEAVES IT CLOSED

(2026-07-31, `flt-lean-345`.) Two branches, each individually correct, both merged cleanly,
and the arithmetic came out backwards. `flt-lean-203` MERGED two per-prime leaves in
`MazurTorsion.lean` into one uniform leaf and proved both over it — 2 open leaves become 1.
`flt-lean-164`, the same day, HOISTED that whole region into a new upstream module
(`FreyCurve/IsogenySignature.lean`) which `MazurTorsion.lean` imports. The merge kept the
hoisted copies of the two per-prime statements — **in their original, still-sorried form** —
and kept the merged leaf where `203` wrote it, in the DOWNSTREAM file. Result on `merger`:

* the two per-prime leaves were open again, upstream, where the thing that closes them is
  **not expressible** (import order forbids it);
* the merged leaf was open downstream with **ZERO consumers** — nothing in the tree
  referenced it, so it was proving nothing for anybody;
* the frontier read **3 open leaves where the day's work had made it 1**, and every scan
  agreed, because all three are ordinary well-formed leaves in ordinary well-formed files.

This is the delete×refactor orphan hazard one level up: there the casualty is a declaration,
here it is a *proof obligation's position in the import order*, which no name-based,
statement-based or count-based check can see. Note the count went 1 → 3 **upward**, so even
"did the frontier get worse" does not flag it — a rising count reads as disclosure.

**The check is cheap and it is the one nobody runs: after merging a branch that MOVED code
between modules, grep each leaf the branch CLOSED for its consumers.** A leaf with zero
consumers is either free-floating or stranded, and both are defects:

    git grep -n '<leafName>' -- '*.lean' | grep -v '<the file that declares it>'

**The repair generalises: move the OBLIGATION up, not the consumers down.** The uniform leaf
plus the two small bridges it needs (`FullTranslationDatum`, ~77 lines, and the
full → translation collapse) went above the per-prime chain; both per-prime statements then
became three-line corollaries, and the tame case `5 ≤ q` closed outright on the way past.
Cost: one block move, no mathematics. And while re-deriving the cut, price the case split
again — `5 ≤ q` had been PROVEN at the `PotentiallyGoodModel` level for days, and the leaf
was still stated uniformly over all `q`, so narrowing it to `q ∈ {2, 3}` (plus the two free
reductions its own docstring already recorded: integral coefficients, `0 < v_q(Δ)`) cost one
theorem and removed three whole hypothesis-classes from what the next prover owes.

