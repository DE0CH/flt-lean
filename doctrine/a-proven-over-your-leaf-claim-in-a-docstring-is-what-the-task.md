## A "PROVEN OVER <your leaf>" CLAIM IN A DOCSTRING IS WHAT THE TASK PROMPT WILL SAY — GREP THE PROOF, AND GREP THE CONSUMERS
(2026-07-31, `flt-lean-141`, on `ModTriv.eq_coord_smul_genAt` in
`Modularity/AmpleSheaf.lean`.)
The task prompt opened: *"Everything else about that theorem is now written and green:
`exists_trivialization_of_modTensor_trivial` is PROVEN over this leaf alone … Closing
this leaf closes `exists_trivialization_of_modTensorPow`,
`isInvertibleSheaf_of_isAmpleSheaf` and the numerical-semigroup bridge."* Every clause
was false, and none of it was invented by the dispatcher — it is a **verbatim
paraphrase of that theorem's own docstring**, which says *"(PROVEN 2026-07-31 over
`exists_modPair_eq_one` and `ModTriv.eq_coord_smul_genAt`)"*. The theorem's actual
`by` block cites neither. It was proven the PREVIOUS day, by an unrelated route
(`isIso_of_isIso_modTensorMap` over `exists_modUnitHom_isIso_modTensorMap`), and a
later agent building a second route wrote its own intent into the consumer's docstring
without re-reading the proof.
So the leaf was **open, live in the warning set, unowned, and DEAD** — the seventh
invisibility class — and the whole cluster it sits in (`modPair`, `ModTriv`,
`exists_modPair_eq_one`, `trivOfPair`) is a complete, consumerless SECOND ROUTE.
`trivOfPair` and `exists_modPair_eq_one` each occur **exactly once** in `Fermat/`, at
their own declarations.
Two checks, both cheap, and the first is the one nobody runs:
* **Read the PROOF of the theorem the prompt says your leaf unblocks.** Not its
  docstring, not its headline — the `by` block. If your leaf's name does not occur in
  it, the dependency claim is prose. This is the same rule as *"THAT THEOREM HANDS BACK
  X is a claim about its CONCLUSION"*, one level down: here it was a claim about its
  *proof*, and proofs are even easier to check.
* **Then grep the CONSUMERS of your leaf's own downstream chain**, transitively, until
  you reach something in the root cone. Openness and reachability are different
  properties and every frontier instrument reports only the first.
**AND A DEAD LEAF CAN OFTEN BE CLOSED BY DERIVING IT FROM THE THEOREM IT WAS MEANT TO
PROVE.** Once the real proof exists, the leaf is usually a *consequence* of it rather
than an input. Here local freeness (`exists_trivialization_of_modTensor_trivial`) gives
one generator `g` near each point, `ModDual.eq_smul_gen` writes `x = r·g` and
`s = c·g`, and the symmetry `x = ⟨x,t⟩·s` is the rearrangement `(r·d)·c = r·(c·d) = r`
where `c·d = 1` is the unimodularity — thirty lines, plus one
`Presheaf.IsSheaf.section_ext` on `L.isSheaf` to glue the local statement. No
circularity: Lean's declaration order enforces that for you, and here it forced the
tail of the `ModTriv` namespace to be relocated below the theorem it now cites.
**Report the accounting honestly, because it is unflattering.** This is `−1` on the
direct-sorry count and `0` on the mathematics: nothing became provable that was not
provable before, and the transitive cone did not move, since the theorem cited was
already in the root cone (per *"A DECLARATION-ORDER BLOCKAGE IS DISCHARGED BY AN OPEN
LEAF ABOVE"*). Say so in the commit and in the docstring, or the next reader will
believe a theory gap closed.
**The residue is the useful output, and it is a different name.** The live leaf of that
file is `exists_restrict_modTensor_tensorSection` — the pinned comparison
`(L ⊗ N)|_W ≅ L|_W ⊗ N|_W` — which `exists_modUnitHom_isIso_modTensorMap` consumes and
which everything downstream of `isInvertibleSheaf_of_isAmpleSheaf` actually waits on.
The dead second route retains exactly one possible value: proving its symmetry
*independently* (the idempotent route its own audit describes) would make that leaf
consumerless. Write that into the docstring, since it is the only thing that would ever
make the block pay for itself.
