## A PROMPT THAT CITES MACHINERY YOU CANNOT FIND IS A PHANTOM — check `merger` BEFORE building it
(2026-07-31, `flt-lean-327`.) The release-window section above says the fix for a suspected
phantom is `git show merger:<file> | grep <name>`. What it does not give is a CHEAP LOCAL
TRIGGER telling you when that is worth doing, and without one the check gets skipped exactly
when it is needed. Here is one, and it costs a single grep.
This task's prompt said, in capitals, that the hard analytic machinery its target needs — four
named `orbitProd` lemmas — was "ALREADY PROVEN OUTRIGHT in the same section", and instructed
`grep for orbitProd in MazurTorsion.lean BEFORE planning anything`. The grep returned **nothing**,
on `main`, at the dispatch HEAD. So did `Gamma0Cusp`, `cuspSetoid`, and the whole
`ModularCurve/Gamma0Index.lean` module the prompt named as a route.
The naive reading is "the prompt's names are stale, so build the machinery". That reading is
expensive and wrong. The correct reading:
> **A prompt cites machinery because its author READ that machinery. If it is not on your branch,
> the author was reading a branch you are not on — and the TARGET is very likely proven there too,
> because whoever proved the helpers is the obvious person to have proved the target.**
Which is what had happened: `numCusps_le_order_qExpansion_norm`, the whole `orbitProd`/`CuspOrbits`
block, its consumer `cuspForm_coe_eq_zero_of_sturm`, and the `relIndex_gamma0GL` half were ALL
proven and sorry-free on `merger`, hoisted into `ModularCurve/X0.lean`. Not one of them was on
`main`. Building any of it would have been a duplicate, and a delete-vs-modify conflict against a
hoist that moved the declarations between files.
So: **an empty grep for machinery your prompt calls proven is not a stale name — it is evidence
you are looking at the wrong branch.** Check `merger` for your TARGET before you plan, not after
you are stuck. Note the ordinary ownership tooling cannot help here: `~/.flt-inflight.jsonl` is
pruned when a worktree goes `batched`, so the agent that did the work leaves no record.
**And the mirror-image trap: a prompt is written from ONE branch, so it inherits that branch's
frontier wholesale — including facts it presents as settled.** This prompt correctly reported
`relIndex_gamma0GL` as "PROVEN on 2026-07-31, do not re-prove it". True on `merger`; a `sorry` on
`main`. Both halves of the prompt — what to build and what not to — were about a tree the agent
was not given.
