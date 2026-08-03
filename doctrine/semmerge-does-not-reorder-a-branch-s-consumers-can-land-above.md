## semmerge DOES NOT REORDER: a branch's CONSUMERS can land above merger's PRODUCER

(Same release, `MoretBailly.lean`.)  The README says an added helper can land BELOW
its consumer.  The mirror happens too and is commoner when the branch RESTRUCTURED
the file: `flt-lean-294` had `stepanovTotalFilt` at line 14885 and its new
`stepanov_totalFilt_*` block after it; merger had `stepanovTotalFilt` at 18423.
semmerge placed the branch's new block next to its merger-side neighbours, i.e. at
~15500 — **2900 lines above the definition it consumes**.

The symptom is `Function expected at` on `(stepanovTotalFilt R).mem`, which reads as
an arity bug in a definition that is perfectly correct.  `grep` finds the name, so
none of the phantom-declaration checks fire.

**Diagnose by comparing the DECLARATION LINE with the first USE line**, and repair by
computing the MINIMAL producer block: list the declarations below the first use, and
keep only those actually named above it.  Here that took a 590-line candidate down to
171 (`StepanovFilt` through `stepanovTotalFilt_mem_monomial`); everything past
`stepanovTotalFilt_mem_monomial` was needed only by later consumers and could stay.
Then hoist that block, with the standard receipt — sorted line multiset identical
before and after, and a token scan showing the block uses none of the declarations it
jumps over.

