## A LEAF THAT INVITES A CUT AND DECLINES IT "BECAUSE NOTHING WOULD CONSUME IT" — the consumer is the leaf

(2026-07-31, `hasCubeIso_of_symm_of_normalized`.) Its docstring said, correctly, "a prover who
wants the general Corollary 2 as a separate leaf should cut it … this statement is three formal
steps below it", and then declined to, "only because this project forbids free-floating
declarations and nothing would yet consume it." That reason is wrong by one step: **the leaf
itself is the consumer.** Cut the general statement, prove the leaf over it, and nothing floats.
It was three formal steps, exactly as advertised — and two survey agents had already read that
paragraph and moved on, because "this is a theory build" is true of the general form too and so
reads as a reason to do nothing.

The trade is worth taking even though the leaf COUNT does not move (one out, one in):

- the open statement shed `[Field K]` and two of its three hypotheses, which were being
  discharged in the derivation all along;
- it is now the statement the literature proves, so a future prover can follow a book instead
  of reverse-engineering a project-specific corollary;
- it is stated for arbitrary points over an arbitrary base, so its OTHER classical consequences
  are reachable from the same leaf rather than needing their own cuts later.

**And when you hoist a field-based statement to an arbitrary base, KEEP THE CONSTANT TERM the
reference drops.** Mumford's cube identity omits `0^* L` because over a field `Pic(Spec k) = 0`
makes it free. Transcribing it verbatim over a general base silently asserts `e^* L ≅ 𝒪` — put
`x = y = z = 0` and every one of the seven factors collapses to `0^* L`, so the identity reads
`(0^*L)^{⊗4} ≅ (0^*L)^{⊗3}`. Restoring the term makes that case a tautology, which is what a
correct third-difference identity must do. **The general test: specialise your statement to the
degenerate point where a reference's ambient hypothesis was doing the work, and check you get a
tautology and not a hidden assertion.**

