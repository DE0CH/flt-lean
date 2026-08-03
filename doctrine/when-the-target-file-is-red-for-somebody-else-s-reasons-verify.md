## WHEN THE TARGET FILE IS RED FOR SOMEBODY ELSE'S REASONS: VERIFY AGAINST THE RELEASE OLEAN WITH THE MERGER-ONLY DEPENDENCIES **STUBBED VERBATIM**
(2026-07-31, `flt-lean-381`, `X0.lean`.) The scratch-module doctrine assumes your
target module BUILDS, so that a scratch can `public import` its olean. Under the
release window that assumption fails routinely in the worst way: `merger`'s copy of a
giant module can be RED — here 100+ errors, `maxErrors` reached at line 73478 with more
beyond, every one of them a pre-existing merge wound and none of them mine — and then
there is no olean, no scratch, and a 40-minute build that only re-prints somebody else's
errors. Repairing a hundred wounds is the merge worker's job, not yours (it alone knows
which side of each merge won), so waiting for green is waiting forever.
**The way through: verify against `~/.flt-release-lake`'s olean — which is `main`, and
green — and STUB the handful of declarations that exist only on `merger`, copying their
statements VERBATIM out of `merger`'s source.**
    S=$(cat ~/.flt-release-lake/sha)
    git diff --stat $S main -- Fermat/            # empty ⇒ that olean IS main's
    cp -rs ~/.flt-release-lake/build/lib /tmp/relean-N/
    LEAN_PATH="/tmp/relean-N/lib/lean:$LP" LEAN_SRC_PATH="$LSP" lean Scratch.lean
Then, in the scratch, for each name your block uses, decide which side it is on:
    git show $S:<path> | grep -c '<name>'         # 0 ⇒ merger-only ⇒ stub it
and stub the merger-only ones as `theorem stub_<name> <signature copied verbatim> := sorry`.
Here that was **four** names out of ~16, and the run came back with exactly four
`declaration uses 'sorry'` warnings and **no errors** — i.e. every application in the block
typechecks against the real snapshot for twelve of the dependencies and against a
mechanically transcribed signature for the other four. Two rounds, ~2 minutes each,
against a build that cannot be made to finish at all.
**What this does and does not prove.** It proves the mathematics, the instance
resolution, the argument order and the tactic scripts. It does NOT prove the four
transcriptions — so extract them with `sed`/`awk` from the merger source rather than
retyping, and say in the commit that this is how they were checked. And it says nothing
about the target's import surface or notation scope, exactly as the doctrine already
warns.
**Do the stubbed run as a SECOND scratch, not the first.** The first should contain only
the declarations that need no stubs; those are usually the pure-algebra ones, which are
where the tactic failures actually live (four of the five real errors in this task were
there — a `field_simp` that did not close, a mathlib name that does not exist at this pin
(`isUnit_of_mul_eq_one`), an over-eager `rw` chain, and a `Subsingleton` instance that
needed `@Subsingleton.elim _ (myLemma R _) _ _` instead of a `haveI`). Getting those green
first means the stubbed run tests only what it is for.
