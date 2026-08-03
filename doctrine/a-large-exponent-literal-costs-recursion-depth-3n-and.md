## A LARGE EXPONENT LITERAL COSTS RECURSION DEPTH `3n`, AND `maxRecDepth` LARGE MAKES IT WORSE
(2026-07-31, measured over about twenty probe builds while closing the `p = 11` and `p = 17`
rows of Mazur's non-CM table.)
`X ^ n` for a `ℕ` LITERAL `n` is a trap whenever the elaborator has to unify a term containing
it against a pattern. Unification falls through to `whnf`, `whnf` unfolds `npowRec`, and
`npowRec` recurses **once per unit of `n`** — measured depth `≈ 3n`. A chain step at
`n = 3466` elaborates; the same step at `n = 6932` needs `maxRecDepth 20000`; the certificates
here run to `n = 23 ^ 11 = 952809757913927`.
**Three things about this cost a whole session between them.**
1. **The failure has NO LOCATION.** Past the stack it is `Stack overflow detected. Aborting.`
   and nothing else — no line, no declaration, no tactic. Every natural next step is wrong:
   `lake env lean -s 65536`, `-s 262144` and `-s 524288` all still die (the last one is also
   silently misparsed and reports `no such file or directory`). To get a *located* error, drop
   `maxRecDepth` to ~20000 and read the errors; that is diagnosis, not a fix attempt.
2. **`set_option maxRecDepth` LARGE IS THE WRONG DIRECTION.** At `4000000` these files crash;
   at `20000` they compile. A high limit lets a doomed reduction run until the C stack dies
   instead of failing fast so the elaborator can take another route. The predecessor's file
   carried `maxRecDepth 10000000`, which is exactly how a locatable error became a crash.
3. **The symptom mimics whatever you were last worried about.** Because depth scales with the
   exponent and the exponents grow along a chain, the failures appear at a *boundary partway
   down the chain* — which reads convincingly as "the polynomial identities got too big". Two
   full rewrites were spent shrinking the identities (degree 230 → degree 22, `expand` →
   square-and-multiply). Both were sound engineering and **neither fixed anything**, because
   the degree was never the problem.
**The fix is to keep the exponent out of unification, behind a definition:**
```lean
def XPow {q : ℕ} (f : (ZMod q)[X]) (n : ℕ) (a : (ZMod q)[X]) : Prop := f ∣ X ^ n - a
```
State every chain step as `XPow f n a` rather than `f ∣ X ^ n - a`. Now `n` is an *argument*,
unification assigns `?n := 952809757913927` and never looks inside `X ^ ?n`. Same statements,
same proofs, seconds instead of a crash. Cross into the raw `∣` exactly once, at the end,
where the target is fixed and there is no pattern to match.
Corollary, learned the same way: **do not `rw` a `ℕ` equation into exponent position.**
`rw [hexp]` inside `X ^ (Nat.card (ZMod ℓ)) ^ m` puts the literal straight back and the
blow-up returns. Move the arithmetic into a `ℕ`-only lemma (`xpow_card` here) where no
polynomial appears.
Everything lives in `Fermat/FLT/EllipticCurve/MazurNonCMFrobenius.lean`; the four generated
row modules under `MazurNonCMFrobenius/` are produced by `gen_modules.py` at the repo root
(`gen_frobenius.py`, `gen_binpow.py`, `gen_factored.py`, `gen_coprime.py`, `gen_row.py`), which
also re-derives every certificate and cross-checks it against PARI/GP before emitting Lean.
**And a mathematical corollary worth more than the tooling: `H ∣ X ^ (q ^ m) - X` does NOT
need `H`'s factors to be irreducible.** Factor `H = ∏ fᵢ`, prove each `fᵢ ∣ X ^ (q ^ m) - X`
separately, and reassemble with `IsCoprime.mul_dvd` off explicit Bézout certificates. That
needs pairwise COPRIMALITY only — which is a one-line `⟨u, v, by ring_nf⟩` — where proving
irreducibility of a degree-11 factor over `F₂₃` is circular (the standard test *is* this
divisibility). It is also `k²` cheaper, since every `ring_nf` call scales with `(deg f)²`.
