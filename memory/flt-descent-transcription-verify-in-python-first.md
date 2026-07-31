---
name: flt-descent-transcription-verify-in-python-first
description: A MazurLevelN descent transcribes mechanically once you derive the two binary forms; verify every certificate numerically in Python before writing Lean, and the whole chain compiles first try
metadata:
  type: feedback
---

`MordellWeil.lean`'s `MazurLevel11` chain is a **template, not just a
precedent**: the ~600 lines from `halving_norm_relation` down to
`integral_leaf_aux` are pure ℤ and transcribe to any other curve once two things
are computed. Doing this for level `19` (`MordellWeil19.lean`, 2026-07-31)
compiled **green on the first build**, in one pass, with no failed tactic.

**What has to be derived (everything else is copy-with-new-constants):**

1. **The two binary forms**, from the duplication formula on the monic model
   `W² = U³ + a₂U² + a₄U + a₆`:

       F(X, Y) = X⁴ − 2a₄X²Y² − 8a₆XY³ + (a₄² − 4a₂a₆)Y⁴,
       G(X, Y) = X³ + a₂X²Y + a₄XY² + a₆Y³,

   and `U(2Q) = F/(4YG)`. At level `19` (`a₂ = 4`, `a₄ = a₆ = 16`) the `Y⁴`
   coefficient VANISHES — `U = 0` is the `3`-torsion point, duplicating to
   itself — which is why the exceptional set has one element where level `11`
   has two, and why `trivial_ascends` there needs `hcov` and here does not.
2. **`m` as a linear form in the witness `(a, b, c)`.** Match
   `2c·e² = c³·P(m/c)` for the minimal polynomial `P`: writing `m = b + λc` and
   equating coefficients pins `λ` from the `b²c` coefficient alone, and the other
   two then check. Level `11`: `m = b + 2c`; level `19`: `m = b − 2c`.
3. **The Bezout cofactors** for `forms_common_dvd`: `gcdext(f, g)` in PARI/GP,
   homogenised and multiplied by `4Y`; then the SAME for the reversed
   polynomials — and there add the syzygy `(u, w) ↦ (u + λG, w − λF)` with
   `λ ≡ w₀/X⁴ (mod Y)` to make the `G`-cofactor divisible by `4Y`. Without that
   step the second identity comes out as `c·X⁶Y`, not `c·X⁷`, and does not fit
   the lemma.
4. **The archimedean split**, from where `4f(t) ≥ t⁴` fails. Factor
   `4F − X⁴` — at level `19` it is `X(X − 8Y)(3X² + 24XY + 64Y²)` with the
   quadratic definite — and cover the gap with `16Y·G − X⁴`.
5. **The sieve**: greedy over prime powers `< 256`, masks = square-sets.

**The lever: check all of it in Python before touching Lean.** Every
`linear_combination` certificate is a polynomial identity, so a 30-line
random-integer evaluator refutes a wrong cofactor in milliseconds where Lean
costs a 50-second build. The same script verifies the Bezout identities, the
archimedean factorisations, the exhaustive-search claim, and that the sieve
really covers the box. See [[flt-cleaner-statement-harder-proof]] for the
complementary point about *where* to cut; this one is about how to land the cut
without burning build cycles.

Reusable across levels without copying: `MazurLevel11.reduced_fraction`,
`qrMaskBad`, `qrMaskBad_sq`, `not_isSquare_*`, `sq_ne_mul_sq_of_not_isSquare`,
and `RationalPointDescent.exists_int_model`.

What does NOT transcribe is the `2`-descent proper (`exists_halving_witness`):
that needs the cubic ring `ℤ[θ]` of the curve's own `2`-division field, and it is
a different field at every level.
