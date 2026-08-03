## CUTTING A LEAF DROPS THE ENCLOSING PROOF'S CONTEXT — and a vacuous hypothesis is the usual casualty

(2026-07-31, `flt-lean-313`, two leaves in one file, both FALSE AS STATED.)

`chordSum_xWitness` and `chordSum_yMultiplier` were cut out of
`isDiffCharCert_add_of_ne` in `DifferentialCharacter.lean`. Both carried the witness
certificates of the two summands,

    hrat₁ : ∀ P, φ P ≠ 0 → x(φP)·B₁(x P) = A₁(x P) ∧ y(φP)·E₁(x P) = C₁(x P)·y P + D₁(x P)

and neither carried `φ ≠ 0`. **For `φ = 0` that hypothesis is VACUOUS** — its premise
never fires — so `A₁, …, E₁` is an ARBITRARY tuple and both identities are refutable in
one line (`W = W'`, `φ = 0`, `ψ = id`, witnesses `X,1,1,0,1`, and `A₁ = 0, B₁ = E₁ = 1`,
which even satisfies the nondegeneracy hypothesis `hG : A₂B₁ − A₁B₂ ≠ 0`).

The enclosing proof had `φ ≠ 0` and `ψ ≠ 0` in scope from `hφP : φ P ≠ 0`, so nobody
writing the cut noticed they were being used. That is the general shape:

**A cut statement inherits the WRITTEN hypotheses and loses the AMBIENT ones. Before
publishing a leaf, instantiate every hypothesis of the form `∀ …, <premise> → …` at the
degenerate case where the premise is unsatisfiable, and check the conclusion still holds.**
If it does not, the missing hypothesis is almost always already in the caller's hand — here
`hφ0`/`hψ0` cost the consumer nothing and no statement above them changed.

This file already recorded the same trap one level up ("the degenerate-witness trap" in
`DifferentialCharacter.lean`'s own module docstring, for `IsDiffChar 0 c`). It recurred
because the docstring warned about the DEFINITION, and the new leaves were about the
WITNESSES. A trap documented at one level does not vaccinate the level below it.

### `ring` treats `Polynomial.C 2` as an ATOM — `simp only [map_ofNat]` first

Same day, cost one build cycle, and it will bite anyone moving one of this project's many
`C`-headed polynomial lemmas from point level to polynomial level. `diffChar_yWitness_onePart`
is stated with `C 2 * D * B + …`; every existing consumer uses it after `eval`, where
`eval_C` has already turned `C 2` into the numeral `2`. The FIRST polynomial-level
`linear_combination` over it failed with a residual of exactly the shape

    -(… * C 2 * D * 2) + (… * D * 4) - (B ^ 3 * C 2 ^ 2 * D ^ 2) + (B ^ 3 * D ^ 2 * 4) = 0

i.e. `(4 − 2·C 2)(…) + (4 − (C 2)²)(…)`, which is zero only once you know `C 2 = 2`.
`ring` does not: `Polynomial.C 2` is an opaque application, not a numeral.

    simp only [map_ofNat] at hone      -- turns `C 2` into `2`; then `linear_combination` closes it

Read that residual shape as a diagnosis, not as "my coefficients are wrong": a failure whose
leftover is a *numeral mismatch on a single atom* is this, and re-deriving the coefficients
(which is what one does by reflex) will never fix it.

