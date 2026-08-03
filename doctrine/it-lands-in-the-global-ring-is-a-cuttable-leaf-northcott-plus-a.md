## "It lands in the GLOBAL ring" is a cuttable leaf — Northcott plus a pigeonhole is ~40 lines

(2026-07-31, `Modularity/TateModule.lean`.) A recurring shape here is a leaf whose stated content is
*a coherent family of level data defines an element of a COMPLETION, and the content is that it lies
in the GLOBAL ring `𝒪_D`*. That sentence reads as atomic. It is not; it factors mechanically:

    coherent (s_b − s_a ∈ Iᵃ for a ≤ b)  +  UNIFORMLY BOUNDED representatives  ⇒  a global t ∈ 𝒪_D

and the second half is **pure algebra with no geometry in it**:
`NumberField.Embeddings.finite_of_norm_le` (Northcott — the algebraic integers of `D` whose
archimedean absolute values are all `≤ C` form a FINITE set), pulled back along the injective
`algebraMap (𝓞 D) D`; pigeonhole the witness sequence `u : ℕ → 𝓞 D` onto a value `t` attained at
INFINITELY many levels; then for each `n` pick `m > n` with `u m = t` and split
`t − s_n = (u_m − s_m) + (s_m − s_n) ∈ Iᵐ + Iⁿ = Iⁿ`. About 40 lines.

It does not reduce the leaf count — one `sorry` replaces one `sorry` — and it does not touch the
missing theory. What it buys is that the residual leaf is a **BOUND**, which is the form the
literature states and names (here `‖φ t‖ ≤ 2√N`, the Riemann hypothesis for abelian varieties),
instead of a mixed completion-versus-global assertion that reads as mysterious.

Two traps, both about quantifier order, and both fatal to the cut:

* State the bound hypothesis as `∀ n, ∃ uₙ`, **never** `∃ u, ∀ n`. The strong form is what is
  classically true, and modulo `⋂ₙ Iⁿ = 0` it is EQUIVALENT to the conclusion — stating it makes the
  new lemma vacuous and the "proof" a one-liner that has moved nothing.
* Leave the constant EXISTENTIAL (`∃ C, ∀ n, ∃ u, …`) unless a consumer reads its value. Baking a
  numeral in makes the leaf harder than the consumer needs and risks a false leaf if the constant is
  off by a factor.
* `hcoh` must stay a hypothesis of the consumer. It is the only thing that propagates the
  pigeonholed value DOWN from level `m` to level `n`, and without it the statement is FALSE: take
  `s_n = 0` for even `n` and `1` for odd `n`, each its own bounded witness; a global `t` would lie in
  `⋂ₙ Iⁿ = 0` and satisfy `t − 1 ∈ ⋂ₙ Iⁿ = 0`.

