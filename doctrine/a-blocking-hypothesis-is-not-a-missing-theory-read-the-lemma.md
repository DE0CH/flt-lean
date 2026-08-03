## A BLOCKING HYPOTHESIS IS NOT A MISSING THEORY — READ THE LEMMA THE COROLLARY CAME FROM

(2026-07-31, `flt-lean-204`, on Serre's type-`A₀` core in `Modularity/Interface.lean`.)

The leaf's docstring named the globalisation half as blocked on **Kronecker–Weber**
(`Γℚ^ab ≅ Ẑˣ`), "ABSENT from mathlib at this pin: grepped 2026-07-28, no `KroneckerWeber` in
`Mathlib/`, in `Fermat/`, or in `~/cs/FLT`". The grep was correct and the verdict was wrong.

What the argument needs is *an everywhere-unramified continuous character of `Γℚ` is trivial*.
The tree has `minkowski_character_trivial`, which says exactly that — **but only for a character
with an OPEN KERNEL**, which a `ℚ̄_p`-valued character of infinite image does not have. That one
hypothesis is the entire reason the node read as blocked on a missing theory.

`minkowski_character_trivial` is a five-line COROLLARY of
`open_normal_subgroup_eq_top_of_inertia_le` in the same file, and **the parent needs no open
kernel** — it needs an open normal subgroup containing every inertia image. For a character into
`ℚ̄_p` that is handed over by ultrametric geometry: each ball `{x : ‖x − 1‖ < ε}`, `ε ≤ 1`, is a
multiplicative subgroup, its preimage is open (continuity), normal (the target is commutative,
so a character is a class function), and contains every inertia image; Minkowski makes it `⊤` for
EVERY `ε`; the balls are a neighbourhood basis of `1`, so `ψ = 1`. Forty lines, no class field
theory, no Kronecker–Weber.

**The general rule: when a lemma's HYPOTHESIS is what blocks you, find the theorem it was derived
from.** Corollaries are specialised to their first consumer, and the specialisation is exactly
what gets thrown away. The tree records "we have X" at the granularity of the corollary, so the
parent's extra strength is invisible to any inventory search. This is the third distinct way this
project has manufactured a phantom "missing theory" — after
[searching for how to PRODUCE an object instead of for the deciding invariant] and [reading a
leaf's own MISSING MACHINERY list as reliable about strength] — and all three are cured by
reading the statement rather than the summary.

**Corollary, same day, same proof, and worth its own line: A CONTINUITY YOU CANNOT PROVE MAY BE
HANDED TO YOU BY A HYPOTHESIS.** The glue needs `χ_cyc : Γℚ → ℚ̄_p` continuous, and nothing on
this pin proves `cyclotomicCharacter` continuous — that alone would have sunk the assembly. But
the leaf already carries `hcyc : ∀ γ, δ₁ γ * δ₂ γ = χ_cyc γ`, and `δ₁`, `δ₂` are continuous by
hypothesis, so `χ_cyc` is continuous by `funext` in two lines. Before costing "`X` is
continuous/measurable/finite" as missing machinery, check whether some hypothesis already equates
`X` to something that has the property. In a statement with many hypotheses this is common and
it is easy to miss, because the hypothesis was written for a different purpose.

