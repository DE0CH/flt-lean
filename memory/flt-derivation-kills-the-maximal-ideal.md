---
name: flt-derivation-kills-the-maximal-ideal
description: A "not derivable from the axioms, needs a ring generator" verdict is route-specific; a derivation kills 𝔪 for free, factors through the residue field, and dies there because the residue field is perfect
metadata:
  type: project
---

`LowerRamificationData.mem_gp_one_of_dvd_smul_unif_sub` (Serre *Corps Locaux* IV §1
Lemma 1) carried a careful 2026-07-30 audit concluding it "is not derivable from the
fields of `LowerRamificationData`". The audit's computation was right and its verdict
was wrong. It observed that `δ_x(σ) := (σ • x − x)/unif mod 𝔪` is a DERIVATION in `x`,
hence "determined by its value on a ring generator" — and the axioms supply no
generator, i.e. no monogenicity `𝒪_L = 𝒪_0[unif]`.

But a derivation with `δ(unif) = 0` kills `𝔪_L = unif·𝒪_L` for free, since
`δ(unif·y) = δ(unif)·ȳ + unif‾·δ(y) = 0`. So it FACTORS through the residue field and
becomes a derivation *of a field*, which kills every `p`-th power. Perfectness replaces
monogenicity, and the residue field here is perfect for nothing: it is algebraic over
the finite `κ(𝒪ᵥ)`.

**Why:** the audit searched for the object its textbook route consumes (a generator) and
correctly reported its absence. It never asked what the obstruction does on its own
domain. A generator is one exit; the second is a property the target already has.

**How to apply:** when a docstring says "needs X and nothing weaker", treat "nothing
weaker" as unaudited. Ask what the offending object does *unconditionally* on the
sub-object it is already known to kill (an ideal, a subgroup, a filtration step) —
factoring through the quotient often lands you somewhere with a free structural theorem.
Concretely in this repo: the residue field of `Oᵥ` is algebraic over a FINITE field, so
`∃ Q, x^Q ≡ x mod 𝔪 ∧ Q ≡ 0 mod 𝔪` — that is
`exists_pow_sub_self_mem_maximalIdeal` in `ArtinConductor.lean`, and it is the only
arithmetic input the whole lemma needed. It also makes the finished proof avoid the
residue field entirely: `unif ∣ Q` plus `geom_sum₂_mul` does the rest by divisibility.

See [[audit-searched-production-not-invariant]] and
[[flt-leaf-cost-estimates-are-hypotheses]] — same failure shape, different axis.
