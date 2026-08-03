## `∉ (small ideal)` IS NOT `∉ 𝔪` — the commonest direction error in a duality argument
(2026-07-31, found while proving `exists_tateWeilRawFamily_of_qAdicWeilSystem`.) A leaf's
prescribed route ended "the contrapositive turns a nonzero pairing value into
`C ∉ span {(q:O)}^N`, and then locality of `O` plus `hker` upgrade that to `IsUnit`". The
first half is right; the second is not, and the error is worth naming because it reads as a
routine last step.
In a local ring, `IsUnit c` is `c ∉ 𝔪` — non-membership in the BIGGEST proper ideal.
A duality hypothesis of the shape `c ∈ J ⟹ (θ-estimate)` contrapositives to `c ∉ J`, and `J`
is always SMALL (here `span {(q:O)}^N ⊆ span {j π}^{eN} ⊆ 𝔪`). Non-membership in a subideal
is *weaker* than non-membership in the whole maximal ideal, so the implication runs backwards.
Getting `IsUnit` needs an UPPER bound on `θ` over `𝔪` itself, which is a different and usually
missing clause — in this development the module's own docstring already recorded that no such
estimate exists at exponents that are not multiples of the ramification index.
Test before believing any "and therefore it is a unit": write down which ideal the argument
actually excludes, and check it is `𝔪` and not something inside it. Eight formal clauses of
that leaf went through exactly as prescribed; this one line was the whole of what was left.
