---
name: flt-uniqueness-clause-needs-subsingleton-base
description: A fine-moduli/uniqueness clause written without an "over the base" clause is FALSE over any base with a nontrivial automorphism — test it at Spec 𝔽_{ℓ²}
metadata:
  type: project
---

A `∃!`-style universal property stated over a base `S` splits into an EXISTENCE
clause and a UNIQUENESS clause, and it is tempting to give the over-`S` clause
(`m ≫ str = g`) only to existence, on the grounds that uniqueness "is a
statement about the moduli scheme alone". **That reasoning is wrong**, and the
refutation is uniform: a semilinear rival.

`X1.lean`'s `IsFineGamma1Moduli` was written that way. Take `K = 𝔽_{ℓ²}`, `σ`
the Frobenius, `d` a `Γ₁(N)`-datum defined over `𝔽_ℓ` and base-changed to `K`,
and `m₁ : Spec K ⟶ Y` its classifying `K`-point. Then

    m₂ := Spec σ ≫ m₁       satisfies   m₂^* dY = σ^*(m₁^* dY) = σ^* d ≅ d

so `m₁` and `m₂` BOTH exhibit `d` as a base change of the universal family,
while `m₂ ≫ str = Spec σ ≠ 𝟙 = m₁ ≫ str`. Rigidity at `N ≥ 4` pins the
classifying morphism only **among morphisms over the base**; it says nothing
about a rival that moves the base.

**Why the leaf survived anyway, and the rule to take away.** It is used only at
`SpecF ℓ`, where `Hom(T, SpecF ℓ)` is a subsingleton (`ZMod ℓ` is a quotient of
the initial ring `ℤ`) — `subsingleton_hom_specF` in `X0.lean`, the `𝔽_ℓ` twin of
`subsingleton_hom_specQ`. So the notion is correct at the two bases this
development uses and at essentially no others. When you generalise such a
structure off `SpecQ`/`SpecF ℓ`, **carry `∀ Z, Subsingleton (Z ⟶ S)` as an
explicit hypothesis** rather than assuming the clause was decoration; that is
what `exists_isFineGamma1Moduli_of_atlas` does.

Corollary for auditors: the base subsingleton is a hypothesis that is
*load-bearing twice over*. In `exists_isFineGamma1Moduli` the primality of `ℓ`
is cited for "`ZMod ℓ` is a field"; it is ALSO what makes the uniqueness clause
true at all, and that second role is invisible until the statement is moved off
its base. See [[flt-forall-over-structure-needs-pinned-field]].
