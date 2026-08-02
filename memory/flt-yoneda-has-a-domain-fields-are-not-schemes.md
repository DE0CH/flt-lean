---
name: flt-yoneda-has-a-domain-fields-are-not-schemes
description: "A moduli property quantified over FIELD points cannot produce a morphism of schemes — read the quantifier's domain before pricing a leaf that wants an automorphism."
metadata: 
  node_type: memory
  type: project
  originSessionId: 62c2cdf1-263b-496e-9d6d-d5afbcd67619
  modified: 2026-08-02T17:04:03.782Z
---

`[[flt-forall-test-object-leaf-reduces-to-universal]]` says a functorial bundle
quantified over ALL TEST SCHEMES **is** a morphism: instantiate at the object itself,
feed it `𝟙`. True, and it has closed several leaves that looked structurally blocked.

**Check the DOMAIN of the `∀` first, because the converse prices the leaf.** A
fine-moduli property indexed by FIELDS —

    (∀ (F : Type u) [Field F] [Algebra ℚ F] (x : Spec F ⟶ X₀), …)
  ∧ (∀ F, an object over F comes from an F-point)

— pins `X₀` on field points only. Yoneda needs all of `Scheme`; a bijection of
`F`-points for every field does not determine a scheme (non-reduced test objects are
what it cannot see), so `Aut_K (X₀ ⊗ K)` is **not** reachable from it.

Measured 2026-08-02 on `MoretBailly.lean`'s leaf A2a1-ii
(`hasSplitHilbertBlumenthalCocycleModel_of_levelTwistCocycle`): its `hmodel`
hypothesis is field-indexed, so the transport of the level-twisting cocycle `g` to
`Aut_K (X₁ ⊗ K)` is genuine geometry (Taylor §4 / Rapoport §1), not the bookkeeping
its "the group theory is already done and is handed in" docstring reads as promising.

**Corollary used to justify pinning the existential:** over an ALGEBRAICALLY CLOSED
base the Galois-equivariance clause of a level structure is VACUOUS — it quantifies
over `Field.absoluteGaloisGroup F`, trivial at `F = K̄`. So `X ⊗ K̄` classifies the same
objects whatever `ρ` normalises the level structure, and every `ρ`-model is a `ℚ`-form
of ONE `K̄`-scheme. That makes "the `ρ₀`-model is the twist of the `ρ₁`-model on the
same base space" true by the citation — but NOT derivable from the field-indexed
hypothesis, so it is a judgement to be written into the audit, per
`[[flt-cut-so-each-half-is-a-consequence]]`.

**Why:** the two readings of one `∀` differ by a whole citation's worth of work, and
the docstring that prices the leaf usually does not distinguish them.

**How to apply:** before costing any leaf that demands a morphism (automorphism,
isogeny, section, group law) out of a moduli hypothesis, grep the hypothesis for
`∀ (T : Scheme` versus `∀ (F : Type u) [Field F`. The first is bookkeeping; the second
is geometry.
