---
name: flt-rational-certificate-clears-to-torsion
description: "A ℚ-certificate cleared to ℤ gives only a TORSION statement; the multiplier is produced after the parameter it must divide, and a change of variable repairs it."
metadata: 
  node_type: memory
  type: project
  originSessionId: d001810a-ff8b-4f9f-943e-bea59557a071
  modified: 2026-08-02T16:45:18.810Z
---

(2026-08-02, `flt-lean-119`, `exists_localizedSystemGens_identities_of_ratRetraction`
in `Modularity/MoretBailly.lean`, now PROVEN.)

A leaf of the shape `N * z ∈ span (gens … N)` — where the generating set itself
depends on `N` — has a circularity its own route note did not see:

* the representatives are integral only once `N` clears their denominators, so `N`
  is chosen first;
* the ℚ-certificate's cofactors then produce a multiplier `M` **after** `N` exists,
  and nothing makes `M` divide a power of `N`.

And `M | N^∞` is exactly what is needed, because the leading `N` is decoration —
the ideal already contains `N·b·y − 1`, so `N` is a unit modulo it. What the
factor stands in for is TORSION: `z` dying over ℚ only gives `M z ∈ span` over ℤ.
Not automatic — `k = 1`, `g = 2X₀`, `b = 1`, `N = 1`, `z = X (some 0)`:
`ℤ[X]/(2X)` has `X` 2-torsion.

**Repair: a change of variable.** Rabinowitsch presentations are indexed by what
they invert, so `X none ↦ M · X none` carries `gens … N₁` to `gens … (N₁·M)`,
where `M` HAS become a unit. Hence `M z ∈ span(gens N₁) ⟹ subNone M z ∈
span(gens (N₁ M))`. Build every tuple's `none` component with an explicit
`X none` factor so the substituted tuple can be divided by `M` again — free here,
since `1/N = b · X none` is the integral expression for the denominator.

See [[flt-leaf-cost-estimates-are-hypotheses]]: the route note was right about
steps 1–2 and wrong about step 3, and the error is only visible once written.
