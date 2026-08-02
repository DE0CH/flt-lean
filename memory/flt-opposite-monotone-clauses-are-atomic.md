---
name: flt-opposite-monotone-clauses-are-atomic
description: "A leaf \"∃ A, P A ∧ Q A\" whose two clauses move oppositely as A is further quotiented is atomic in A — every split is refuted at once, and the intrinsic maximality pin moves the hard half instead of removing it."
metadata: 
  node_type: memory
  type: project
  originSessionId: faa2c7e2-a4a7-4e11-83a7-eefa55f0c116
  modified: 2026-08-02T02:38:36.415Z
---

For a leaf of the shape `∃ A, P A ∧ Q A` where `A` is a quotient (or subobject),
ask which way `P` and `Q` move when `A` is replaced by a FURTHER quotient. If they
move oppositely the leaf is ATOMIC in `A`: every split along the `A`-axis is refuted
in both directions at once, with no per-direction witness hunt.

Measured on `exists_eisensteinQuotientCert_of_heckeDecomposition`
(`FreyCurve/MazurTorsion.lean`, 2026-08-02). The formal-immersion certificate is
monotone UP (`cert (u ≫ π) ⟹ cert u`, injectivity on tangent vectors passes to a
first factor); the rank-`0` clause is monotone DOWN (Poincaré). The extreme
`A := J`, `u := 𝟙` then satisfies the monotone-up clause **as a consequence of the
leaf itself** — write the leaf's witness as `𝟙 ≫ u_e` — and fails the other wherever
`J(ℚ)` has positive rank (`N = 37`: `ellrank 37a1 = 1`). That is cheaper than the
witness the file already carried, which needed to know when `q` divides a Manin
constant.

**The trap is the repair the monotonicity suggests.** Taking `A` MAXIMAL for the
monotone-down clause pins it intrinsically, needs none of the theory the file was
blaming, and makes the leaf *equivalent* to "monotone-up clause at the maximal
object" — but the only route to that is "the maximal object dominates the intended
one", which IS the hard half. The cut moves the hard half and pays for the maximality
theory besides. **A pin that makes a split EXPRESSIBLE is not one that makes it
CHEAPER**; the expressibility obstruction is just the one you see first.

Rider: read the DIRECTION of a helper lemma's maps before believing a route that
names it. `isTorsion_of_finite_jointKer` wants `φ : ∀ i, G →+ H i`, maps OUT of the
group whose torsion you want; a Hecke decomposition gives maps out of `J`, not out
of `A`, so the recorded route would have proved `J₀(N)(ℚ)` torsion, which is false at
`N = 37`. See [[flt-leaf-cost-estimates-are-hypotheses]],
[[flt-route-residue-is-the-cheap-route]], [[flt-leaf-can-be-atomic]].
