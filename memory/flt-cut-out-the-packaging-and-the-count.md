---
name: flt-cut-out-the-packaging-and-the-count
description: "A leaf whose conclusion is a linear map into Fin B → K with a dimension count has two removable layers; pin only what monic division forces, leave the degree box existential"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: b32ecbf6-4382-4a60-bb6a-9331617f15d1
  modified: 2026-08-02T09:55:37.398Z
---

A dimension-count leaf in this tree looks like

    ∃ (B : ℕ) (Φ : families →ₗ[K] (Fin B → K)),
      B < unknownCount ∧ ∀ a, shape a → Φ a = 0 → <the mathematics>

Two of its three layers are not mathematics and come out with a provable
assembly: the PACKAGING (`Fin B`, the linear map, coefficient extraction) and the
COUNT. Cut so the residual produces the raw objects — here `Θ ν : families →ₗ[K]
K[X][Y][Y']`, `ν < M` — inside a degree box, plus ONE arithmetic conjunct.

**Why:** get the box wrong and the leaf is false, so make the *estimated* part of
the box EXISTENTIAL (`∃ D : ℕ → ℕ`) and constrain only the total,
`∑_{ν<M} (d−1)·d·(D ν + 1) < unknownCount`. That is exactly as weak in the count
as `B < unknownCount` was, so nothing can be lost. Then PRE-PROVE the arithmetic
for the box the route is expected to hit, as a separate theorem the leaf's prover
cites — the obligation stays discharged without being pinned.

**Pin only what MONIC DIVISION forces.** `deg_{Y'} ≤ d − 2` (reduction mod the
monic `e₂`) and `deg_Y ≤ d − 1` (mod the monic `F`) are not estimates and must
stay pinned; they are what the count's shape rests on.

**The assembly, ~120 lines:** index the box as
`(ν : Fin M) × (Fin (d−1) × Fin d × Fin (D ν + 1))` — `Sigma` only because the
`X`-degree depends on `ν` — take `B := Fintype.card`, get `Fin B ≃ Idx` from
`Fintype.equivFin`, define `Φ` as a raw structure literal (`map_add'`/`map_smul'`
are `funext n; simp`), and recover `Θ ν a = 0` from `Φ a = 0` by
`Polynomial.ext` three times, discharging each out-of-box coefficient with
`Polynomial.coeff_eq_zero_of_natDegree_lt`. Do NOT compose typed `lcoeff`s:
`Polynomial.lcoeff R n` is `R`-linear, and the outer coefficient of `K[X][Y][Y']`
is `K[X][Y]`-linear, not `K`-linear.

To use `Φ a = 0` at a box index, avoid `rw` on `eqv (eqv.symm idx)` (the pattern
sits under an unreduced structure literal). Prove
`∀ idx, <coeff at idx> = 0` by `obtain ⟨n, rfl⟩ := eqv.surjective idx; exact
congrFun hΦ n` — surjectivity, not the round-trip equation.

ACCOUNTING: one leaf in, one leaf out. Say so; the delta is zero and the win is
that the open statement mentions no `Fin B` and no count. Relatives:
[[flt-leaf-blocked-by-declaration-order]], [[flt-weaken-the-leaf-to-an-inequality]].
