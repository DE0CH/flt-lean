---
name: flt-absorbed-constant-needs-invariant-clauses
description: When a cut removes an existential constant by absorbing it into the witness, every surviving clause must be invariant under the translation absorbed — the non-invariant reading is false by the ORIGINAL witness
metadata:
  type: project
---

A leaf that binds a correction `e` because its witness is pinned only up to
something is routinely re-cut to bind the witness alone, `e` going into a
translation. The simplification is real. **The other clauses are the trap:
absorbing `e` hides the freedom rather than deleting it, so every surviving
clause must be blind to the translation `κ ↦ κ + δ`.**

Seen 2026-07-31 in `X0.lean`'s Hecke cluster
(`exists_heckeCorrespondenceMorphism_atkinLehnerCommuting`). Of the two
natural morphism-form readings of `w_J (c x) = c (w x) − c (w o)`:

    (naive)      w_J (P x)       = P (w x) − P (w o)   -- FALSE
    (invariant)  w_J (P x − P o) = P (w x) − P (w o)   -- TRUE

the naive one gains `w_J δ` on the left and nothing on the right, so it
silently demands `w_J δ = 0` — which unwinds to `ε = 0` for the SAME
base-point defect `ε = T_ℓ[o] − (ℓ+1)[o]` that refuted this cluster on
2026-07-29 (`N = 37`, `ℓ = 2`, `o` non-cuspidal). The original witness
refutes the new statement one restatement later, wearing a different face.

**Why:** invariance under the absorbed symmetry is exactly the condition
that the clause constrains only what the datum determines. It is also what
keeps the reduction cheap — the invariant form collapsed to the parent's
clause by abelian-group algebra alone, where the naive one would have needed
additivity of `RelPoint.post wJ hwJ`, a genuine obligation smuggled into
glue. **A cut whose glue starts needing real theorems is usually the
non-invariant cut.**

**How to apply:** name the symmetry the removed existential absorbed, apply
it to both sides of each surviving clause, and repair any clause whose sides
transform differently by normalising against the same datum the other side
uses. A clause built from DIFFERENCES of the witness's values is invariant
for free — and is usually the parent's clause transcribed, so the fix is
never a weakening. See also [[flt-audit-voided-by-structure-field]]: a second
restatement voids the first audit, and here the 2026-07-30 audit that ADDED
`e` certifies a statement that no longer exists.
