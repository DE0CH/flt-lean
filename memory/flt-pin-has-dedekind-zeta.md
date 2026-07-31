---
name: flt-pin-has-dedekind-zeta
description: The pin HAS NumberField.dedekindZeta and the Dirichlet class number formula; "no Chebotarev/no Dedekind zeta in the pin" was a search for the THEORY, not the OBJECT
metadata:
  type: project
---

`Mathlib/NumberTheory/NumberField/DedekindZeta.lean` (Xavier Roblot) is in the pin and
carries `NumberField.dedekindZeta`, `NumberField.dedekindZeta_residue_pos`, and
`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT` — the **Dirichlet class number
formula**, `(s-1)·ζ_K(s) → ρ_K > 0` as `s → 1⁺`, over an ARBITRARY number field, resting
on `NumberField.Ideal.tendsto_norm_le_div_atTop₀` (ideal counting via `ZLattice.covolume`).

**Why:** `finrank_eq_one_of_forall_inertiaDeg_eq_one` (the density input of Chebotarev)
was cut on 2026-07-31 with a docstring, and dispatched with a prompt, both asserting the
pin had "Dirichlet's theorem for `k = ℚ` and NOTHING over a general number field — there
is no Chebotarev and no Dedekind zeta anywhere in the pin (checked by grep)". False. The
grep was for the THEORY the argument is narrated with (Chebotarev, Dirichlet density,
`L(1,χ) ≠ 0`); what is present is the OBJECT the proof consumes, under its own name, in a
file called exactly that. The leaf was proven the same day over three residual statements
of elementary Dirichlet-series bookkeeping, in `Fermat/FLT/NumberField/Density.lean`.

**How to apply:** before costing a node off an absence claim, list the concrete objects
the proof needs — a zeta function, a residue, a counting asymptotic, a covolume — and `ls`
the mathlib directory each would live in; `ls Mathlib/NumberTheory/NumberField/` would
have ended this in one call. And when a mathlib theorem is *close* to what you want, read
its PROOF: the `LSeriesSummable` input all three residual leaves need was sitting inside
the class number formula's own proof body, unexported, and lifting eight lines out gave it.
See [[flt-inventory-audits-understate-what-exists]], [[flt-absence-audit-names-one-module]],
[[flt-missing-machinery-may-be-downstream]], [[flt-leaf-cost-estimates-are-hypotheses]].
