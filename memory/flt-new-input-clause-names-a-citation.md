---
name: flt-new-input-clause-names-a-citation
description: "A leaf's \"the only genuinely NEW input is X\" clause searches for the citation's vocabulary, not the object's — grep the file that defines the leaf's own vocabulary first."
metadata: 
  node_type: memory
  type: project
  originSessionId: 8f0ae2c1-c2e2-4cc5-82b2-42e6d5a1e1e3
  modified: 2026-08-02T06:26:42.011Z
---

2026-08-02, `flt-lean-337`: `exists_frobLift_conj_pow_mem_wildInertiaGroup`
(`HardlyRamified/HilbertModularity.lean`) was cut 2026-07-31 with a careful
`WHAT A PROVER MUST DO` naming *"the only genuinely new input … the existence of
a Frobenius lift for the unramified quotient — Serre, Local Fields IV §2"*. It
was already in the tree, PROVEN, as
`Field.AbsoluteGaloisGroup.adicArithFrob` + `isArithFrobAt_adicArithFrob`, in
`Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean` — **the file that
defines `localInertiaGroup`**, i.e. the one supplying the leaf's own vocabulary.
The leaf closed in ~120 lines with no new input.

**Why:** the audit searched `ArtinConductor.lean` for the CITATION's words
("unramified", "residue field"). The object is `arithFrobAt'`, a wrapper on
mathlib's `RingTheory/Frobenius.lean`, whose content is
`Ideal.Quotient.stabilizerHom_surjective_of_profinite` — no local field, no
"unramified" in the statement. No grep for the theory can find it.

**How to apply:** before writing or believing "the only new input is X", list the
OBJECTS the classical proof consumes and grep the tree for each by TYPE, by the
mathlib CLASS that would carry it, and by the mathlib DIRECTORY it would live in
— and read the declaration list of the module that defines the leaf's own
vocabulary first. Related: [[flt-inventory-audits-understate-what-exists]],
[[flt-leaf-cost-estimates-are-hypotheses]],
[[flt-leaf-names-the-module-holding-its-answer]].

**Toolkit banked in CLAUDE.md** (local Frobenius at `v`): `adicArithFrob`,
`AlgHom.IsArithFrobAt.apply_of_pow_eq_one` (congruence → equality on `μ_n`),
`HeightOneSpectrum.natCard_under_maximalIdeal` (the exponent is
`Nat.card (𝓞 K ⧸ v.asIdeal)`), `conj_mem_localInertiaGroup` (inertia normal),
`smul_eq_self_of_pow_eq_one_algebraicClosure` (inertia fixes `μ_n`).
