---
name: flt-char0-machinery-is-base-generic
description: In TateModule.lean the char-0 Tate-module machinery is base-field-generic except for cyclotomicCharacter — check which [NumberField F] are load-bearing before rebuilding it for a finite base
metadata:
  type: project
---

`Fermat/FLT/Modularity/TateModule.lean` has two parallel developments: a
characteristic-zero one over `[NumberField F]` and a finite-base one over
`[Field k] [Finite k]`. The finite-base leaves are routinely described as
needing their own copy of the machinery. **That is usually false.** The
`[NumberField F]` instance on the char-0 side is load-bearing in exactly one
place — hanging `cyclotomicCharacter` on `F` for the Galois multiplier — and
nothing else in those clauses refers to it.

Concretely, on 2026-07-31 `exists_levelWeilPairing_of_traceDualFrobeniusLog_finiteBase`
was cut in two by observing that:

* `TatePt` and `exists_tatePt_val_eq` (the section of `T ↠ A[Iᵏ]`) carry only
  `[Field F]` and apply over a finite `k` **verbatim**;
* `IsTateWeilPairing` becomes base-generic by dropping `[NumberField F]`,
  `q` and `[Algebra ℤ_[q] O]`, and replacing the cyclotomic multiplier with a
  parameter `χ : 𝒪_D` for one fixed `σ` — which is precisely the modelling
  `IsLevelWeilPairing` already uses, and for the reason recorded there (over a
  finite field the only `σ` in play is the `N`-power Frobenius).

**Why to apply:** the reduction "Tate-module pairing ⟶ level-`Iⁿ` pairing" then
ports from `exists_tateWeilSystem_of_qAdicWeilSystem`'s proof move for move and
is ~180 lines, discharging one of the four steps of a leaf that had none. The
transport to the honest quotient `𝒪_D ⧸ Iⁿ` is a reduction map `ψ : O → 𝒪_D⧸Iⁿ`
built from the pin (`hdense` chooses the representative, `hker` makes the class
independent of the choice); it needs neither `IsAdicComplete` nor `IsLocalRing`,
and perfectness transports for the single reason that a ring map sends units to
units.

**How to apply:** before writing a finite-base copy of anything in
`TateModule.lean`, grep the char-0 declaration's proof for `cyclotomicCharacter`
and for `NumberField`. If the only hits are in the multiplier, generalise the
statement instead of duplicating it. See [[flt-missing-machinery-may-be-downstream]]
and [[flt-inventory-audits-understate-what-exists]] — same failure mode, different
axis: the machinery exists, stated one instance too strong.
