---
name: flt-theory-absence-claims-need-a-directory
description: "A leaf's \"this axis needs geometry the pin does not have\" names a THEORY, which no identifier grep can refute — ask which directory of Fermat/ would own it"
metadata: 
  node_type: memory
  type: project
  originSessionId: 786981a8-766d-4042-a5b3-6a0692f35937
  modified: 2026-08-01T07:01:39.964Z
---

`Modularity/Interface.lean`'s Eichler–Selberg leaf
(`exists_trace_heckeOpN_int_of_two_le`) listed Eichler–Shimura point counting as
an unsearched axis and said it "needs modular-curve geometry over `ℤ` that this
pin does not have". False when written: `ModularCurve/X0.lean`, which that file
`public import`s, already had `Fermat.card_relPoint_x0_eichlerShimura`
(`#X₀(N)(𝔽_ℓ) = ℓ + 1 − Tr(T_ℓ)`), PROVEN. The prime case of the leaf is four
lines over it, with no new leaf (2026-08-01, closed this way).

**Why:** an absence claim about a THEORY has no identifier, so every natural
grep (`Eichler`, `DeligneRapoport`, `Hurwitz` over mathlib) confirms it. The
refuting grep is for the CONCLUSION in this tree's own vocabulary —
`grep -rn "eichlerShimura\|card_relPoint" --include=*.lean Fermat/`.

**How to apply:** before believing an axis is blocked on missing geometry /
commutative algebra / class field theory, name the DIRECTORY of this project
that would own it (`Fermat/FLT/ModularCurve/`, `Fermat/FLT/Mathlib/`,
`Fermat/FLT/NumberField/`) and read its declaration list. Same family as
[[flt-inventory-audits-understate-what-exists]] and
[[flt-missing-machinery-may-be-downstream]], but UPSTREAM and directly imported.

Rider: `origin/main` moves under you mid-session (the pool shares one object
store), so re-run the staleness check right before an expensive build and
compare against the FILE `~/.flt-release-lake/sha`, which does not move.
