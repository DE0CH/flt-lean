---
name: sheafification-unit-is-locally-surjective
description: In this pin the sheafification unit of PresheafOfModules IS locally surjective and reachable — instance search fails, explicit application works; plus the Γ(Z,V)-spelled tensor trick
metadata:
  type: reference
---

Two facts about `Fermat/FLT/Modularity/AmpleSheaf.lean` and
`Fermat/FLT/ModularCurve/RelativePicard.lean` that several route audits in those
files had recorded as unavailable, established by compiler check 2026-07-31
(`flt-lean-89`, proving `exists_modPair_eq_one`).

**1. `modTensorMk L N` IS `CategoryTheory.toSheafify` on underlying presheaves,
BY `rfl`** — no rewriting, no `toPresheaf_map_sheafificationAdjunction_unit_app`.
So local surjectivity of the sheafification unit is one step away:

```lean
Presheaf.imageSieve_mem (Opens.grothendieckTopology Z)
  (CategoryTheory.toSheafify (Opens.grothendieckTopology Z)
    (PresheafOfModules.Monoidal.tensorObj (R := Z.presheaf) L.val N.val).presheaf)
  (U := op U) w
```

**Instance search does NOT find `IsLocallySurjective J (toSheafify J P)` when the
goal is stated through `PresheafOfModules`** — the failure message names exactly
the instance that does exist, which reads as "the pin does not have it" and is
why the audits concluded that. Applying `Presheaf.imageSieve_mem` with the
topology and the presheaf given EXPLICITLY works. All three required instances
(`HasWeakSheafify`, `WEqualsLocallyBijective`, the `toSheafify` one) are present
for `Opens.grothendieckTopology Z` / `AddCommGrpCat.{u}`; check them one at a
time with `infer_instance` before believing a synthesis failure.

`Opens.mem_grothendieckTopology` is `.rfl`, so "the sieve is covering" unfolds
directly to "for each `z ∈ U` some `V ∋ z` carries a preimage".

**2. Write tensors of section modules over `Γ(Z, V)`, never over the
`forget₂`-spelled ring.** `PresheafOfModules.Monoidal.tensorObj` carries
`↑((Z.presheaf ⋙ forget₂ CommRingCat RingCat).obj (op V))`; `TensorProduct.add_tmul`
and friends then refuse to fire, and hand-writing that ring in a `rw` fails
instance synthesis for `Module _ ↑Γ(L,V)`. The fix is `RelativePicard.lean`'s
`evLin` trick — take `ModuleCat.Hom.hom` of the presheaf morphism's `app` and
STATE its domain as `TensorProduct Γ(Z,V) Γ(L,V) Γ(N,V)`. Everything then
rewrites normally. `Fermat.modTensorMkLin` is that wrapper, already declared.

Also: **`RingedSpace.isUnit_res_basicOpen` needs no affineness** — the
restriction of a section to its own basic open is a unit over an arbitrary
ringed space. Several notes here prescribe an affine open plus
`IsAffineOpen.isLocalization_basicOpen` for this; that detour is unnecessary.

Related: [[flt-schematic-density-is-in-the-pin]] — same shape of error, a
"not in the pin" verdict that was a spelling or search artefact.
