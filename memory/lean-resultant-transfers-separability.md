---
name: lean-resultant-transfers-separability
description: Separability does not transfer along a ring map, but Res(f,f') does — mathlib has Polynomial.resultant with isUnit_resultant_iff_isCoprime and resultant_map_map
metadata:
  type: reference
---

`Polynomial.Separable` transfers only FORWARD along a ring hom
(`Separable.map`), so "separable mod `p` ⟹ separable over `ℚ`" — the shape
every good-reduction leaf needs — has no direct lemma. The tool is the
resultant, and mathlib has it at this pin in
`Mathlib/RingTheory/Polynomial/Resultant/Basic.lean` (NOT transitively
imported by most files — add `public import` explicitly):

- `Polynomial.isUnit_resultant_iff_isCoprime (hf : f.Monic) :
   IsUnit (resultant f g) ↔ IsCoprime f g` — and `Separable f` is
  *definitionally* `IsCoprime f (derivative f)` (`Polynomial.separable_def`).
- `Polynomial.resultant_map_map (φ : R →+* S) :
   resultant (f.map φ) (g.map φ) m n = φ (resultant f g m n)`.

So for `f ∈ ℤ[X]` monic: `Res(f, f')` is an INTEGER; a unit mod `p` ⟹ nonzero
⟹ a unit in `ℚ`. Closed the `ℚ`-separability side condition of
`exists_degreeMap` in `HyperellipticJacobian.lean` (2026-07-31).

**The trap: `resultant` takes its sizes as `optParam`s defaulting to the
natDegrees, and `f'.natDegree` DROPS in bad characteristic** — for a sextic
it is `5` over `ℚ` but `4` over `ZMod 3`, since `6 ≡ 0`. So the two sides of
`resultant_map_map` are about different matrices unless you pass `m n`
explicitly. Pad with `Polynomial.resultant_add_right_deg`, whose correction
factor is `f.coeff m ^ k` — which is `1` for monic `f` at `m = deg f`.

Related trap, same file: `PlaceData.Pic` is a plain `def` for a quotient
type, so a bare `QuotientAddGroup.mk` elaborates at the *unfolded* type and
then `rw` refuses to fire inside a hom whose domain is written `Pic`
("not type-correct under `instances` transparency"). Package the quotient map
once as a named `AddMonoidHom` with `Pic` as its stated codomain
(`mkPic E : E.Divisors →+ E.Pic := QuotientAddGroup.mk' E.picRel`) and every
`map_add`/`map_zsmul` rewrite then works. See
[[flt-see-the-merge-before-the-merger]] for the other half of this file's
merge hazards.
