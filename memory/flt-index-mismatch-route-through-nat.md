---
name: flt-index-mismatch-route-through-nat
description: "When `p^1` vs `p` (or any numeral index) separates two spellings of one object, factor both sides through ℕ instead of building the type equivalence."
metadata: 
  node_type: memory
  type: project
  originSessionId: 49320d93-0034-4430-8c43-040fbb626b7e
  modified: 2026-08-02T17:04:03.171Z
---

`ℓ ^ 1` is NOT `rfl`-equal to `ℓ` for a variable `ℓ` — `ℓ * 1` unfolds to `0 + ℓ`
and `Nat.add` recurses on its second argument. So `ZMod (ℓ^1)` and `ZMod ℓ` are
different types, and at this pin there is **no lemma identifying
`PadicInt.toZMod` with `PadicInt.toZModPow 1`** (two independent `toZModHom`s).

Closing `det_eq_cycCharModN_of_isHardlyRamified` (2026-08-02, `flt-lean-312`,
`Modularity/MoretBailly.lean`) needed to compare mathlib's `ℓ`-adic
`cyclotomicCharacter` — whose spec is stated with `toZModPow n` over
`ZMod (p^n)` — with this project's `cycCharModN` over `ZMod ℓ`.

**Do not build the comparison isomorphism. Route both sides through `ℕ`**, which
carries no index: take `m := (PadicInt.toZModPow 1 x).val` and prove
`algebraMap ℤ_[ℓ] k x = (m : k)` and `(m : ZMod ℓ) = χ̄_ℓ τ` separately; the ends
meet at `map_natCast`. The single `pow_one` lives in one ideal-membership lemma
over `PadicInt.ker_toZModPow 1`.

Generalises to `Fin (n+1)` vs `Fin m`, re-indexed matrices, `ZMod (p^1)` vs
`ZMod p`: **find the un-indexed carrier both sides map out of, never the
isomorphism between them.**

Two riders from the same proof:
* "`algebraMap ℤ_[ℓ] k` factors through `ℤ/ℓ` because `(ℓ:k)=0`, which is
  `zmodCastOf`" is a LEMMA, not a step — `zmodCastOf` is only the map; the
  factorisation is where `hchar` is spent (~6 lines over `ker_toZModPow`).
* `rw [hxe]` with `hxe : x = f x + …` rewrites the `x` inside `f x` too, giving a
  goal that reads like a wrong lemma. `conv_lhs => rw [hxe]` is the fix.

See [[flt-cutters-route-note-is-reliable]]: this leaf's route note named exactly
the right tools, because whoever cut it had just read the proof it came out of.
