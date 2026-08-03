## A `p ^ 1` vs `p` INDEX MISMATCH IS NOT A TYPE PROBLEM — ROUTE BOTH SIDES THROUGH `ℕ`
(2026-08-02, `flt-lean-312`, closing `det_eq_cycCharModN_of_isHardlyRamified` in
`Modularity/MoretBailly.lean`.)  A recurring shape whenever two developments name
the same object with different-but-equal numerals: mathlib states the `p`-adic
cyclotomic character's defining property through
`PadicInt.toZModPow n : ℤ_[p] →+* ZMod (p ^ n)`, while this project's mod-`ℓ`
vocabulary (`cycCharModN`, `zmodCastOf`) lives over `ZMod ℓ`.  At `n = 1` those
are the same group and **not the same type**: `ℓ ^ 1` unfolds to `ℓ * 1 = 0 + ℓ`,
and `Nat.add` recurses on its SECOND argument, so `0 + ℓ` is not `rfl`-equal to
`ℓ` for a variable `ℓ`.  This pin also has **no lemma identifying
`PadicInt.toZMod` with `PadicInt.toZModPow 1`** — they are two independent
`toZModHom`s — so the obvious repair (build the comparison `ZMod (ℓ^1) ≃+* ZMod ℓ`
and transport) is a small development in its own right.
**Do not build the type equivalence.  Factor BOTH sides through a type that does
not carry the index — here `ℕ`.**  Everything went through one natural number
    m := (PadicInt.toZModPow 1 (χ_ℓ τ)).val
and the two ends met at `map_natCast`, because `ℕ → k` and `ℕ → ZMod ℓ` are both
ring homs and neither mentions `ℓ ^ 1`:
* `algebraMap ℤ_[ℓ] k (χ_ℓ τ) = (m : k)`;
* `(m : ZMod ℓ) = χ̄_ℓ τ`, by `modularCyclotomicCharacter.unique`;
* `zmodCastOf hchar (m : ZMod ℓ) = (m : k)`.
The single `pow_one` needed is confined to one ideal-membership lemma
(`PadicInt.ker_toZModPow 1` gives `span {(ℓ:ℤ_[ℓ]) ^ 1}`, rewritten to
`span {(ℓ:ℤ_[ℓ])}`).  Generalises to `Fin (n+1)` vs `Fin m`, `ZMod (p^1)` vs
`ZMod p`, `Matrix (Fin 2)` vs a re-indexed basis: **when an index is the only
thing separating two spellings, look for the un-indexed carrier both sides map out
of, and never for the isomorphism between them.**
Two riders, both measured on the same leaf.
* **"`algebraMap` factors through the residue field because `(ℓ : k) = 0`" is a
  LEMMA, not a step.**  The leaf's docstring priced it as "which is `zmodCastOf`",
  but `zmodCastOf` is only the map `ZMod ℓ →+* k`; that `algebraMap ℤ_[ℓ] k` EQUALS
  it composed with reduction is where `hchar` is actually spent, and it is the only
  place it is spent.  It is ~6 lines over `PadicInt.ker_toZModPow` — cheap, but it
  has to be written, and a route note that names the target map rather than the
  factorisation reads as though it does not.
* **`rw [hxe]` where `hxe : x = f x + …` rewrites the `x` INSIDE `f x` too.**  The
  goal came back as `↑(f x).val = ↑(f (↑(f x).val + ℓ * y)).val`, which reads like a
  wrong lemma and is not.  `conv_lhs => rw [hxe]` is the one-character fix; the
  general form is that any equation whose RHS mentions its own LHS must be applied
  positionally.
**And the cut's own route note was RIGHT**, which is worth recording because this
file is mostly a catalogue of route notes that were not.  It named
`cyclotomicCharacter.spec`, `modularCyclotomicCharacter.unique` and the two
existing consumers of the latter (`cycCharModN_eq_one`,
`fixes_sqrtNegThree_iff_cycCharModN`) as the model, and every one of those was the
right tool.  A route note written by whoever CUT the leaf out of a proof they had
just read is evidence; it is the ones written before anyone tried that decay.
