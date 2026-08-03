---
name: flt-refuted-cut-refutes-one-middle-object
description: A refutation of a cut whose middle object must be CHOSEN says nothing about a cut whose middle object is DEFINED by hypotheses already in the file
metadata:
  type: project
---

(2026-08-02, `flt-lean-41`, `hilbertAuxCotangentFinrank_le` in
`HardlyRamified/HilbertModularity.lean`.) That leaf carried a careful, correct,
bolded refutation of its own decomposition, ending *"Do not dispatch a 'build the
untwisted Selmer vocabulary over `F`' task at this leaf. The blocker is `L_HR`,
not the vocabulary."* Every clause was true and its prescribed refuting greps
still came back negative a day later.

**It refuted ONE middle object, and the distinguishing property is worth naming:
the refuted cut's middle object had to be CHOSEN.** Splitting through a Selmer
group `H¹_L` means the cutter picks a family of local conditions `L`, and the
refutation is that the two available spellings fail in OPPOSITE directions
(relax at `S` and half (b) is false; tighten and half (a) is false). That
argument needs a choice to bite on.

**A middle object that is DEFINED by a predicate already in the file cannot be
chosen wrong.** Here the deformation functor's `k[ε]`-points are pinned by
`IsHilbertRaisedLevelHardlyRamified`, which the file already carries, so no `L_w`
is ever spelled and the squeeze argument has nothing to attack. The sibling
module had taken exactly that cut at the `ℚ` level a day earlier and its own
docstring calls the result "gate-free — no cup product, no local invariant map,
**no Selmer group**".

**The check, before inheriting any "this does not decompose" verdict: ask whether
the refuted middle object was a CHOICE or a DEFINITION.** If the refutation turns
on "whichever way you spell it", it is scoped to objects that need spelling, and
a functor-of-points / already-defined-predicate middle object is outside its
scope. Same family as [[flt-audit-scoped-to-declaration-it-read]] and
[[flt-atomicity-verdict-checks-hypotheses-only]], with the axis being the KIND of
middle object rather than the hypothesis list.

**AND READ WHICH HYPOTHESIS THE SIBLING LEVEL DECLINED TO USE — it is often
exactly the one your leaf has.** The `ℚ` level needed `#classes ≤ #points` and
got it from a SURJECTION, because the INJECTION needs "two homs into `k[ε]`
agreeing on charpoly data are equal", which its docstring names as *"precisely
trace generation (Carayol)"* and does not have. This leaf needs the opposite
inequality — and carries `h𝒟Qt : IsTraceGenerated`, added by its own falsity
audit for an unrelated reason. **The hypothesis a falsity audit adds to repair a
leaf can be the hypothesis that opens its cut**; when an audit adds one, re-read
the sibling level's declined steps for it.

Two riders, both measured on the same run:

* **A port's hypothesis is decided by the ONE nontrivial step, not by the
  statement.** Generalising the `ℚ` count from `J = (ℓ)` to arbitrary `J` looks
  free — the definitions are literally the same `comap` with `J` for
  `span {(ℓ:R)}` — but `cotFrob_add` runs on `CharP (R ⧸ (𝔪² ⊔ J)) ℓ` through
  `add_pow_char_pow`, so the real hypothesis is `span {(ℓ:R)} ≤ J ≤ 𝔪`. Find the
  step that consumes the special value before promising the generalisation.
* **A structure can carry no tie to the parameter everything else assumes.**
  `TaylorWilesCoefficients` has no `Algebra ℤ_[ℓ]` and no residue-characteristic
  field — `Patching.lean` says so in as many words — so `(ℓ : R) ∈ Ideal.map c 𝔪_𝒪`
  is NOT immediate. It comes from the surjectivity hypothesis instead: `hc` makes
  `k` a quotient of `𝒪`, so `ker (π.comp c) = 𝔪_𝒪`, and `(ℓ : k) = 0` puts `ℓ`
  in it. Derive such facts from the surjection, not from the structure.
