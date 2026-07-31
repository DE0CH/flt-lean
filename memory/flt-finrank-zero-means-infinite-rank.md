---
name: flt-finrank-zero-means-infinite-rank
description: In this development `Module.finrank A M` is over an arbitrary CommRing, so `finrank = 0` also means INFINITE rank and submodule monotonicity is FALSE without `finrank A M ≠ 0`
metadata:
  type: project
---

`GaloisRep K A M` carries only `[CommRing A] [TopologicalSpace A]
[AddCommGroup M] [Module A M]` — **no `Module.Finite`, no `Module.Free`, no
field.** So every conductor/codimension statement in
`Fermat/FLT/Deformations/RepresentationTheory/ArtinConductor.lean` is written
with `Module.finrank A M` at that generality, and `Module.finrank` is
`(Module.rank A M).toNat`.

**Why:** `Cardinal.toNat` sends every infinite cardinal to `0`. So
`finrank A M = 0` is *ambiguous* — it is what rank `0` looks like AND what
rank `ℵ₀` looks like — and in the second case a submodule can have
`finrank = 5 > 0 = finrank A M`. `Submodule.finrank_mono` does not apply
(it wants `[Module.Finite R t]`), and the bare monotonicity statement is
genuinely FALSE.

**How to apply:** prove monotonicity as
`Cardinal.toNat_le_toNat (Submodule.rank_mono h) (…)` under the hypothesis
`Module.finrank A M ≠ 0`, which is exactly what forces
`Module.rank A M < ℵ₀` (via `Cardinal.toNat_eq_zero`). It is in the file as
`GaloisRep.finrank_le_finrank_of_le`. Then case-split: the
`finrank A M = 0` branch of any codimension statement is separately TRIVIAL,
because `ρ.wildCodim v = 0 - _ = 0` and every codimension is `0 - _ = 0` in
`ℕ` truncated subtraction, so both sides of a counting clause are `0`.

Corollary for statements: ℕ-truncated subtraction is doing real work in these
conclusions, and it is what makes the degenerate branch true rather than
ill-formed. Do not "fix" a codimension by casting it to ℤ.

See [[flt-cut-the-open-inclusion-not-the-equality]] for the other lesson from
the same proof.
