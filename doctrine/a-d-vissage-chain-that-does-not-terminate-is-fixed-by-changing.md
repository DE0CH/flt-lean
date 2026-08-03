## A DÉVISSAGE CHAIN THAT DOES NOT TERMINATE IS FIXED BY CHANGING THE INDUCTION VARIABLE, NOT THE CHAIN
(2026-08-01, `flt-lean-229`, closing `isSplitTorusAt_of_subring_entries` in
`Modularity/Patching.lean` — the last leaf of the raised-level Schlessinger machine.)
A leaf whose route is *"Schlessinger dévissage: filter `C ⊂ ⋯ ⊂ A` by adjoining one
element of `𝔪_A` at a time and apply the gluing clause at each step"* is the standard
shape here, and it is **the standard way for such a route to be wrong**. Each step of
that chain needs the deformation condition on a QUOTIENT of the smaller ring, and going
UP the chain that is never in hand — so the recursion is not well-founded on the chain
index, however many steps you write.
**The repair is to induct on `Nat.card A` — the AMBIENT ring — and use ONE fibre product
per step.** With `I := 𝔪_A^{n-1}` the last nonvanishing power (so `I ≠ ⊥`, `𝔪_A·I = ⊥`)
and `J := ι(C) ∩ I`, both branches land at a strictly smaller ambient ring:
* `J ≠ ⊥` — `C ≅ A ×_{A/J} (C/ι⁻¹J)` is a genuine cartesian square with a SURJECTIVE
  leg, and the small side is the inductive hypothesis at `C/ι⁻¹J ↪ A/J`;
* `J = ⊥` — the SAME `C` embeds in `A ⧸ I`, the IH applies there and concludes the goal
  verbatim, with no transport at all.
A plain `induction n` on a `Nat.card A ≤ n` bound then suffices; the `zero` case is
vacuous because a local ring is nontrivial. **`J` being an IDEAL OF `A` rather than an
`ι(C)`-submodule is the one step that spends "`C` surjects onto the residue field"**:
`a = ι c + m` and `m·x ∈ 𝔪_A·I = 0` for `x ∈ I`, so `a·x = ι(c)·x`.
Two structural notes that are worth more than the instance:
* **State the descent with an INJECTIVE RING HOM `ι : C →+* A`, not with `C : Subring A`.**
  Every recursive call lands at a pair (`C/ι⁻¹J ↪ A/J`, and `C ↪ A/I`) that is not a
  `Subring` of the original `A`; the `Subring.map` bookkeeping is pure cost. Derive the
  `Subring` form as a one-line corollary at `ι := C.subtype`.
* **Prove the WHOLE structure by induction, not the one field you were asked for.** The
  gluing clause returns the full condition, so an induction that carries only the leaf's
  field cannot use it. Here the induction proves `IsRaisedLevelHardlyRamified` and the
  leaf is its `isSplitTorusAt` projection. Check the direction: the induction must NOT
  call the subring-descent theorem that is proven OVER the leaf, or it is circular.
### THE HYPOTHESIS THE PROSE ASSUMED AND THE SIGNATURE DID NOT
The same leaf's docstring justified a step parenthetically — *"`C` and `A` having the
same residue field (`πA` is surjective and factors through `C` …)"* — and
`Function.Surjective (πA.comp C.subtype)` was **in no binder**. Both of the leaf's own
recorded routes need it, and without it the statement is refuted in shape by
`A = 𝔽₄ ⊇ C = 𝔽₂`, `ρ(Frob) = [[0,1],[1,1]]`. This is CLAUDE.md's standing rule
(*read a docstring for sentences of the form "X, because Y", and check that Y is in the
binder list*) firing on the leaf that rule was written about — so run it on every leaf
you are dispatched at, including ones whose docstring already looks exhaustive.
**And the missing hypothesis was free at the top, as it nearly always is.** Threading
`hCsurj` and `hQp` through three signatures changed no proof above them, because the
chain's terminus already held `hc2' : πA.comp f = ι.comp ev` with both factors
surjective. **Trace the consumer chain to its terminal hypotheses BEFORE concluding a
leaf must be stated in the generality it currently is** — and check the changed
declarations have no consumer outside the file (`grep -rn <name> Fermat/ | grep -v <file>`),
which converts a class-7 interface-split hazard into a purely local edit.
### `charFrob` TRANSPORTS ALONG AN ENTRYWISE EMBEDDING, AND THAT ONE LEMMA SERVES FOUR TIMES
The bookkeeping obligation of any such descent is *"entries of `ρC` map to entries of
`ρA` ⟹ `(ρC.charFrob v).map ι = ρA.charFrob v`"*. It is six lines over
`GaloisRep.toLocal_apply` (the exposed `rfl`-lemma — a bare `rfl` FAILS under the module
system, `IsAlgClosed.lift` not being exposed), `LinearMap.charpoly_toMatrix` at
`Pi.basisFun`, and `Matrix.charpoly_map`, under
`set_option backward.isDefEq.respectTransparency false`. Stated once for a general `ι`,
it also discharges the `charFrob` clause at every `Ideal.Quotient.mk` in the induction,
since `toMatrix'_pushforwardFrame` says the pushforward's entries are exactly the
images. Do not write a `charFrob_pushforwardFrame` as well.
**And check `framedGaloisRep_ext_toMatrix'` before writing your own.** "Two framed
representations with the same matrices are equal" is already in
`HardlyRamified/Deformation.lean`; the duplicate compiles perfectly and is invisible
until somebody greps.
