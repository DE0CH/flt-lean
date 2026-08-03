## A ROUTE THAT NEEDS A *COUNT* USUALLY DOES NOT — CORRECT THE GENERATORS YOU WERE GIVEN, DO NOT EXTRACT NEW ONES
(2026-08-02, `flt-lean-367`, `exists_span_range_eq_of_span_union_pderiv_mem` in
`HardlyRamified/ModThree.lean`.)  A leaf whose conclusion is *"there are exactly `h`
generators of `I`, all lying in some distinguished subset `S`"* invites the classical
route, and this one's docstring wrote it out: pass to `R̄ = R/3R`, bound `μ(Ī)` BELOW by
Krull's height theorem (`ht Ī = dim R̄ − dim B̄ = h`) and ABOVE by the old generators,
extract a minimal generating set from `S̄`, lift, Nakayama.  That is dimension theory of
power series rings — none of it at this pin — and it is the whole reason the leaf was
priced as hard.
**The count is never needed, because the leaf already HANDS you `h` generators.**  Do not
extract a new family from `S`; CORRECT the old one into `S`, one generator at a time.  The
correction lands in `𝔪·I`, and Nakayama discards exactly that:
    Pᵢ = Σₖ a_{ik} sₖ  (sₖ ∈ S)   ⟹   P'ᵢ := Σₖ C(constantCoeff a_{ik}) · sₖ ∈ S
    Pᵢ − P'ᵢ = Σₖ (a_{ik} − C(constantCoeff a_{ik})) · sₖ ∈ 𝔪·I
    I = span (range P) ≤ span (range P') + 𝔪·I   ⟹   I = span (range P')
`Fin h` is preserved **by construction** — there is nothing to count — and the whole
proof is `Submodule.mem_span_set'` plus ONE application of
`Submodule.le_of_le_smul_of_le_jacobson_bot`.  Measured: ~200 lines against an unbounded
theory build, and the four helper lemmas are elementary.
**The two conditions, and both are usually free in this development.**
* **`S` must be an additive subgroup closed under multiplication by CONSTANTS** — not an
  ideal, which is exactly why it looked as if one had to extract from it.  Here
  `S = {f ∈ I | ∀ j, ∂f/∂Xⱼ ∈ (3)}`: closed under `+` because `∂` is additive, and under
  `C c ·` because `∂(C c · f) = C c · ∂f`, while `∂(a·f) = (∂a)f + a(∂f)` escapes it.
  Whenever a leaf's distinguished set is cut out by a DERIVATION, a trace, a valuation
  bound or any other additive condition, it has this shape.
* **The coefficient subring must reach the residue field.**  In `MvPowerSeries σ 𝒪` with
  `𝒪` local this is free and needs no computation of the residue field at all:
  `a − C(constantCoeff a)` has zero constant coefficient, hence is a non-unit by
  `MvPowerSeries.isUnit_iff_constantCoeff`, hence lies in `𝔪_R`.  Same for a polynomial
  ring, a monoid algebra, or any graded ring with `R₀` local.
**So the standing check, before costing any "minimal generating set / Krull height /
`μ(I) = h`" step: does the leaf's hypothesis list already contain a family of the right
size?**  If it does, the count is a property of THAT family and is not yours to re-derive.
The tell in the docstring here was explicit and read as a warning rather than as a gift —
*"the count `μ(Ī) = h` is what forces the new generating set to have exactly `h` members
and hence keeps `P'` indexed by `Fin h`"* — which is true of the route that DISCARDS `P`
and false of every route that keeps it.
Rider on the leaf's own hypothesis list: `hfon` (the Fontaine hypothesis), `hloc`, `hsurj`
and `Module.Finite` turned out to be unused; only `Module.Flat`, `hidem`, `hker` and `hb`
are load-bearing.  Keep them (a signature change is a merge hazard for no gain) and SAY SO
in the docstring — a successor must not infer anything about `IsFontaineAlgebra` from its
presence.
### Two mathlib pieces this needed, both easy to miss
* **`Submodule.le_of_le_smul_of_le_jacobson_bot`** (`Mathlib/RingTheory/Nakayama.lean`) is
  the form of Nakayama that fits `I ≤ N + 𝔞·I ⟹ I ≤ N` directly, with no quotient module
  and no `⊥`-shaped restatement.  That file has eight Nakayama variants; read the list
  before rolling your own.
* **`Module.Flat.isSMulRegular_of_nonZeroDivisors`** (`Mathlib/RingTheory/Flat/TorsionFree.lean`)
  is "flat + `r` a nonzerodivisor of the base ⟹ `r` is a nonzerodivisor on the module".
  Transporting it across a quotient by an IDEMPOTENT ideal `J = (ε)` needs no
  decomposition `A ≅ A/(ε) × A/(1−ε)` and no direct-summand theory — four lines suffice:
  `3a = εx` gives `3εa = ε²x = εx = 3a`, so `3(a − εa) = 0`, so `a = εa ∈ (ε)`.
