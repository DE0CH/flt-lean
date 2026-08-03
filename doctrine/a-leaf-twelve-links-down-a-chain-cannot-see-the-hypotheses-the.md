## A LEAF TWELVE LINKS DOWN A CHAIN CANNOT SEE THE HYPOTHESES THE TOP OF THE CHAIN HOLDS — WALK THE CALL GRAPH UP AND DIFF THE BINDER LISTS
(2026-08-02, `flt-lean-84`, `exists_trace_discrim_isSquare_of_hilbertDeformationDatum`
in `HardlyRamified/HilbertModularity.lean`.) CLAUDE.md already records that *the
missing hypothesis is usually already in the caller's hand*. The instance that
matters most is the one where the caller is not the consumer but the TOP of a long
chain, and the hypothesis was dropped at link ONE.
That leaf carries only `F`-level data (`hirrF`, an `F`-level deformation datum,
`IsTotallyReal F`, `5 ≤ ℓ`). Its docstring correctly showed it FAILS whenever the
residual image lies in the normalizer of a Cartan subgroup, and correctly said no
group-theoretic proof can exist. What no pass had done is **walk the consumer chain
to its top and read the binder list there**:
    (★) → …_discrim_isSquare → …_charpoly_split → …TaylorWilesPrime{,Set}
        → injective_classifyingMap_hilbertHeckeDatum → …
        → exists_finiteIndex_isIntegral_charpolyCoeff_of_isHardlyRamified
The terminal theorem carries `hbar : IsHardlyRamified … ρbar` and
`hirr : ρbar.IsIrreducible` — the **ℚ-level** conditions — and discards both at its
first call, along with `[Finite k]`, `IsGalois ℚ F` and the `hw2` clause, each of
which survives a few links further and then dies. Over `ℚ` those hypotheses close
the obstruction outright; over an arbitrary totally real `F` nothing can. So the
leaf is not "hard", it is **stated without its input**, and the repair is a
threading, discharged at the top from hypotheses already present, with no consumer
outside the module changing.
**The check is one script and it should be run on any leaf priced as needing new
theory:** build the in-file consumer graph (comment-stripped, attribute each token
to its enclosing declaration, iterate `X ← consumers(X)` to a fixpoint), then print
the SIGNATURE of every declaration on the path. A hypothesis that appears at the top
and not at the bottom is a candidate repair, and it is far cheaper than the theory
the docstring is asking for.
* **Do the arithmetic of what each surviving hypothesis buys, precisely, and write it
  down.** Here `isTameAtTwo` was named by the docstring as "the only candidate", which
  is true and understates the problem: it gives exactly that inertia above `2` acts
  unipotently, hence trivially when the image is in a Cartan normalizer, hence that the
  representation is unramified outside `ℓ` and flat at `ℓ`. Over `ℚ` that contradicts
  irreducibility (level one, weight two); over a general totally real `F` it does not.
  "Names the right clause" and "delivers the conclusion" are different claims.
* **A chain whose links each forward a shrinking hypothesis list is where this happens.**
  Grep the chain for the hypotheses that appear at link *n* and not at link *n+1*; that
  set is the whole space of cheap repairs.
### PEEL THE PLANE GEOMETRY OFF SUCH A LEAF — it is ~150 lines and it is permanent
The same run banked the entire group-theoretic content as
`exists_end_det_one_trace_discrim_isSquare`: for an involution `J` of determinant `−1`
on a plane there is an explicit determinant-one `M` making
`(tr M ² − tr (J M) ²)(tr M ² − tr (J M) ² − 4 det M)` a nonzero square. The recipe,
reusable for anything that needs a witness in a `J`-adapted basis:
* `J ≠ ±1` because both have determinant `1` (`LinearMap.det_id`; `−1 = (−1 : k) • 1`
  and `LinearMap.det_smul` gives `(−1)^2 = 1`);
* eigenvectors WITHOUT any spectral theory: `J ≠ −1` gives `w` with `J w ≠ −w` and then
  `J w + w` is a nonzero `+1`-eigenvector; symmetrically `J w' − w'` for `−1`;
* `linearIndependent_fin2` plus `basisOfLinearIndependentOfCardEqFinrank` — note
  `Basis` is `Module.Basis` at this pin, so let `set` infer the type rather than
  ascribing it;
* then `Matrix.toLin`/`LinearMap.toMatrix_toLin`, `LinearMap.det_toLin`,
  `LinearMap.trace_eq_matrix_trace`, `LinearMap.toMatrix_mul`, `Matrix.mul_fin_two`,
  `Matrix.det_fin_two_of`, `Matrix.trace_fin_two_of`.
**And the arithmetic fact that decides the witness, which is worth knowing before
searching for one.** In the `J`-eigenbasis the product is `16 abcd`; writing `P = ad`,
`Q = bc`, a determinant-one `M` has `P − Q = 1`, so `abcd = PQ = Q² + Q`. Over `ℤ`
that is a perfect square only for `Q ∈ {0, −1}`, i.e. only when it vanishes — **so no
integer matrix works and a genuine division is unavoidable**. `Q = −4/3` gives
`Q² + Q = (2/3)²`, which is why the witness is `!![1, 2; 2z, z]` with `z = (−3)⁻¹` and
why a `3 ≠ 0` hypothesis appears from nowhere.
### A RECUT THAT STRENGTHENS THE LEAF MUST NAME THE CIRCUMSTANCE IN WHICH IT IS FALSE, AND THE ESCAPE HATCH
The residual leaf here is the Mazur–Serre big-image statement "every determinant-one
endomorphism is `ρbar|_{G_F}(g)`". That is STRICTLY stronger than what was replaced and
is **false as soon as `k` is strictly larger than the field of definition of `ρbar`** —
an image inside `SL₂(k₀)` for a proper subfield cannot be all of `SL(V)`, while the old
leaf only gets easier there (every element of `k₀ˣ` is a square in a quadratic
extension). Landing that silently would be the "leaf that is false is worse than one
that is open" failure.
What makes it acceptable is that the strengthening is **repairable in one line, and the
docstring says how**: the consumer's proof spends only the witness, whose four entries
lie in the PRIME FIELD, so the leaf may be weakened to "some `M` in the image with
`det M = 1` and `tr M ² − tr (J M) ² = 4(−3)⁻¹`" — implied by `SL₂(k₀) ⊆ image` in a
`J`-adapted basis, hence true whenever Mazur–Serre is, and still enough because the
final computation uses no basis at all. **When you strengthen a leaf, compute the exact
failure regime and write the weaker sufficient form into the docstring; a strengthening
whose escape hatch is recorded is a decision, one that is not is a trap.**
