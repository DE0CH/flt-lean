## A CITATION LEAF CAN BE A CITATION ONLY BECAUSE ITS PRODUCERS DISCARD CLAUSES THEY ALREADY ESTABLISH
(2026-08-02, `flt-lean-54`, `X0.lean`. Frontier −1, no new mathematics, 28 s to verify.)
`isAffine_rigidifiedModuliSchemeData_of_isUnit` was a `sorry` leaf carrying the
parenthesis of Katz–Mazur (8.1.1). Its own docstring, under **"What the prover of this
node owes"**, contained the complete proof:
> `M(𝒮) = Y(n) ⊗ R` is affine by (4.7.2) … the `Γ₀(N)`-problem is affine, indeed
> **finite**, over `(Ell)` by (6.6.1) … and a scheme finite over an affine scheme is
> affine. **That last step is NOT a citation and is available in the pin.**
Both inputs are established INSIDE the two leaves above it, and both were thrown away by
their CONCLUSIONS: `FullLevelModuliSchemeData` had no `IsAffine M` field although (4.7.2)
says "a smooth **affine** curve `Y(n)`", and `exists_relativeGamma0ModuliOverFullLevel`'s
existential had no finiteness conjunct although (6.6.2) says "**finite** and flat". Adding
one field and one conjunct — each a clause of a citation those leaves already carry, so
**free to their still-open provers** — turned the third leaf into two applications:
build the affine inhabitant, then transport along the already-proven rigidity iso
(`IsAffine.of_rigidifiedModuliSchemeData`).
**This is the standing "THAT THEOREM HANDS BACK X is a claim about its CONCLUSION" rule
read in the direction that CLOSES a leaf rather than blocking one.** The recorded version
warns a CONSUMER not to believe a docstring about what an upstream theorem exports. The
productive reading is the opposite: when a leaf's docstring derives it from clauses of
OTHER leaves' citations, check whether those leaves EXPORT the clauses — and if not, add
them. The standing rule (*a `sorry` leaf's conclusion may be strengthened for free when
the new clause is part of the citation it already carries*) makes it cost nothing.
**The check is mechanical and worth running on any leaf whose docstring says "and that
step is not a citation":**
    for each input clause the docstring names, grep the producing declaration's
    CONCLUSION (not its docstring) for that clause; a clause named in the prose and
    absent from the type is a free strengthening
**Two disciplines that made it safe.** Keep the old statement as a WRAPPER — the assembly
moved to `exists_affine_rigidifiedModuliSchemeData_of_isUnit` and the original
`exists_rigidifiedModuliSchemeData_of_isUnit` became a one-line `.elim` over it, so all
three call sites were untouched and no consumer could regress. And verify DIFFERENTIALLY
with a PREFIX SCRATCH: `head -<end of your edit>` plus the closing `end`s elaborates the
whole edited region in **28 seconds** against ~45 minutes for the 119 k-line file, and
comparing its `sorry` warning set against the same prefix of `git show HEAD:<file>` gives
the receipt — here `{5998, 6770, 6882, 7130}` became `{5998, 6781, 6893}`, a single
constant shift of `+11` (the lines the new field's docstring added) and one deletion.
**Rider on the direction NOT to go.** The same cluster invites dropping `IsUnit (N : R)`
to reach the base `ℤ[1/n]` where Katz–Mazur state (4.7.2). That is the mirror move and it
is WRONG: `CyclicSubgroupOfOrder.geom_cyclic` is the NAIVE cyclic condition, so at `p ∣ N`
in characteristic `p` a supersingular curve admits no datum at all and (6.6.1) — a
Drinfeld statement — does not apply. **Strengthening a `sorry` leaf's CONCLUSION with a
clause of its own citation is free; weakening its HYPOTHESES is a new claim.** The two
look alike and only one of them is bookkeeping.
