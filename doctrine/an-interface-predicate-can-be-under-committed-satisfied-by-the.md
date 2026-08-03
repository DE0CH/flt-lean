## AN INTERFACE PREDICATE CAN BE UNDER-COMMITTED: SATISFIED BY THE WRONG NORMALISATION

(2026-07-31, same cluster, and it is the subtler half.) `IsTraceDualFunctional`
pins a functional `θ : O → ℤ_q` by four clauses, and
`exists_traceDualFunctional_of_adicPin` PROVES it, so it looks settled. It was
not: at a RAMIFIED `I` the four clauses are satisfied by `θ_m = Tr(δ π^m ·)`
for EVERY `0 ≤ m ≤ e-1`, not only by the correct `m = 0`. Consequences:

- the third clause's hypothesis ("`φ` kills `I^k`") was one the intended input
  never satisfies — the Weil functional kills `I^{e·k}` — so the clause was
  dead at every positive level, and the leaf whose whole route it is could not
  be started;
- every constant it could return lay in `(jπ)^{(e-1)k}`, hence was a NON-UNIT,
  hence could never satisfy the consumer's perfectness clause.

**The producer was already correct** — it builds `θ` as a GENERATOR of
`Hom_{ℤ_q}(O, ℤ_q)`, which is `m = 0` on the nose — so strengthening the
statement cost its proof nothing. One `have hNk : k ≤ N` was deleted, and it
was the line that had been throwing the extra strength away.

The lesson generalises past this file: **when a leaf's prescribed route "just
does not work", check whether the INTERFACE it routes through is weaker than
the object that satisfies it.** A predicate proven inhabited is not thereby
adequate; ask what ELSE inhabits it. The mechanical test is a scaling family —
perturb the intended witness by a unit, a uniformizer power, a twist — and see
which clauses still hold. If a wrong scaling survives every clause, the
predicate cannot support any conclusion that needs the right one.

Related trap in the same vocabulary, since it cost a false start: a
"perfect pairing `𝒪_D/I^k × O/(jπ)^k → ℤ_q/q^k`" gloss in a docstring can be
WELL-DEFINED-FALSE while the formal clauses beside it are true. `Tr(δ I^k 𝒪)`
is `q^{⌊k/e⌋}ℤ_q`, not `q^k ℤ_q`, so that pairing does not descend at all for
`e ≥ 2`. Read the CLAUSES, not the gloss.

