## THE DEGENERATE OBJECT REFUTES EVERY UNGUARDED PERFECTNESS CLAUSE

(2026-07-31.) `exists_tateWeilRawFamily_of_qAdicWeilSystem` was refuted with no
arithmetic at all: take the ZERO abelian scheme, `A = S`, `f = 𝟙 S`.
`AbelianSchemeStruct` asks for a group law plus `IsProper`, `Smooth`,
`GeometricallyConnected` — **there is no nontriviality axiom in it**, and `𝟙 S`
satisfies all three, its fibres being points. Then every `RelPoint` is a
singleton, so `TatePt` is a singleton, so the ALTERNATING clause
(`C N t t ∈ 𝔪`) and the PERFECTNESS clause (`∃ t s, IsUnit (C N t s)`) are the
same statement about the same element and contradict each other. The two proven
consumers inherited the defect, because their conclusions carry a unit clause
too.

The general shape, worth running as a standing check: **any leaf whose
conclusion asserts a UNIT VALUE, a NONDEGENERACY, or a BASIS needs a hypothesis
that the object is nonzero, and that hypothesis is easy to lose in a cut** —
the geometric half of a decomposition keeps `hdim`, the arithmetic half gets
the pairing handed to it as a binder, and nobody notices that the pairing's own
axioms are vacuously satisfiable on the zero object. Here the finite-base
sibling had exactly the right hypothesis (`hne`) with the reason written on it,
and the characteristic-zero half had simply dropped it. **When two halves of a
development mirror each other, DIFF THEIR BINDER LISTS** — that is a
five-minute check and it found this one.

Corollary about audits: this leaf carried two 2026-07-30 falsity audits, both
CORRECT, neither of which saw it. They were about the normalisation, and they
presupposed a nonzero Tate module. CLAUDE.md's existing rule — a second
restatement VOIDS the earlier audit — is what prompted re-running it from
scratch, and it earned its keep.

