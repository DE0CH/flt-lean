## A COUNTEREXAMPLE IS ONLY AS STRONG AS THE HYPOTHESIS LIST IT WAS TESTED AGAINST

(2026-07-31, flt-lean-110.) `exists_hilbertFixing_rootsOfUnity_discrim_isSquare`
carried a FALSITY AUDIT that three independent passes had confirmed — an explicit
elliptic curve, an exhaustive matrix enumeration, and a by-hand derivation, all
agreeing. I re-verified all three a fourth time (Python enumeration, PARI/GP on the
curve) and they are right. The leaf IS false as stated.

The audits were nevertheless leading the repair in the wrong direction, because
none of them asked **which hypotheses the witness spends that the leaf does not
state but its CONSUMERS do.** Here the witness forces `det ρ̄(Γ F) = {1}`, hence
`Γ F ⊆ ker χ̄_ℓ`, hence `F ⊇ ℚ(ζ_ℓ)` — so **`F` is totally imaginary**. And
`NumberField.IsTotallyReal F` is exactly what the eventual consumer carries, and is
already threaded as an instance binder through 2 800 lines of the same file.

So the refutation is of *the leaf as stated*; the leaf-plus-`htr` is untouched by
it. The two repairs that follow differ by an order of magnitude — threading one
plain hypothesis through eight signatures, discharged at the top, versus a
coefficient-field enlargement `k ↝ k(√d)` rethreaded through a definition whose
Selmer clause would have to move to `k'` — and the audit had recorded only the
expensive one as "forced".

The rule: **before accepting that a leaf needs a structural repair, diff its
hypothesis list against its consumers', and check the witness against the
difference.** A leaf is routinely stated more generally than any call site needs,
and a counterexample living in the gap refutes only the generality. The cheap
repair — push the consumer's hypothesis down to the leaf — is invisible unless
that diff is taken, and it is a move this development has already made
successfully at least once in the same file.

Corollary, for whoever writes the audit: **say which hypotheses your witness
satisfies, not merely that it satisfies "every hypothesis".** All three passes
here truthfully verified every clause the leaf states, and that is precisely why
the gap survived three reviews — the check they each performed cannot see it.

