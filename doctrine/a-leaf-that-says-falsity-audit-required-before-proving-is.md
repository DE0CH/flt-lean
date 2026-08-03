## A LEAF THAT SAYS "FALSITY AUDIT REQUIRED BEFORE PROVING" IS USUALLY FALSE — AND NOT IN THE WAY ITS AUTHOR GUESSED
(2026-08-02, `flt-lean-242`, on items (5c) and (5d) of the obstruction audit in
`HardlyRamified/Deformation.lean`. Two leaves, two audits, both came back POSITIVE, and
**neither failed along the axis its own audit named**.)
This development has a convention — a leaf whose author could not check it writes
`FALSITY AUDIT — REQUIRED BEFORE PROVING` into the docstring and names what to check. That
line is worth far more than it looks, and it is systematically not acted on: it reads as
housekeeping, so successors treat the leaf as ordinary open work and go looking for a proof.
Both of these had stood for two days with the audit unrun. **Run it first; it is cheaper than
one build cycle and it decides whether there is a task at all.**
**And do not let the audit's own guess bound your search.** Both audits asked the same
question — *does the statement need the residual datum named?* — and that was not what killed
either leaf:
* **(5d) died on the residue characteristic**, which the docstring had explicitly and (on its
  own terms, correctly) declined to constrain: "the place is `2`, so `ℓ` does not enter — if a
  proof needs it, that is a signal the statement is wrong". The signal was real and pointed the
  other way. The witness is `ℤ/16 ↠ ℤ/8` with the SCALAR representation `δ ⊗ id`,
  `δ(Frob) = 3`: `3² = 1` in `ℤ/8`, and the two lifts `3, 11` both square to `9 ≠ 1` in `ℤ/16`,
  so the tame quotient character cannot lift. Repair: `IsUnit (2 : S)`.
* **(5c) died on SATISFIABILITY of its own conclusion**, with no arithmetic involved at all.
  `IsFlatAtLocal τ` demands a bijection between `Fin 2 → S` and the `ℚ̄_v`-points of a
  finite flat group scheme — a FINITE set — so for any `S` with an infinite open-ideal quotient
  the conclusion is unsatisfiable while every hypothesis holds. Witness:
  `S = TrivSqZeroExt k M` with `M` infinite, `R = k`, `ρv` trivial.
Three checks fall out, in the order they pay:
1. **ASK WHETHER THE CONCLUSION CAN HOLD AT ALL before asking whether it is provable.** A
   conclusion that quantifies over a structure with a finiteness, freeness or nondegeneracy
   clause is unsatisfiable for legitimate instances of an unconstrained hypothesis. This is the
   cheapest refutation there is and it needs none of the leaf's mathematics.
2. **TEST THE STEP THE DOCSTRING CALLS FREE.** (5d)'s own route note said the character lifts
   "with no choice to make and no obstruction". Writing that step out is four lines
   (`(w(1+j))² = w² (1+2j)`, solvable for `j` iff `2` is invertible) and it is where the leaf
   dies. An author writes "unobstructed" about the step they did not do.
3. **REFUTE WITH A SCALAR OBJECT when the conclusion mentions a CHOSEN line, quotient or
   flag.** `ρ = u ⊗ id` satisfies such a clause for *every* choice, so the refutation assumes
   nothing about which one a putative lift picks — which is exactly the escape route that kills
   most first attempts at these witnesses. (Mine died twice before this: an upper-triangular
   `ρ` lets a lift twist the diagonal character and escape.)
**And check that your witness refutes the leaf you think it does.** The `ℤ/16` witness kills
(5d) and does NOT kill (5c): the scalar `δ ⊗ id` *does* lift to `ℤ/16`, by `δ̃ ⊗ id` with
`δ̃(Frob) = 3` of order `4`; the lift is again unramified, hence again flat, and fails only
`δ̃² = 1`, which (5c) does not ask for. Instantiate the witness against the surviving
hypotheses AND against the conclusion, per the standing rule; here that took ten minutes and
changed the verdict on one of the two leaves.
**The refutation is worth formalising even when one input stays classical.** The engine —
*a tame lift of a scalar representation forces the tame character to reduce to the scalar,
hence `u` to lift to a square root of `1`* — is 30 lines, uses no arithmetic of `ℚ₂`, no
topology and no hypothesis on `ψ`, and is now `sq_eq_one_of_isTameAtTwoLocal_lift_of_scalar`.
With the `ℤ/16` arithmetic settled by `decide`, the whole counterexample is machine-checked
except for "`ℚ₂` has an unramified quadratic extension". Say exactly which step is classical;
a refutation with one named classical input is a decision the next reader can check, and a
prose witness is not.
**Iteration note, measured.** A scratch module that `public import`s the target's own built
`.olean` and restates the new declarations under primed names ran at **8–10 seconds** against
a ~20-minute build of the 26 000-line module. The entire refutation — engine, arithmetic,
`IsSmallExtension` for `ℤ/16 ↠ ℤ/8`, and the assembled counterexample — was developed in six
such rounds and transplanted into the real file unchanged. Two pin traps met on the way:
`isUnit_of_mul_eq_one` does NOT exist here (use `isUnit_iff_exists_inv`), and there is no
`IsLocalRing (ZMod n)` instance in mathlib — prove it by `decide` through
`IsLocalRing.of_isUnit_or_isUnit_one_sub_self`, after supplying `Fact (1 < n)` for
`Nontrivial`.
