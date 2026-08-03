## A RECORDED "THIS CUT IS IMPOSSIBLE" REFUTES ONE SPLIT, NOT ALL SPLITS — look for a PINNING clause
(2026-07-31, `exists_fundamentalCharacter_of_semistabilityDefect`, node `A₀-3b-i`.) A leaf whose
conclusion is `∃ x, P x ∧ Q x` invites the obvious split: leaf 1 produces an `x` with `P x`; leaf 2
takes such an `x` as a HYPOTHESIS and proves `Q x`. That split is FALSE whenever `P` fails to
determine `x` — leaf 2 must then prove `Q` for EVERY `P`-satisfying witness, and `Q` typically holds
only for the intended one. This node carried a careful, correct, explicit counterexample to exactly
that split (`N = 29`, `e = 4`, `ψ' = ψ_L^15` is surjective and satisfies `ψ'^e = χ|_J`, yet no
`ψ'^r` with `r ≤ e` equals `λ|_J`), together with a note that strengthening `P` to "`ψ` generates
the character group" does not repair it. A prior agent read that as a proof the node is ATOMIC and
made no change.
**It is not. The counterexample refutes splitting along `P`; it says nothing about splitting along a
DIFFERENT clause.** The repair is not a stronger PROPERTY of `x` but a clause that PINS it — a
defining property with at most one solution, satisfied by the intended witness. Here that was the
compatibility that DEFINES the level-one fundamental character,
    ∀ σ ∈ J, ∃ τ ∈ I_N, τ^e σ⁻¹ ∈ P_N ∧ ψ σ = χ τ,
whose uniqueness proof is two lines (the tame quotient is torsion-free, so `e·τ̄ = e·τ̄'` forces
`τ τ'⁻¹ ∈ P_N`), which kills the recorded witness on sight (it would force `ψ_L^14 = 1`), and which
turned one atomic node into two citable leaves: local-field theory with no curve in it, and
Raynaud's classification with no tame theory in it.
The checklist when a split is blocked by a witness-ambiguity counterexample:
1. Ask what **defines** the intended witness, not what is **true** of it. A defining property is
   usually a compatibility with something already named in the statement — not new vocabulary.
2. Prove the pinning clause has at most one solution and put that argument in the docstring. It is
   the whole of what makes the second leaf faithful, and the only thing a reviewer must check.
3. Re-run the recorded counterexample against the new clause and say in the docstring that it dies.
   The old counterexample is still TRUE and must be KEPT, relabelled as refuting the old cut only.
Expect the pinning clause to be strictly harder to prove than the property it replaces (it was here:
it needs the tame quotient torsion-free, not merely procyclic). That is the right trade — it moves
work off the unprovable side onto the provable one.
