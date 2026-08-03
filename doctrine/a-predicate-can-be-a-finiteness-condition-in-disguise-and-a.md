## A PREDICATE CAN BE A FINITENESS CONDITION IN DISGUISE — AND A SMOOTHNESS LEAF THEN CONCLUDES IT WITHOUT MEANING TO
(2026-08-02, `flt-lean-123`, refuting `exists_flatLocalLift_of_isSmallExtension` in
`HardlyRamified/Deformation.lean` — Ramakrishna's smoothness of the flat local
deformation condition.)
A liftability/smoothness leaf has the shape *"`P` holds over `R`; along a small
extension `ψ : S ↠ R` produce a lift over `S` with `P`"*. Everybody audits `P` as a
condition on the OBJECT. **Audit it twice more, as a condition on the COEFFICIENT
RING**, and each of the two questions can refute the leaf on its own:
1. **WHAT DOES `P` FORCE ABOUT THE RING?** `GaloisRep.IsFlatAt`/`IsFlatAtLocal` says the
   space is equivariantly bijective to the geometric points of the generic fibre of a
   FINITE flat Hopf algebra — so the space is FINITE, so `A ⧸ I` is finite at every open
   ideal. The leaf's CONCLUSION therefore asserts that `S` is pro-finite for its own
   topology, and its hypotheses said nothing that could imply it. An infinite DISCRETE
   `S` makes the conclusion unsatisfiable for **every** `τ`, so the leaf was FALSE.
2. **WHEN IS `P` VACUOUS?** The same predicate quantifies over the open ideals of the
   coefficient ring. If the only open ideal is `⊤` — true for the indiscrete topology on
   any ring, and for the ORDINARY topology on any non-discrete FIELD (`ℚ_p`, `ℝ`, `ℚ`),
   whose only ideals are `⊥` and `⊤` with `⊥` open iff discrete — the hypothesis carries
   no arithmetic at all and the leaf asserts liftability from nothing.
Both halves are cheap Lean (~90 lines total, first compile) and together they are a
COMPLETE refutation whose witness needs no arithmetic: `S = R = ℚ_p`, `ψ = id`, with the
DISCRETE topology on the source and the usual one on the target. `IsSmallExtension` is
immediate because the maximal ideal of a field is `⊥`.
**The finiteness half was much cheaper than it looks, and the reason generalises:**
`Finite.algHom` (`Mathlib/LinearAlgebra/FreeModule/Finite/Matrix.lean`) makes
`M →ₐ[K] L` finite from `[Module.Free K M] [Module.Finite K M] [IsDomain L]` — **no
separability, no étaleness, no `IsAlgClosed`**. Over a field the freeness is automatic
and `Module.Finite.base_change` is an instance, so "finitely many geometric points" is
`inferInstance`. Whenever a predicate's witness is a Hom-set out of a finite algebra,
its cardinality is one `inferInstance` away and does not need the theory the predicate
advertises.
**AND THE AUDIT'S OWN "WHAT TO CHECK" LINE POINTED AT THE WRONG AXIS.** The 2026-07-31
docstring asked whether the missing hypothesis was the RESIDUAL DATUM (a `ρbar` over `k`,
plus Mazur-category structure), recorded a judgement that it was not needed, and was right
about that for the wrong reason: with the topology hypothesis restored, the residual
representation is *recovered* from the leaf's own quantifier (`𝔪_R` is one of the open
ideals, so the reduction is flat and no `ρbar` need be carried). The axis that mattered —
the TOPOLOGIES — is not mentioned anywhere in the audit it prescribes. This is the
standing "an audit names the author's search, not a property of the statement" rule with
a new tell: **when a predicate is defined by quantifying over the open ideals of a ring,
the topology IS a hypothesis of every statement that mentions it, and a statement that
never constrains it is almost certainly false.**
Corollary for the repair, and it is what keeps a restatement honest: state the fix as the
weakest binders that kill the specific counterexamples (`[CompactSpace S]` for defect 1,
`IsAdic (𝔪 R)` for defect 2, `IsAdic (𝔪 S)` for the third pathology the two do not
cover), and then CHECK EACH IS DISCHARGED AT THE CALL SITE before committing —
`HardlyRamifiedDeformation` carries `isAdic` as a structure field and
`compactSpace_of_isAdic_of_pi` (proven in the same file) turns it into `CompactSpace`, so
this restatement weakens the leaf and narrows nothing.
