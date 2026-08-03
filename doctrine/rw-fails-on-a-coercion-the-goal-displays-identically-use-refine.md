## `rw` FAILS ON A COERCION THE GOAL DISPLAYS IDENTICALLY — USE `refine Eq.trans`

(2026-07-31, `flt-lean-15`, proving `eq_two_or_eq_three_of_stableCyclic_of_autPoint_not_stable`
in `ModularCurve/X0.lean`. Three of five compile iterations went to this one trap.)

`Field.absoluteGaloisGroup ℚ` reaches `AlgHom` by more than one coercion path — via
`(σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom`, and via the `AlgHomClass`
instance directly. **Both pretty-print as `↑σ`.** So the failure reads:

    Tactic `rewrite` failed: Did not find an occurrence of the pattern
      (Point.map ↑σ) (ψ g)
    in the target expression
      (Point.map ↑σ) (ψ g) = k • ψ g

— the pattern and the target are *character-for-character identical on screen* and are
different terms underneath. Restating the step in the hypothesis's own syntax does NOT
help; a `have step : <hcomm's exact syntax> := by rw [hcomm …]` failed the same way,
because it is the ELABORATION that differs, not the source text.

**The fix is to stop using `rw` for that step.** `exact`, `refine` and `Eq.trans` unify
up to defeq, so they cross the coercion boundary for free:

    refine Eq.trans (hcomm (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) hσv g) ?_
    refine Eq.trans (congrArg ψ hk.symm) ?_
    exact map_zsmul ψ k g

Same trap, same cure, three more times in that one proof: `↑G` vs `g` after `set`
(fixed by `show _ = … • g`), an instance-level mismatch on `Module.finrank` inside
`LinearMap.det_smul` (fixed by `exact hdetscal _` instead of `rw [hfr]`), and
`(c • P).1` under a `Subtype.ext`. **Rule of thumb: when a rewrite fails and the printed
pattern equals the printed target, the terms differ by a coercion or an instance — switch
to a defeq-checking tactic rather than hunting for the right `simp` lemma.** Turning on
`set_option pp.explicit true` shows the difference if you need to see it.

Corollary, and it is why this cost so little in the end: **develop against a scratch
module.** Iterations on `Scratch15.lean` (one `public import`, ~120 lines) were **5
seconds** each; the same edits against `X0.lean` are a full rebuild of 82 000 lines. Five
iterations of blind coercion-fighting is a fine trade at 5 s and unaffordable at 30 min.

