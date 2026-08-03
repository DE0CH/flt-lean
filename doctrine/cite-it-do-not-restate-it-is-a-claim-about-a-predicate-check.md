## "CITE IT, DO NOT RESTATE IT" IS A CLAIM ABOUT A PREDICATE — CHECK THE PREDICATE, NOT THE NAME

(2026-08-01, `flt-lean-127`, cutting `tail_lt_head_coeff_sub_frickePartner_x1TwentyFive`
in `X1.lean`.) That leaf's docstring, and the task prompt generated verbatim from it,
listed two owed items and said of the second — Deligne's `‖aₙ‖ ≤ 2n` — that it is
*"SHARED with the `Γ₀` layer (`X0.lean`'s `norm_coeff_le_two_mul_self`) … **Cite it, do
not restate it**"*, and that *"closing it there closes it here"*. The name exists, the
theorem is real, and it is **not citable**: it is stated over `IsWeightTwoEigenform M g a`
with `g : CuspForm (Gamma0GL M) 2`, while what is in hand is
`IsWeightTwoEigenformOn (Gamma1GL 25) 25 χ f a` — a *different structure*, bridged
(`isWeightTwoEigenformOn_gamma0_iff`) only at `χ = 1`, which is exactly the case a
nebentypus cluster does not have.

**A `grep` for the name confirms the citation and says nothing about whether it applies.**
The check that does is one `sed` of the cited declaration's own binder list, comparing the
PREDICATE and the AMBIENT GROUP against yours. It costs ten seconds and it decides whether
your cut is `1 → 2` or `1 → 3`.

Two riders, both general:

* **A twin predicate is where this hides.** This tree deliberately carries `X`/`XOn`,
  `Γ₀`/`Γ₁`, base-specific/base-general pairs, with a bridge theorem that holds on a
  sub-case. A docstring written on one side names the other side's theorem because the
  MATHEMATICS is shared; the LEAN is not. Say which you mean.
* **"Closing it there closes it here" is then false, and the honest replacement is
  "these are one theorem at two generalities; whoever proves either should prove the
  general one and derive the other".** Write the second sentence, and state the new leaf
  with the SAME conclusion as its twin so the unification is a one-line corollary.

