## WHEN A CUT ABSORBS A CONSTANT, EVERY OTHER CLAUSE MUST BE INVARIANT UNDER THE TRANSLATION IT ABSORBED

(2026-07-31, `flt-lean-306`, the Atkin–Lehner half of the `X0.lean` Hecke cluster —
the second cut of that cluster in one day, and the reason the first one deliberately
stopped short.)

The move is now a standard one here: a leaf binds an existential correction
`e` because its witness is only pinned up to something, and a later cut REMOVES `e`
by absorbing it into the choice of the witness — `exists_heckeCorrespondenceFamily`'s
`(c, e)` became `exists_heckeCorrespondenceMorphism`'s bare `κ`, the constant going
into a translation `κ ↦ κ ≫ τ`. That is a real simplification and it is correct.

**The trap is the OTHER clauses.** Absorbing `e` does not delete the freedom it
represented — it hides it. The witness is still determined only up to the translation
`κ ↦ κ + δ`, so **every clause of the new statement must be blind to `δ`**. A clause
that is not is pinning something the datum does not determine, and it is FALSE for
exactly the reason the pre-absorption statement was false.

**CORRECTION AND SHARPENING (2026-08-01, `flt-lean-73`, running this check on the `Γ₁`
twin): "every clause must be blind to `δ`" is over-stated, and read literally it
condemns every correct cut of this shape.** The statement is an EXISTENTIAL over `κ`,
so if no clause saw `δ` the statement would determine nothing and would be satisfied by
any translate — the absorbed constant would not have been absorbed, only discarded. The
rule that is actually true, and that the section's own worked example obeys:

> **AT MOST ONE clause may see `δ`, and it is the clause that FIXES the translate.
> Every OTHER clause must be blind to it.**

So the check has a per-clause verdict with THREE outcomes, not two: *invariant* (fine),
*sensitive and it is the pinning clause* (fine, and necessary), *sensitive and it is not*
(the defect). On the `Γ₀` Atkin–Lehner leaf there were two clauses, the recipe (pinning,
sensitive) and the equivariance — and the equivariance in naive form was the third case,
which is what made it false. On the `Γ₁` twin, which has the recipe and nothing else, the
recipe is sensitive and there is nothing for it to disagree with, so the cut is safe; a
reader applying the over-stated rule would have rejected a correct statement.

**And the clause you must check is absent, not merely present-and-invariant.** What makes
dropping `e` legitimate is that the parent's base-point clause `c o = 0` is GONE. Carry it
over as `post κ o = 0` — invariant under nothing, and the obvious thing to keep, since it
looks like a harmless normalisation — and it plus the recipe force `ε = 0`, i.e. exactly
the parent's pre-repair defect, in a statement that has no constant left to blame. So run
the check over the clauses you DELETED as well as the ones you kept, and record in the
docstring which deletion is load-bearing.

Concretely, the clause here was `w_J (c x) = c (w x) − c (w o)`. Its two candidate
morphism-form readings look equally natural:

    (naive)      w_J (P x)         = P (w x) − P (w o)          -- FALSE
    (invariant)  w_J (P x − P o)   = P (w x) − P (w o)          -- TRUE

Translate `P ↦ P + δ`: the right-hand side is a difference of two values of `P`, so
`δ` cancels; the naive left-hand side gains `w_J δ` and the invariant one does not.
So the naive form silently demands `w_J δ = 0` for the `δ` that the recipe cannot
see — and unwinding, it is equivalent to `ε = 0` for the very base-point defect
`ε = T_ℓ[o] − (ℓ+1)[o]` whose non-vanishing refuted this cluster on 2026-07-29
(`N = 37`, `ℓ = 2`, `o` non-cuspidal). **The same witness refutes the new statement,
one restatement later, in a form nobody would recognise as the same defect.**

The check is mechanical and costs a minute of algebra, so run it every time:

1. name the symmetry the removed existential was absorbing (here: translation of `κ`);
2. apply it to each surviving clause, both sides;
3. any clause whose two sides transform differently is wrong — repair it by
   normalising the offending side against the SAME datum the other side uses
   (here: subtract `P o`, which is what the parent's `c` already was).

Two corollaries worth having:

* **A clause built out of DIFFERENCES of the witness's values is automatically
  invariant.** That is why the fix is always available and why it is never a
  weakening: `P x − P o` is exactly the parent's `c`, so the invariant form is the
  parent's clause transcribed, not a new statement.
* **Invariance is also what keeps the glue cheap.** The invariant form reduced to the
  parent's clause by abelian-group algebra alone, with no additivity of
  `RelPoint.post wJ hwJ` — an additivity that IS derivable from the character
  hypothesis but only through `isAdditiveOn_of_post_zero`, i.e. by moving a genuine
  obligation into what was supposed to be reduction glue. A cut whose glue starts
  needing real theorems is usually the non-invariant cut.

And the standing rule this instantiates, from the section above on two
individually-correct edits: **a second restatement VOIDS the first audit.** The
2026-07-30 audit that added `e` certified a statement that no longer exists once `e`
is absorbed; it does not transpose, and reading it as covering the new form is how the
naive clause would have shipped.

