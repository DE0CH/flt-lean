## An audit that NAMES its own refuting check has probably not RUN it
(2026-07-31.) `smoothOfRelativeDimension_finrank_cuspForm`'s ATOMICITY AUDIT
(2026-07-28, `FreyCurve/MazurTorsion.lean`) closed with *"Refuting check for both
clauses, and it is cheap: a base-change lemma for `IsJacobianOf` … refutes the
verdict"*, and separately advertised that very lemma as **the one spin-off worth
dispatching on its own** — "a genuinely separable and much smaller task, and the
one piece of this leaf a successor could land independently".
`Fermat.isJacobianOf_baseChange` had been in `ModularCurve/X0.lean` since
**2026-07-27 — the day before the audit was written** — a complete `IsJacobianOf`
with three fields proven outright and the fourth discharged by
`universal_jacobianBaseChangeAj`. One `grep` refutes the verdict. Three days and
two agents later, nobody had run it.
**This is a different failure mode from a stale audit.** A stale audit is wrong
because the tree moved under it. This one was wrong *when written*, and wrong in
the one place its author looked hardest — because writing the refuting check down
feels like discharging it. The check is simultaneously the cheapest work in the
task and the work least likely to have been done.
So: **when a docstring names the check that would refute it, run that check
FIRST, before reading the rest of the docstring.** It costs one `grep` and it
decides whether the task exists at all. And before queueing anyone at an
advertised spin-off, `grep` the tree for the spin-off's own name: an advertised
spin-off is a *hypothesis about the tree*, not a fact about it, and the audit's
author was by construction not looking for it — they were looking for reasons the
leaf was hard.
**Corollary for AUTHORS of audits.** An audit that names a refuting check must say
whether the check was RUN and what it returned, with the command and the date.
"Refuting check: X" reads to every later agent as "X is absent". Write "ran
`grep …` on 2026-07-28, zero hits", or do not write the check at all.
**Second corollary, and it is the general form of the same day's finding.** When a
universal property fails to base-change, the question is never "can someone prove
the base-change lemma" but "which PRESENTATION of the object is being
base-changed". Fields about maps **INTO** `J` transport for free —
`Hom_{S'}(T, J ×_S S') ≅ Hom_S(T, J)` is the defining adjunction of the fibre
product. Fields about maps **OUT of** `J` do not: maps out of a base change are
`Hom_S(J, Res_{S'/S} A')`, i.e. Weil restriction, which needs `S' ⟶ S` finite
locally free and which **does not exist anywhere at this pin** (`grep -rn
"WeilRestriction\|weilRestriction"` over mathlib and over `Fermat/`: zero hits in
both). That is why `IsCoarseModuliY0` two of three clauses base-change and
initiality does not (`X0.lean`'s `SpecialFibreCoarse` subsection), and why
`IsJacobianOf`'s `aj`/`aj_pre`/`aj_base` do and `universal` does not. The
resolution both times was the same and it is worth reaching for directly:
**replace the universal property by the representability presentation** —
`Gamma0AtlasData` there, `IsRelPicZeroOf` (`ModularCurve/RelativePicard.lean`)
here — every field of which is about maps into the object, so it base-changes by
inspection.

### SECOND CONFIRMED INSTANCE, AND THE GENERALISATION: N BLOCKERS DECAY INDEPENDENTLY, SO RE-RUN ALL N

(2026-08-01, `flt-lean-355`, on `smoothOfRelativeDimension_finrank_cuspForm` — the
very leaf whose audit the section above uses as its example. Three days later the
audit was still being dispatched verbatim, and by then **all three** of its axes
were stale, not just the one recorded above.)

The section above records that this audit's *refuting check* for axis 2 fires
(`isJacobianOf_baseChange`, X0.lean:78018, ~34 000 lines above the leaf). Two
further clauses had rotted meanwhile, each by somebody else's unrelated work:

* axis 1's *"no genus of a scheme, no `h¹(𝒪_X)`, no Riemann–Roch exists here, so
  the middle term of the split cannot be written down"* — refuted by
  `Fermat/FLT/Mathlib/AlgebraicGeometry/CurveGenus.lean`, created 2026-07-31 and
  `public import`ed by `X0.lean` at line 1062;
* the leaf's own headline, *"the place the `Modularity` subtree is meant to be fed
  in"* — refuted by `finrank_cuspForm_eq_x0Genus` becoming PROVEN, which makes the
  leaf's conclusion **literally the same proposition** as a modular-form-free one.

**The generalisable rule: an audit that lists N independent blockers is N separate
dated claims, and they expire on N independent clocks. Re-run every one of them,
not the one that looks likeliest.** The instinct is to check the blocker you have
an idea about; the leaf becomes attackable when the LAST one falls, so the ones you
skip are exactly the ones that decide it. Cost here: four `grep`s, about ten
minutes, against an audit three agents had inherited without re-running.

**Corollary, and it is the part that changed what could be delivered: when one of
the halves of a bridge becomes PROVEN, the leaf holding the other half should be
RESTATED to spend it.** `dim J_0(N) = dim_ℂ S_2(Γ_0(N))` and
`dim J_0(N) = x0Genus N` are interchangeable the moment `dim_ℂ S_2 = x0Genus` is
proven — so the leaf can be re-stated with every mention of `ℂ`, `CuspForm` and
`Gamma0GL` deleted, at `1 → 1` and with the faithfulness audit transferring
verbatim (the two conclusions are the same proposition under the shared `0 < N`,
so a counterexample refutes one iff it refutes the other). The count does not move
and must be reported as not moving; what changes is that the residue no longer
requires its prover to know any modular-forms theory. **Grep a leaf's docstring for
the phrase "where subtree X feeds in" and check whether X has already fed in.**

