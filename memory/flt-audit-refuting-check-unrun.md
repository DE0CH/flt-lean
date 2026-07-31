---
name: flt-audit-refuting-check-unrun
description: An audit that names its own refuting check has probably not run it — grep for the named lemma before believing the verdict or queueing its advertised spin-off
metadata:
  type: project
---

`smoothOfRelativeDimension_finrank_cuspForm`'s ATOMICITY AUDIT (2026-07-28,
`FreyCurve/MazurTorsion.lean`) named its own refuting check — "a base-change
lemma for `IsJacobianOf` … refutes the verdict" — and advertised that lemma as
the one spin-off worth dispatching alone, "genuinely separable and much smaller".
`Fermat.isJacobianOf_baseChange` had been in `ModularCurve/X0.lean` since
2026-07-27, **the day before**. Three days and two agents passed before anyone
ran the grep.

**Why:** writing the refuting check down feels like discharging it. It is
simultaneously the cheapest work in the task and the least likely to have been
done — and unlike an ordinary stale audit, this one was wrong *when written*.

**How to apply:** when a docstring names the check that would refute it, run that
check FIRST, before reading the rest. Before queueing anyone at an advertised
spin-off, grep the tree for the spin-off's own name — it is a hypothesis about
the tree, not a fact. When authoring an audit, state whether the check was RUN,
with the command and the date; "Refuting check: X" reads as "X is absent".

Related: the general form is [[flt-base-change-into-vs-out-of]] — maps INTO an
object base-change for free, maps OUT need Weil restriction, so the fix is to
change the PRESENTATION, not to prove the lemma. See also
[[flt-inventory-audits-understate-what-exists]] and
[[flt-leaf-cost-estimates-are-hypotheses]].
