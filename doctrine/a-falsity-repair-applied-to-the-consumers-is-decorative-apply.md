## A FALSITY REPAIR APPLIED TO THE CONSUMERS IS DECORATIVE — APPLY IT AT THE TOP OF THE CHAIN, AND CHECK BY DELETING IT
(2026-08-01, `flt-lean-305`, `HopfAlgebra/ShortExact.lean`.) A leaf is refuted and the repair is a
new hypothesis. The repair is then applied to a *cluster* of declarations — and the one place it
must go is the one place it can be missed, because a chain's declarations are edited from the
bottom, where the consumers are, and the leaf is at the top.
`exists_lift_ker_le_span_cartierDual` was refuted on 2026-07-31 (`ℤ[√-5]`, `G' = μ₂`, `G'' = ℤ/4`)
and repaired with `[IsLocalRing R]`. The module header recorded the intention exactly — *"it and
the four statements above it in the chain now carry `[IsLocalRing R]`"* — and the instance landed
on the five statements **below** it. So the file's single open leaf, and the refuted declaration
itself, did not carry it.
**A hypothesis present on every consumer and absent from the leaf discharges NOTHING**, because
the derivations in between do not consume it — they just forward it. The refutation therefore
passes straight through the repaired consumers and back up into the leaf, which stayed FALSE for a
day while every instrument reported ordinary open work: green build, one `sorry`, correct warning
set, correct frontier scan, correct ownership checks, no duplicate, no cycle.
**THE CHECK IS ONE SCRATCH AND IT IS MECHANICAL: delete the new hypothesis and see whether the
chain still compiles.** Restate each consumer under a primed name with the instance removed and
its proof copied verbatim; if it compiles, the hypothesis is dead on that declaration and the
refutation is still live above it. Here that was two consumers, 80 lines of copy-paste, and
**8 seconds** — against a refuted leaf that had already drawn one dispatch. Do this every time a
falsity repair adds a hypothesis to more than one declaration; an unused instance binder on a
theorem produces no linter warning, so nothing else will tell you.
**The tell, and it is in the docstring rather than the code: an EQUIVALENCE claim beside a
REFUTED sibling.** This leaf's own FAITHFULNESS section said *"equivalent to the statement it
replaces — Nakayama one way, `le_sup_left` the other — hence neither stronger nor weaker than
`exists_basis_cartierDual` **for any base**"*. Every word true, and it is precisely the transport
that carries the counterexample from the sibling into the leaf. An equivalence is a two-way street
for refutations as well as for proofs, so a paragraph asserting equivalence to something that has
just been refuted is not reassurance — it is the proof of danger, and it reads as the opposite.
When you refute a declaration, **grep its neighbourhood for "equivalent"** and check each hit.
Three riders:
* **Say which end of the chain you repaired, in the commit and in the docstring**, naming the
  declarations. "The chain now carries `[IsLocalRing R]`" is not checkable and was, here, false.
* **Adding a hypothesis cannot break a faithfulness audit in the other direction** — it only
  shrinks the instance class — so the re-audit is short: everything the old audit certified at the
  *restricted* base survives verbatim, and only its claims about the excluded bases are withdrawn.
  Write that sentence; an audit labelled "inherited" with no argument is the failure mode this
  file already records.
* **The frontier does not move, `1 → 1`, and nothing became provable.** What changed is that the
  file's one open obligation is TRUE rather than refuted. Report it that way — a restatement that
  leaves the count alone is otherwise indistinguishable from a no-op, and this one is the
  difference between a dispatchable leaf and an agent sent to prove something false.
