## A DEAD HYPOTHESIS CAN BE THE ONLY THING BLOCKING A ROUTE — grep the binder through the WRAPPER CHAIN

(2026-08-02, `flt-lean-267`, on `weilValue_self_config_eq_one` in
`EllipticCurve/WeilPairing.lean`.)  This file already says a hypothesis an audit calls
unused is free strength, and that an unused binder costs a prover nothing.  Both are
about hypotheses that are HARMLESS.  There is a third case, and it is the expensive one:
**a dead hypothesis on a PROVEN theorem can make that theorem inapplicable at exactly the
value its consumer needs**, and then it is not decoration — it is a wall, and nothing
reports it.

`translationChar_setup_value` proves the value law `B = c^e·A`, `e ∈ {1, p−1}`, where
`A`, `B` are character-for-character the two products of the open leaf's own `hA`/`heq`
— i.e. it proves `z = c^e` and the leaf is exactly `c = 1`.  It carried
`(hc1 : c ≠ 1)`, so it could not be used at `c = 1`, which is the only value the
alternation branch cares about.  `hc1` was DEAD: it occurred once, in the binder list of
`exists_millerRatio_eval_translationChar_of_avoid`, and was forwarded unused through two
wrappers.  Deleting it is a pure weakening; the chain rebuilt green, and a leaf that two
route analyses had priced at a chapter of Silverman became one equation.

**The check is one grep per binder and it is not the linter's.**  Lean's
`unusedVariables` fires on the declaration that OWNS the binder, so it flags
`_of_avoid` — and says nothing about the two wrappers that forward it, which are where a
consumer meets it.  Follow the binder by NAME down the chain instead:

    grep -n '\bhc1\b' <each file in the chain>      # binder + every forwarding call site

A binder that appears only in signatures and in forwarding argument lists, never in a
proof body, is dead in ALL of them.  Then ask the question the linter never asks: **is
there a value of that variable which a consumer needs and the hypothesis excludes?**  If
yes, removing it is the whole task.

Two riders:

* **Removing a dead hypothesis changes ARITY, so it is an interface edit** — the class-7
  hazard.  Do it in its own commit, list the call sites (here six: three binders and three
  forwarding argument lists), and check that the sites which genuinely USE the hypothesis
  keep it (here `weilValueProp_translationChar_witness`, whose nondegeneracy branch really
  does need `c ≠ 1`).  `grep` for the name afterwards and read every survivor.
* **The dead binder is usually a fossil of the FIRST consumer.**  This chain was built for
  the nondegeneracy branch, where `c ≠ 1` is genuinely in hand, so it was passed along out
  of habit; the alternation branch is the second consumer and is the one it locks out.
  When a proven theorem is "almost" what a leaf needs, diff its binder list against what
  the leaf can supply before concluding the theorem is the wrong tool.

