## A REDUNDANT HYPOTHESIS IS WORTH DROPPING WHEN IT IS **DERIVABLE** AND **CONTAINED**
(Same run, on `pow_dvd_log_valuation_of_exists_fixed_rootOfUnity_of_not_forall_commutator_fixed`
in `Interface.lean`.) This file already says to KEEP a hypothesis you cannot justify
— *"it costs the prover nothing and cannot make the leaf false; deleting it is the
move that can go wrong"*. That advice is about a hypothesis that **might be needed**,
and following it blindly at one that provably cannot be is the wrong call. Two tests
separate the cases, and both are cheap.
**1. Is it DERIVABLE from the surviving hypotheses?** If so, the statement with it
and the statement without it IMPLY EACH OTHER, and the distinction that matters is
one people conflate: here the PROPOSITIONS `hnab` and `hncomm` are genuinely
inequivalent (`hncomm` is strictly stronger — that was the point of the narrowing
that introduced it), while the THEOREMS are equivalent, because `hncomm` together
with `hfix` yields `hnab` in one line through a PROVEN lemma. **Dropping a derivable
hypothesis is therefore not a restatement in the sense that voids an audit** — every
audit transfers verbatim, in both directions. Say so explicitly, or the next reader
will re-run the falsity audit for nothing.
**2. Is the edit CONTAINED?** `grep -rn` the two declaration names tree-wide,
comment-stripped, and count the call sites. Mine came back as exactly two
declarations and two call sites, all inside one file inside a thousand-line window —
so the class-7 interface-split hazard, which is the real argument for leaving
redundant binders alone, simply did not apply. Had a consumer been in another module
I would have left it.
What tipped it from cosmetic to worth doing: the redundant binder was costing the
top-level caller **three lines of inline derivation to manufacture an argument
nothing reads**, and the file CONTRADICTED ITSELF about it — one docstring bullet
called the redundancy deliberate while the narrowing note and the consumer's own
docstring both said the binder "has been replaced". A union merge had kept both
notes and both binders. **Two notes in one file disagreeing about a binder is the
tell**; reconcile it in writing wherever you land, because leaving the contradiction
is what guarantees the next owner re-opens the question.
Receipt to demand of yourself for a change like this, since it touches a proven
theorem: same `EXIT=0`, same job count, **same `declaration uses 'sorry'` count in
both directions**, and a message-keyed diff of the whole warning set that comes back
EMPTY. Mine did (16 → 16 and 37 → 37, zero warning-set delta), which is what makes
"logically equivalent" a checked claim rather than an argument.
