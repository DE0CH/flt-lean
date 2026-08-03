## A CUT IS A HYPOTHESIS UNTIL YOU ASSEMBLE IT — and `∃` is the wrong shape for half of them
(2026-07-31, `TateModule.lean`, cutting step 3 out of
`exists_finset_abelianReductionDatum_of_mult`.) Decomposing a leaf produces sub-leaves
whose statements *look* like they fit the consumer. Re-reading does not check that.
**Write the assembly — the theorem that takes the sub-leaves plus the residual
obligation and returns the consumer's conclusion — and let the compiler check it.** It
costs one extra declaration, it is `sorry`-free by construction, and it converts "these
pieces should fit" into a receipt. It also itemises the residual obligation better than
any prose can: the assembly's remaining arguments *are* the work that is left.
The defect it caught here is invisible to reading and worth knowing in general:
**A lemma whose conclusion is `∃ f, P f` cannot be used to build a structure that lives
in `Type`.** `Exists.casesOn` eliminates only into `Prop`, so `obtain ⟨f, hf⟩ := lem`
fails with `recursor 'Exists.casesOn' can only eliminate into 'Prop'` the moment the
goal carries data. `IsAbelianReductionDatum` carries `gen`, `sp` and `frobPt`, so it is
in `Type`, and the existential form of the step-3 lemma was unusable for the one purpose
it was written for.
So: **when a decomposition lemma produces DATA that a structure field will hold, state it
non-existentially** — name the construction (`relPointTwist`) and state its property
about that name (`relPointTwist_fibre`). Keep the `∃` version as a one-line corollary if
consumers want it. `Exists.choose` also works but drags `Classical.choice` into a
definition that did not need it.
A second thing fell out of restating it that way, and it generalises: two structure
fields that looked independent (`gen_frob` at the generic fibre, `sp_frob` at the special
one) turned out to be **one lemma at two instantiations**, differing only in which
`j : O ⟶ κ` and which Galois element you feed it. If two axioms of a structure have the
same shape with different names, try to state one lemma and apply it twice before writing
two proofs.
