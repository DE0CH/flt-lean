## DERIVE ONE RIVAL CUT FROM THE OTHER BEFORE DELETING — the derivation is the receipt that the deletion is LOSSLESS
(2026-08-02, `flt-lean-92`, on `geomPic_exists_finiteCover_kummer` in
`ModularCurve/HyperellipticJacobian.lean` — the same orphan cluster the two
sections above are about, met a third time.)
When two rival cuts of one node both land, the sections above tell you how to
DETECT it (a parent whose docstring names a different leaf from its proof body; a
declaration whose only comment-stripped occurrence is its own) and how to avoid
deleting a REVIVED one.  Neither tells you what the loser's leaves are worth, and
`[[flt-both-rival-cuts-landed]]` says outright that the standing tie-breakers "do
not separate them".  **One thing does separate them, decisively and cheaply: try
to PROVE the loser's leaf from the winner's.**
Here the 2026-07-30 cut asked for a finite COVER of `Γ` on whose blocks every
Kummer cochain is constant; the 2026-07-31 recut asked instead for a finite-index
`H ≤ Γ` fixing a choice of `p`-division points, plus finiteness of `J[p]`.  The
cover statement is a **consequence** of the other two, in ~35 lines that compiled
first try in a **4.7 s** scratch:
* label `σ` by the pair `(σ H, the permutation it induces on J[p])` — both
  components live in a FINITE type, so the fibres of that labelling are a finite
  cover;
* `act σ` preserves `J[p]` because it is additive (`← map_nsmul`), and `J[p]` is
  finite by the winner's second leaf, so the label type really is finite;
* on a fibre, split `Q = Y P + (Q − Y P)`: the first summand is fixed the same way
  by `σ` and `τ` because they share a coset of `H` (`act_mul` plus `hYfix`), the
  second is `p`-torsion and they induce the same permutation of it.  Hence
  `act σ Q = act τ Q`, which is stronger than the cover clause asked for.
**What that buys is not a proof anybody wants — it is the receipt.**  "No
consumer" says the leaf is unreachable *today*; "it is a theorem of the survivors"
says it can never be needed *at all*, because everything it could ever supply
already follows from leaves that are in the cone.  So the deletion is lossless as
a matter of mathematics rather than of bookkeeping, and — the part that outlives
this cluster — **any future proposal to re-cut along the loser's axis is refuted
in advance**, which is what stops a resurrection loop from costing a dispatch
every time `semmerge.py` restores the block.
**Do it before you delete, not after**, and keep the derivation somewhere the tree
survives: a scratch that `public import`s the module and restates the loser under
a primed name costs seconds, and it must NOT be committed (a proven statement
nothing consumes is free-floating, which is exactly the defect you are removing).
Record the argument in the deletion note or here, in prose, so it can be
re-derived rather than re-discovered.
**When the derivation FAILS, you have learned the more valuable thing**: the two
cuts are genuinely incomparable, the loser carries content the winner does not,
and the deletion would lose it.  That is the case where the orphan should be kept
and re-pointed instead — and it is indistinguishable from the lossless case by
every name-keyed, consumer-keyed and count-keyed check in this file.
Corollary on what to COMMIT when a pending branch already did the deletion: be
CONCORDANT, not clever.  `flt-lean-26` had deleted these two the previous day on a
branch that is an ancestor of neither `main` nor `merger`, and the file had not
drifted between that branch's base and `main` — so `git cherry-pick -x <sha>`
reproduced it byte-exactly and the two branches now merge delete-against-delete,
which is trivial.  **Proving the leaf instead would have created a
modify-against-delete conflict reversing a decision two agents had already taken**
(the recut author in `50c80802`, then `flt-lean-26`), and that is the one shape a
merge worker cannot adjudicate without an author.  Check
`git merge-base --is-ancestor <sha> main` and `git diff --stat <base> main -- <the
files>` first; an empty drift is the licence to cherry-pick rather than re-do.
