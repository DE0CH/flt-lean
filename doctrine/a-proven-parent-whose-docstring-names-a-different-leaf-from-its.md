## A PROVEN PARENT WHOSE DOCSTRING NAMES A DIFFERENT LEAF FROM ITS PROOF BODY IS A DUPLICATE-CUT DETECTOR
(2026-07-31, `flt-lean-272`, `ModularCurve/RelativePicard.lean`.) The duplicate-cut sections
above give the shape — one node cut twice under two names, both kept by a merge, both counted
as ordinary open work by every instrument — and `tools/merge/dupstmt.py` for finding it. This
run found one that **all** of those missed, and the thing that gave it away is worth having as
a check of its own, because it costs one `grep` and needs no tooling.
`surj_of_isRelPicOverAffines` is PROVEN. Its docstring says, twice, that it is proven "over
`relPicEquiv_of_forall_restrict`". Its proof body calls `relPicEquiv_of_locally_relPicEquiv`.
Both exist, 60 lines apart, and they are the SAME STATEMENT — cut a day apart, kept by a
merge, differing only by `{L L'}` against `(A B)`, `_hL/_hL'/_hloc` against `_hA/_hB/_hcov`,
and one implicit-vs-explicit `strX`. The one the body calls is live; the other had **zero**
code uses anywhere in `Fermat/` and a queued task naming it.
**So when a proven declaration's docstring names the leaf it rests on, check that the PROOF
BODY names the same one.** A mismatch is not sloppiness: a docstring is written once, at the
moment of the cut, and cannot change under a merge, whereas the body is the half a merge
resolves. The mismatch is therefore *evidence about the merge*, and in this instance the two
names were the two halves of a duplicated cut. Same family as the class-7 interface split,
detectable from the prose rather than from a build.
* **A name-based duplicate scan cannot see this and neither could the statement-based one.**
  `dupstmt.py` normalises binder GROUPING and the leading `_`; it did not normalise binder
  ALPHA-RENAMING or explicit-vs-implicit brackets, which is exactly how this pair hid. It now
  has a third, weakest key (`DUP-STMT-ALPHA`) that also renames the top-level binders
  positionally AND the variables bound by `∀`/`∃`/`fun` inside the types — the last of those
  mattered, since the two copies agreed in every component except `∀ t : T` against `∀ x : T`.
  Calibration on the 2026-07-31 tree: with the pair present it reports that pair and nothing
  else. **Re-run the calibration when you touch it; a scan that reports nothing is
  indistinguishable from a scan that is broken.**
* **Do not delete the loser blind — read what its docstring has that the winner's does not.**
  Here the dead twin carried the `X = C ⊔ C` faithfulness witness and the `_o`/`Br T`
  discussion, neither of which is in the survivor. It was PROVEN by one application of the
  survivor, marked slated for deletion, and the fold-in named as the deleter's first job.
  That keeps the frontier drop (`−1`) without losing prose that nothing else records.

### `#print axioms` ON THE PARENT SPLITS THE TWO REPAIRS — and the orphan is a BLOCK, not a leaf

(2026-08-01, `flt-lean-349`, `Modularity/MoretBailly.lean`,
`exists_hypEvalData_of_birationalNormalForm`.) The section above says to check the parent's
proof body against its docstring. Two refinements, both measured, and each decides something
the grep alone does not.

**1. The mismatch has TWO causes with OPPOSITE repairs, and one command tells them apart.**
The parent may be proven over a *different open leaf* (a rival cut; the repair is to RE-ROUTE,
since one leaf usually implies the other), or proven *outright over nothing* (the repair is to
DELETE, since there is nothing to route to). Reading the body does not settle it — the call
you are looking for may be several lemmas deep. `#print axioms <parent>` settles it in one
line: `sorryAx` present ⇒ some leaf is still carrying it, go find which; absent ⇒ the parent
owes nothing and every leaf its docstring names is dead. Here it came back
`[propext, Classical.choice, Quot.sound]`, which is the whole of the argument for deletion.

**It runs from an IMPORTER in ~5 s** — a scratch that `public import`s the module — so it does
not need the declaring file and does not need a build. **Put a KNOWN-SORRIED declaration from
the same module in the same run as a CONTROL**: a clean answer and a check that is silently
looking at nothing are otherwise the same output. Mine printed `sorryAx` for the control on
the line below the three clean ones.

**2. The orphan is the leaf PLUS everything cut to serve it — compute the FIXPOINT.** Deleting
the named leaf alone is the obvious move and it leaves the worse half behind. A leaf cut out of
a parent normally arrives with a support block, and when the leaf dies the block dies with it —
silently, because the block is PROVEN and no frontier instrument looks at proven code. Here the
fixpoint over the in-file use graph, rooted at the leaf, returned **thirteen declarations and
294 lines, twelve of them proven**: the leaf, `hypEval` and its three projection lemmas, the
two span lemmas, the membership criterion `mem_span_pair_of_hypEval_eq_zero`, `coeffProj` /
`coeff_coeffProj` / `dvd_of_map_dvd_map`, and `hypQuotAway` / `hypQuotAway_apply`. Deleting only
the leaf would have left ~260 lines that read as live machinery to every future reader and that
nothing can reach.

The fixpoint is ten lines: mask comments, take each declaration's line range as up to the next
declaration, and iterate *"a declaration is dead when every occurrence of its name outside its
own range lies inside the dead set"*. Two cautions that decide correctness:

* **an `@[simp]` lemma is used without its name appearing**, so name-counting cannot prove it
  dead in general. It is safe here only because the simp lemmas being deleted are ABOUT a
  definition that is also being deleted, so no surviving goal can contain their pattern. Check
  that specifically; do not let the fixpoint decide it for you.
* **the dead range can straddle a `section`/`namespace` `end`.** Mine spanned
  `end LocalisedHypersurfaceMembership`, and deleting the range wholesale would have unbalanced
  the file — a scope wound, which reports thousands of lines away. Assert every boundary line by
  content before writing, and re-run a scope scan and a comment-depth scan afterwards.

**3. Say what did NOT happen.** The module's `sorry` count drops by one and no mathematics was
proven; a bare `−1` reads as progress on the citation the leaf named (here Schmidt Ch. VI §7).
Put that in the commit subject. And quote the recovery command with the *parent commit's* sha in
a note left where the block stood — the deleted docstring here carried a correct seven-step
worked route that is worth restoring if a future certificate leaf wants the criterion.

**4. A DELETION-ONLY branch is invisible to `semmerge.py`**, which propagates additions and never
deletions, so it can be silently reverted to a no-op with the merge reporting success. Say in
`to_merger` that the branch is a deletion and needs a plain `git merge`.

**RE-CONFIRMED 2026-08-02 in the same file, and the variant is worth one line: BOTH cuts
can still be `sorry`.** `IsRelPicZeroOf.listSum_map_post_eq_of_listSum_aj_eq` (morphism
form, equal degree) and `listSum_map_eq_of_relPicEquiv_divisor` (natural family, divisor
form) are two cuts of one node made the same day, ~120 lines apart, and the parent's
docstring named the first while its `by` block called the second. The section above reads
as though the survivor is a PROVEN theorem you delegate to; here the survivor was an open
leaf, and delegating to it is still the right move and still closes the orphan, because
**the survivor was strictly STRONGER** — arbitrary natural family, arbitrary pair of
lengths — so the orphan is an instance of it. Six lines, `101 → 100`.
Three riders. **Compare STRENGTH, not proof status**, when choosing which twin survives:
the stronger one is the one every consumer can be re-pointed at. **Check DECLARATION
ORDER before planning the delegation** — it only works because the survivor sits above
the orphan; the other way round it is a relocation in a contended file. And **the
hypotheses the delegation does not spend are the answer to a question the orphan's own
docstring usually asks**: this one said *"a prover who finds `_hpt` genuinely unused
should say so rather than delete it"*, and the measured answer was the opposite pair —
`_hpt` is spent, `_hlen` is not, because the divisor-form hypothesis carries the two
lengths on opposite sides and never needs them equal. Report that; it is the only part
of such a run that is new information rather than merge repair.
