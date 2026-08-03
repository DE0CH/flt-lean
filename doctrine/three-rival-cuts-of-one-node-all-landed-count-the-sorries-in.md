## THREE RIVAL CUTS OF ONE NODE, ALL LANDED: COUNT THE SORRIES IN THE BLOCK, THEN FUSE — the peels are on DIFFERENT AXES and combine
(2026-08-02, `flt-lean-93`, the Abel's-theorem block of `ModularCurve/X0.lean`.)  The
section above says two rival cuts can be complementary and should both be banked.
The same thing happens with THREE, it is worse, and the resolution is better than
"bank both": **build the leaf that dominates all of them and every rival becomes a
corollary.**  Frontier `3 → 1`, in one run, with no mathematics done.
The block carried three `sorry`s cut out of one node on three different days:
| leaf | what it peeled | consumers |
|---|---|---|
| `listSum_map_eq_of_relPicEquiv_divisor` | `Pic⁰` out of the HYPOTHESIS (divisor form) | 1 — **LIVE** |
| `…listSum_map_post_eq_of_listSum_aj_eq` | naturality out of the CONCLUSION (morphism form), + equal degree | **0** |
| `…listSum_map_eq_of_listSum_aj_eq_of_compactSpace` | nothing; the original + `[CompactSpace T]` | **0** |
**Every one of the three docstrings claimed to be the leaf its consumer rested on.**
Only the first was, and the thing that says so is the consumer's PROOF BODY — the
already-recorded detector, firing three times in one 300-line block.  Two of the
three were phantom dispatch targets; one of them drew this task.
**THE CHEAP DETECTOR, and it is a different question from "is my leaf owned":** count
the open leaves in the enclosing block and read each one's consumers.  Three `sorry`s
within 300 lines, whose docstrings each cite the same classical theorem, is not three
obligations — it is one node cut three times.  One comment-stripped reverse-dependency
scan settles which are orphans, and it must be SUFFIX-AWARE (`X.foo` is reached as
`h.foo`), or dot-notation call sites are invisible and every leaf looks dead.
**THE FUSION TEST: do the peels touch DIFFERENT PARTS OF THE STATEMENT?**  Hypothesis
vocabulary versus conclusion vocabulary versus a side condition are independent axes,
and a cut on one axis says nothing about another — which is exactly why two careful
agents produced two "better" statements neither of which dominates.  When the axes are
disjoint, the fused statement takes every peel at once and each rival is a one-liner
over it.  When they are not (both weaken the same hypothesis), you are choosing, not
fusing, and the tie-breakers in the section above apply.
**KEEP THE LIVE ONE'S NAME, BINDERS AND POSITION; DELETE THE ORPHANS.**  The live leaf
becomes PROVEN over the fused leaf, so its consumer never moves and no signature
changes — the class-7 interface split cannot arise.  The orphans, once proven, are
consumerless PROVEN theorems, i.e. free-floating, which this project forbids: delete
them and fold their analysis into the survivor's docstring.  Here that analysis was
most of the value in the block (the missing primitive shared with a Hecke leaf, a
re-checked pin absence, a second classical route sharing its subtree with a sibling
leaf, and the one extra input that route needs); a deletion that drops it is a loss
even though the count improves.
**AND THE BOOKKEEPING A LOSING CUT'S DOCSTRING SAYS IS "NOW WRITTEN" MAY NEVER HAVE
LANDED.**  The morphism-form cut's docstring had a section headed *"WHAT THE TWO
REDUCTIONS BELOW DISCHARGE, i.e. what a prover no longer writes … free is not the same
as written, and they are now written."*  Neither reduction was in the file: the merge
kept that branch's LEAF and the other branch's rewritten consumer body, so the
reductions went with the body.  Both had to be written here, and both were cheap —
which is the point.  **Grep for the reduction, do not believe the paragraph.**
### The two reductions, because they recur wherever a leaf is stated on a functor of points
* **YONEDA IS ALREADY PROVEN AND IS CALLED `pre_self`.**  A natural family
  `c : ∀ {T} (g : T ⟶ S), RelPoint f g → RelPoint astr g` plus its naturality
  hypothesis IS postcomposition with the single morphism `(c f ⟨𝟙 C, _⟩).1`.  Three
  lines, over `RelPoint.pre_self` in `Modularity/AbelianSchemeIsogeny.lean` — a lemma
  filed under a name sharing no keyword with anything in the consumer's vocabulary.
  So **a leaf carrying a natural family and a naturality hypothesis is over-stated**:
  restate it with a morphism and the hypothesis disappears.
* **PADDING A LIST WITH THE BASE POINT IS THREE SHORT LEMMAS, NOT "a real chunk of
  tensor bookkeeping".**  To drop an equal-length hypothesis, cons the base point on
  and note it multiplies BOTH sides of the divisor comparison by the same ideal sheaf
  — one associator, one braiding, one `relPicEquiv_tensor_left`.  `List.replicate
  (k+1) b ++ l` is `b :: (List.replicate k b ++ l)` DEFINITIONALLY, so the induction
  step has nothing to transport, and `le_total` plus `relPicEquiv_symm` covers both
  directions.  The whole chain compiled first try.
**Say in the commit that the count moved and the mathematics did not.**  A `−2` that
proves nothing reads like a theory gap closing; what it actually buys here is that the
survivor is now the same SHAPE as a sibling leaf blocked on the same missing primitive
(the trace of a finite locally free morphism on the functor of points), which turns a
standing "build it once, not twice" recommendation from aspiration into something an
owner can act on.  That, not the delta, is the argument for the work.
### THE DETECTOR IS NOW A SCRIPT: `tools/merge/orphanleaf.py`, 39 s, and 37 of 378 leaves are candidates
A check worth re-running every release is a script, not a paragraph — so the sweep
above is one.  `python3 tools/merge/orphanleaf.py` scans every sorried declaration
under `Fermat/` and reports the ones with **no code occurrence anywhere outside their
own declaration**.  Measured on `8695a922`: **378 sorried declarations, 37 orphan
candidates** — about one open leaf in ten may be dead.  It needs no build and no
oleans, and `--root` defaults to the repo the script lives in rather than to a
hardcoded staging path.
**Every hit is a CANDIDATE, and the list is a REVIEW list, not a gate.**  It is a
token scan, so it cannot see a name reached only through `simp`/`aesop`/instance
search.  Confirm with one `grep -n`, and read the parent's PROOF BODY rather than its
docstring — the docstring is what is wrong in these cases.  Two hits were confirmed by
hand here (`exists_veryAmpleSystem_of_isAmpleSheaf`, `geomPic_hilbert90`), and the
sweep independently rediscovered the four `HyperellipticJacobian` orphans an earlier
agent had recorded in this file, which is the corroboration that the method works.
**It had THREE bugs before it was right, all silent, and all worth knowing because the
same three are latent in any name-matching scan over this tree:**
* **dot notation** — `X.foo` is reached as `h.foo`, so matching must be on the LAST
  COMPONENT and the regex must not exclude a preceding `.`.  With `.` in the negative
  lookbehind, every dot-notation call site is invisible and the scan reports roughly
  double;
* **explicit universe parameters** — `theorem foo.{u, v}` makes a naive name regex
  capture `foo.{u,`, whose last component matches nothing.  Ten `Patching.lean`
  declarations were reported as orphans for exactly this.  (`tools/merge/frontier.py`
  has the same trap, already recorded above.);
* **the token PRE-FILTER used to make it fast** — tokenising on `alnum _ ' .` makes
  `foo.{u, v}` yield the token `foo.`, with a TRAILING DOT, which equals neither `foo`
  nor anything ending in `.foo`; so the filter rejected the consumer's own file and the
  declaration was reported as an orphan anyway.  `exists_traceGenerated_auxDeformationDatum`
  IS consumed and was reported dead by two successive versions because of it.
**So calibrate after every change: run with the pre-filter removed and require the two
lists to be IDENTICAL.**  Here that is 37 = 37, against 39 s with the filter and ~25
minutes without — which is the whole reason the filter is there, and the whole reason
it has to be checked.
