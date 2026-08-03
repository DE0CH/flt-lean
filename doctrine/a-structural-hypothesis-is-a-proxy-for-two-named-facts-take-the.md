## A STRUCTURAL HYPOTHESIS IS A PROXY FOR TWO NAMED FACTS — TAKE THE FACTS, AND EVERY BASE AT WHICH IT FAILS INHERITS THE DEVELOPMENT
(2026-08-02, `flt-lean-294`, recutting `exists_gamma0AtlasOver_bcQuotient_specLocSpecial`
in `X0.lean`.)  A theorem whose hypothesis is a broad structural property — `Module.Flat`,
`IsField`, `PerfectField`, `IsNoetherianRing`, `IsDomain` — almost never uses that property
directly.  **Grep its own proof for the hypothesis and read every hit.**  In this development
the answer is repeatedly ONE or TWO lines, each a call to a named lemma; and then
> restating the theorem over those lemmas' CONCLUSIONS, with the original kept as a
> two-line wrapper, is strictly additive, changes no signature, cannot break a consumer,
> and hands the whole development to every sibling base at which the property FAILS.
Measured here: `InvariantBaseChange.exists_unique_of_isPullback` carried `[Module.Flat k K]`,
and its own module docstring already said *"flatness is consumed in exactly one place"*.  It
was two — `isInvariant_tensor` and `injective_bcInclusion` — and both produce statements about
the base-changed triple (`B ⊗ K` is the invariant subring of `A ⊗ K`; the inclusion is still
injective).  Those two ARE what Katz–Mazur (8.1.6) is about, and Remark (8.1.7)'s
counterexamples at `p = 2, 3` are counterexamples to them and to nothing geometric.  So the
flatness-free version is the honest theorem, the flat one is its corollary, and the
non-flat consumer — the special fibre `ℤ_(ℓ) → 𝔽_ℓ` of an integral model, i.e. exactly the
base change (8.1.6) does not cover — now owes only commutative algebra.
**THE HALF THAT MATTERS MORE, AND IT IS WHY THE SIBLING LEAF HAD BEEN STUCK: the hypothesis
was also bundling a TRANSLATION LAYER that never used it.**  `bcQuotient_of_flat` is three
formal steps (identify the classifying map with the quotient map; convert a moduli
non-separation hypothesis into `G`-invariance; get the base-point clause from a second
application) wrapped around ONE call to the flat theorem.  **None of the three knows what the
base is** — its own docstring said so, in bold — and yet a leaf at a base where flatness
fails could not reach them, because they existed only inside a theorem that demanded it.
Naming the middle (`BcQuotUniversal`) and proving `bcQuotient_of_bcQuotUniversal` at an
ARBITRARY base morphism deleted the entire modular-to-GIT layer from the leaf.
**So the check, whenever a leaf is "the twin at another base" of a proven theorem:** read the
proven theorem's PROOF and ask whether it is *hypothesis-free glue composed with one
hypothesis-consuming step*.  If it is — and in a development that separates "the modular
half" from "the GIT half" it usually is — the recut is to name the glue, prove it at an
arbitrary base, and expose the step.  The count does not move; what leaves the leaf is
everything the glue was carrying.  Here that was `Gamma0AtlasOver`, `BcQuotient`,
`Gamma0Datum`, `RelPoint` and `IsBaseChangeOf`, and the residue is one line of GIT.
Three riders, each of which cost or saved real time:
* **A docstring's "flatness is consumed in exactly one place" is a COUNT, and counts rot.**
  It was two.  Both were in the same file, ten lines apart.  Re-grep before quoting.
* **A hypothesis used only to derive another hypothesis should be dropped, not kept.**
  `exists_unique_of_isPullback`'s `[Algebra.IsInvariant B A G]` and `hinj` fed
  `isInvariant_tensor`/`injective_bcInclusion` and nothing else, so the general version has
  neither — three hypotheses replaced by two strictly weaker ones.
* **Take the algebra structures as INSTANCE ARGUMENTS plus their two defining equations,
  rather than reading them off with `Spec.preimage` inside a `letI` chain.**  The `letI`
  version cannot be lifted into a STATEMENT without dragging `IsScalarTower` and
  `SMulCommClass` proofs into it; the instance-argument version has one `letI` left (matching
  `isInvariant_tensor`'s own idiom) and a caller constructing the object has all of it in
  hand.  That decision is what made the last-mile bridge writable at all.
**And the throughput note, because it is a 80× ratio.**  X0 is 119 000 lines and rebuilds in
**580 s**; a scratch that `public import`s its already-built olean and restates the new
declarations under primed names ran in **7 s**, and all four new declarations — including a
120-line transplanted proof — compiled there FIRST TRY and moved into the file unchanged.
Seeding made it possible at all: `git diff --stat $(cat ~/.flt-release-lake/sha) HEAD -- Fermat/`
was EMPTY, so `rsync -a --delete ~/.flt-release-lake/build/ .lake/build/` took **14 seconds**
and made X0's olean current instead of rebuilding it to start work.  Run that diff first,
always; when it is empty the snapshot is not a cache, it is the answer.
