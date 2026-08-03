## TWO LEAVES OVER ONE STRUCTURE CAN BE JOINTLY INCONSISTENT — refute the PAIR, and you need not decide which is false
(2026-08-02, `flt-lean-67`, on `CyclicSubgroupOfOrder.geom_cyclic` in
`ModularCurve/X0.lean`.)  A structure `S` that under-specifies its object
poisons its leaves in a shape no single-leaf audit can see, and the cheapest
refutation does not require settling the hard question the audit got stuck on.
The cluster had two leaves over `RigidifiedModuliSchemeData`, whose `universal`
field makes `M` represent the functor of `Gamma0Datum`s:
* `exists_rigidifiedModuliSchemeData_of_isUnit` — `∃ M, …` (an inhabitant);
* `isAffine_rigidifiedModuliSchemeData_of_isUnit` — `∀ M, IsAffine M.M`.
`CyclicSubgroupOfOrder` pinned the CARDINALITY of the geometric fibres of the
level subgroup and not its RANK, so at characteristic `p ∤ N` the functor
admitted `C₀ + ker F^k` for every `k` — rank `N·p^k`.  Rank is locally
constant, so any representing `M` splits as `⨆_k M_k` with every piece
nonempty, hence is not quasi-compact, hence **not affine**.  So the two leaves
contradict each other, and *neither one alone looks wrong*.
**The move that makes this cheap: you do not have to decide whether the
enlarged functor is representable.**  The recorded audit had stalled exactly
there ("what is NOT established is that the enlarged functor is
*non*-representable"), and it is a genuinely hard question.  It is also the
wrong one.  Either the functor is representable and the `∀` leaf is false, or
it is not and the `∃` leaf is; a disjunction of two falsities is a refutation
of the cluster, and the repair — to the structure — is the same in both
branches.  **When an under-specification audit stalls on "but maybe the bigger
thing is still fine", look for a second leaf that asserts a PROPERTY of the
bigger thing.  Quasi-compactness, finiteness, affineness, dimension and
connectedness are the ones that break first, because the junk is separated
from the honest objects by a locally constant invariant.**
**A `∀ (M : SomeStructure), P M` leaf is only as true as the structure is
SMALL, so its refuting check must ask what ELSE inhabits the structure.**  The
check actually recorded on the affineness leaf was *"exhibit two inhabitants
that are not isomorphic as schemes"* — a check on the wrong axis, which would
have found nothing, because the inhabitants ARE all isomorphic and the
statement was false anyway.  The `∀`-shaped junk-witness worry that this file
documents at length is about the structure being too WEAK to pin its object;
this is the same defect one level out, where the structure is too weak to pin
the CLASS, and no amount of rigidity between inhabitants detects it.
### `ker F^k` IS THE UNIVERSAL JUNK SUBGROUP SCHEME IN CHARACTERISTIC `p`
The earlier audit guessed that refuting this would need the supersingular
locus, "where the subgroups of `E[p^k]` of a given rank with trivial geometric
points move in a positive-dimensional family".  It does not, and the guess is
what made the question look expensive.  **The kernel of the `k`-th relative
Frobenius is finite locally free of rank `p^k`, is a closed subgroup scheme
over ANY `𝔽_p`-base, needs NO hypothesis on the curve** (it is `μ_{p^k}` at an
ordinary fibre and `ker F^k` at a supersingular one, uniformly), **and has no
points over any field** — it is `Spec` of a local artinian algebra with the
base's residue field, so every field-valued point factors through its closed
point.  One object per `k`, defined over the whole base, already gives
infinitely many pairwise non-isomorphic inhabitants.
So: **any clause phrased as "the geometric fibres have exactly `N` points" is
blind to a factor of `ker F^k`, at every base of positive characteristic.**
Check for that before believing a fibre-cardinality clause pins a rank.  Over a
`ℚ`-scheme it does, by Cartier — which is why such clauses survive review: they
are correct at the base the development evaluates and false at the base a later
leaf generalises to.  A justification of the form *"a finite flat group scheme
is étale, so its rank equals the number of geometric points"* is CIRCULAR:
Cartier needs the ORDER invertible, and the order is what is not pinned.
### A LOCAL REPAIR CANNOT FIX A FUNCTOR — and "route 2 remains unexplored and unneeded" is the sentence to re-read
The same defect had been found at a leaf in 2026-07-27 and repaired the cheap
way: `[AlgebraicGeometry.Etale (c.ι ≫ f)]` threaded as a hypothesis through the
seven declarations whose PROOFS needed it, with a note recording that
strengthening the structure itself "remains unexplored and unneeded".  That
repair is correct and it cannot reach the representability leaves, because
there the offending object is universally quantified **inside the conclusion**
of an `∃!` — there is no binder to hang a hypothesis on.
**So the discriminator between "hypothesis on the leaf" and "field on the
structure" is not taste: it is whether the object is in the leaf's BINDER LIST
or in its CONCLUSION.**  A defect that shows up in both places must be repaired
at the structure, and a note saying the structural route is unneeded was
written by someone who had only seen the first kind.
### THE ENGINEERING TRICK THAT MADE IT A PRODUCERS-ONLY DIFF
Adding a field to a structure in a 116 000-line file sounds like a whole-file
refactor.  It is not, if the field is a `Prop`-valued CLASS:
    structure Foo … where
      …
      etale : AlgebraicGeometry.Etale (ι ≫ f)
    instance (c : Foo …) : AlgebraicGeometry.Etale (c.ι ≫ f) := c.etale
Every pre-existing `[AlgebraicGeometry.Etale (c.ι ≫ f)]` binder is then
**redundant rather than broken** — satisfied automatically at every call site —
so not one consumer had to be touched.  The diff is the structure, the
instance, and the PRODUCERS.  Here that was four producers (one base change,
free by stability under base change; one torsion construction, free from an
existing `etale_torsionFst`; and two copies of one span construction), plus one
new named leaf for the span, and **X0 built green on the first attempt**.
Two riders.  Enumerate the producers by grepping for a NAMED FIELD of the
structure (`grep -rn "geom_cyclic :=" Fermat/`) rather than for the structure's
name — the type name appears in hundreds of consumers and in prose, the field
name appears in producers only.  And check for anonymous constructors
(`⟨…⟩`) before choosing where in the field list to insert: with none, position
is free and the field can go where it reads best.
