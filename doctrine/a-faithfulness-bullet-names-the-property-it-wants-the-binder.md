## A FAITHFULNESS BULLET NAMES THE PROPERTY IT WANTS; THE BINDER MAY BE STRICTLY WEAKER — DIFF THE PROSE AGAINST THE SIGNATURE
(2026-08-02, `flt-lean-115`, `exists_genRelPic` in `Modularity/GeneralisedPicard.lean`.)
This development writes a FAITHFULNESS section on every mature leaf, one bullet per
hypothesis, of the form *"`hfoo` — `X → S` is P, **which is what gives** Q"*. The bullet is
the author's account of WHY the hypothesis is there, and it is written in mathematical
English while the binder is written in Lean. **The two can name different properties, and
when they do, the leaf is usually FALSE — because the argument in the docstring is correct
and the statement does not supply its input.**
Here the bullet said *"`hproper`, `hflat`, `hgi` on `strX` — `X → S` proper flat with
geometrically **integral** fibres, which is what gives `f_*𝒪_X = 𝒪_S` universally"*, and the
signature said `hgi : GeometricallyIrreducible strX`. `GeometricallyIrreducible` is
`geometrically (IrreducibleSpace ·)` — a condition on the geometric fibres as TOPOLOGICAL
SPACES — and **mathlib records the gap itself**:
    GeometricallyIntegral.eq_geometricallyReduced_inf_geometricallyIrreducible :
      @GeometricallyIntegral = (@GeometricallyReduced ⊓ @GeometricallyIrreducible)
so "integral" is "irreducible" plus exactly the reducedness the signature omitted. Without
it `f_*𝒪_X ≠ 𝒪_S`, invertible sheaves acquire automorphisms, and the naive functor of
rigidified pairs is not even a separated presheaf — while `surj`/`inj` assert it is
represented by a scheme, i.e. that it IS a sheaf. Refuted by `X = Spec k[ε]` over
`S = Spec k` with `Z` the reduced point (every hypothesis holds: finite hence proper, free
hence flat, one-point geometric fibres hence irreducible, `ι ≫ strX = 𝟙`), tested against
any `T` with `H¹(T,𝒪_T) ≠ 0`.
**The check is two greps and belongs on every faithfulness bullet you read or write:**
1. **Take the noun in the prose and the class in the binder, and ask whether they are the
   same class.** `integral`/`irreducible`, `reduced`/`normal`, `finite`/`quasi-finite`,
   `proper`/`separated`, `flat`/`faithfully flat` are the pairs that recur, and mathlib
   usually has a lemma stating the difference — grep for the stronger name and read what it
   decomposes into.
2. **Find the in-tree PRODUCER of the property the bullet promises, and read ITS hypothesis
   list.** That list is the true one. Here `f_*𝒪 = 𝒪` universally is
   `HasUniversallyTrivialPushforward`, and its producer
   `hasUniversallyTrivialPushforward_of_isProper_of_flat` demands
   `[GeometricallyReduced f]` and `[LocallyOfFinitePresentation f]` — neither of which the
   leaf had. A bullet promising a property the leaf cannot derive is the tell.
**And when the argument has TWO steps, check that the bullet checks both.** This one
established injectivity of `Γ(T,𝒪^×) → Γ(Z_T,𝒪^×)` (from faithful flatness of `Z`, and
correctly) and silently assumed `Aut(ℒ) = Γ(X_T,𝒪^×) = Γ(T,𝒪^×)`, which is the OTHER
injectivity and the one that failed. The module docstring even claimed the bullet "is the
check that this is not a leaf that will turn out to be FALSE AS STATED" — a check that
verifies one of the two steps it needs reads exactly like a check that verifies both.
**THE REPAIR IS AN ADDED HYPOTHESIS NAMING THE CONSUMED PROPERTY, NOT A RESTATEMENT OF THE
GEOMETRY.** Adding `hpush : HasUniversallyTrivialPushforward strX` (i) kills the witness on
the nose — there `strX.app ⊤` is `k → k[ε]`, not an isomorphism; (ii) is the predicate the
sibling file already uses for the same purpose
(`exists_relPicOf_of_hasUniversallyTrivialPushforward`); (iii) unblocks the route, since the
leaf's own geometric hypotheses could not reach it (`GeometricallyIrreducible → Geometrically
Connected` does not synthesize either, so the flat producer was unusable); and (iv) is
discharged by the sole consumer in ONE call, because it holds `Smooth` and `IsProper`. Since
the change only ADDS a binder it cannot make a true statement false, so the *other*
faithfulness bullet is inherited verbatim rather than re-run — **say that, and say why**, per
the standing rule that a restatement voids the earlier audit.
### A LEAF THAT EXISTS TO SUBSTITUTE FOR A HYPOTHESIS CANNOT CONSUME A THEOREM REQUIRING IT
(Same leaf, and it is the more expensive half to discover.) That docstring's route named its
right-hand term as *"`Fermat.exists_relPicFull` (BLR 8.2/1), already in this module's import
closure"*. It is in the closure and it is **inapplicable**: it takes
`(o : RelPoint strX (𝟙 S))`, i.e. a SECTION of `X ⟶ S`, and the entire reason MB introduces
the rigidificator `Z` — finite flat surjective over `S` — is that no section exists. Witness:
over `ℚ`, the conic `x²+y²+z²=0` is smooth proper geometrically integral with no rational
point, and its closed points all have degree `2`, so `Z` exists and `o` does not. The
consumer is in exactly that position — it is trying to PRODUCE rational points.
So the general check, and it costs one read of the cited theorem's binder list:
**when a leaf's hypotheses are a known SUBSTITUTE for some hypothesis `h` (a multisection for
a section, a rigidificator for a base point, a finite étale cover for a rational point), no
theorem carrying `h` can be an input to it** — and a docstring citing one has mis-stated the
logical direction. In the literature the implication usually runs the other way: BLR 8.2/3
and FGA make the RIGIDIFIED functor primary, precisely because its objects have no
automorphisms, and recover `Pic` from it as a quotient. Taking `Z = S`, `ι = o` degenerates
the sequence, so this leaf strictly SUBSUMES the theorem its docstring cited as its input.
Record that, or the next prover spends the run trying to apply it.
