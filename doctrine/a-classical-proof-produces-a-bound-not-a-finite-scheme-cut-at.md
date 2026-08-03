## A CLASSICAL PROOF PRODUCES A **BOUND**, NOT A FINITE SCHEME — cut at the word "hence"
(2026-08-02, `flt-lean-354`, on `exists_normEndoPair_of_surjective_isAdditiveOn`
A leaf whose conclusion contains `IsFinite` of some kernel is almost always TWO
obligations wearing one statement, and the seam is visible in the textbook
sentence the leaf cites.  Poincaré reducibility ends:
> … and `N` acts on `Y` as `[n]`, so `n·m` kills `ker N ∩ ker u`, **hence** that
> kernel is finite.
Everything before "hence" is the citation — a polarisation, a dual abelian
variety, a norm endomorphism.  Everything after it is **in-tree scheme
plumbing that is provable today**, and in this instance it was ~150 lines:
read the bound at the tautological point, factor the kernel through `J[k]`,
mono + proper, Zariski's main theorem.  Leaving the two bundled means every
prover who ever attacks the citation must also rediscover the plumbing.
**So: when a leaf's conclusion carries a scheme-theoretic FINITENESS, ask what
the classical argument literally produces.**  If the answer is "an integer that
kills it", restate the leaf with the integer and prove the passage.  Here that
took the leaf from
    ∃ c d, … ∧ IsFinite (pullback.snd (pullback.fst d e ≫ u) e')     -- old
to
    ∃ N n m, N ≫ N = [n] ≫ N ∧ N ≫ u = 0 ∧
      ∀ x : T ⟶ J, x ≫ u = 0 → x ≫ ([m] ≫ N) = x ≫ [n*m]            -- new
— no `IsFinite`, no pullback, no kernel scheme, no image scheme, and every
clause is a sentence in Mumford §19.  **Count 1 → 1; say so.**  What changed is
what is LEFT in the leaf, which is the only thing worth judging a recut by.
### THE TECHNIQUE: read the bound at the TAUTOLOGICAL POINT of the kernel
The bridge from "every `T`-point of `Z` is killed by `k`" to "`Z` is a finite
`ℚ`-scheme" is not an induction over points.  It is ONE instantiation:
* `Z := ker d ∩ ker u` is a double pullback, so it comes with `w : Z ⟶ J` (the
  two `pullback.fst`s composed) satisfying `w ≫ d = 0` and `w ≫ u = 0` by the
  two `pullback.condition`s, and `w ≫ jstr = zstr` by `kerHomι_comp_structure`
  applied twice;
* the bound AT `x := w` is therefore a single morphism equation
  `w ≫ [k] = zstr ≫ e`, i.e. `Z` factors through `J[k]` by `pullback.lift`;
* that factorisation `t` is MONO (both projections are base changes of the
  split monos `zeroSection`, so `w` is mono, and `t ≫ pullback.fst = w`) and
  PROPER (`MorphismProperty.of_postcomp` against a separated structure
  morphism, twice), hence FINITE by `isFinite_of_mono_of_isProper`;
* and `J[k] ⟶ Spec ℚ` is finite by `isFinite_flat_nTorsion_base` read through
  `nTorsionStructure_eq_snd` — a two-line recipe already in this file.
**Quantifying the bound over ALL test schemes costs nothing and buys the
instantiation.**  State it as `∀ {T} (x : T ⟶ J), … → x ≫ [k] = 0`, not at
geometric points: the geometric-point form cannot be read at `w`, and in
characteristic `0` a producer gets the `∀ T` form for free because a kernel of
a homomorphism of abelian schemes is reduced.
### `RelPoint jstr jstr` **IS** `End(J)` — so `[n] − N` exists even where the file has no morphism subtraction
`X0.lean` has no subtraction of two endomorphisms, and building one looks like a
prerequisite for `c := [n] − N`.  It is not.  `RelPoint jstr jstr` is
`{v : J ⟶ J // v ≫ jstr = jstr}`, i.e. the endomorphisms of `J` over the base,
and `abJ.addCommGroup jstr` is already an `AddCommGroup` on it.  So
    C : RelPoint jstr jstr := n • ⟨𝟙 J, Category.id_comp jstr⟩ - ⟨N, hN⟩
and `c := C.1`.  **`C.1` is opaque and never needs to be computed** — every fact
about `c` is obtained through `RelPoint.post`.
The step that makes this usable, and it is the reusable half: **additivity of
`post c` in the POINT is additivity of `pre` in the ENDOMORPHISM**, because
    RelPoint.post c hc x   and   RelPoint.pre x.1 x.2 ⟨c, hc⟩
have the same underlying morphism `x.1 ≫ c`, so they are equal by
`Subtype.ext rfl`.  `RelPoint.pre x.1 x.2` is an `AddMonoidHom` by the structure
fields `pre_add` and `pre_zero`, so `map_sub`/`map_nsmul` give
    RelPoint.post C.1 C.2 x = n • x - RelPoint.post N hN x
which is visibly additive in `x`.  `IsAdditiveOn abJ abJ C.1 C.2` then falls out
in four lines.  The same `Subtype.ext rfl` in the other slot (via `postAddHom`)
computes `C.1 ≫ N` and `C.1 ≫ u` from `N ≫ N = [n] ≫ N` and `N ≫ u = 0`.
**Watch the slot.**  `post v hv x` is `x.1 ≫ v` — the ENDOMORPHISM is on the
right.  `post N hN C` is `C.1 ≫ N` and `post C.1 C.2 Nr` is `N ≫ C.1`; they are
different, and conflating them is one wasted round.
### A recut can make a hypothesis stop being load-bearing — check, and say so
The old leaf's conclusion contained `Surjective (c ≫ u)`, so `hsurj` was
load-bearing for it (witness `J := E`, `A := E × E`, `u := (𝟙, 0)`).  The new
leaf's conclusion has no surjectivity clause, and the norm endomorphism of
`(ker u)⁰` exists whether or not `u` is surjective — at `u := (𝟙, 0)` the leaf
is satisfied by `N := 0`, at `u := 0` by `N := 𝟙, n = m = 1`.  So `hsurj`
migrated OUT of the citation and INTO the proven bridge, where it is spent
turning `c ≫ u = u ≫ [n]` into a surjection.
That is a strict improvement and it must be written down, because the two
statements now disagree about the same binder and a reader who checks only one
docstring will draw the wrong conclusion.  **Keep the hypothesis anyway** —
adding one cannot make a leaf false, every call site has it, and removing it is
a signature change in a file with concurrent editors.
