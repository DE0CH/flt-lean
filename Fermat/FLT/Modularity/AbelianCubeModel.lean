module

public import Fermat.FLT.Modularity.AbelianSchemeIsogeny
public import Fermat.FLT.Mathlib.NumberTheory.ProjectiveHeight

/-!
# The cube model of an abelian scheme's group of rational points

This module exists to BREAK AN IMPORT CYCLE, and carries no mathematics of its
own beyond the two declarations that were moved into it.

`ModularCurve/HyperellipticJacobian.lean` needs `exists_cubeModel_of_abelianScheme`
inside the proof body of `exists_cubeModel_pic_of_infinite`.  That theorem used to
live in `ModularCurve/X0.lean`, and the edge was taken (2026-07-31, `flt-lean-389`)
as a direct `import Fermat.FLT.ModularCurve.X0`, with a note asserting "there is no
cycle, since `X0.lean` does not mention" this file.

**That analysis checked the DIRECT edge only, and there is a cycle through the
transitive closure:**

    X0  --imports-->  FreyCurve/IsogenySignature  --imports-->  HyperellipticJacobian
        <-------------------- imports --------------------------

so adding `HyperellipticJacobian --> X0` closed the loop and `lake build` failed
with `build cycle detected` on the ROOT target — i.e. nothing in the project built
at all, not merely the three modules involved.  (This is the trap CLAUDE.md records
under *A DOCSTRING'S CLAIM ABOUT THE IMPORT GRAPH IS A HYPOTHESIS*: walk the
closures, do not read off the direct edges.)

The repair is the one `flt-lean-389`'s own comment prescribed — hoist the two
declarations out of `X0.lean` — with one change.  It named
`Modularity/AbelianSchemeIsogeny.lean` as the destination, which is correct
architecturally and expensive in practice: `X0.lean` `public import`s that module,
so adding `ProjectiveHeight` to it rebuilds the largest cone in the tree.  A new
module costs one file and rebuilds only its own consumers.

Both declarations are stated here with `Spec (CommRingCat.of ℚ)` written out,
because `SpecQ` is an `abbrev` declared in `X0.lean` and therefore not available
upstream of it.  `SpecQ` is reducible, so every existing call site in `X0.lean`
elaborates against these statements unchanged and no delegation is needed.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace Fermat

/-!
The two declarations below were MOVED here verbatim from
`Fermat/FLT/ModularCurve/X0.lean` (lines 43692-44001) on 2026-07-31, to break the
import cycle described at the top of this file.  Only the STATEMENTS changed, and
only by writing `SpecQ` out as `Spec (CommRingCat.of ℚ)` -- that `abbrev` is
declared in `X0.lean` and so is not available upstream of it.  `SpecQ` is
reducible, so every call site in `X0.lean` elaborates against these unchanged.
The docstrings are the originals and their audit history is unaltered.
-/

/-- **THE COORDINATE DICTIONARY: a symmetric normalized ample invertible sheaf
with the theorem of the cube gives a `CubeModel` on the group of rational
points** (sorry leaf, cut 2026-07-28 out of
`exists_cubeModel_of_abelianScheme` below).

This is the SHEAF-LEVEL half of that leaf which is *not* Mumford §6.  Its
hypotheses are exactly the conclusion of
`Fermat.exists_isAmpleSheaf_symmetric_cube`
(`Modularity/AbelianSchemeIsogeny.lean`), so between the two the parent is
proven, and the geometry is now asserted in one place shared with
`Fermat.exists_isAmpleSheaf_cube_of_isAlgClosed`.

**WHY THIS CUT IS FAITHFUL WHERE THE COORDINATE-LEVEL ONE IS FALSE.**  The
coordinate-level split — "any symmetric projective embedding of `A(ℚ)`
satisfies the theorem of the cube" — is refuted by
`E : y² + y = x³ − x`, `E(ℚ) ≅ ℤ`, `coords n = (1, n³, n⁶)`, whose height
`6 log|n|` breaks the parallelogram law (see `CubeModel`'s docstring, and the
parent's).  That counterexample does **not** lift to this statement, and the
reason is the whole point of cutting here: `coords` is no longer an arbitrary
injection of the abstract group into `ℙⁿ(ℚ)` but is *manufactured from `L`*, so
`n ↦ (1 : n³ : n⁶)` would have to be the restriction to `E(ℚ)` of a morphism
`E ⟶ ℙ²` given by three global sections of an invertible sheaf.  `E(ℚ)` is
Zariski-dense in `E`, so such a morphism is determined by that restriction, and
a morphism of degree `d` has naïve height `≍ d · ĥ(P) ≍ d n²`, never
`6 log|n|`.  The hypotheses here therefore constrain the height, which is
exactly what the coordinate-level hypotheses failed to do.

**WHAT THE PROOF OWES**, and none of it is new geometry:

* *very ampleness*: `L^{⊗3}` is very ample (Mumford §6, Application 1) and
  projectively normal, and the cube identity survives the third power because
  it is multiplicative in `L`.  This is the one classical input, and it is
  about `L` alone, not about the group;
* *evaluation at rational points*: for `P : RelPoint jstr (𝟙 SpecQ)`, i.e.
  `P.1 : Spec ℚ ⟶ J`, the sheaf `P.1^* L` is invertible on `Spec ℚ`, hence
  trivial (`Pic (Spec ℚ) = 0`; the space is a single point, so the only open
  containing it is `⊤`).  Composing `Fermat.modPullbackSection` — PROVEN in
  `Modularity/AmpleSheaf.lean`, and the bridge whose absence the parent's
  docstring used to record — with a trivialization gives `coords P i ∈ ℚ`,
  well defined up to the one scalar by which the trivialization is ambiguous.
  That ambiguity is precisely the projective ambiguity `CubeModel` allows;
* *`coords_ne_zero`* is base-point-freeness of a very ample system,
  *`injective_of_smul`* is that a closed immersion is a monomorphism, read on
  `ℚ`-points;
* *`cube` / `cube_eval`*: the section `σ^* s_k ⊗ δ^* s_l` of
  `σ^* L ⊗ δ^* L ≅ p₁^* L^{⊗2} ⊗ p₂^* L^{⊗2}` is, by Künneth and projective
  normality, a bidegree-`(2,2)` polynomial in the `s_i`, i.e. a form of degree
  `2` in the Segre variables.  The single common scalar `c` in `cube_eval` is
  the ambiguity of the trivializations at `P + Q` and `P − Q`;
* *`rel` / `rel_eval`*: `J ×_ℚ J` is projective, so the Segre image is closed
  and its homogeneous ideal finitely generated (Hilbert basis);
* *`cube_nonvanishing`*: `(P, Q) ↦ (P + Q, P − Q)` is a morphism defined
  everywhere, which is `σ` and `δ` being morphisms — an identity of schemes,
  not a rational-map argument.

**MISSING MACHINERY** (the check that refutes this list is
`grep -rn "VeryAmple\|Kunneth\|Künneth\|projectivelyNormal" Fermat/
.lake/packages/mathlib/Mathlib/ ~/cs/FLT/`): very ample sheaves, the map to
`Proj` attached to a linear system, and the Künneth formula.  Note the second
of those is what `AbelianScheme.lean`'s docstring records as absent — there is
no functor-of-points description of `Hom(T, Proj 𝒜)` at this pin — and it is
needed only to *derive* `injective_of_smul`; the evaluation half of the
dictionary needs nothing beyond `modPullbackSection`.

**THE NEXT CUT, AND THE CLAUSE WITHOUT WHICH IT IS FALSE.**  The obvious way to
split this leaf again is to separate the EMBEDDING (produce `L`, a section
family `s : Fin dim → Γ(L, ⊤)`, and the `coords` they induce at `ℚ`-points,
with `coords_ne_zero` and `injective_of_smul`) from the FORMS (produce `cube`,
`rel` and their evaluation properties from `HasCubeIso`).  Carrying `L` and `s`
across the cut does defeat the `(1, n³, n⁶)` counterexample, so unlike the
coordinate-level split this one is not *obviously* false — but as stated it is
**still not provable**, and the reason is worth writing down because it is not
the reason one expects.

**THAT CUT WAS EVALUATED IN FULL ON 2026-07-30 (flt-lean-167) AND DECLINED.
Recorded here so the next agent does not re-derive it.**  The mathematics is
vouchable — with the spanning clause, `σ^* s_k ⊗ δ^* s_l` lands in
`Γ(M^{⊗2}) ⊗ Γ(M^{⊗2})` by Künneth and is therefore bidegree `(2,2)` in the
`s_i`, so the FORMS half is true — but the cut cannot be *stated* without
inventing machinery that does not exist, and inventing it badly manufactures a
false leaf, which is worse than leaving this one open:

* the interface has to carry `coords` MANUFACTURED FROM `s`, i.e.
  `coords P i = ` the value of `modPullbackSection P.1 M (s i)` read through a
  trivialization `modPullback P.1 M ≅ modUnit SpecQ` and an identification
  `Γ(SpecQ, ⊤) ≅ ℚ`.  Carrying `coords` as a bare function instead is exactly
  the coordinate-level cut refuted above by `(1, n³, n⁶)`;
* the spanning clause is `IsVeryAmpleSheaf`-strength, and **`VeryAmple` exists
  nowhere**: `grep -rn "VeryAmple\|veryAmple"` over `Fermat/`,
  `.lake/packages/mathlib/` and `~/cs/FLT/` returns four hits, all four of
  them prose in "missing machinery" notes (`CurveAffineComplement.lean:102`,
  `Descent.lean:146`, `AbelianSchemeIsogeny.lean:13679`,
  `MoretBailly.lean:32139`) and no definition.  `Künneth` returns nothing at
  all, in the project or in mathlib.

So the EMBEDDING half would have to *define* very ampleness and projective
normality before it could state its own conclusion, and the FORMS half would
consume that definition.  A half-built `IsVeryAmpleSheaf` is a worse object
than this monolith, which at least has one complete classical proof (Mumford
§6) that a successor can follow end to end.  The right order is: build very
ampleness and the linear-system-to-`Proj` map FIRST, as their own subject,
and only then make this cut.

`cube_eval` asks for polynomials of degree `2` in the Segre variables
`z (i,j)`, i.e. for `σ^* s_k ⊗ δ^* s_l` to lie in the image of
`Sym²⟨s⟩ ⊗ Sym²⟨s⟩ → Γ(p₁^* L^{⊗2} ⊗ p₂^* L^{⊗2}, ⊤)`.  A family `s` can define
a perfectly good closed immersion while spanning a proper subspace of
`Γ(L, ⊤)`, and then that image is a proper subspace too and no such polynomials
exist.  So the FORMS half must be given a SPANNING hypothesis — that the
products `s_i · s_j` generate the global sections of `L^{⊗2}`, i.e. projective
normality of the system — and the EMBEDDING half must produce it.  That is
exactly the content the third power `L^{⊗3}` is taken for, so the spanning
clause is not an extra assumption but the honest name of a step this leaf is
already making silently.  **Do not make this cut without it.**

**FAITHFULNESS.**  *Not vacuous*: the conclusion is the parent's, whose
non-vacuity audit is unchanged (`coords_ne_zero` and `injective_of_smul` make
`A(ℚ)` inject into `ℙⁿ(ℚ)`, and `Fermat.finite_setOf_logHeight_coords_le` then
makes bounded-height sets finite, so no bounded height can satisfy the package).
*Not stronger than the geometry supplies*: every hypothesis is a conjunct of
`exists_isAmpleSheaf_symmetric_cube`, which is Mumford §6 verbatim.  `hsym` and
`hzero` are the two that a careless prover would drop — `hsym` is what makes
the cube's right-hand side `p₁^* L^{⊗2} ⊗ p₂^* L^{⊗2}` rather than
`p₁^*(L ⊗ [−1]^* L) ⊗ p₂^*(L ⊗ [−1]^* L)`, and `hzero` is what normalizes the
scalar `c`.

*The CHEAP CASE quoted from `CubeModel`'s audit was WRONG, and is corrected
there* (2026-07-31).  The recipe `dim = 1`, `coords ≡ ![1]`, `cube = z` does
not witness "`A(ℚ)` finite": a constant `coords` satisfies `injective_of_smul`
only for a SUBSINGLETON group, and `z` is homogeneous of degree `1` where
`cube_homogeneous` asks for `2`.  The claim survives with an indicator witness
(`dim = Fintype.card A`, `coords P = Pi.single (e P) 1`, `rel` the products
`z k * z l` over `k ≠ l`, `cube (a, b)` the sum of `z (e P, e Q) ^ 2` over the
pairs with `P + Q = e.symm a` and `P − Q = e.symm b`), spelled out in full on
`Fermat.CubeModel` in `Fermat/FLT/Mathlib/NumberTheory/ProjectiveHeight.lean`.
The audit's conclusion is unaffected; the correction matters because the cheap
case is the evidence that this leaf is not asking a producer for more than the
geometry supplies, and the version quoted here supported a much weaker claim
than the one it was cited for.

**MISSING-MACHINERY CHECK RE-RUN 2026-07-31, still empty.**
`grep -rln 'IsVeryAmple\|VeryAmple\|Kunneth\|Künneth' .lake/packages/mathlib/Mathlib/ ~/cs/FLT/`
returns NOTHING at our pin.  So both classical inputs — very ampleness of
`L^{⊗3}` together with projective normality of the system it defines, and the
Künneth identification
`Γ(p₁^* L^{⊗2} ⊗ p₂^* L^{⊗2}, ⊤) ≅ Γ(L^{⊗2}, ⊤) ⊗ Γ(L^{⊗2}, ⊤)` that turns the
cube isomorphism into forms of bidegree `(2, 2)` — have to be built here, on
top of `Modularity/AmpleSheaf.lean`.  Note which of the six bullets above that
leaves *cheap*: the evaluation half (`coords`, and `coords_ne_zero` from
base-point-freeness) needs only `modPullbackSection` and the triviality of
`Pic (Spec ℚ)`, both available.  The expensive half is `cube` / `cube_eval`,
and it is expensive for the Künneth reason, not for the ampleness reason. -/
theorem nonempty_cubeModel_of_isAmpleSheaf_cube {J : Scheme.{0}}
    {jstr : J ⟶ Spec (CommRingCat.of ℚ)}
    (ab : AbelianSchemeStruct jstr) (L : J.Modules)
    (hinv : IsInvertibleSheaf L) (hamp : IsAmpleSheaf L)
    (hsym : Nonempty (modPullback ab.negSelfHom L ≅ L))
    (hzero : Nonempty (modPullback ab.zeroSection L ≅ modUnit (Spec (CommRingCat.of ℚ))))
    (hcube : ab.HasCubeIso L) :
    letI := ab.addCommGroup (𝟙 Spec (CommRingCat.of ℚ))
    Nonempty (CubeModel (RelPoint jstr (𝟙 Spec (CommRingCat.of ℚ)))) :=
  sorry

/-- **`A` embeds in `ℙⁿ_ℚ` by a symmetric very ample line bundle, the
theorem of the cube holds for that embedding, and `(P, Q) ↦ (P+Q, P−Q)` is
a morphism** (PROVEN 2026-07-28 over the sheaf-level cut described below; cut
2026-07-28 out of `exists_cubeEmbedding_of_abelianScheme` below) — the
GEOMETRIC half of Mordell–Weil.

**WHAT THIS CUT SHED, AND WHY IT IS A CUT AND NOT A RESTATEMENT.**  Its
predecessor asked in addition for `CubeEmbedding.cert` / `cert_eval`: an
*effective Nullstellensatz certificate*, i.e. explicit polynomials
`cert (k, j)` with `∑_j cert (k,j) · cube j = z_k^{certDeg+2}` at every
Segre point.  That is commutative algebra, not geometry, and no producer
coming from algebraic geometry has those polynomials in hand.  `CubeModel`
asks instead for what the geometry actually supplies —

* `rel` / `rel_eval`: homogeneous forms cutting out the Segre image of
  `A × A` in `ℙ^{dim²−1}` (`A × A` is projective, so the image is closed
  and its homogeneous ideal is finitely generated);
* `cube_nonvanishing`: over an ALGEBRAIC CLOSURE, the forms `cube` have no
  common zero on the affine cone over that image apart from the origin —
  which is exactly the statement that `(P, Q) ↦ (P + Q, P − Q)` is a
  morphism defined everywhere, not merely a rational map

— and `Fermat.CubeModel.nonempty_cubeEmbedding` manufactures the
certificate.  That bridge is PROVEN, over
`Fermat.exists_homogeneousCertificate`
(`Fermat/FLT/Mathlib/NumberTheory/ProjectiveHeight.lean`), which is in turn
proven from `Mathlib`'s `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`
plus one new homogeneous-component lemma.  So the cut costs no new sorry:
the frontier keeps exactly one leaf here, and that leaf is now purely
geometric.

**Note the `ℚ`-rationality of the certificate came for free**, which is the
one thing that could have made the bridge hard.  `Mathlib`'s Nullstellensatz
is stated for an ideal over a base field `k` with its zero locus taken in an
algebraically closed extension `K`, and it returns the radical **over `k`** —
so no faithful-flatness descent from `ℚ̄` to `ℚ` had to be written.

TRUE and classical (Mumford, *Abelian Varieties*, §6 and §8, for the
theorem of the cube and projectivity; Hindry–Silverman, *Diophantine
Geometry* Theorem B.5.1; Silverman, *AEC* VIII.6.2 for the elliptic case).
`ab.proper` and `ab.smooth` make `A` an abelian variety over `ℚ`, so it is
projective and carries a symmetric ample line bundle `L` — take any ample
`L₀` and set `L = L₀ ⊗ [−1]^* L₀`.  A sufficiently high power of `L` is
very ample and embeds `A` in `ℙⁿ_ℚ`; that is `coords` together with
`coords_ne_zero` and `injective_of_smul`.  The theorem of the cube then
says

  `σ* L ⊗ δ* L ≅ p₁* L² ⊗ p₂* L²`   on `A × A`,

`σ (P,Q) = P + Q` and `δ (P,Q) = P − Q`; in coordinates that is a family of
forms of bidegree `(2,2)`, i.e. of degree `2` in the Segre variables
`z (i,j) = xᵢ y_j`, computing the Segre product of `φ(P+Q)` and `φ(P−Q)`
from `(φ(P), φ(Q))` — and that is `cube` with `cube_eval`.

**Note the cancellation the consumer depends on**: *individually* `h(P+Q)`
and `h(P−Q)` are each only bounded by `2h(P) + 2h(Q) + O(1)`, and it is
precisely the cube — that their SEGRE PRODUCT has bidegree `(2,2)`, not
each factor separately — which makes the sum come out right.  A producer
that establishes the two factors separately has not proven the
parallelogram law.

**MISSING MACHINERY**, and it really is all that is left: projectivity of
an abelian variety, symmetric very ample line bundles, and the theorem of
the cube.  The check that would refute this is
`grep -rn "TheoremOfTheCube\|VeryAmple\|IsVeryAmple" Fermat/
.lake/packages/mathlib/Mathlib/ ~/cs/FLT/`.  What this project DOES have,
and a producer should start from, is
`Fermat/FLT/Modularity/AmpleSheaf.lean`: `Fermat.IsInvertibleSheaf`,
`Fermat.IsAmpleSheaf`, `Fermat.modTensor` / `Fermat.modTensorPow`,
`Fermat.modPullback` and the pseudo-functoriality lemmas — enough to WRITE
`σ*L ⊗ δ*L ≅ p₁*L² ⊗ p₂*L²`.  There is also a sibling leaf
`Fermat.exists_isAmpleSheaf_cube_of_isAlgClosed`
(`Fermat/FLT/Modularity/AbelianSchemeIsogeny.lean`) asserting the same
geometry in the `[n]^*L ≅ L^{⊗n²}` form over an algebraically closed field;
whoever proves one should look at the other, since a symmetric ample `L`
with the cube is the common input.  `Mathlib` also has
`Mathlib/NumberTheory/Height/EllipticCurve.lean`, whose
`WeierstrassCurve.abs_logHeight_addSubMap_sub_two_mul_logHeight_le` is the
elliptic instance of `cube` — worth reading first, since it shows the exact
shape a producer has to build.

**FAITHFULNESS AUDIT.**  *Not vacuous in general.*  `coords_ne_zero` and
`injective_of_smul` force `A(ℚ)` to inject into `ℙⁿ(ℚ)`, and
`Fermat.finite_setOf_logHeight_coords_le` then makes every bounded-height
set finite, so no constant or bounded height can satisfy the package once
`cube_eval` and `cube_nonvanishing` are in force.  It *is* cheap exactly
when `A(ℚ)` is finite, and that is correct rather than a defect: a finite
group is finitely generated, so the consumer's conclusion holds for that
reason anyway.  **The witness quoted here until 2026-07-30 — `dim = 1`,
`coords ≡ ![1]`, `cube = z`, `relDim = 0` — is REFUTED and has been
corrected on `CubeModel` itself** (`Fermat/FLT/Mathlib/NumberTheory/
ProjectiveHeight.lean`): `dim = 1` forces `Subsingleton A` outright, from
`coords_ne_zero` and `injective_of_smul` alone and whatever `coords` is, so
it covers the trivial group only.  The replacement is the indicator basis
at `dim = Nat.card A`; the conclusion of this audit is unaffected.

*Not weaker than what it produces.*  `CubeModel.nonempty_cubeEmbedding` and
`CubeEmbedding.toProjectiveHeightSource` are both proven, so this leaf
implies the two leaves it replaced; nothing downstream lost content.

**THE AXIS SEARCHED, AND THE ONE THAT WAS NOT.**  The obvious further cut —
split the embedding (`coords`, `injective_of_smul`, `rel`) from the cube
(`cube`, `cube_eval`, `cube_nonvanishing`), leaving "any symmetric
projective embedding of `A(ℚ)` satisfies the theorem of the cube" — is
**FALSE**, with a cheap counterexample recorded in `CubeModel`'s docstring:
`E : y² + y = x³ − x` has `E(ℚ) ≅ ℤ`, and `coords n = (1, n³, n⁶)` is an
injection into `ℙ²(ℚ)` compatible with `[−1]` (via `diag(1,−1,1)`) whose
height `6 log|n|` violates the parallelogram law.  Nothing about the
abstract group plus an injection into `ℙⁿ(ℚ)` constrains the height.  So
COORDINATE-LEVEL cuts of this leaf are exhausted.  The axis NOT searched is
the SHEAF level: state the embedding as an invertible sheaf `L` with global
sections `s : Fin dim → Γ(L, ⊤)`, and the cube as an isomorphism of sheaves
on `pullback jstr jstr`; then "very ample `L` with the cube" and "the
coordinate dictionary" become two genuinely separate leaves.

**THAT SHEAF-LEVEL CUT WAS MADE ON 2026-07-28, and the blocker this docstring
recorded against it was ALREADY FALSE when it was written.**  The paragraph
that stood here said "there is no `Γ(L, ⊤) → Γ(modPullback P L, ⊤)`
pullback-of-sections map in `AmpleSheaf.lean`".  There is:
`Fermat.modPullbackSection` (`Modularity/AmpleSheaf.lean`), PROVEN, built from
the unit of the pullback/pushforward adjunction.  The second half of the note —
that `Hom(T, Proj 𝒜)` has no functor-of-points description at this pin — is
still true and is simply not needed: the coordinate dictionary evaluates
sections at rational points through `modPullbackSection` and a trivialization
of `P^* L`, and never mentions `Proj`.

So this declaration is **NO LONGER A LEAF**.  It is now PROVEN over

* `Fermat.exists_isAmpleSheaf_symmetric_cube`
  (`Modularity/AbelianSchemeIsogeny.lean`) — over ANY field, an abelian
  variety carries a symmetric, normalized, ample invertible `L` satisfying the
  theorem of the cube `σ^* L ⊗ δ^* L ≅ p₁^* L^{⊗2} ⊗ p₂^* L^{⊗2}`.  This is
  the SHARED geometric core: the sibling leaf
  `Fermat.exists_isAmpleSheaf_cube_of_isAlgClosed` is now proven over it too,
  so Mumford §6 is asserted in exactly one place in the development instead of
  two;
* `Fermat.nonempty_cubeModel_of_isAmpleSheaf_cube` immediately above — the
  COORDINATE DICTIONARY, which turns that sheaf into the `CubeModel` package.

*The conclusion is `Nonempty`, not a chosen embedding*, because nothing
downstream depends on WHICH embedding is used; only its existence is
consumed. -/
theorem exists_cubeModel_of_abelianScheme {J : Scheme.{0}}
    {jstr : J ⟶ Spec (CommRingCat.of ℚ)}
    (ab : AbelianSchemeStruct jstr) :
    letI := ab.addCommGroup (𝟙 Spec (CommRingCat.of ℚ))
    Nonempty (CubeModel (RelPoint jstr (𝟙 Spec (CommRingCat.of ℚ)))) := by
  obtain ⟨L, hinv, hamp, hsym, hzero, hcube⟩ := exists_isAmpleSheaf_symmetric_cube ℚ ab
  exact nonempty_cubeModel_of_isAmpleSheaf_cube ab L hinv hamp hsym hzero hcube

end Fermat

end
