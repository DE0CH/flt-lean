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

/-!
### The embedding/forms cut, MOVED here 2026-08-02 because its consumer had been hoisted

The apparatus and the two sorry leaves below were cut out of
`nonempty_cubeModel_of_isAmpleSheaf_cube` on 2026-07-31, at a moment when that theorem
was still declared in `ModularCurve/X0.lean`.  Later the same day, release 28 HOISTED the
theorem into THIS module to break the
`X0 -> FreyCurve/IsogenySignature -> ModularCurve/HyperellipticJacobian -> X0` import
cycle, and it took the PRE-CUT version of it (see the note above: "moved here verbatim
from `X0.lean` lines 43692-44001").  From that moment the two halves sat in `X0.lean`,
which `public import`s this module and is therefore DOWNSTREAM of their own consumer, and
**no proof term in the project reached either of them**: they were open leaves that
nothing could ever consume, and a comment-stripped grep for their names returned their own
declaration lines and docstrings and nothing else.

That is CLAUDE.md's `DELETE x REFACTOR` orphaning with the refactor being a HOIST rather
than a deletion, and it is invisible to every frontier instrument: both halves compile,
both emit `declaration uses 'sorry'`, both pass every ownership test, and the parent
kept its own `sorry` because the hoist could not carry a proof that had been written
against declarations it was leaving behind.

Moving them up is the repair, and it is what makes the cut real: the parent below is now
PROVEN over the two halves, so the direct-sorry count of the pair
(`X0.lean`, this file) goes 3 -> 2 and every remaining leaf is reachable.  Only the
STATEMENTS changed in the move, and only by writing `SpecQ` out as
`Spec (CommRingCat.of ℚ)` -- exactly the substitution the note above describes, `SpecQ`
being an `abbrev` declared in `X0.lean` and so unavailable upstream of it.
-/

/-! ### Evaluating global sections at rational points

**Why this apparatus exists (2026-07-31).**  `nonempty_cubeModel_of_isAmpleSheaf_cube`
below used to assert its `coords` outright.  A `CubeModel` whose `coords` are merely
*asserted to exist* cannot be cut further along the embedding/forms axis, because the
resulting FORMS half would be the coordinate-level statement refuted on `CubeModel`'s
docstring by `E : y² + y = x³ − x`, `coords n = (1, n³, n⁶)`.  The four declarations
here MANUFACTURE `coords` from a sheaf and a section family, which is what defeats that
counterexample and makes the cut faithful.

**THE TRICK THAT MAKES THIS CHEAP, and it is worth reusing.**  Evaluating a section of
an invertible sheaf at a point normally means germs, stalks, or a trivialization over
some unnamed neighbourhood.  None of that is needed here, for one reason: over
`Spec ℚ` the base is a SINGLE point, so the trivialization one carries is a GLOBAL
isomorphism `P^*M ≅ 𝒪` rather than a restriction — and then

* `nonvanishingAt_of_iso` transports non-vanishing across it with no bookkeeping;
* `nonvanishingLocus_modUnit` identifies the non-vanishing locus of a section of `𝒪`
  with its basic open;
* on `Spec` of a FIELD a basic open is `⊤` or `⊥` according as the section is a unit or
  zero (`Scheme.basicOpen_of_isUnit` / `Scheme.basicOpen_zero`).

So "does not vanish at the point" becomes "is nonzero in `ℚ`" in three rewrites, with
no `restrict`, no stalk and no `PrimeSpectrum` topology.  Carrying the trivialization
as a restriction `(P^*M)|_U ≅ 𝒪_U` instead costs the whole `trivializedSection`
apparatus and the identification `Γ((⊤ : Opens), ⊤) ≅ Γ(Spec ℚ, ⊤)`.

`nonvanishingAt_modPullbackSection` is stated for an arbitrary morphism of schemes and
has nothing to do with `SpecQ`; it BELONGS in `Modularity/AmpleSheaf.lean` beside
`nonvanishingLocus_modPullback_of_isAmpleSheaf`, whose proof it generalizes verbatim
(that one is the closed-immersion, ample, whole-locus form; this is the pointwise form
for an invertible sheaf).  It is declared here only because editing `AmpleSheaf.lean`
re-elaborates the whole 81k-line cone of this module; hoist it next time that file is
touched for another reason. -/

/-- **NON-VANISHING IS DETECTED ON PULLBACKS** (PROVEN 2026-07-31): for an invertible
`A` and ANY morphism `f`, the pulled-back section `f^*s` is non-vanishing at `x` exactly
when `s` is non-vanishing at `f x`.

This is `nonvanishingLocus_modPullback_of_isAmpleSheaf`
(`Modularity/AmpleSheaf.lean`) with its ampleness and closed-immersion hypotheses
removed: that proof never used either — it used only that `A` is invertible near
`f x`, which `IsInvertibleSheaf` gives directly — and it is the pointwise statement
rather than the equality of loci. -/
theorem nonvanishingAt_modPullbackSection {X Y : Scheme.{u}} (f : X ⟶ Y) {A : Y.Modules}
    (hA : IsInvertibleSheaf A) (s : Γ(A, ⊤)) (x : X) :
    NonvanishingAt (modPullback f A) (modPullbackSection f A s) x
      ↔ NonvanishingAt A s (f.base x) := by
  obtain ⟨U, hU, ⟨φ⟩⟩ := hA (f.base x)
  obtain ⟨ψ, hψ⟩ := exists_trivialization_modPullback f φ s
  have hxU : x ∈ f ⁻¹ᵁ U := hU
  rw [nonvanishingAt_iff_trivializedSection _ ψ hxU,
    nonvanishingAt_iff_trivializedSection s φ hU]
  exact hψ x hxU

/-- **A global section of `𝒪` on `Spec ℚ`, as a rational number** — the canonical
`Γ(Spec R, ⊤) ≅ R` at `R = ℚ`. -/
noncomputable def ratOfSpecQ (r : Γ((Spec (CommRingCat.of ℚ)), ⊤)) : ℚ :=
  (Scheme.ΓSpecIso (CommRingCat.of ℚ)).hom r

/-- `ratOfSpecQ` is injective at `0`, because it is half of an isomorphism. -/
theorem ratOfSpecQ_eq_zero_iff (r : Γ((Spec (CommRingCat.of ℚ)), ⊤)) : ratOfSpecQ r = 0 ↔ r = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [ratOfSpecQ, h]⟩
  have h1 := Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of ℚ)) r
  rw [show (Scheme.ΓSpecIso (CommRingCat.of ℚ)).hom r = (0 : ℚ) from h] at h1
  rw [← h1]
  simp

/-- **ON `Spec ℚ`, NON-VANISHING OF A SECTION OF `𝒪` IS BEING NONZERO IN `ℚ`**
(PROVEN 2026-07-31).

`nonvanishingLocus_modUnit` turns the left side into membership of the basic open of
`r`, and over a FIELD a basic open is `⊤` or `⊥` according as `r` is a unit or zero —
so the point-set topology of `Spec ℚ` never has to be touched. -/
theorem nonvanishingAt_modUnit_specQ (r : Γ((Spec (CommRingCat.of ℚ)), ⊤)) (x : (Spec (CommRingCat.of ℚ))) :
    NonvanishingAt (modUnit (Spec (CommRingCat.of ℚ))) r x ↔ ratOfSpecQ r ≠ 0 := by
  have hloc := nonvanishingLocus_modUnit (Spec (CommRingCat.of ℚ)) r
  have hx : NonvanishingAt (modUnit (Spec (CommRingCat.of ℚ))) r x ↔ x ∈ (Spec (CommRingCat.of ℚ)).basicOpen r := by
    have : x ∈ nonvanishingLocus (modUnit (Spec (CommRingCat.of ℚ))) r ↔ x ∈ ((Spec (CommRingCat.of ℚ)).basicOpen r : Set (Spec (CommRingCat.of ℚ))) := by
      rw [hloc]
    exact this
  rw [hx]
  by_cases h : ratOfSpecQ r = 0
  · have hr : r = 0 := (ratOfSpecQ_eq_zero_iff r).1 h
    subst hr
    simp [Scheme.basicOpen_zero, h]
  · have hu : IsUnit r := by
      have h2 : IsUnit (ratOfSpecQ r) := isUnit_iff_ne_zero.2 h
      have h3 : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv (ratOfSpecQ r)) :=
        h2.map (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv.hom
      rwa [show (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv (ratOfSpecQ r) = r from
        Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of ℚ)) r] at h3
    have hb : (Spec (CommRingCat.of ℚ)).basicOpen r = ⊤ := (Spec (CommRingCat.of ℚ)).basicOpen_of_isUnit hu
    rw [hb]
    simp [h]

/-- **THE SAME, THROUGH A GLOBAL TRIVIALIZATION** (PROVEN 2026-07-31): for an
invertible sheaf on `Spec ℚ` presented as `N ≅ 𝒪`, a section is non-vanishing exactly
when its image in `ℚ` is nonzero. -/
theorem nonvanishingAt_iff_ratOfSpecQ {N : (Spec (CommRingCat.of ℚ)).Modules} (ψ : N ≅ modUnit (Spec (CommRingCat.of ℚ)))
    (t : Γ(N, ⊤)) (x : (Spec (CommRingCat.of ℚ))) :
    NonvanishingAt N t x ↔ ratOfSpecQ (ψ.hom.val.app (Opposite.op ⊤) t) ≠ 0 := by
  rw [← nonvanishingAt_modUnit_specQ]
  refine ⟨fun h => nonvanishingAt_of_iso ψ t x h, fun h => ?_⟩
  simpa only [Iso.symm_hom, modIso_inv_hom] using nonvanishingAt_of_iso ψ.symm _ x h

/-- **THE VALUE OF A GLOBAL SECTION AT A RATIONAL POINT**, read through a
trivialization of its pullback: `modPullbackSection` carries `t : Γ(M, ⊤)` to
`Γ(P^*M, ⊤)`, `φ` identifies that with `Γ(𝒪_{Spec ℚ}, ⊤)`, and `ratOfSpecQ` reads the
result as a rational number.

Changing `φ` multiplies every `ptSectionValue M φ t` by one common nonzero scalar —
an isomorphism `𝒪 ≅ 𝒪` on `Spec ℚ` is multiplication by a unit of `ℚ` — which is
exactly the projective ambiguity `CubeModel` allows.  That is why the two leaves below
may take `φ` as given data rather than having to pin it down. -/
noncomputable def ptSectionValue {J : Scheme.{0}} {jstr : J ⟶ (Spec (CommRingCat.of ℚ))} (M : J.Modules)
    {P : RelPoint jstr (𝟙 (Spec (CommRingCat.of ℚ)))} (φ : modPullback P.1 M ≅ modUnit (Spec (CommRingCat.of ℚ))) (t : Γ(M, ⊤)) : ℚ :=
  ratOfSpecQ (φ.hom.val.app (Opposite.op ⊤) (modPullbackSection P.1 M t))

/-- **THE BRIDGE** (PROVEN 2026-07-31): the coordinate `ptSectionValue M φ t` is nonzero
exactly when `t` does not vanish at the image point of `P`.

This is what makes `CubeModel.coords_ne_zero` a THEOREM below rather than a hypothesis:
its geometric content is base-point-freeness of the linear system, a statement about
`M` and `s` on `J` that mentions no coordinates at all. -/
theorem ptSectionValue_ne_zero_iff {J : Scheme.{0}} {jstr : J ⟶ (Spec (CommRingCat.of ℚ))} (M : J.Modules)
    (hM : IsInvertibleSheaf M) {P : RelPoint jstr (𝟙 (Spec (CommRingCat.of ℚ)))}
    (φ : modPullback P.1 M ≅ modUnit (Spec (CommRingCat.of ℚ))) (t : Γ(M, ⊤)) (x : (Spec (CommRingCat.of ℚ))) :
    ptSectionValue M φ t ≠ 0 ↔ NonvanishingAt M t (P.1.base x) := by
  rw [ptSectionValue, ← nonvanishingAt_iff_ratOfSpecQ φ _ x,
    nonvanishingAt_modPullbackSection P.1 hM t x]

/-- **PROJECTIVE NORMALITY OF THE SYSTEM `s`**: the products `s i · s j` generate the
global sections of `M ⊗ M`.

**THIS IS THE CLAUSE WITHOUT WHICH THE EMBEDDING/FORMS CUT IS FALSE**, and it is not an
extra assumption but the honest name of a step the undivided leaf was making silently.
`CubeModel.cube_eval` asks for the bidegree-`(2,2)` forms `σ^* s_k ⊗ δ^* s_l` to be
POLYNOMIALS of degree `2` in the Segre variables, i.e. to lie in the image of
`Sym²⟨s⟩ ⊗ Sym²⟨s⟩ → Γ(p₁^*M^{⊗2} ⊗ p₂^*M^{⊗2}, ⊤)`.  A family `s` can define a perfectly
good closed immersion while spanning a proper subspace of `Γ(M, ⊤)`; the image is then a
proper subspace too, and no such polynomials exist.  So the FORMS half must be given
this hypothesis and the EMBEDDING half must produce it.

It is exactly what the THIRD power is taken for: `L^{⊗n}` on an abelian variety is
projectively normal for `n ≥ 3` (Koizumi; Mumford, *On the equations defining abelian
varieties I*), which is the same threshold at which `L^{⊗n}` becomes very ample.  So the
two clauses of the embedding leaf are one classical theorem, not two.

Stated over `modTensor M M` rather than `modTensorPow M 2`; the two are isomorphic by
the unitor (`modTensorPow M 2 = modTensor M (modTensor M (modUnit J))`), and the
`modTensor` form is the one `tensorSection` produces with no transport. -/
def SpansSquare {J : Scheme.{u}} (M : J.Modules) {dim : ℕ} (s : Fin dim → Γ(M, ⊤)) : Prop :=
  ∀ t : Γ(modTensor M M, ⊤), ∃ c : Fin dim × Fin dim → Γ(J, ⊤),
    t = ∑ p : Fin dim × Fin dim, c p • tensorSection (s p.1) (s p.2)

/-- **THE EMBEDDING HALF: an ample invertible sheaf on an abelian variety over `ℚ` has a
very ample, projectively normal third power** (sorry leaf, cut 2026-07-31 out of
`nonempty_cubeModel_of_isAmpleSheaf_cube` below).

This is Mumford, *Abelian Varieties* §6 Application 1 (`L^{⊗3}` is very ample) together
with Koizumi's theorem (`L^{⊗n}` is projectively normal for `n ≥ 3`) — one classical
package about `L` alone, saying nothing about the group law.  What it delivers:

* `M` with `M ≅ L^{⊗3}`, invertible, and a finite family `s : Fin dim → Γ(M, ⊤)`;
* `φ`, a trivialization of `P^*M` at each rational point.  `P^*M` is invertible on
  `Spec ℚ` and `Pic(Spec ℚ) = 0`, so this is free; it is handed over rather than
  constructed because constructing it needs "an invertible sheaf on a one-point scheme
  is globally trivial", which is true and is not in the pin;
* BASE-POINT FREENESS, `∀ z, ∃ i, NonvanishingAt M (s i) z`.  Note this is stated on
  `J`, about the sheaf — no coordinates — and `ptSectionValue_ne_zero_iff` converts it
  into `CubeModel.coords_ne_zero`;
* SEPARATION OF RATIONAL POINTS, in the coordinate-free form "some `2 × 2` minor of the
  two coordinate vectors is nonzero".  For nonzero vectors over a field, all minors
  vanishing IS proportionality, so this says exactly that the map to `ℙ^{dim−1}(ℚ)`
  induced by `s` is injective, which is that a closed immersion is a monomorphism;
* `SpansSquare`, projective normality — see its docstring for why the cut is FALSE
  without it.

**FAITHFULNESS AUDIT** (fresh, not inherited: this leaf did not exist before today).

*True.*  Every clause is a consequence of `L^{⊗3}` being very ample and projectively
normal on the abelian variety `A = J`.  Base-point freeness and injectivity on
`ℚ`-points are properties of a closed immersion `φ_{L³} : A ↪ ℙ^{dim−1}`; the minor
form of injectivity needs the coordinate vectors to be nonzero, which base-point
freeness supplies, and then "non-proportional ⟺ some minor ≠ 0" is linear algebra over
a field.

*Not vacuous.*  `dim = 0` is excluded by base-point freeness as soon as `J` is nonempty
(there is then no `i` at all), and constant `coords` are excluded by separation as soon
as `A(ℚ)` has two elements.  So this leaf cannot be discharged by a degenerate system,
which is precisely the failure mode `CubeModel`'s corrected non-vacuity note records
for `dim = 1`.

*Not stronger than the geometry supplies.*  Nothing here mentions the cube, and the
hypotheses are only `hinv` and `hamp` — symmetry and normalization are NOT used, and
adding them would record hypotheses this half does not read.  `ab` is kept because the
constant `3` is an abelian-variety statement: for a general proper scheme only "some
power" is very ample. -/
theorem exists_veryAmpleSystem_of_isAmpleSheaf {J : Scheme.{0}} {jstr : J ⟶ (Spec (CommRingCat.of ℚ))}
    (ab : AbelianSchemeStruct jstr) (L : J.Modules)
    (hinv : IsInvertibleSheaf L) (hamp : IsAmpleSheaf L) :
    ∃ (M : J.Modules) (dim : ℕ) (s : Fin dim → Γ(M, ⊤))
      (φ : ∀ P : RelPoint jstr (𝟙 (Spec (CommRingCat.of ℚ))), modPullback P.1 M ≅ modUnit (Spec (CommRingCat.of ℚ))),
      IsInvertibleSheaf M ∧ Nonempty (M ≅ modTensorPow L 3) ∧
      (∀ z : J, ∃ i, NonvanishingAt M (s i) z) ∧
      (∀ P Q : RelPoint jstr (𝟙 (Spec (CommRingCat.of ℚ))), P ≠ Q → ∃ i j,
        ptSectionValue M (φ P) (s i) * ptSectionValue M (φ Q) (s j)
          ≠ ptSectionValue M (φ P) (s j) * ptSectionValue M (φ Q) (s i)) ∧
      SpansSquare M s :=
  sorry

/-- **THE FORMS HALF: the theorem of the cube, read through a projectively normal very
ample system, is a family of quadratic forms in the Segre variables** (sorry leaf, cut
2026-07-31 out of `nonempty_cubeModel_of_isAmpleSheaf_cube` below).

Given the system `(M, s, φ)` that `exists_veryAmpleSystem_of_isAmpleSheaf` produces,
this manufactures every remaining field of `CubeModel`:

* `cube` / `cube_eval` from `hcube`.  `HasCubeIso` is multiplicative in `L`, so
  `σ^*L ⊗ δ^*L ≅ p₁^*L^{⊗2} ⊗ p₂^*L^{⊗2}` gives the same identity for `M ≅ L^{⊗3}`.
  Under it, `σ^* s_k ⊗ δ^* s_l` is a global section of
  `p₁^*M^{⊗2} ⊗ p₂^*M^{⊗2}`, which Künneth identifies with
  `Γ(M^{⊗2}, ⊤) ⊗ Γ(M^{⊗2}, ⊤)`, and `hspan` writes each factor as a quadratic form in
  the `s_i` — bidegree `(2,2)`, i.e. degree `2` in the Segre variables;
* `rel` / `rel_eval`: `J ×_ℚ J` is projective, so the Segre image is closed and its
  homogeneous ideal is finitely generated (Hilbert basis);
* `cube_nonvanishing`: `(P, Q) ↦ (P + Q, P − Q)` is `⟨σ, δ⟩`, a morphism defined
  everywhere, so over `ℚ̄` the forms have no common zero on the cone over the Segre
  image apart from the origin.

**THE BLOCKER IS KÜNNETH, NOT AMPLENESS.**  A sweep on 2026-07-31 found
`grep -rn 'IsVeryAmple\|VeryAmple\|Kunneth\|Künneth'` empty across
`.lake/packages/mathlib` and `~/cs/FLT` at this pin, so both classical inputs must be
built inside `Fermat/`.  Of the two, very ampleness is consumed only by the OTHER half;
what this one needs is the identification
`Γ(p₁^*N ⊗ p₂^*N', ⊤) ≅ Γ(N, ⊤) ⊗ Γ(N', ⊤)` on a product of proper `ℚ`-schemes.  A
prover should aim there first.

**FAITHFULNESS AUDIT** (fresh; this leaf did not exist before today).

*True.*  Mumford §6; Hindry–Silverman *Diophantine Geometry* B.5.1; Silverman *AEC*
VIII.6.2 in the elliptic case.

*The dependence on `φ` is harmless, and this is the clause that could have made the
leaf false.*  `cube_eval` demands ONE scalar `c` valid for all `k` simultaneously.
Replacing `φ (P+Q)` by `α · φ (P+Q)` and `φ (P−Q)` by `β · φ (P−Q)` multiplies the whole
right-hand side by `α β`, uniformly in `k`, and the left-hand side by the corresponding
scalars at `P` and `Q` raised to bidegree `(2,2)` — again uniformly.  So the truth of
the statement does not depend on WHICH trivializations the embedding half handed over,
which is what lets `φ` be a hypothesis instead of a construction.

*`hsym` and `hzero` are the two a careless prover would drop.*  `hsym` is what makes the
cube's right-hand side `p₁^*L^{⊗2} ⊗ p₂^*L^{⊗2}` rather than
`p₁^*(L ⊗ [−1]^*L) ⊗ p₂^*(L ⊗ [−1]^*L)`; `hzero` normalizes the scalar `c`.

*Not stronger than the geometry supplies.*  `hamp` is deliberately ABSENT: ampleness is
consumed entirely by the embedding half, and what survives into the forms is the
spanning clause, which is the part of it this half actually reads. -/
theorem exists_cubeForms_of_veryAmpleSystem {J : Scheme.{0}} {jstr : J ⟶ (Spec (CommRingCat.of ℚ))}
    (ab : AbelianSchemeStruct jstr) (L : J.Modules) (hinv : IsInvertibleSheaf L)
    (hsym : Nonempty (modPullback ab.negSelfHom L ≅ L))
    (hzero : Nonempty (modPullback ab.zeroSection L ≅ modUnit (Spec (CommRingCat.of ℚ))))
    (hcube : ab.HasCubeIso L)
    (M : J.Modules) (hM : IsInvertibleSheaf M) (hML : Nonempty (M ≅ modTensorPow L 3))
    {dim : ℕ} (s : Fin dim → Γ(M, ⊤))
    (φ : ∀ P : RelPoint jstr (𝟙 (Spec (CommRingCat.of ℚ))), modPullback P.1 M ≅ modUnit (Spec (CommRingCat.of ℚ)))
    (hspan : SpansSquare M s) :
    letI := ab.addCommGroup (𝟙 (Spec (CommRingCat.of ℚ)))
    ∃ (cube : Fin dim × Fin dim → MvPolynomial (Fin dim × Fin dim) ℚ) (relDim : ℕ)
      (relDeg : Fin relDim → ℕ) (rel : Fin relDim → MvPolynomial (Fin dim × Fin dim) ℚ),
      (∀ k, (cube k).IsHomogeneous 2) ∧
      (∀ P Q : RelPoint jstr (𝟙 (Spec (CommRingCat.of ℚ))), ∃ c : ℚ, c ≠ 0 ∧ ∀ k : Fin dim × Fin dim,
        MvPolynomial.eval (fun m : Fin dim × Fin dim =>
            ptSectionValue M (φ P) (s m.1) * ptSectionValue M (φ Q) (s m.2)) (cube k)
          = c * (ptSectionValue M (φ (P + Q)) (s k.1) *
              ptSectionValue M (φ (P - Q)) (s k.2))) ∧
      (∀ i, (rel i).IsHomogeneous (relDeg i)) ∧
      (∀ P Q : RelPoint jstr (𝟙 (Spec (CommRingCat.of ℚ))), ∀ i,
        MvPolynomial.eval (fun m : Fin dim × Fin dim =>
          ptSectionValue M (φ P) (s m.1) * ptSectionValue M (φ Q) (s m.2)) (rel i) = 0) ∧
      (∀ z : Fin dim × Fin dim → AlgebraicClosure ℚ, z ≠ 0 →
        (∀ i, MvPolynomial.aeval z (rel i) = 0) → ∃ k, MvPolynomial.aeval z (cube k) ≠ 0) :=
  sorry


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
and it is expensive for the Künneth reason, not for the ampleness reason.

**NO LONGER A LEAF (2026-08-02).**  The cut described in the paragraph headed *THE NEXT
CUT* above — and DECLINED there on 2026-07-30 for a reason that was correct when
written — was made on 2026-07-31 once the coordinate-manufacturing apparatus
(`ptSectionValue`, `ptSectionValue_ne_zero_iff`) and the projective-normality clause
(`SpansSquare`) existed to state it with.  This theorem is now PROVEN over

* `exists_veryAmpleSystem_of_isAmpleSheaf` — the EMBEDDING half, Mumford §6
  Application 1 plus Koizumi;
* `exists_cubeForms_of_veryAmpleSystem` — the FORMS half, the theorem of the cube read
  through that system.

Everything this assembly does itself is the two clauses those halves are stated so as to
make cheap, and neither of them is geometry:

* `coords_ne_zero` is BASE-POINT FREENESS through `ptSectionValue_ne_zero_iff`,
  instantiated at any point of `Spec ℚ` (there is one — `Nonempty (Spec ℚ)`);
* `injective_of_smul` is the SEPARATION clause read contrapositively: `coords P = c •
  coords Q` makes every `2 × 2` minor of the two coordinate vectors vanish
  (`(c·vᵢ)·v_j = (c·v_j)·vᵢ`), and the separation clause produces a nonzero one whenever
  `P ≠ Q`.  That is the whole of "a closed immersion is injective on `ℚ`-points", in the
  coordinate-free minor form the embedding half hands over.

The remaining eight fields are the forms half's five conjuncts and the three numerals
that index them, passed through unchanged.

So the objection recorded above — *"the cut cannot be STATED without inventing machinery
that does not exist, and inventing it badly manufactures a false leaf"* — was answered by
manufacturing `coords` FROM the sheaf rather than carrying it as a bare function, which
is exactly what defeats the `(1, n³, n⁶)` counterexample the coordinate-level cut dies
on; see the apparatus section at the top of this file.  What the objection was RIGHT
about is that the FORMS half still owes Künneth, and that obligation is now isolated in
one leaf that mentions no coordinates the geometry did not produce. -/
theorem nonempty_cubeModel_of_isAmpleSheaf_cube {J : Scheme.{0}}
    {jstr : J ⟶ Spec (CommRingCat.of ℚ)}
    (ab : AbelianSchemeStruct jstr) (L : J.Modules)
    (hinv : IsInvertibleSheaf L) (hamp : IsAmpleSheaf L)
    (hsym : Nonempty (modPullback ab.negSelfHom L ≅ L))
    (hzero : Nonempty (modPullback ab.zeroSection L ≅ modUnit (Spec (CommRingCat.of ℚ))))
    (hcube : ab.HasCubeIso L) :
    letI := ab.addCommGroup (𝟙 Spec (CommRingCat.of ℚ))
    Nonempty (CubeModel (RelPoint jstr (𝟙 Spec (CommRingCat.of ℚ)))) := by
  letI := ab.addCommGroup (𝟙 (Spec (CommRingCat.of ℚ)))
  obtain ⟨M, dim, s, φ, hM, hML, hbpf, hsep, hspan⟩ :=
    exists_veryAmpleSystem_of_isAmpleSheaf ab L hinv hamp
  obtain ⟨cube, relDim, relDeg, rel, hcubehom, hcubeeval, hrelhom, hreleval, hnonvan⟩ :=
    exists_cubeForms_of_veryAmpleSystem ab L hinv hsym hzero hcube M hM hML s φ hspan
  refine ⟨{ dim := dim
            coords := fun P i => ptSectionValue M (φ P) (s i)
            coords_ne_zero := ?_
            injective_of_smul := ?_
            cube := cube
            cube_homogeneous := hcubehom
            cube_eval := hcubeeval
            relDim := relDim
            relDeg := relDeg
            rel := rel
            rel_homogeneous := hrelhom
            rel_eval := hreleval
            cube_nonvanishing := hnonvan }⟩
  · -- `coords_ne_zero`: base-point freeness at any point of `Spec ℚ`.
    intro P hP
    obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of ℚ) : Scheme.{0}) := inferInstance
    obtain ⟨i, hi⟩ := hbpf (P.1.base x)
    exact (ptSectionValue_ne_zero_iff M hM (φ P) (s i) x).2 hi
      (by simpa using congrFun hP i)
  · -- `injective_of_smul`: proportional coordinate vectors have all minors zero.
    intro P Q c _ hPQ
    by_contra hne
    obtain ⟨i, j, hij⟩ := hsep P Q hne
    refine hij ?_
    have hi := congrFun hPQ i
    have hj := congrFun hPQ j
    simp only [Pi.smul_apply, smul_eq_mul] at hi hj
    rw [hi, hj]
    ring

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
