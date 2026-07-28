/-
Mathlib/AlgebraicGeometry/BirationalFunctionField.lean — own work for the
Fermat project (not vendored).

# The `Birational ↔ functionField ≃` dictionary

`Mathlib` has, on the geometric side, `Scheme.PartialMap`, `Scheme.RationalMap`,
`Scheme.PartialIso`, `Scheme.Birational`, `Scheme.BirationalOver` and
`Scheme.IsRationalOver`; and, on the algebraic side, `Scheme.functionField`,
`RationalMap.fromFunctionField`, `RationalMap.ofFunctionField` and the bijection
`RationalMap.equivFunctionFieldOver` between `S`-rational maps `X ⤏ Y` and
`S`-morphisms `Spec K(X) ⟶ Y`.

What it does **not** have is the last step of the dictionary: that an
*isomorphism* of function fields over `S` is a *birational* map over `S`.  The
bijection above is a bijection of `Hom`-sets, not an equivalence of categories,
and nothing in `Mathlib` turns a mutually inverse pair of rational maps into a
`Scheme.PartialIso`.  That single missing bridge is what this file supplies, as
`birationalOver_of_iso_specFunctionField`, **proven here** over two lemmas that
between them carry all of its residue:

* `exists_opens_iso_of_partialMap_equiv_id` — the purely geometric half: two
  partial maps whose two round trips are the identity restrict to an
  isomorphism of dense opens.  It mentions no base scheme at all.
  **PROVEN 2026-07-28.**
* `partialMap_comp_equiv_id_of_fromSpecStalkOfMem` — the purely stalk-level
  half: the round trip of two partial maps whose germs at the generic point are
  mutually inverse *is* the identity.  **PROVEN 2026-07-28.**

Both are now closed, so `birationalOver_of_iso_specFunctionField` is
unconditionally proven.

Everything else — the spreading out in both directions, the dominance of both
partial maps, the composite germ computation that `Mathlib` lacks, the
`S`-compatibility and the final assembly out of `Opens.birationalOver_of_dense`
and `Hom.birationalOver` — is proven.

The other main declaration here, `exists_iso_specFunctionField_affineSpace_of_isDominant`,
is **Lüroth's theorem in scheme language**: a curve over a field dominated by the
affine line has function field `K`-isomorphic to `K(t)`.  Lüroth itself is
already proven in `Mathlib` (`Mathlib/FieldTheory/RatFunc/Luroth.lean`,
`RatFunc.Luroth.algEquiv`), so that statement is *only* the translation between
the scheme-level `Spec` picture and the intermediate-field picture Lüroth is
stated in; no new mathematics of Lüroth type is left in it.  It too is now
**proven**, over the two lemmas that carry the translation:

* `exists_iso_specRatFunc_specFunctionField_affineSpace` — the affine-space
  half, `K(𝔸(n; Spec K)) ≃ K(t)` over `K`, mentioning neither `P` nor Lüroth.
  **PROVEN 2026-07-28.**
* `exists_iso_specRatFunc_specFunctionField_of_isDominant` — the curve half.
  **PROVEN 2026-07-28**, in turn over a further split at the exact point where
  `hcurve` enters:
  * `exists_hom_functionField_ratFunc_of_isDominant` — the stalk-map embedding
    `K(P) ↪ K(t)` over `K`.  Needs no `hcurve` (and is true for `P = Spec K`).
    **PROVEN 2026-07-28.**
  * `exists_iso_specRatFunc_specFunctionField_of_hom` — that such an embedding
    of the function field of a CURVE is an isomorphism.  Mentions neither `𝔸`
    nor `u`.  **PROVEN 2026-07-28**, over
    `not_surjective_specPreimage_of_smoothOfRelativeDimension_one` — "the
    structure map `K ⟶ K(P)` of a smooth curve is not surjective", which is
    where `hcurve` is consumed and is the one statement here that is false
    without it.  **PROVEN 2026-07-28.**

**THIS FILE IS SORRY-FREE** (2026-07-28).

The first two are stated in a deliberately identical shape — an isomorphism out
of the common object `Spec (RatFunc K)`, commuting with the maps down to
`Spec K` — which is what makes the assembly of the Lüroth statement out of them
a single `Iso.trans`.

## Import note

`CurveExtension` is imported for `infinite_of_smoothOfRelativeDimension_one`
alone, which is the arithmetic input to the non-degeneracy leaf.  It costs no
module in any cone: `X0.lean` is this file's only consumer and already
`public import`s `CurveExtension` directly.

Together these give, in three lines, "a curve over a field dominated by `𝔸¹`
is rational over that field" — the statement that replaces `ℙ¹` and
Riemann–Hurwitz in `Fermat/FLT/ModularCurve/X0.lean`
(`birationalOver_affineLine_of_isDominant`, the only consumer).

## Why no `ℙ¹` and no genus appear anywhere

Rationality of a curve over `K` is expressible against `𝔸¹` alone, as
`Scheme.BirationalOver strP (𝔸(n; Spec K) ↘ Spec K)` for a one-element index
`n`, because birationality only sees a dense open.  So the projective line is
never constructed and the genus of a scheme — which exists neither in `Mathlib`,
nor in `~/cs/FLT`, nor in this project — is never needed.
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.AlgebraicGeometry.Birational.Composition
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.RatFunc.Luroth
public import Fermat.FLT.Mathlib.AlgebraicGeometry.CurveExtension

@[expose] public section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

/-! ### Generic points and dominance -/

/-- **A dominant morphism of irreducible schemes carries the generic point to the generic
point** (PROVEN).

`Mathlib` has this for open immersions (`genericPoint_eq_of_isOpenImmersion`) but not for
dominant morphisms, where it is strictly easier: the image of the generic point is a generic
point of the closure of the image, and dominance says that closure is everything.

This is what makes the function field of the source receive the function field of the target:
the stalk map of `f` at the generic point is then a map `K(Y) ⟶ K(X)`. -/
theorem genericPoint_eq_of_isDominant {X Y : Scheme.{u}} (f : X ⟶ Y) [IsDominant f]
    [IrreducibleSpace X] [IrreducibleSpace Y] :
    f (genericPoint X) = genericPoint Y := by
  refine ((genericPoint_spec Y).eq ?_).symm
  have h := (genericPoint_spec X).image f.continuous
  rwa [Set.image_univ, f.denseRange.closure_range] at h

/-- **A morphism whose image contains the generic point of an irreducible target is dominant**
(PROVEN).  The converse of `genericPoint_eq_of_isDominant`, and the form in which dominance is
actually checked below: the closure of a set containing the generic point is everything. -/
theorem isDominant_of_genericPoint_mem_range {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IrreducibleSpace Y] (h : genericPoint Y ∈ Set.range f.base) : IsDominant f := by
  refine ⟨?_⟩
  have h2 : closure ({genericPoint Y} : Set Y) ⊆ closure (Set.range f.base) :=
    closure_mono (Set.singleton_subset_iff.mpr h)
  rw [(genericPoint_spec Y).def] at h2
  exact dense_iff_closure_eq.mpr (Set.univ_subset_iff.mp h2)

/-- **A partial map spread out from an isomorphism at the generic point is dominant** (PROVEN).

If the germ of `F` at `x` factors as an isomorphism `φ` followed by `Spec 𝒪_{Y,η} ⟶ Y` at the
generic point `η` of `Y`, then `η` is in the image of `F.hom` — it is the image of the closed
point of `Spec 𝒪_{Y,η}` pulled back through `φ` — so `F.hom` is dominant.

This is what makes `Scheme.PartialMap.comp` applicable to the two partial maps produced by
spreading out an isomorphism of function fields; `comp` requires the left factor to be
dominant, and nothing else in the construction supplies that. -/
theorem Scheme.PartialMap.isDominant_hom_of_fromSpecStalkOfMem
    {X Y : Scheme.{u}} [IrreducibleSpace Y] (F : X.PartialMap Y) {x : X} (hx : x ∈ F.domain)
    (φ : Spec (X.presheaf.stalk x) ⟶ Spec Y.functionField) [IsIso φ]
    (h : F.fromSpecStalkOfMem hx = φ ≫ Y.fromSpecStalk (genericPoint Y)) :
    IsDominant F.hom := by
  have hφ : φ ((inv φ) (IsLocalRing.closedPoint Y.functionField))
      = IsLocalRing.closedPoint Y.functionField := by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl
  refine isDominant_of_genericPoint_mem_range _
    ⟨(F.domain.fromSpecStalkOfMem x hx) ((inv φ) (IsLocalRing.closedPoint Y.functionField)), ?_⟩
  have key : F.fromSpecStalkOfMem hx ((inv φ) (IsLocalRing.closedPoint Y.functionField))
      = genericPoint Y := by
    rw [h, Scheme.Hom.comp_apply, hφ, Scheme.fromSpecStalk_closedPoint]
  exact key

/-! ### The two residues of the bridge -/

/-- **Two partial maps whose round trips are the identity restrict to an isomorphism of dense
opens** (**PROVEN 2026-07-28**) — the purely geometric residue of the
`Birational ↔ functionField ≃` bridge.  It mentions no base scheme, no field, no function
field and no ring: it is a statement about partial maps and opens alone.

This is the content of Hartshorne I.4.5 / Stacks 0BXA once the
function-field side has been discharged.  The construction is a single intersection:

* `hFG` gives a dense open `W₁ ≤ (F.comp G).domain` on which `G ∘ F` is the inclusion of `W₁`;
* `hGF` gives a dense open `W₂ ≤ (G.comp F).domain` on which `F ∘ G` is the inclusion of `W₂`;
* put `U := W₁ ⊓ F.hom ⁻¹ᵁ W₂` (pushed into `X` along `F.domain.ι`) and
  `V := W₂ ⊓ G.hom ⁻¹ᵁ W₁` (pushed into `Y` along `G.domain.ι`).

Then `F` maps `U` into `V`: for `x ∈ U` we have `F x ∈ W₂` by construction, and
`G (F x) = x ∈ W₁`, so `F x ∈ G.hom ⁻¹ᵁ W₁`.  Symmetrically `G` maps `V` into `U`.  The two
restrictions are mutually inverse — that is exactly `hFG` and `hGF` read on `U` and `V` — so
they assemble into `i : U.toScheme ≅ V.toScheme`, and `i.hom ≫ V.ι = X.homOfLE _ ≫ F.hom` by
construction.

**Density is where irreducibility is used, and only there.**  `U` and `V` are nonempty opens
(they contain the images of the generic points) of irreducible spaces, hence dense.  Over a
reducible scheme the intersection could be empty and the statement would be false.

**Why the conclusion is stated with `i.hom ≫ V.ι = X.homOfLE hUF ≫ F.hom` rather than as a
`Scheme.PartialIso`.**  The consumer needs the compatibility with structure maps to `S`, and
that is derived from this equation together with `F`'s own `IsOver` datum — see
`birationalOver_of_iso_specFunctionField` below, where the whole `S`-side of the argument is
four rewrites.  Packaging the conclusion as a `PartialIso` instead would force this leaf to
carry a base scheme it does not otherwise need.

**The check that would refute this note**: a `Mathlib` declaration producing a
`Scheme.PartialIso` (or `Scheme.Birational`) from a pair of partial or rational maps whose
composites are the identity.  A `grep -rn "Birational" .lake/packages/mathlib/Mathlib/` on
2026-07-28 found only `Birational/{Birational,Dominant,Composition}.lean` and
`AlgebraicGeometry/RationalMap.lean`, none of which has one.

**PROOF NOTE — why the whole proof is phrased in the UNFOLDED vocabulary of
`PartialMap.comp`.**  `(F.comp G).domain` and `F.domain.ι ''ᵁ (F.hom ⁻¹ᵁ G.domain)` are equal
only by *delta*, and `rw` type-checks its motive at `instances` transparency, which does not
unfold `comp`.  A single `X.homOfLE (h : U ≤ (F.comp G).domain)` sitting next to a morphism
whose source Lean recorded as the image open therefore makes every later `rw` fail with
`Application type mismatch`, and the failure is reported as "did not find the pattern".  So
`hW₁l₀`/`e₁₀` are converted ONCE, by `exact` (which does unfold at default transparency), into
`hW₁l`/`e₁` phrased with the image open, and nothing below ever mentions `comp` again.  The
same device gives `e₁ : X.homOfLE hW₁l ≫ ψ ≫ G.hom = W₁.ι` from the raw round-trip equation,
where `ψ` is the "`F` restricted to the composite domain, landing in `G.domain`" morphism.

The two mutually inverse morphisms are produced by `IsOpenImmersion.lift` against `V.ι` and
`U.ι`, so the conclusion `i.hom ≫ V.ι = X.homOfLE hUF ≫ F.hom` is literally `lift_fac` and
costs nothing; the work is the two range conditions, each of which needs the round trip on
POINTS (`congr($eU u)`), and the two `𝟙` identities, each of which is the round trip on
MORPHISMS after cancelling the mono `U.ι` resp. `V.ι`. -/
theorem exists_opens_iso_of_partialMap_equiv_id {X Y : Scheme.{u}}
    [IrreducibleSpace X] [IrreducibleSpace Y]
    (F : X.PartialMap Y) (G : Y.PartialMap X) [IsDominant F.hom] [IsDominant G.hom]
    (hFG : (F.comp G).equiv (Scheme.PartialMap.id X))
    (hGF : (G.comp F).equiv (Scheme.PartialMap.id Y)) :
    ∃ (U : X.Opens) (V : Y.Opens) (_ : Dense (U : Set X)) (_ : Dense (V : Set Y))
      (i : U.toScheme ≅ V.toScheme) (hUF : U ≤ F.domain),
      i.hom ≫ V.ι = X.homOfLE hUF ≫ F.hom := by
  obtain ⟨W₁, hW₁, hW₁l₀, hW₁r, e₁₀⟩ := hFG
  obtain ⟨W₂, hW₂, hW₂l₀, hW₂r, e₂₀⟩ := hGF
  have hid₁ : X.homOfLE hW₁r ≫ (Scheme.PartialMap.id X).hom = W₁.ι := by
    have h : (Scheme.PartialMap.id X).hom = ((Scheme.PartialMap.id X).domain).ι ≫ 𝟙 X := rfl
    rw [h, Category.comp_id, Scheme.homOfLE_ι]
  have hid₂ : Y.homOfLE hW₂r ≫ (Scheme.PartialMap.id Y).hom = W₂.ι := by
    have h : (Scheme.PartialMap.id Y).hom = ((Scheme.PartialMap.id Y).domain).ι ≫ 𝟙 Y := rfl
    rw [h, Category.comp_id, Scheme.homOfLE_ι]
  rw [Scheme.PartialMap.restrict_hom, Scheme.PartialMap.restrict_hom, hid₁] at e₁₀
  rw [Scheme.PartialMap.restrict_hom, Scheme.PartialMap.restrict_hom, hid₂] at e₂₀
  -- From here on everything is phrased in the *unfolded* vocabulary of `PartialMap.comp`,
  -- so that no `rw` ever has to see through the definition of `comp`.
  have hCA : F.domain.ι ''ᵁ (F.hom ⁻¹ᵁ G.domain) ≤ F.domain := F.domain.ι_image_le _
  have hDB : G.domain.ι ''ᵁ (G.hom ⁻¹ᵁ F.domain) ≤ G.domain := G.domain.ι_image_le _
  have hW₁l : W₁ ≤ F.domain.ι ''ᵁ (F.hom ⁻¹ᵁ G.domain) := hW₁l₀
  have hW₂l : W₂ ≤ G.domain.ι ''ᵁ (G.hom ⁻¹ᵁ F.domain) := hW₂l₀
  set ψ : (F.domain.ι ''ᵁ (F.hom ⁻¹ᵁ G.domain)).toScheme ⟶ G.domain.toScheme :=
    (F.domain.ι.isoImage (F.hom ⁻¹ᵁ G.domain)).inv ≫ F.hom ∣_ G.domain with hψdef
  set χ : (G.domain.ι ''ᵁ (G.hom ⁻¹ᵁ F.domain)).toScheme ⟶ F.domain.toScheme :=
    (G.domain.ι.isoImage (G.hom ⁻¹ᵁ F.domain)).inv ≫ G.hom ∣_ F.domain with hχdef
  have hψι : ψ ≫ G.domain.ι = X.homOfLE hCA ≫ F.hom := by
    rw [hψdef, Category.assoc, morphismRestrict_ι, ← Category.assoc,
      Scheme.Opens.isoImage_ι_inv_ι]
  have hχι : χ ≫ F.domain.ι = Y.homOfLE hDB ≫ G.hom := by
    rw [hχdef, Category.assoc, morphismRestrict_ι, ← Category.assoc,
      Scheme.Opens.isoImage_ι_inv_ι]
  have e₁ : X.homOfLE hW₁l ≫ ψ ≫ G.hom = W₁.ι := by
    rw [hψdef, Category.assoc]; exact e₁₀
  have e₂ : Y.homOfLE hW₂l ≫ χ ≫ F.hom = W₂.ι := by
    rw [hχdef, Category.assoc]; exact e₂₀
  -- the two dense opens
  set S : X.Opens := F.domain.ι ''ᵁ (F.hom ⁻¹ᵁ W₂) with hSdef
  set T : Y.Opens := G.domain.ι ''ᵁ (G.hom ⁻¹ᵁ W₁) with hTdef
  have hSne : (S : Set X).Nonempty := by
    simpa [hSdef, ← Set.nonempty_preimage_iff] using
      F.hom.denseRange.inter_open_nonempty _ W₂.2 hW₂.nonempty
  have hTne : (T : Set Y).Nonempty := by
    simpa [hTdef, ← Set.nonempty_preimage_iff] using
      G.hom.denseRange.inter_open_nonempty _ W₁.2 hW₁.nonempty
  have hSd : Dense (S : Set X) := S.2.dense hSne
  have hTd : Dense (T : Set Y) := T.2.dense hTne
  set U : X.Opens := W₁ ⊓ S with hUdef
  set V : Y.Opens := W₂ ⊓ T with hVdef
  have hUd : Dense (U : Set X) := hW₁.inter_of_isOpen_left hSd W₁.2
  have hVd : Dense (V : Set Y) := hW₂.inter_of_isOpen_left hTd W₂.2
  have hUW₁ : U ≤ W₁ := inf_le_left
  have hVW₂ : V ≤ W₂ := inf_le_left
  have hUC : U ≤ F.domain.ι ''ᵁ (F.hom ⁻¹ᵁ G.domain) := hUW₁.trans hW₁l
  have hUF : U ≤ F.domain := hUC.trans hCA
  have hVD : V ≤ G.domain.ι ''ᵁ (G.hom ⁻¹ᵁ F.domain) := hVW₂.trans hW₂l
  have hVG : V ≤ G.domain := hVD.trans hDB
  have eU : X.homOfLE hUC ≫ ψ ≫ G.hom = U.ι := by
    rw [show X.homOfLE hUC = X.homOfLE hUW₁ ≫ X.homOfLE hW₁l from
      (Scheme.homOfLE_homOfLE X hUW₁ hW₁l).symm, Category.assoc, e₁, Scheme.homOfLE_ι]
  have eV : Y.homOfLE hVD ≫ χ ≫ F.hom = V.ι := by
    rw [show Y.homOfLE hVD = Y.homOfLE hVW₂ ≫ Y.homOfLE hW₂l from
      (Scheme.homOfLE_homOfLE Y hVW₂ hW₂l).symm, Category.assoc, e₂, Scheme.homOfLE_ι]
  have hUCA : X.homOfLE hUC ≫ X.homOfLE hCA = X.homOfLE hUF := Scheme.homOfLE_homOfLE X hUC hCA
  have hVDB : Y.homOfLE hVD ≫ Y.homOfLE hDB = Y.homOfLE hVG := Scheme.homOfLE_homOfLE Y hVD hDB
  -- `F` maps `U` into `V`
  have hrangeF : Set.range (X.homOfLE hUF ≫ F.hom).base ⊆ Set.range V.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨u, rfl⟩
    have hu1 : u.1 ∈ W₁ := u.2.1
    have hval : (X.homOfLE hUF u).1 = u.1 := Scheme.homOfLE_apply hUF u
    refine ⟨?_, ?_⟩
    · -- `F u ∈ W₂`
      have hu2 : u.1 ∈ F.domain.ι ''ᵁ (F.hom ⁻¹ᵁ W₂) := u.2.2
      rw [← hval, Scheme.Opens.mem_ι_image_iff] at hu2
      exact hu2
    · -- `F u ∈ T`
      refine ⟨ψ (X.homOfLE hUC u), ?_, ?_⟩
      · show G.hom (ψ (X.homOfLE hUC u)) ∈ W₁
        have h3 := congr($eU u)
        simp only [Scheme.Hom.comp_apply] at h3
        rw [h3]
        exact hu1
      · have h1 := congr($hψι (X.homOfLE hUC u))
        have h2 := congr($hUCA u)
        simp only [Scheme.Hom.comp_apply] at h1 h2
        rw [h2] at h1
        exact h1
  -- `G` maps `V` into `U`
  have hrangeG : Set.range (Y.homOfLE hVG ≫ G.hom).base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨v, rfl⟩
    have hv1 : v.1 ∈ W₂ := v.2.1
    have hval : (Y.homOfLE hVG v).1 = v.1 := Scheme.homOfLE_apply hVG v
    refine ⟨?_, ?_⟩
    · have hv2 : v.1 ∈ G.domain.ι ''ᵁ (G.hom ⁻¹ᵁ W₁) := v.2.2
      rw [← hval, Scheme.Opens.mem_ι_image_iff] at hv2
      exact hv2
    · refine ⟨χ (Y.homOfLE hVD v), ?_, ?_⟩
      · show F.hom (χ (Y.homOfLE hVD v)) ∈ W₂
        have h3 := congr($eV v)
        simp only [Scheme.Hom.comp_apply] at h3
        rw [h3]
        exact hv1
      · have h1 := congr($hχι (Y.homOfLE hVD v))
        have h2 := congr($hVDB v)
        simp only [Scheme.Hom.comp_apply] at h1 h2
        rw [h2] at h1
        exact h1
  set p : U.toScheme ⟶ V.toScheme :=
    IsOpenImmersion.lift V.ι (X.homOfLE hUF ≫ F.hom) hrangeF
  set q : V.toScheme ⟶ U.toScheme :=
    IsOpenImmersion.lift U.ι (Y.homOfLE hVG ≫ G.hom) hrangeG
  have hpV : p ≫ V.ι = X.homOfLE hUF ≫ F.hom := IsOpenImmersion.lift_fac _ _ _
  have hqU : q ≫ U.ι = Y.homOfLE hVG ≫ G.hom := IsOpenImmersion.lift_fac _ _ _
  have key1 : p ≫ Y.homOfLE hVG = X.homOfLE hUC ≫ ψ := by
    rw [← cancel_mono G.domain.ι, Category.assoc, Category.assoc, Scheme.homOfLE_ι, hpV, hψι,
      ← Category.assoc, hUCA]
  have key2 : q ≫ X.homOfLE hUF = Y.homOfLE hVD ≫ χ := by
    rw [← cancel_mono F.domain.ι, Category.assoc, Category.assoc, Scheme.homOfLE_ι, hqU, hχι,
      ← Category.assoc, hVDB]
  have hpq : p ≫ q = 𝟙 U.toScheme := by
    rw [← cancel_mono U.ι, Category.assoc, hqU, Category.id_comp, ← Category.assoc, key1,
      Category.assoc]
    exact eU
  have hqp : q ≫ p = 𝟙 V.toScheme := by
    rw [← cancel_mono V.ι, Category.assoc, hpV, Category.id_comp, ← Category.assoc, key2,
      Category.assoc]
    exact eV
  exact ⟨U, V, hUd, hVd, ⟨p, q, hpq, hqp⟩, hUF, hpV⟩

/-- **The round trip of two partial maps with mutually inverse germs at the generic point is
the identity** (PROVEN 2026-07-28) — the stalk-level half of the
`Birational ↔ functionField ≃` bridge.

It is the germ-injectivity of an integral scheme that makes this work, and the proof is three
steps:

1. *The generic point lies in `(F.comp G).domain`.*  That domain is
   `F.domain.ι ''ᵁ F.hom ⁻¹ᵁ G.domain`, so this says `F.hom` carries the generic point of `X`
   to a point of `G.domain`.  In fact it carries it to the generic point of `Y`: by `hF` the
   image lies in `Set.range (Y.fromSpecStalk (genericPoint Y))`, which is
   `{y | y ⤳ genericPoint Y}` (`Scheme.range_fromSpecStalk`), and the only generization of a
   generic point in a `T0` space is itself.  Then `hy` applies.
2. *The germ of the composite is `X.fromSpecStalk (genericPoint X)`.*  `Mathlib` has no
   `fromSpecStalkOfMem_comp` — `Birational/Composition.lean` has `comp_restrict_left`,
   `comp_restrict_right` and `comp_assoc` and nothing about stalks — so it is computed here,
   and the trick that avoids unfolding `Opens.fromSpecStalkOfMem` at all is to **cancel the
   monomorphism `G.domain.ι`**: the partial-composite germ
   `Φ := W.fromSpecStalkOfMem η ≫ (isoImage).inv ≫ F.hom ∣_ G.domain` satisfies
   `Φ ≫ G.domain.ι = F.fromSpecStalkOfMem hx = φ ≫ Y.fromSpecStalk _`, which is also what
   `φ ≫ G.domain.fromSpecStalkOfMem _ hy` gives, so the two agree.  Composing with `G.hom`
   turns the right-hand side into `φ ≫ G.fromSpecStalkOfMem hy = φ ≫ ψ ≫ X.fromSpecStalk _`,
   and `hφψ` finishes.
3. *Conclude.*  `PartialMap.equiv_of_fromSpecStalkOfMem_eq` at the generic point, whose
   `X.IsGermInjectiveAt` hypothesis is free for an integral `X`, against
   `PartialMap.fromSpecStalkOfMem_toPartialMap` for the identity side.

**`φ` is NOT required to be an isomorphism, only a split mono via `hφψ`**, and step 1 is what
makes that enough: the identification `F.hom (genericPoint X) = genericPoint Y` comes from the
*range* of `Y.fromSpecStalk`, not from invertibility of `φ`.  At the one call site `φ` happens
to be an isomorphism, but assuming it would hide which fact is doing the work. -/
theorem partialMap_comp_equiv_id_of_fromSpecStalkOfMem {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y]
    (F : X.PartialMap Y) (G : Y.PartialMap X) [IsDominant F.hom]
    (hx : genericPoint X ∈ F.domain) (hy : genericPoint Y ∈ G.domain)
    (φ : Spec X.functionField ⟶ Spec Y.functionField)
    (hF : F.fromSpecStalkOfMem hx = φ ≫ Y.fromSpecStalk (genericPoint Y))
    (ψ : Spec Y.functionField ⟶ Spec X.functionField)
    (hG : G.fromSpecStalkOfMem hy = ψ ≫ X.fromSpecStalk (genericPoint X))
    (hφψ : φ ≫ ψ = 𝟙 _) :
    (F.comp G).equiv (Scheme.PartialMap.id X) := by
  -- the closed point of `Spec 𝒪_{X,η}` is `η`, seen inside `F.domain`
  have hptι : F.domain.ι (F.domain.fromSpecStalkOfMem (genericPoint X) hx
      (IsLocalRing.closedPoint X.functionField)) = genericPoint X := by
    rw [← Scheme.Hom.comp_apply, Scheme.Opens.fromSpecStalkOfMem_ι,
      Scheme.fromSpecStalk_closedPoint]
  have hpt : F.domain.fromSpecStalkOfMem (genericPoint X) hx
      (IsLocalRing.closedPoint X.functionField) = ⟨genericPoint X, hx⟩ := Subtype.ext hptι
  -- step 1: `F` carries the generic point of `X` to the generic point of `Y`
  have h1 : F.fromSpecStalkOfMem hx (IsLocalRing.closedPoint X.functionField)
      = (Y.fromSpecStalk (genericPoint Y)) (φ (IsLocalRing.closedPoint X.functionField)) := by
    rw [hF, Scheme.Hom.comp_apply]
  have hmem : F.hom ⟨genericPoint X, hx⟩
      ∈ Set.range (Y.fromSpecStalk (genericPoint Y)).base := by
    refine ⟨φ (IsLocalRing.closedPoint X.functionField), ?_⟩
    rw [← h1]
    show F.hom (F.domain.fromSpecStalkOfMem (genericPoint X) hx
      (IsLocalRing.closedPoint X.functionField)) = F.hom ⟨genericPoint X, hx⟩
    rw [hpt]
  rw [Scheme.range_fromSpecStalk] at hmem
  have hFgen : F.hom ⟨genericPoint X, hx⟩ = genericPoint Y :=
    (hmem.antisymm ((genericPoint_spec Y).specializes (Set.mem_univ _))).eq
  have hxV : (⟨genericPoint X, hx⟩ : F.domain) ∈ F.hom ⁻¹ᵁ G.domain := by
    show F.hom ⟨genericPoint X, hx⟩ ∈ G.domain
    rw [hFgen]; exact hy
  have hz : genericPoint X ∈ (F.comp G).domain := ⟨⟨genericPoint X, hx⟩, hxV, rfl⟩
  -- step 2: the germ of the composite, computed by cancelling `G.domain.ι`
  have hWle : F.domain.ι ''ᵁ (F.hom ⁻¹ᵁ G.domain) ≤ F.domain := F.domain.ι_image_le _
  have hstalk : (F.domain.ι ''ᵁ (F.hom ⁻¹ᵁ G.domain)).fromSpecStalkOfMem (genericPoint X) hz
        ≫ X.homOfLE hWle
      = F.domain.fromSpecStalkOfMem (genericPoint X) hx := by
    rw [← cancel_mono F.domain.ι, Category.assoc, Scheme.homOfLE_ι,
      Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.Opens.fromSpecStalkOfMem_ι]
  have hΦ : (F.domain.ι ''ᵁ (F.hom ⁻¹ᵁ G.domain)).fromSpecStalkOfMem (genericPoint X) hz
        ≫ (F.domain.ι.isoImage (F.hom ⁻¹ᵁ G.domain)).inv ≫ (F.hom ∣_ G.domain)
      = φ ≫ G.domain.fromSpecStalkOfMem (genericPoint Y) hy := by
    rw [← cancel_mono G.domain.ι, Category.assoc, Category.assoc, morphismRestrict_ι,
      Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
      ← Category.assoc ((F.domain.ι.isoImage (F.hom ⁻¹ᵁ G.domain)).inv),
      Scheme.Opens.isoImage_ι_inv_ι, ← Category.assoc, hstalk, ← hF]
    rfl
  have hgerm : (F.comp G).fromSpecStalkOfMem hz = X.fromSpecStalk (genericPoint X) := by
    have hsplit : (F.comp G).fromSpecStalkOfMem hz
        = ((F.domain.ι ''ᵁ (F.hom ⁻¹ᵁ G.domain)).fromSpecStalkOfMem (genericPoint X) hz
          ≫ (F.domain.ι.isoImage (F.hom ⁻¹ᵁ G.domain)).inv ≫ (F.hom ∣_ G.domain)) ≫ G.hom := by
      rw [Category.assoc, Category.assoc]
      rfl
    rw [hsplit, hΦ, Category.assoc]
    show φ ≫ G.fromSpecStalkOfMem hy = _
    rw [hG, ← Category.assoc, hφψ, Category.id_comp]
  -- step 3
  refine Scheme.PartialMap.equiv_of_fromSpecStalkOfMem_eq _ _ hz trivial ?_
  rw [hgerm, Scheme.PartialMap.fromSpecStalkOfMem_toPartialMap, Category.comp_id]

/-! ### The bridge: an isomorphism of function fields over `S` is a birational map over `S` -/

/-- **An isomorphism of function fields over `S` is a birational map over `S`** (PROVEN
2026-07-28 over the two leaves above) — the `Birational ↔ functionField ≃` bridge that
`Mathlib` lacks.

The proof is the standard "spread out both directions and intersect" argument:

* `PartialMap.ofFromSpecStalk sX sY (e.hom ≫ Y.fromSpecStalk _) _ : X.PartialMap Y` and,
  from `e.inv` and the inverse commuting triangle, `G : Y.PartialMap X`.  These need
  `IsIntegral` on the source and `LocallyOfFiniteType` on the target — exactly the hypotheses
  here — and they come with their germs (`fromSpecStalkOfMem_ofFromSpecStalk`) and with their
  commuting triangles over `S` (`ofFromSpecStalk_comp`).
* Both are dominant, by `PartialMap.isDominant_hom_of_fromSpecStalkOfMem` above.
* Their two round trips are the identity, by
  `partialMap_comp_equiv_id_of_fromSpecStalkOfMem`, fed with `e.hom_inv_id` and `e.inv_hom_id`.
* `exists_opens_iso_of_partialMap_equiv_id` then produces dense opens `U ≤ X`, `V ≤ Y` and an
  isomorphism `i : U ≅ V` with `i.hom ≫ V.ι = X.homOfLE _ ≫ F.hom`, and `F`'s commuting
  triangle turns that into `i.hom ≫ V.ι ≫ sY = U.ι ≫ sX`.
* Finally `Opens.birationalOver_of_dense` on both sides and `Hom.birationalOver` on `i.hom`
  compose to `BirationalOver sX sY`.

**The `IsOver` condition is carried by `hcomm` alone** — no separatedness hypothesis is needed
anywhere, because the `S`-compatibility never has to be *re-derived* from an equality of
rational maps; it is transported from `ofFromSpecStalk_comp` through one restriction.

**WHY THE HYPOTHESES ARE WHAT THEY ARE.**  `LocallyOfFiniteType` on both structure morphisms
is what makes spreading out possible at all (`spread_out_of_isGermInjective'`), and it cannot
be dropped: without it, `Spec K(X) ⟶ Y` need not extend over any open of `X`.  `IsIntegral`
gives the germ-injectivity that makes the spread-out unique, i.e. makes
`equiv_of_fromSpecStalkOfMem_eq` available; without it, `Spec K(X) ⟶ Y` does not determine the
rational map. -/
theorem birationalOver_of_iso_specFunctionField {S X Y : Scheme.{u}}
    (sX : X ⟶ S) (sY : Y ⟶ S) [IsIntegral X] [IsIntegral Y]
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY]
    (e : Spec X.functionField ≅ Spec Y.functionField)
    (hcomm : e.hom ≫ Y.fromSpecStalk (genericPoint Y) ≫ sY
      = X.fromSpecStalk (genericPoint X) ≫ sX) :
    Scheme.BirationalOver sX sY := by
  have hF0 : (e.hom ≫ Y.fromSpecStalk (genericPoint Y)) ≫ sY
      = X.fromSpecStalk (genericPoint X) ≫ sX := by
    rw [Category.assoc]; exact hcomm
  have hG0 : (e.inv ≫ X.fromSpecStalk (genericPoint X)) ≫ sX
      = Y.fromSpecStalk (genericPoint Y) ≫ sY := by
    rw [Category.assoc, ← hcomm, ← Category.assoc, ← Category.assoc, e.inv_hom_id,
      Category.id_comp]
  set F : X.PartialMap Y := Scheme.PartialMap.ofFromSpecStalk sX sY _ hF0 with hFdef
  set G : Y.PartialMap X := Scheme.PartialMap.ofFromSpecStalk sY sX _ hG0 with hGdef
  have hxF : genericPoint X ∈ F.domain :=
    Scheme.PartialMap.mem_domain_ofFromSpecStalk sX sY _ hF0
  have hyG : genericPoint Y ∈ G.domain :=
    Scheme.PartialMap.mem_domain_ofFromSpecStalk sY sX _ hG0
  have hFgerm : F.fromSpecStalkOfMem hxF = e.hom ≫ Y.fromSpecStalk (genericPoint Y) :=
    Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk sX sY _ hF0
  have hGgerm : G.fromSpecStalkOfMem hyG = e.inv ≫ X.fromSpecStalk (genericPoint X) :=
    Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk sY sX _ hG0
  haveI : IsDominant F.hom :=
    Scheme.PartialMap.isDominant_hom_of_fromSpecStalkOfMem F hxF e.hom hFgerm
  haveI : IsDominant G.hom :=
    Scheme.PartialMap.isDominant_hom_of_fromSpecStalkOfMem G hyG e.inv hGgerm
  have hFG : (F.comp G).equiv (Scheme.PartialMap.id X) :=
    partialMap_comp_equiv_id_of_fromSpecStalkOfMem F G hxF hyG e.hom hFgerm e.inv hGgerm
      e.hom_inv_id
  have hGF : (G.comp F).equiv (Scheme.PartialMap.id Y) :=
    partialMap_comp_equiv_id_of_fromSpecStalkOfMem G F hyG hxF e.inv hGgerm e.hom hFgerm
      e.inv_hom_id
  obtain ⟨U, V, hU, hV, i, hUF, hi⟩ := exists_opens_iso_of_partialMap_equiv_id F G hFG hGF
  have hFover : F.hom ≫ sY = F.domain.ι ≫ sX :=
    Scheme.PartialMap.ofFromSpecStalk_comp sX sY _ hF0
  have hkey : i.hom ≫ V.ι ≫ sY = U.ι ≫ sX := by
    rw [← Category.assoc, hi, Category.assoc, hFover, ← Category.assoc, Scheme.homOfLE_ι]
  exact (Scheme.Opens.birationalOver_of_dense U sX hU).symm.trans
    ((Scheme.Hom.birationalOver i.hom (V.ι ≫ sY) (U.ι ≫ sX) hkey).trans
      (Scheme.Opens.birationalOver_of_dense V sY hV))

/-! ### Lüroth, in scheme language -/

/-- **The function field of affine `n`-space over `K` with `Unique n` is `K(t)`, compatibly
with the structure morphism to `Spec K`** (**PROVEN 2026-07-28**) — step 2 of the Lüroth
translation, isolated because it mentions neither `P`, nor `u`, nor smoothness, nor Lüroth:
it is pure affine bookkeeping about `𝔸(n; Spec K)`.

**Why the conclusion is a triangle over `Spec K` rather than a bare `≅`.**  A bare ring
isomorphism `K(𝔸) ≃ RatFunc K` is useless downstream: the consumer needs to know it is the
one *over* `K`, and the only place that can be pinned is the statement.  Composing the
displayed `e.hom` with the two-step map down to `Spec K` and demanding
`Spec.map (algebraMap K (RatFunc K))` says exactly that, and it says it without introducing
an `Algebra K (𝔸(n; Spec K)).functionField` instance that `Mathlib` does not have and that
would have to be justified anyway.

**Route (each step exists in the pin; this is bookkeeping, not mathematics).**

1. `g := (AffineSpace.SpecIso n (CommRingCat.of K)).hom : 𝔸(n; Spec K) ⟶ Spec (MvPolynomial n K)`
   is an isomorphism, so `g (genericPoint 𝔸) = genericPoint (Spec (MvPolynomial n K))`
   (`genericPoint_eq_of_isOpenImmersion`), which is `⊥` (`genericPoint_eq_bot_of_affine`).
2. `Scheme.SpecMap_stalkMap_fromSpecStalk g` moves `𝔸.fromSpecStalk` across `g`, and
   `AffineSpace.SpecIso_inv_over` — `(SpecIso n R).inv ≫ 𝔸(n; Spec R) ↘ Spec R
   = Spec.map (CommRingCat.ofHom C)` — is exactly the base compatibility, already proven in
   `Mathlib`.  So the whole left-hand side becomes a composite of `Spec.map`s.
3. `Spec.fromSpecStalk_eq'` — `(Spec R).fromSpecStalk x = Spec.map (StructureSheaf.toStalk R _)`
   — turns the remaining geometric factor into a ring map, after which
   `Spec.map_comp`/`Spec.map_inj` reduce the goal to an equality of ring maps `K ⟶ RatFunc K`.
4. The ring iso itself: `functionField_isFractionRing_of_affine` makes
   `(Spec (MvPolynomial n K)).functionField` a fraction field of `MvPolynomial n K`;
   `MvPolynomial.uniqueAlgEquiv K n : MvPolynomial n K ≃ₐ[K] K[X]` (this is the current name —
   `pUnitAlgEquiv` is deprecated since 2026-04-15 and takes `PUnit`, not a general `Unique n`)
   transports that to a fraction field of `K[X]`, i.e. to `RatFunc K`, and
   `IsFractionRing.ringEquivOfRingEquiv` supplies the isomorphism, with
   `ringEquivOfRingEquiv_algebraMap` giving the `K`-compatibility in one rewrite.

**Two `CommRingCat` traps, both of which cost a cycle here and neither of which is visible in
the mathematics.**

*First: the `Algebra`/`IsFractionRing` instances on `↥(CommRingCat.of R)` are NOT found by
instance search*, even though `IsDomain ↥(CommRingCat.of (MvPolynomial n K))` and
`IrreducibleSpace ↥(Spec (CommRingCat.of (MvPolynomial n K)))` both are.  Supply them by name:
`letI := (StructureSheaf.toStalk _ (genericPoint _)).hom.toAlgebra` — which is literally
`Mathlib`'s own instance, so nothing is being changed, only re-found — and then
`functionField_isFractionRing_of_affine _`.  This also has the pleasant side effect that
`algebraMap` is *definitionally* `toStalk`, which is what lets the `K`-compatibility be
discharged by a single `show`.

*Second: use `Spec.fromSpecStalk_eq`, NOT `Spec.fromSpecStalk_eq'`.*  The two differ only by
which spelling of the ring map they expose — `(ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ x`
versus `StructureSheaf.toStalk R x` — and `Mathlib` proves the second FROM the first by `rfl`,
so they are interchangeable to `exact`.  They are *not* interchangeable to `rw`: `toStalk R x`
lands in `(structurePresheafInCommRingCat R).stalk x`, while the isomorphism produced above
lands in `(Spec R).presheaf.stalk x`.  Those are equal only by delta, `rw` type-checks its
motive at `instances` transparency, and the resulting `Spec.map_comp` failure is reported as
"did not find an occurrence of the pattern" with the pattern plainly visible in the goal.
The primed version is the one that "breaks abstraction boundaries", and that is exactly the
abstraction boundary `rw` is standing on. -/
theorem exists_iso_specRatFunc_specFunctionField_affineSpace {K : Type u} [Field K]
    {n : Type u} [Unique n] :
    ∃ e : Spec (CommRingCat.of (RatFunc K)) ≅
        Spec (𝔸(n; Spec (CommRingCat.of K))).functionField,
      e.hom ≫ (𝔸(n; Spec (CommRingCat.of K))).fromSpecStalk
            (genericPoint (𝔸(n; Spec (CommRingCat.of K)))) ≫
          (𝔸(n; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K))
        = Spec.map (CommRingCat.ofHom (algebraMap K (RatFunc K))) := by
  have hbase := AffineSpace.SpecIso_inv_over (n := n) (CommRingCat.of K)
  set g : 𝔸(n; Spec (CommRingCat.of K)) ⟶ Spec (CommRingCat.of (MvPolynomial n K)) :=
    (AffineSpace.SpecIso n (CommRingCat.of K)).hom with hg
  have hstr : (𝔸(n; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K))
      = g ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := n) (R := K))) := by
    rw [← hbase, hg, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  haveI : IsIso g := by rw [hg]; infer_instance
  have hgen : g (genericPoint (𝔸(n; Spec (CommRingCat.of K))))
      = genericPoint (Spec (CommRingCat.of (MvPolynomial n K))) :=
    genericPoint_eq_of_isOpenImmersion g
  have hstalk := Scheme.SpecMap_stalkMap_fromSpecStalk g
    (x := genericPoint (𝔸(n; Spec (CommRingCat.of K))))
  obtain ⟨φ, hφ⟩ : ∃ φ : (Spec (CommRingCat.of (MvPolynomial n K))).presheaf.stalk
        (g (genericPoint (𝔸(n; Spec (CommRingCat.of K))))) ≅ CommRingCat.of (RatFunc K),
      CommRingCat.ofHom (MvPolynomial.C (σ := n) (R := K)) ≫
          ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial n K))).inv ≫
            (Spec (CommRingCat.of (MvPolynomial n K))).presheaf.germ ⊤
              (g (genericPoint (𝔸(n; Spec (CommRingCat.of K))))) trivial) ≫ φ.hom
        = CommRingCat.ofHom (algebraMap K (RatFunc K)) := by
    rw [hgen]
    letI alg : Algebra ↥(CommRingCat.of (MvPolynomial n K))
        ↥(Spec (CommRingCat.of (MvPolynomial n K))).functionField :=
      (StructureSheaf.toStalk (CommRingCat.of (MvPolynomial n K))
        (genericPoint ↥(Spec (CommRingCat.of (MvPolynomial n K))))).hom.toAlgebra
    haveI hfr : IsFractionRing ↥(CommRingCat.of (MvPolynomial n K))
        ↥(Spec (CommRingCat.of (MvPolynomial n K))).functionField :=
      functionField_isFractionRing_of_affine _
    refine ⟨(IsFractionRing.ringEquivOfRingEquiv
      (A := ↥(CommRingCat.of (MvPolynomial n K))) (B := Polynomial K)
      (K := ↥(Spec (CommRingCat.of (MvPolynomial n K))).functionField)
      (L := RatFunc K)
      (MvPolynomial.uniqueAlgEquiv K n).toRingEquiv).toCommRingCatIso, ?_⟩
    ext c
    show (IsFractionRing.ringEquivOfRingEquiv
        (A := ↥(CommRingCat.of (MvPolynomial n K))) (B := Polynomial K)
        (K := ↥(Spec (CommRingCat.of (MvPolynomial n K))).functionField) (L := RatFunc K)
        (MvPolynomial.uniqueAlgEquiv K n).toRingEquiv)
        (algebraMap ↥(CommRingCat.of (MvPolynomial n K))
          ↥(Spec (CommRingCat.of (MvPolynomial n K))).functionField (MvPolynomial.C c))
      = algebraMap K (RatFunc K) c
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    simp [← MvPolynomial.algebraMap_eq]
  haveI : IsIso (Scheme.Hom.stalkMap g (genericPoint (𝔸(n; Spec (CommRingCat.of K))))) :=
    inferInstance
  set ψ := inv (Scheme.Hom.stalkMap g (genericPoint (𝔸(n; Spec (CommRingCat.of K))))) ≫ φ.hom
    with hψ
  have hkey : Scheme.Hom.stalkMap g (genericPoint (𝔸(n; Spec (CommRingCat.of K)))) ≫ ψ
      = φ.hom := by
    rw [hψ]; exact IsIso.hom_inv_id_assoc _ _
  have h2 : Spec.map ψ ≫
      Spec.map (Scheme.Hom.stalkMap g (genericPoint (𝔸(n; Spec (CommRingCat.of K)))))
      = Spec.map φ.hom := by
    rw [← Spec.map_comp, hkey]
  refine ⟨asIso (Spec.map ψ), ?_⟩
  rw [asIso_hom, hstr,
    ← Category.assoc ((𝔸(n; Spec (CommRingCat.of K))).fromSpecStalk _) g, ← hstalk,
    Spec.fromSpecStalk_eq]
  simp only [Category.assoc]
  rw [← Category.assoc, h2, ← Spec.map_comp, ← Spec.map_comp, Category.assoc, hφ]

/-- **The stalk map of a dominant `u : 𝔸(n; Spec K) ⟶ P` at the generic point is a `K`-embedding
`K(P) ↪ K(t)`** (**PROVEN 2026-07-28**) — step 1 of the Lüroth translation, and the last piece
of it that is about SCHEMES rather than about fields.

Note what is *absent* from the hypotheses: `hcurve`.  Nothing here needs `P` to be a curve, or
even to be positive-dimensional; the degenerate `P = Spec K` satisfies this statement with
`φ = algebraMap K (RatFunc K)`.  That is precisely why the non-degeneracy has to be carried
separately by `exists_iso_specRatFunc_specFunctionField_of_hom` below, and it is the honest
place to see that `hcurve` is load-bearing exactly once.

Injectivity of `φ` is not asserted because it is free downstream: `P.functionField` is a field
(`IsIntegral P`) and `RatFunc K` is nonzero, so any ring map between them is injective.  Adding
it to the statement would only oblige every caller to re-derive it.

**Proof.**  `genericPoint_eq_of_isDominant` identifies `u (genericPoint 𝔸)` with `genericPoint P`,
`Scheme.SpecMap_stalkMap_fromSpecStalk` is the commuting square for the stalk map, `hu` turns
`u ≫ strP` into the structure morphism of `𝔸`, and
`exists_iso_specRatFunc_specFunctionField_affineSpace` closes the triangle.  The one piece of
friction is that `Scheme.Hom.stalkMap u (genericPoint 𝔸)` lands in `P.presheaf.stalk
(u (genericPoint 𝔸))` and the conclusion needs `P.functionField`; `rw`ing the point is not
available (the surrounding composite becomes ill-typed at `instances` transparency), so the
point is moved by an `eqToHom` whose defining property is proven by `rintro x rfl` on a
UNIVERSALLY QUANTIFIED point — the standard way to `subst` an equation whose sides are both
closed terms. -/
theorem exists_hom_functionField_ratFunc_of_isDominant {K : Type u} [Field K]
    {n : Type u} [Unique n] {P : Scheme.{u}} {strP : P ⟶ Spec (CommRingCat.of K)}
    [IsIntegral P]
    (u : 𝔸(n; Spec (CommRingCat.of K)) ⟶ P)
    (hu : u ≫ strP = 𝔸(n; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K))
    (hdom : IsDominant u) :
    ∃ φ : P.functionField ⟶ CommRingCat.of (RatFunc K),
      Spec.map φ ≫ P.fromSpecStalk (genericPoint P) ≫ strP
        = Spec.map (CommRingCat.ofHom (algebraMap K (RatFunc K))) := by
  obtain ⟨eA, hA⟩ := exists_iso_specRatFunc_specFunctionField_affineSpace (K := K) (n := n)
  have hu' : u (genericPoint (𝔸(n; Spec (CommRingCat.of K)))) = genericPoint P :=
    genericPoint_eq_of_isDominant u
  have transport : ∀ (x : ↥P) (h : x = u (genericPoint (𝔸(n; Spec (CommRingCat.of K))))),
      Spec.map (eqToHom (congrArg P.presheaf.stalk h) ≫
          Scheme.Hom.stalkMap u (genericPoint (𝔸(n; Spec (CommRingCat.of K))))) ≫
        P.fromSpecStalk x
      = (𝔸(n; Spec (CommRingCat.of K))).fromSpecStalk
          (genericPoint (𝔸(n; Spec (CommRingCat.of K)))) ≫ u := by
    rintro x rfl
    simp
  refine ⟨(eqToHom (congrArg P.presheaf.stalk hu'.symm) ≫
      Scheme.Hom.stalkMap u (genericPoint (𝔸(n; Spec (CommRingCat.of K))))) ≫
      Spec.preimage eA.hom, ?_⟩
  rw [Spec.map_comp, Spec.map_preimage, Category.assoc, ← Category.assoc _ (P.fromSpecStalk _),
    transport _ hu'.symm, Category.assoc, hu, hA]

/-- **A smooth curve over `K` has strictly more rational functions than `K`** (**PROVEN
2026-07-28**) — this is where `hcurve` is consumed, and it is the whole reason the Lüroth
statement below is not vacuous.

The map whose surjectivity is denied is the ring map underlying `P.fromSpecStalk (genericPoint P)
≫ strP : Spec K(P) ⟶ Spec K`, i.e. the structure map `K ⟶ K(P)`.  It is phrased through
`Spec.preimage` rather than as `algebraMap` on purpose: `Mathlib` has no
`Algebra K X.functionField` instance, and declaring one here would fix a particular instance in
the STATEMENT, which is exactly the kind of choice a leaf should not make on its consumers'
behalf.  `Spec.preimage` is canonical (`Scheme.Spec` is fully faithful), so there is nothing to
choose.

**FALSITY WITHOUT `hcurve`.**  Drop `hcurve` and take `P = Spec K`: then `K(P) = K`, the map is
the identity, and the statement is false.  So this is the load-bearing hypothesis of the whole
Lüroth translation, and it is used nowhere else in this file.

**Route.**  Suppose `K ⟶ K(P)` is surjective, and let `U` be any nonempty affine open of `P`.
`Γ(P, U) ⟶ K(P)` is injective (`Scheme.germToFunctionField_injective`, which needs
`IsIntegral P`), and the composite `K ⟶ Γ(P, U) ⟶ K(P)` is the assumed surjection, so
`Γ(P, U) ⟶ K(P)` is bijective and `Γ(P, U)` is a FIELD.  Hence `U ≅ Spec Γ(P, U)` has exactly
one point (`instance : Unique (PrimeSpectrum R)` for a field `R`).  Affine opens form a basis,
so every point of `P` has a singleton open neighbourhood, i.e. `P` is discrete; a discrete
preirreducible space is a subsingleton.  But `hcurve` gives `Infinite P` by
`infinite_of_smoothOfRelativeDimension_one` (proven in `CurveExtension.lean`) — contradiction.

**Do not try to run this argument on a single affine open.**  "Some nonempty affine open is a
single point" is NOT a contradiction: `Spec` of a DVR has a one-point open (its generic point)
while the scheme has two points.  The argument genuinely needs *every* affine open, which is
what turns it into a statement about the topology of `P` rather than about one ring.

**The step that looked expensive and is not.**  "The composite `K ⟶ Γ(P, U) ⟶ K(P)` is the
structure map" would be a painful `appTop` computation if done on global sections.  It is
free at the level of SCHEMES: `IsAffineOpen.fromSpecStalk` *is* `Spec.map (germ) ≫ hU.fromSpec`
by definition, and `fromSpecStalk_eq_fromSpecStalk` says that equals `P.fromSpecStalk` for any
affine open containing the point.  So `Spec.map_injective` turns the desired factorisation
`α = β ≫ germ` into a three-rewrite identity of scheme morphisms, with
`β := Spec.preimage (hU.fromSpec ≫ strP)` — no `appTop`, no `ΓSpecIso`.  Prefer this shape
whenever a ring-level factorisation through an affine open is needed.

**Last step, once `Γ(P, U)` is a field**: the *generic point* does the topology.  Rather than
"discrete + preirreducible ⟹ subsingleton", note that a singleton open must contain the generic
point (`IsGenericPoint.mem_open_set_iff`), so every point of `P` *equals* `genericPoint P`
directly.  One `Subsingleton.elim` inside `↥U` finishes it. -/
theorem not_surjective_specPreimage_of_smoothOfRelativeDimension_one {K : Type u} [Field K]
    {P : Scheme.{u}} {strP : P ⟶ Spec (CommRingCat.of K)}
    [IsIntegral P] (hcurve : SmoothOfRelativeDimension 1 strP) :
    ¬ Function.Surjective
      (Spec.preimage (P.fromSpecStalk (genericPoint P) ≫ strP)).hom := by
  haveI := hcurve
  haveI : Infinite ↥P := infinite_of_smoothOfRelativeDimension_one strP
  intro hsurj
  have hpt : ∀ x : ↥P, x = genericPoint P := by
    intro x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      P.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    have hηU : genericPoint P ∈ U :=
      ((genericPoint_spec P).mem_open_set_iff U.2).mpr ⟨x, Set.mem_univ x, hxU⟩
    have hinj : Function.Injective (P.presheaf.germ U (genericPoint P) hηU) :=
      germ_injective_of_isIntegral P (genericPoint P) hηU
    have hfac : Spec.preimage (P.fromSpecStalk (genericPoint P) ≫ strP)
        = Spec.preimage (hU.fromSpec ≫ strP) ≫ P.presheaf.germ U (genericPoint P) hηU := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, ← Category.assoc,
        ← IsAffineOpen.fromSpecStalk, hU.fromSpecStalk_eq_fromSpecStalk hηU]
    have hsurjgerm : Function.Surjective (P.presheaf.germ U (genericPoint P) hηU) := by
      intro y
      obtain ⟨c, hc⟩ := hsurj y
      exact ⟨(Spec.preimage (hU.fromSpec ≫ strP)).hom c, by rw [← hc, hfac]; rfl⟩
    letI : Field ↥Γ(P, U) :=
      ((RingEquiv.ofBijective (P.presheaf.germ U (genericPoint P) hηU).hom
        ⟨hinj, hsurjgerm⟩).toMulEquiv.isField (Field.toIsField _)).toField
    have hinj2 : Function.Injective (hU.isoSpec.hom.base) := by
      intro a b hab
      have h := congrArg (hU.isoSpec.inv.base) hab
      simpa [← Scheme.Hom.comp_apply] using h
    haveI : Subsingleton ↥(Spec Γ(P, U)) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum ↥Γ(P, U)))
    haveI : Subsingleton ↥U := hinj2.subsingleton
    exact congrArg Subtype.val (Subsingleton.elim (⟨x, hxU⟩ : ↥U) ⟨genericPoint P, hηU⟩)
  exact absurd ⟨fun a b => (hpt a).trans (hpt b).symm⟩ (not_subsingleton ↥P)

/-- **A `K`-embedding `K(P) ↪ K(t)` of the function field of a CURVE is an isomorphism**
(**PROVEN 2026-07-28**, over the non-degeneracy leaf immediately above) — Lüroth, and nothing
else.

Compared with `exists_iso_specRatFunc_specFunctionField_of_isDominant`, which it is used to
prove, this drops `n`, `u` and `hdom` entirely: the affine line has done its work by producing
`φ`, and what remains is a statement about a field extension `K ⊆ K(P) ⊆ K(t)`, namely:

1. *The image is not `⊥`* — supplied by
   `not_surjective_specPreimage_of_smoothOfRelativeDimension_one` above, which is where
   `hcurve` is consumed and without which this leaf is FALSE (`P = Spec K`).  The translation
   from "`K ⟶ K(P)` is not surjective" to "`Φ.fieldRange ≠ ⊥`" is three lines and uses only
   injectivity of `Φ`, which is free because `K(P)` is a field.
2. *Lüroth.*  `RatFunc.Luroth.algEquiv` — **already proven in the pin
   (`Mathlib/FieldTheory/RatFunc/Luroth.lean`); do not reprove it** — applied to
   `E := Φ.fieldRange`, gives `K⟮X⟯ ≃ₐ[K] E`, and `AlgEquiv.ofInjectiveField Φ` gives
   `K(P) ≃ₐ[K] E`.  `Spec` of the composite is the required `e`, and its triangle over `Spec K`
   is one `AlgEquiv.commutes`.

**The isomorphism is NOT `Spec.map φ`**, and cannot be: `φ` may have degree `> 1` — that is the
whole content of Lüroth — so Lüroth's *different* generator is what makes `e` exist.  Hence the
existential, and hence `hφ` is used only for the `K`-compatibility, never as the answer.

**How the `K`-algebra structures are obtained, and why not by instances.**  Both `K(P)` and
`K(t)` must be seen as `K`-algebras before `IntermediateField` and Lüroth apply, and `Mathlib`
has no `Algebra K X.functionField` instance.  They come from `hφ`, not from declared instances:
`α := Spec.preimage (P.fromSpecStalk _ ≫ strP)` is the structure map `K ⟶ K(P)` (canonical,
since `Scheme.Spec` is fully faithful), `letI := α.hom.toAlgebra` makes it the algebra map, and
`Spec.map_inj` turns `hφ` into `α ≫ φ = algebraMap K (RatFunc K)` — which is literally the
`commutes'` field of the `AlgHom`.  Declaring instances instead runs into the
`↥(CommRingCat.of R)` synthesis failures documented on the affine-space leaf above. -/
theorem exists_iso_specRatFunc_specFunctionField_of_hom {K : Type u} [Field K]
    {P : Scheme.{u}} {strP : P ⟶ Spec (CommRingCat.of K)}
    [IsIntegral P] (hcurve : SmoothOfRelativeDimension 1 strP)
    (φ : P.functionField ⟶ CommRingCat.of (RatFunc K))
    (hφ : Spec.map φ ≫ P.fromSpecStalk (genericPoint P) ≫ strP
      = Spec.map (CommRingCat.ofHom (algebraMap K (RatFunc K)))) :
    ∃ e : Spec (CommRingCat.of (RatFunc K)) ≅ Spec P.functionField,
      e.hom ≫ P.fromSpecStalk (genericPoint P) ≫ strP
        = Spec.map (CommRingCat.ofHom (algebraMap K (RatFunc K))) := by
  have hnotsurj := not_surjective_specPreimage_of_smoothOfRelativeDimension_one hcurve
  set α := Spec.preimage (P.fromSpecStalk (genericPoint P) ≫ strP)
  have hαmap : Spec.map α = P.fromSpecStalk (genericPoint P) ≫ strP := Spec.map_preimage _
  have hαφ : α ≫ φ = CommRingCat.ofHom (algebraMap K (RatFunc K)) := by
    rw [← Spec.map_inj, Spec.map_comp, hαmap]
    exact hφ
  letI : Algebra K ↥P.functionField := α.hom.toAlgebra
  have hcomm : ∀ c : K, φ.hom (algebraMap K ↥P.functionField c) = algebraMap K (RatFunc K) c :=
    fun c => congrArg (fun f : CommRingCat.of K ⟶ CommRingCat.of (RatFunc K) => f.hom c) hαφ
  let Φ : ↥P.functionField →ₐ[K] RatFunc K := { φ.hom with commutes' := hcomm }
  have hΦinj : Function.Injective Φ := Φ.toRingHom.injective
  have hE : Φ.fieldRange ≠ ⊥ := by
    intro h
    refine hnotsurj fun y => ?_
    have hy : Φ y ∈ Φ.fieldRange := ⟨y, rfl⟩
    rw [h, IntermediateField.mem_bot] at hy
    obtain ⟨c, hc⟩ := hy
    exact ⟨c, hΦinj (by rw [← hc, ← hcomm c]; rfl)⟩
  let θ : ↥P.functionField ≃ₐ[K] ↥Φ.fieldRange := AlgEquiv.ofInjectiveField Φ
  let ρ : ↥P.functionField ≃ₐ[K] RatFunc K := θ.trans (RatFunc.Luroth.algEquiv hE).symm
  refine ⟨asIso (Spec.map (ρ.toRingEquiv.toCommRingCatIso.hom)), ?_⟩
  rw [asIso_hom, ← hαmap, ← Spec.map_comp]
  congr 1
  ext c
  exact ρ.commutes c

/-- **The function field of a curve over `K` dominated by the affine line is `K(t)`, compatibly
with the structure morphism** (**PROVEN 2026-07-28** over the two leaves immediately above) —
steps 1, 3 and 4 of the Lüroth translation, i.e. everything in it that is not pure affine
bookkeeping.

Stated in the SAME shape as `exists_iso_specRatFunc_specFunctionField_affineSpace` above, which
is what makes the assembly of `exists_iso_specFunctionField_affineSpace_of_isDominant` three
rewrites: two isomorphisms with a common source `Spec (RatFunc K)` and a common triangle over
`Spec K` compose to an isomorphism of the two targets over `Spec K`.

The proof is `exists_hom_functionField_ratFunc_of_isDominant` (the scheme-theoretic half:
the stalk-map embedding `K(P) ↪ K(t)`, proven, and needing no `hcurve`) followed by
`exists_iso_specRatFunc_specFunctionField_of_hom` (the field-theoretic half: `hcurve`-driven
non-degeneracy plus Lüroth, still open).  The split is where `hcurve` enters, which is also
where the statement stops being true without it. -/
theorem exists_iso_specRatFunc_specFunctionField_of_isDominant {K : Type u} [Field K]
    {n : Type u} [Unique n] {P : Scheme.{u}} {strP : P ⟶ Spec (CommRingCat.of K)}
    [IsIntegral P] (hcurve : SmoothOfRelativeDimension 1 strP)
    (u : 𝔸(n; Spec (CommRingCat.of K)) ⟶ P)
    (hu : u ≫ strP = 𝔸(n; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K))
    (hdom : IsDominant u) :
    ∃ e : Spec (CommRingCat.of (RatFunc K)) ≅ Spec P.functionField,
      e.hom ≫ P.fromSpecStalk (genericPoint P) ≫ strP
        = Spec.map (CommRingCat.ofHom (algebraMap K (RatFunc K))) := by
  obtain ⟨φ, hφ⟩ := exists_hom_functionField_ratFunc_of_isDominant u hu hdom
  exact exists_iso_specRatFunc_specFunctionField_of_hom hcurve φ hφ

/-- **LÜROTH, in scheme language: the function field of a curve over `K` dominated by the
affine line is `K`-isomorphic to the function field of the affine line** (**PROVEN 2026-07-28**
over the two leaves immediately above, which between them carry all of its residue).

TRUE and classical, and **Lüroth's theorem itself is already in `Mathlib`, proven** —
`Mathlib/FieldTheory/RatFunc/Luroth.lean`, `RatFunc.Luroth.algEquiv`: for every intermediate
field `E` of `K⟮X⟯/K` with `E ≠ ⊥` there is a `K`-algebra equivalence `K⟮X⟯ ≃ₐ[K] E`.  **Do
not reprove it.**  What is left is the translation into schemes, and it is now cut into the
two leaves above, along the line "does this step mention `P` at all?":

* `exists_iso_specRatFunc_specFunctionField_affineSpace` — the affine-space half:
  `K(𝔸(n; Spec K)) ≃ K(t)` over `K`.  No `P`, no `u`, no smoothness, no Lüroth.
* `exists_iso_specRatFunc_specFunctionField_of_isDominant` — the curve half: the stalk-map
  embedding `K(P) ↪ K(t)`, the `hcurve`-driven proof that its image is not `⊥`, and Lüroth.

**Why that cut makes the assembly trivial.**  Both leaves produce an isomorphism *out of the
same object* `Spec (RatFunc K)` and *over the same base* `Spec K`.  Two such isomorphisms
compose to an isomorphism of their targets over `Spec K` by one `Iso.trans` and one
`Iso.inv_hom_id_assoc` — no ring theory, no stalks, and in particular no third statement of
the `K`-algebra compatibility, which is the part that is expensive to say and easy to get
subtly wrong.  Fixing `Spec (RatFunc K)` as the common source is what buys that; a cut into
"`K(𝔸) ≃ K(t)`" and "`K(P) ≃ K(𝔸)`" would have left the composite's base compatibility to be
re-derived here.

**The conclusion does NOT say the isomorphism is the one induced by `u`** — and it is not, in
general: `u` may have degree `> 1`, and Lüroth produces a *different* generator.  That is the
whole point of the theorem, and it is why the conclusion is an existential.  Note also that
`hcurve` is consumed entirely inside the second leaf; this assembly does not look at it.

**`IsIntegral P` is an instance hypothesis rather than derived** so that this statement stands
on its own; at the call site it comes from
`isIntegral_of_smoothOfRelativeDimension_of_geometricallyConnected`, i.e. from smoothness and
geometric connectedness jointly. -/
theorem exists_iso_specFunctionField_affineSpace_of_isDominant {K : Type u} [Field K]
    {n : Type u} [Unique n] {P : Scheme.{u}} {strP : P ⟶ Spec (CommRingCat.of K)}
    [IsIntegral P] (hcurve : SmoothOfRelativeDimension 1 strP)
    (u : 𝔸(n; Spec (CommRingCat.of K)) ⟶ P)
    (hu : u ≫ strP = 𝔸(n; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K))
    (hdom : IsDominant u) :
    ∃ e : Spec P.functionField ≅ Spec (𝔸(n; Spec (CommRingCat.of K))).functionField,
      e.hom ≫ (𝔸(n; Spec (CommRingCat.of K))).fromSpecStalk
            (genericPoint (𝔸(n; Spec (CommRingCat.of K)))) ≫
          (𝔸(n; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K))
        = P.fromSpecStalk (genericPoint P) ≫ strP := by
  obtain ⟨eA, hA⟩ := exists_iso_specRatFunc_specFunctionField_affineSpace (K := K) (n := n)
  obtain ⟨eP, hP⟩ := exists_iso_specRatFunc_specFunctionField_of_isDominant hcurve u hu hdom
  refine ⟨eP.symm ≪≫ eA, ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, hA, ← hP, Iso.inv_hom_id_assoc]

end AlgebraicGeometry
