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
`birationalOver_of_iso_specFunctionField`, **proven here** over two leaves that
between them carry all of its residue:

* `exists_opens_iso_of_partialMap_equiv_id` — the purely geometric half: two
  partial maps whose two round trips are the identity restrict to an
  isomorphism of dense opens.  It mentions no base scheme at all.
* `partialMap_comp_equiv_id_of_fromSpecStalkOfMem` — the purely stalk-level
  half: the round trip of two partial maps whose germs at the generic point are
  mutually inverse *is* the identity.  **This one is now PROVEN** (2026-07-28),
  so `exists_opens_iso_of_partialMap_equiv_id` is the bridge's only open leaf.

Everything else — the spreading out in both directions, the dominance of both
partial maps, the composite germ computation that `Mathlib` lacks, the
`S`-compatibility and the final assembly out of `Opens.birationalOver_of_dense`
and `Hom.birationalOver` — is proven.

The third declaration here, `exists_iso_specFunctionField_affineSpace_of_isDominant`,
is **Lüroth's theorem in scheme language**: a curve over a field dominated by the
affine line has function field `K`-isomorphic to `K(t)`.  Lüroth itself is
already proven in `Mathlib` (`Mathlib/FieldTheory/RatFunc/Luroth.lean`,
`RatFunc.Luroth.algEquiv`), so that leaf is *only* the translation between the
scheme-level `Spec` picture and the intermediate-field picture Lüroth is stated
in; no new mathematics of Lüroth type is left in it.

Together the three give, in three lines, "a curve over a field dominated by `𝔸¹`
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
opens** (sorry leaf, 2026-07-28) — the purely geometric residue of the
`Birational ↔ functionField ≃` bridge.  It mentions no base scheme, no field, no function
field and no ring: it is a statement about partial maps and opens alone.

TRUE and classical; this is the content of Hartshorne I.4.5 / Stacks 0BXA once the
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
`AlgebraicGeometry/RationalMap.lean`, none of which has one. -/
theorem exists_opens_iso_of_partialMap_equiv_id {X Y : Scheme.{u}}
    [IrreducibleSpace X] [IrreducibleSpace Y]
    (F : X.PartialMap Y) (G : Y.PartialMap X) [IsDominant F.hom] [IsDominant G.hom]
    (hFG : (F.comp G).equiv (Scheme.PartialMap.id X))
    (hGF : (G.comp F).equiv (Scheme.PartialMap.id Y)) :
    ∃ (U : X.Opens) (V : Y.Opens) (_ : Dense (U : Set X)) (_ : Dense (V : Set Y))
      (i : U.toScheme ≅ V.toScheme) (hUF : U ≤ F.domain),
      i.hom ≫ V.ι = X.homOfLE hUF ≫ F.hom :=
  sorry

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

/-- **LÜROTH, in scheme language: the function field of a curve over `K` dominated by the
affine line is `K`-isomorphic to the function field of the affine line** (sorry leaf,
2026-07-28).

TRUE and classical, and **Lüroth's theorem itself is already in `Mathlib`, proven** —
`Mathlib/FieldTheory/RatFunc/Luroth.lean`, `RatFunc.Luroth.algEquiv`: for every intermediate
field `E` of `K⟮X⟯/K` with `E ≠ ⊥` there is a `K`-algebra equivalence `K⟮X⟯ ≃ₐ[K] E`.  **Do
not reprove it.**  What is left here is exactly the translation into schemes, in four steps:

1. *The embedding.*  `hdom` gives `u (genericPoint 𝔸) = genericPoint P`
   (`genericPoint_eq_of_isDominant` above), so `u.stalkMap` at the generic point is a ring map
   `K(P) ⟶ K(𝔸)`, injective because `K(P)` is a field.  `hu` makes it a `K`-algebra map.
2. *The target is `K(t)`.*  `𝔸(n; Spec K) ≅ Spec (MvPolynomial n K)` (`AffineSpace.SpecIso`),
   `MvPolynomial n K ≃ₐ[K] K[X]` for `Unique n` (`MvPolynomial.pUnitAlgEquiv` after
   `MvPolynomial.renameEquiv (Equiv.equivPUnit n)`), and the function field of the spectrum of
   a domain is its fraction field (`functionField_isFractionRing_of_affine`), so
   `K(𝔸) ≃ₐ[K] RatFunc K = K⟮X⟯`.
3. *The image is not `⊥`.*  This is the ONLY place `hcurve` is used, and the statement is
   **FALSE without it**: `P = Spec K` is dominated by `𝔸¹_K` (its structure morphism is
   surjective) and its function field is `K`, not `K(t)`.  With `hcurve`, `P` is infinite
   (`infinite_of_smoothOfRelativeDimension_one`, proven in `CurveExtension.lean`), while
   `K(P) = K` would force every affine open `Spec A ⊆ P` to have `K ⊆ A ⊆ Frac A = K`, i.e.
   `A = K`, i.e. `Spec A` a single point — so `P` would be a one-point scheme.
4. *Lüroth and back.*  Apply `RatFunc.Luroth.algEquiv` to `E :=` the image of step 1 to get
   `K⟮X⟯ ≃ₐ[K] E ≃ₐ[K] K(P)`, then turn that `K`-algebra equivalence into the `Spec`-level
   isomorphism and its commuting triangle over `Spec K`.

**The conclusion does NOT say the isomorphism is the one induced by `u`** — and it is not, in
general: `u` may have degree `> 1`, and Lüroth produces a *different* generator.  That is the
whole point of the theorem, and it is why the conclusion is an existential.

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
        = P.fromSpecStalk (genericPoint P) ≫ strP :=
  sorry

end AlgebraicGeometry
