/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Cover.Directed
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Ideal.Pointwise

/-!
# `Spec` of a ring of invariants is a categorical quotient

Let a finite group `G` act by ring automorphisms on a commutative ring `A`, let `B ⊆ A` be the
invariant subring (`Algebra.IsInvariant B A G` together with injectivity of `algebraMap B A`).
Then `π = Spec (B → A) : Spec A ⟶ Spec B` is a **categorical quotient in the category of all
schemes**: every `G`-invariant morphism `φ : Spec A ⟶ Y` to an arbitrary scheme `Y` factors
uniquely through `π`.

This is Mumford, *Geometric Invariant Theory*, Ch. 0 §2 (Amplification 1.3), and Katz–Mazur
Chapter 7 (*Quotients by finite groups*).  Mathlib has the ring-theoretic half
(`Algebra.IsInvariant`, `Algebra.IsInvariant.isIntegral`,
`Algebra.IsInvariant.exists_smul_of_under_eq`) but not the scheme-level statement.

## The route

* `specTarget_universal_of_ringHom` — the case `Y = Spec R`.  Pure algebra: `Spec` is fully
  faithful, so `φ = Spec.map f`; invariance of `φ` is invariance of `f` by `Spec.map_injective`;
  the values of `f` are therefore fixed, hence come from `B`, and injectivity of `ι` makes the
  lift a ring homomorphism and makes it unique.
* `affineTarget_universal_of_ringHom` — `Y` affine, by transport along `Y.isoSpec`.
* `universal_of_range_subset_isAffineOpen` — the image of `φ` lies inside one affine open `V`
  of `Y`.  Existence is the affine case applied to `V`; uniqueness needs `π` surjective, which
  forces any rival factorisation to land in `V` as well.
* The general case: cover `Spec B` by the basic opens `D b` that are *good*, meaning
  `φ (π⁻¹ (D b))` lies in a single affine open of `Y`.  Since `π` is integral (hence closed) and
  surjective and its fibres are the `G`-orbits, every point of `Spec B` lies in a good basic
  open, and goodness is inherited by smaller basic opens — so the good basic opens are a
  **basis**, and the cover they define is locally directed
  (`Cover.LocallyDirected.ofIsBasisOpensRange`).  Gluing along a locally directed cover only
  needs compatibility with the transition maps, which is the uniqueness half of the local
  statement.

The local statement is applied at the **localised** triples `(B_b, A_{ι b}, G)`, which is why
everything above is stated for an arbitrary ring map `ι : B →+* A` with an arbitrary family of
ring endomorphisms `act : Γ → (A →+* A)` rather than as hypotheses on one fixed triple.  The
one genuinely new piece of algebra is that **invariants localise**:
`exists_awayMap_eq_of_fixed` says a fixed element of `A_{ι b}` comes from `B_b`.
-/

@[expose] public section

universe u

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace Fermat.InvariantQuotient

/-! ### The affine case, for an arbitrary family of ring endomorphisms -/

/-- **GIT for the target `Spec R`.**  A morphism `Spec A ⟶ Spec R` invariant under a family
`act` of ring endomorphisms of `A` factors uniquely through `Spec ι` for any injective
`ι : B →+* A` whose image contains every `act`-fixed element.

Stated with a bare family of ring homomorphisms rather than a group action because it is
consumed at localisations, where producing a `MulSemiringAction` instance would be pure
overhead. -/
theorem specTarget_universal_of_ringHom {B A : Type u} [CommRing B] [CommRing A]
    (ι : B →+* A) (hinj : Function.Injective ι)
    {Γ : Type*} (act : Γ → (A →+* A))
    (hfix : ∀ a : A, (∀ σ : Γ, act σ a = a) → ∃ b : B, ι b = a)
    {R : CommRingCat.{u}} (φ : Spec (CommRingCat.of A) ⟶ Spec R)
    (hinv : ∀ σ : Γ, Spec.map (CommRingCat.ofHom (act σ)) ≫ φ = φ) :
    ∃! ψ : Spec (CommRingCat.of B) ⟶ Spec R,
      Spec.map (CommRingCat.ofHom ι) ≫ ψ = φ := by
  classical
  set f : R ⟶ CommRingCat.of A := Spec.preimage φ with hfdef
  have hφ : Spec.map f = φ := Spec.map_preimage φ
  have hfinv : ∀ (σ : Γ) (r : R), act σ (f.hom r) = f.hom r := by
    intro σ r
    have h := hinv σ
    rw [← hφ, ← Spec.map_comp] at h
    exact congrArg (fun u : R ⟶ CommRingCat.of A => u.hom r) (Spec.map_injective h)
  choose g hg using fun r : R => hfix (f.hom r) (fun σ => hfinv σ r)
  have hg1 : g 1 = 1 := hinj (by rw [hg, map_one, map_one])
  have hg0 : g 0 = 0 := hinj (by rw [hg, map_zero, map_zero])
  have hgm : ∀ x y, g (x * y) = g x * g y := by
    intro x y; exact hinj (by rw [hg, map_mul, map_mul, hg, hg])
  have hga : ∀ x y, g (x + y) = g x + g y := by
    intro x y; exact hinj (by rw [hg, map_add, map_add, hg, hg])
  let f' : R →+* B :=
    { toFun := g, map_one' := hg1, map_zero' := hg0, map_mul' := hgm, map_add' := hga }
  have hfactor : CommRingCat.ofHom f' ≫ CommRingCat.ofHom ι = f :=
    CommRingCat.hom_ext (RingHom.ext hg)
  refine ⟨Spec.map (CommRingCat.ofHom f'), ?_, ?_⟩
  · show Spec.map (CommRingCat.ofHom ι) ≫ Spec.map (CommRingCat.ofHom f') = φ
    rw [← Spec.map_comp, hfactor, hφ]
  · intro ψ' hψ'
    have hu : Spec.preimage ψ' ≫ CommRingCat.ofHom ι = f := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, hψ', hφ]
    have hpre : Spec.preimage ψ' = CommRingCat.ofHom f' := by
      refine CommRingCat.hom_ext (RingHom.ext fun r => hinj ?_)
      have h1 := congrArg (fun u : R ⟶ CommRingCat.of A => u.hom r) hu
      have h2 : ι (f' r) = (CommRingCat.Hom.hom f) r := hg r
      simp only [CommRingCat.hom_ofHom, h2]
      simpa using h1
    rw [← Spec.map_preimage ψ', hpre]

/-- **GIT for an affine target**, obtained from `specTarget_universal_of_ringHom` by transport
along `Y.isoSpec`. -/
theorem affineTarget_universal_of_ringHom {B A : Type u} [CommRing B] [CommRing A]
    (ι : B →+* A) (hinj : Function.Injective ι)
    {Γ : Type*} (act : Γ → (A →+* A))
    (hfix : ∀ a : A, (∀ σ : Γ, act σ a = a) → ∃ b : B, ι b = a)
    {Y : Scheme.{u}} [IsAffine Y] (φ : Spec (CommRingCat.of A) ⟶ Y)
    (hinv : ∀ σ : Γ, Spec.map (CommRingCat.ofHom (act σ)) ≫ φ = φ) :
    ∃! ψ : Spec (CommRingCat.of B) ⟶ Y, Spec.map (CommRingCat.ofHom ι) ≫ ψ = φ := by
  obtain ⟨ψ₀, hψ₀, huniq⟩ :=
    specTarget_universal_of_ringHom ι hinj act hfix (φ ≫ Y.isoSpec.hom)
      (by intro σ; rw [← Category.assoc, hinv σ])
  refine ⟨ψ₀ ≫ Y.isoSpec.inv, ?_, ?_⟩
  · show Spec.map (CommRingCat.ofHom ι) ≫ ψ₀ ≫ Y.isoSpec.inv = φ
    rw [← Category.assoc, hψ₀, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · intro ψ' hψ'
    have hψ'2 : Spec.map (CommRingCat.ofHom ι) ≫ ψ' = φ := hψ'
    have hE : ψ' ≫ Y.isoSpec.hom = ψ₀ := huniq _ (by
      show Spec.map (CommRingCat.ofHom ι) ≫ ψ' ≫ Y.isoSpec.hom = φ ≫ Y.isoSpec.hom
      rw [← Category.assoc, hψ'2])
    rw [← hE, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **GIT when the image of `φ` lies inside a single affine open `V` of `Y`.**

Existence is the affine case applied to `V`.  Uniqueness is the point of the surjectivity
hypothesis: it forces any rival factorisation to have image inside `V` too, so that it can be
compared with the affine one. -/
theorem universal_of_range_subset_isAffineOpen {B A : Type u} [CommRing B] [CommRing A]
    (ι : B →+* A) (hinj : Function.Injective ι)
    {Γ : Type*} (act : Γ → (A →+* A))
    (hfix : ∀ a : A, (∀ σ : Γ, act σ a = a) → ∃ b : B, ι b = a)
    (hsurj : Function.Surjective (Spec.map (CommRingCat.ofHom ι)).base)
    {Y : Scheme.{u}} (φ : Spec (CommRingCat.of A) ⟶ Y)
    (hinv : ∀ σ : Γ, Spec.map (CommRingCat.ofHom (act σ)) ≫ φ = φ)
    (V : Y.Opens) (hV : IsAffineOpen V)
    (hrange : ∀ x, φ.base x ∈ V) :
    ∃! ψ : Spec (CommRingCat.of B) ⟶ Y, Spec.map (CommRingCat.ofHom ι) ≫ ψ = φ := by
  haveI : IsAffine V.toScheme := hV
  have hVr : Set.range (V.ι).base = (V : Set Y) := V.range_ι
  have hsub : Set.range φ.base ⊆ Set.range (V.ι).base := by
    rw [hVr]; rintro _ ⟨x, rfl⟩; exact hrange x
  set φ' : Spec (CommRingCat.of A) ⟶ V.toScheme := IsOpenImmersion.lift V.ι φ hsub with hφ'def
  have hφ' : φ' ≫ V.ι = φ := IsOpenImmersion.lift_fac _ _ _
  have hinv' : ∀ σ : Γ, Spec.map (CommRingCat.ofHom (act σ)) ≫ φ' = φ' := by
    intro σ
    rw [← cancel_mono V.ι, Category.assoc, hφ', hinv]
  obtain ⟨ψ₀, hψ₀, huniq⟩ := affineTarget_universal_of_ringHom ι hinj act hfix φ' hinv'
  refine ⟨ψ₀ ≫ V.ι, ?_, ?_⟩
  · show Spec.map (CommRingCat.ofHom ι) ≫ ψ₀ ≫ V.ι = φ
    rw [← Category.assoc, hψ₀, hφ']
  · intro ψ' hψ'
    have hr : Set.range ψ'.base ⊆ Set.range (V.ι).base := by
      rw [hVr]
      rintro _ ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := hsurj y
      have hx : ψ'.base ((Spec.map (CommRingCat.ofHom ι)).base x) = φ.base x := by
        rw [← Scheme.Hom.comp_apply, hψ']
      rw [hx]; exact hrange x
    set ψ'' : Spec (CommRingCat.of B) ⟶ V.toScheme := IsOpenImmersion.lift V.ι ψ' hr with hψ''def
    have hψ'' : ψ'' ≫ V.ι = ψ' := IsOpenImmersion.lift_fac _ _ _
    have hkey : Spec.map (CommRingCat.ofHom ι) ≫ ψ'' = φ' := by
      rw [← cancel_mono V.ι, Category.assoc, hψ'', hψ', hφ']
    rw [← hψ'', huniq _ hkey]

/-! ### Invariants localise -/

section Away

variable {B A : Type u} [CommRing B] [CommRing A] (ι : B →+* A)

theorem powers_le_comap_powers (b : B) :
    Submonoid.powers b ≤ (Submonoid.powers (ι b)).comap ι := by
  rintro x ⟨n, rfl⟩
  exact ⟨n, by simp⟩

theorem powers_le_comap_powers_self (b : B) (s : A →+* A) (hs : s (ι b) = ι b) :
    Submonoid.powers (ι b) ≤ (Submonoid.powers (ι b)).comap s := by
  rintro x ⟨n, rfl⟩
  exact ⟨n, by simp [map_pow, hs]⟩

/-- The map `B_b → A_{ι b}` induced by `ι : B →+* A`. -/
noncomputable def awayMap (b : B) :
    Localization.Away b →+* Localization.Away (ι b) :=
  IsLocalization.map _ ι (powers_le_comap_powers ι b)

/-- A ring endomorphism `s` of `A` fixing `ι b` induces one of `A_{ι b}`. -/
noncomputable def awayAct (b : B) (s : A →+* A) (hs : s (ι b) = ι b) :
    Localization.Away (ι b) →+* Localization.Away (ι b) :=
  IsLocalization.map _ s (powers_le_comap_powers_self ι b s hs)

theorem awayMap_comp (b : B) :
    (awayMap ι b).comp (algebraMap B (Localization.Away b)) =
      (algebraMap A (Localization.Away (ι b))).comp ι :=
  IsLocalization.map_comp _

theorem awayAct_comp (b : B) (s : A →+* A) (hs : s (ι b) = ι b) :
    (awayAct ι b s hs).comp (algebraMap A (Localization.Away (ι b))) =
      (algebraMap A (Localization.Away (ι b))).comp s := by
  delta awayAct
  exact IsLocalization.map_comp _

theorem awayMap_injective (b : B) (hinj : Function.Injective ι) :
    Function.Injective (awayMap ι b) := by
  haveI : IsLocalization ((Submonoid.powers b).map ι) (Localization.Away (ι b)) := by
    rw [Submonoid.map_powers]
    infer_instance
  exact IsLocalization.map_injective_of_injective _ _ _ hinj

/-- **Invariants localise.**  If `x : A_{ι b}` is fixed by every `awayAct` of a finite family
`act` of ring endomorphisms fixing `ι b`, and every `act`-fixed element of `A` comes from `B`,
then `x` comes from `B_b`.

The proof clears denominators uniformly: finiteness of `Γ` lets one power `(ι b) ^ N` witness
all the equalities `act σ (a) = a` at once, and `(ι b) ^ N * a` is then genuinely fixed. -/
theorem exists_awayMap_eq_of_fixed {Γ : Type*} [Finite Γ] (act : Γ → (A →+* A))
    (b : B) (hact : ∀ σ : Γ, act σ (ι b) = ι b)
    (hfix : ∀ a : A, (∀ σ : Γ, act σ a = a) → ∃ c : B, ι c = a)
    (x : Localization.Away (ι b))
    (hx : ∀ σ : Γ, awayAct ι b (act σ) (hact σ) x = x) :
    ∃ y : Localization.Away b, awayMap ι b y = x := by
  classical
  cases nonempty_fintype Γ
  obtain ⟨a, y, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers (ι b)) x
  obtain ⟨n, hn⟩ := y.2
  have hn' : (ι b) ^ n = (y : A) := hn
  have hys : ∀ σ : Γ, act σ (y : A) = (y : A) := by
    intro σ; rw [← hn', map_pow, hact]
  -- for each `σ`, some power of `ι b` equalises `act σ a` and `a`
  have key : ∀ σ : Γ, ∃ m : ℕ, (ι b) ^ m * act σ a = (ι b) ^ m * a := by
    intro σ
    have h := hx σ
    rw [awayAct, IsLocalization.map_mk'] at h
    have h2 : IsLocalization.mk' (Localization.Away (ι b)) (act σ a) y
        = IsLocalization.mk' (Localization.Away (ι b)) a y := by
      rw [← h]; congr 1; exact Subtype.ext (hys σ).symm
    rw [IsLocalization.mk'_eq_iff_eq,
      IsLocalization.eq_iff_exists (Submonoid.powers (ι b))] at h2
    obtain ⟨c, hc⟩ := h2
    obtain ⟨k, hk⟩ := c.2
    have hk' : (ι b) ^ k = (c : A) := hk
    refine ⟨k + n, ?_⟩
    have hcc := hc
    rw [← hk', ← hn'] at hcc
    calc (ι b) ^ (k + n) * act σ a = (ι b) ^ k * ((ι b) ^ n * act σ a) := by ring
      _ = (ι b) ^ k * ((ι b) ^ n * a) := hcc
      _ = (ι b) ^ (k + n) * a := by ring
  choose m hm using key
  set N : ℕ := ∑ σ : Γ, m σ with hN
  have hmN : ∀ σ : Γ, m σ ≤ N := fun σ =>
    Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ σ)
  have hfixN : ∀ σ : Γ, act σ ((ι b) ^ N * a) = (ι b) ^ N * a := by
    intro σ
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (hmN σ)
    rw [map_mul, map_pow, hact, hd, pow_add]
    calc (ι b) ^ m σ * (ι b) ^ d * act σ a
        = (ι b) ^ d * ((ι b) ^ m σ * act σ a) := by ring
      _ = (ι b) ^ d * ((ι b) ^ m σ * a) := by rw [hm σ]
      _ = (ι b) ^ m σ * (ι b) ^ d * a := by ring
  obtain ⟨c, hc⟩ := hfix _ hfixN
  refine ⟨IsLocalization.mk' (Localization.Away b) c
    (⟨b ^ (N + n), N + n, rfl⟩ : ↥(Submonoid.powers b)), ?_⟩
  rw [awayMap, IsLocalization.map_mk', IsLocalization.mk'_eq_iff_eq]
  congr 1
  show (y : A) * ι c = ι (b ^ (N + n)) * a
  rw [hc, ← hn', map_pow]
  ring

end Away

/-! ### The general target -/

/-- Mathlib's `Scheme.Hom.opensRange_localizationAway` is stated for `R : CommRingCat`; this is
the same statement for a bare `CommRing`, where the `Algebra` instance path is the one that
elaboration actually produces. -/
theorem range_specMap_localizationAway {R : Type u} [CommRing R] (r : R) :
    Set.range (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))).base
      = (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) :=
  PrimeSpectrum.localization_away_comap_range _ r

theorem opensRange_specMap_localizationAway {R : Type u} [CommRing R] (r : R) :
    (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))).opensRange
      = PrimeSpectrum.basicOpen r :=
  TopologicalSpace.Opens.ext (range_specMap_localizationAway r)

section General

variable {B A : Type u} [CommRing B] [CommRing A] (ι : B →+* A)

theorem specMap_awayMap_comm (b : B) :
    Spec.map (CommRingCat.ofHom (awayMap ι b)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away b))) =
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (ι b)))) ≫
        Spec.map (CommRingCat.ofHom ι) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    awayMap_comp]

theorem specMap_awayAct_comm (b : B) (s : A →+* A) (hs : s (ι b) = ι b) :
    Spec.map (CommRingCat.ofHom (awayAct ι b s hs)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (ι b)))) =
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (ι b)))) ≫
        Spec.map (CommRingCat.ofHom s) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    awayAct_comp]

/-- Surjectivity of `Spec A_{ι b} ⟶ Spec B_b` follows from surjectivity of `Spec A ⟶ Spec B`,
because both are the restrictions of that map to a basic open and its preimage. -/
theorem comap_awayMap_surjective (b : B) (hsurj : Function.Surjective (PrimeSpectrum.comap ι)) :
    Function.Surjective (PrimeSpectrum.comap (awayMap ι b)) := by
  intro q
  have hxb : b ∉ (PrimeSpectrum.comap (algebraMap B (Localization.Away b)) q).asIdeal := by
    have hmem : PrimeSpectrum.comap (algebraMap B (Localization.Away b)) q ∈
        (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away b) b]
      exact ⟨q, rfl⟩
    exact hmem
  obtain ⟨P, hP⟩ := hsurj (PrimeSpectrum.comap (algebraMap B (Localization.Away b)) q)
  have hPb : ι b ∉ P.asIdeal := fun hmem => hxb (by rw [← hP]; exact hmem)
  have hPr : P ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away (ι b)))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away (ι b)) (ι b)]
    exact hPb
  obtain ⟨P', hP'⟩ := hPr
  refine ⟨P', ?_⟩
  apply PrimeSpectrum.localization_comap_injective (Localization.Away b) (Submonoid.powers b)
  rw [← PrimeSpectrum.comap_comp_apply, awayMap_comp, PrimeSpectrum.comap_comp_apply, hP', hP]

end General

/-! ### The theorem -/

/-- **`Spec` of a ring of invariants is a categorical quotient in the category of ALL schemes.**

Let a finite group `G` act by ring automorphisms on `A`, let `B` be the invariant subring
(`Algebra.IsInvariant B A G` plus injectivity of `algebraMap B A`, with `SMulCommClass G B A`
saying that everything from `B` is `G`-fixed).  Then every `G`-invariant morphism
`φ : Spec A ⟶ Y` to an ARBITRARY scheme `Y` factors uniquely through `Spec (B → A)`. -/
theorem exists_unique_of_isInvariant {B A : Type u} [CommRing B] [CommRing A] [Algebra B A]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G B A]
    [Algebra.IsInvariant B A G]
    (hinj : Function.Injective (algebraMap B A))
    {Y : Scheme.{u}} (φ : Spec (CommRingCat.of A) ⟶ Y)
    (hinv : ∀ σ : G,
      Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G A σ)) ≫ φ = φ) :
    ∃! ψ : Spec (CommRingCat.of B) ⟶ Y,
      Spec.map (CommRingCat.ofHom (algebraMap B A)) ≫ ψ = φ := by
  classical
  set ι : B →+* A := algebraMap B A with hιdef
  set act : G → (A →+* A) := fun σ => MulSemiringAction.toRingHom G A σ with hactdef
  have hfix : ∀ a : A, (∀ σ : G, act σ a = a) → ∃ c : B, ι c = a := fun a ha =>
    Algebra.IsInvariant.isInvariant (A := B) (B := A) (G := G) a ha
  have hactfix : ∀ (σ : G) (b : B), act σ (ι b) = ι b := fun σ b => smul_algebraMap σ b
  -- `π` is integral, hence closed, and surjective
  haveI : Algebra.IsIntegral B A := Algebra.IsInvariant.isIntegral B A G
  haveI : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).mpr hinj
  have hsurjP : Function.Surjective (PrimeSpectrum.comap ι) :=
    Algebra.IsIntegral.comap_surjective B A
  have hintegral : (ι : B →+* A).IsIntegral := fun x => Algebra.IsIntegral.isIntegral x
  have hclosed : IsClosedMap (PrimeSpectrum.comap ι) :=
    PrimeSpectrum.isClosedMap_comap_of_isIntegral ι hintegral
  -- the fibres of `π` are `G`-orbits, so `φ` is constant on them
  have hfibre : ∀ P Q : PrimeSpectrum A,
      PrimeSpectrum.comap ι P = PrimeSpectrum.comap ι Q → φ.base Q = φ.base P := by
    intro P Q hPQ
    obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq B A G P.asIdeal Q.asIdeal
      (congrArg PrimeSpectrum.asIdeal hPQ)
    have hQ : Q = PrimeSpectrum.comap (act g⁻¹) P := by
      apply PrimeSpectrum.ext
      rw [hg]
      ext a
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
      rfl
    rw [hQ]
    exact congrFun (congrArg (fun m : Spec (CommRingCat.of A) ⟶ Y => (m.base : _ → _))
      (hinv g⁻¹)) P
  -- the local pieces
  let jA : ∀ b : B, Spec (CommRingCat.of (Localization.Away (ι b))) ⟶ Spec (CommRingCat.of A) :=
    fun b => Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (ι b))))
  let jB : ∀ b : B, Spec (CommRingCat.of (Localization.Away b)) ⟶ Spec (CommRingCat.of B) :=
    fun b => Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away b)))
  let πb : ∀ b : B, Spec (CommRingCat.of (Localization.Away (ι b))) ⟶
      Spec (CommRingCat.of (Localization.Away b)) :=
    fun b => Spec.map (CommRingCat.ofHom (awayMap ι b))
  -- a basic open `D b` is GOOD when `φ (π⁻¹ (D b))` lies inside one affine open of `Y`
  let Good : B → Prop := fun b => ∃ V : Y.Opens, IsAffineOpen V ∧
    ∀ P : PrimeSpectrum A, P ∈ (PrimeSpectrum.basicOpen (ι b) : Set (PrimeSpectrum A)) →
      φ.base P ∈ V
  have hGood_iff : ∀ b : B, Good b ↔ ∃ V : Y.Opens, IsAffineOpen V ∧
      ∀ P : PrimeSpectrum A, P ∈ (PrimeSpectrum.basicOpen (ι b) : Set (PrimeSpectrum A)) →
        φ.base P ∈ V := fun _ => Iff.rfl
  have hGoodMul : ∀ b c : B, Good b → Good (b * c) := by
    rintro b c ⟨V, hV, hVm⟩
    refine (hGood_iff _).mpr ⟨V, hV, fun P hP => hVm P ?_⟩
    intro hmem
    exact hP (by rw [map_mul]; exact Ideal.mul_mem_right _ _ hmem)
  -- every point of `Spec B` lies in a good basic open
  have hcover : ∀ x : PrimeSpectrum B, ∃ b : B, Good b ∧
      x ∈ (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B)) := by
    intro x
    obtain ⟨P, hP⟩ := hsurjP x
    obtain ⟨V, hVmem, hVy, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
      (show φ.base P ∈ (⊤ : Y.Opens) from trivial)
    have hV : IsAffineOpen V := hVmem
    have hUcClosed : IsClosed {Q : PrimeSpectrum A | φ.base Q ∉ V} := by
      have he : {Q : PrimeSpectrum A | φ.base Q ∉ V} = (φ.base ⁻¹' (V : Set Y))ᶜ := rfl
      rw [he]
      exact (V.2.preimage φ.base.hom.continuous).isClosed_compl
    have him : IsClosed (PrimeSpectrum.comap ι '' {Q : PrimeSpectrum A | φ.base Q ∉ V}) :=
      hclosed _ hUcClosed
    have hxnot : x ∉ PrimeSpectrum.comap ι '' {Q : PrimeSpectrum A | φ.base Q ∉ V} := by
      rintro ⟨Q, hQ, hQx⟩
      exact hQ (by rw [hfibre P Q (by rw [hP, hQx])]; exact hVy)
    obtain ⟨W, ⟨b, hb⟩, hxW, hWle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      PrimeSpectrum.isBasis_basic_opens
      (show x ∈ (⟨(PrimeSpectrum.comap ι '' {Q : PrimeSpectrum A | φ.base Q ∉ V})ᶜ,
        him.isOpen_compl⟩ : Opens (PrimeSpectrum B)) from hxnot)
    refine ⟨b, (hGood_iff _).mpr ⟨V, hV, ?_⟩, ?_⟩
    · intro P' hP'
      by_contra hcon
      have h2 : PrimeSpectrum.comap ι P' ∈ W := by rw [← hb]; exact hP'
      exact hWle h2 ⟨P', hcon, rfl⟩
    · rw [← hb] at hxW; exact hxW
  -- the good basic opens form a basis
  have hbasisGood : ∀ (U : Opens (PrimeSpectrum B)) (x : PrimeSpectrum B), x ∈ U →
      ∃ b : B, Good b ∧ x ∈ PrimeSpectrum.basicOpen b ∧ PrimeSpectrum.basicOpen b ≤ U := by
    intro U x hx
    obtain ⟨b₀, hb₀, hxb₀⟩ := hcover x
    obtain ⟨W, ⟨b₁, hb₁⟩, hxW, hWU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      PrimeSpectrum.isBasis_basic_opens hx
    rw [← hb₁] at hxW hWU
    refine ⟨b₀ * b₁, hGoodMul _ _ hb₀, ?_, ?_⟩
    · rw [PrimeSpectrum.basicOpen_mul]; exact ⟨hxb₀, hxW⟩
    · rw [PrimeSpectrum.basicOpen_mul]; exact le_trans inf_le_right hWU
  -- the cover of `Spec B` by the good basic opens
  let 𝒰 : (Spec (CommRingCat.of B)).OpenCover :=
    { I₀ := {b : B // Good b}
      X := fun i => Spec (CommRingCat.of (Localization.Away i.1))
      f := fun i => jB i.1
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun x => ?_, inferInstance⟩
        obtain ⟨b, hb, hxb⟩ := hcover x
        refine ⟨⟨b, hb⟩, ?_⟩
        have hmem : x ∈ Set.range (Spec.map
            (CommRingCat.ofHom (algebraMap B (Localization.Away b)))).base := by
          rw [range_specMap_localizationAway]; exact hxb
        exact hmem }
  -- the matching cover of `Spec A`
  let 𝒱 : (Spec (CommRingCat.of A)).OpenCover :=
    { I₀ := {b : B // Good b}
      X := fun i => Spec (CommRingCat.of (Localization.Away (ι i.1)))
      f := fun i => jA i.1
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun P => ?_, inferInstance⟩
        obtain ⟨b, hb, hxb⟩ := hcover (PrimeSpectrum.comap ι P)
        refine ⟨⟨b, hb⟩, ?_⟩
        have hmem : P ∈ Set.range (Spec.map
            (CommRingCat.ofHom (algebraMap A (Localization.Away (ι b))))).base := by
          rw [range_specMap_localizationAway]; exact hxb
        exact hmem }
  -- the cover of `Spec B` is locally directed, being a basis
  letI : Preorder {b : B // Good b} :=
    Preorder.lift (fun i : {b : B // Good b} => PrimeSpectrum.basicOpen i.1)
  have hle : ∀ {i j : 𝒰.I₀}, i ≤ j ↔ (𝒰.f i).opensRange ≤ (𝒰.f j).opensRange := by
    intro i j
    show PrimeSpectrum.basicOpen i.1 ≤ PrimeSpectrum.basicOpen j.1 ↔
      (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away i.1)))).opensRange ≤
        (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away j.1)))).opensRange
    rw [opensRange_specMap_localizationAway, opensRange_specMap_localizationAway]
    exact Iff.rfl
  have hbasis : Opens.IsBasis (Set.range fun i : 𝒰.I₀ => (𝒰.f i).opensRange) := by
    rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
    intro U x hx
    obtain ⟨b, hb, hxb, hbU⟩ := hbasisGood U x hx
    refine ⟨(𝒰.f ⟨b, hb⟩).opensRange, ⟨⟨b, hb⟩, rfl⟩, ?_, ?_⟩
    · show x ∈ (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away b)))).opensRange
      rw [opensRange_specMap_localizationAway]; exact hxb
    · show (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away b)))).opensRange ≤ U
      rw [opensRange_specMap_localizationAway]; exact hbU
  letI : 𝒰.LocallyDirected := Scheme.Cover.LocallyDirected.ofIsBasisOpensRange hle hbasis
  -- the local factorisations
  have hLOC : ∀ i : {b : B // Good b},
      ∃! ψ : Spec (CommRingCat.of (Localization.Away i.1)) ⟶ Y, πb i.1 ≫ ψ = jA i.1 ≫ φ := by
    intro i
    obtain ⟨V, hV, hVm⟩ := (hGood_iff i.1).mp i.2
    refine universal_of_range_subset_isAffineOpen (awayMap ι i.1) (awayMap_injective ι i.1 hinj)
      (fun σ : G => awayAct ι i.1 (act σ) (hactfix σ i.1)) ?_ ?_ (jA i.1 ≫ φ) ?_ V hV ?_
    · intro x hxfix
      exact exists_awayMap_eq_of_fixed ι act i.1 (fun σ => hactfix σ i.1) hfix x hxfix
    · exact comap_awayMap_surjective ι i.1 hsurjP
    · intro σ
      show Spec.map (CommRingCat.ofHom (awayAct ι i.1 (act σ) (hactfix σ i.1))) ≫ jA i.1 ≫ φ
        = jA i.1 ≫ φ
      rw [← Category.assoc, specMap_awayAct_comm, Category.assoc, hinv σ]
    · intro z
      rw [Scheme.Hom.comp_apply]
      refine hVm _ ?_
      have hz : (jA i.1).base z ∈ Set.range (Spec.map
          (CommRingCat.ofHom (algebraMap A (Localization.Away (ι i.1))))).base := ⟨z, rfl⟩
      rw [range_specMap_localizationAway] at hz
      exact hz
  choose g hg hguniq using hLOC
  -- the transition maps of the cover are compatible with the local factorisations
  have htrans : ∀ {i j : 𝒰.I₀} (hij : i ⟶ j), 𝒰.trans hij ≫ g j = g i := by
    intro i j hij
    refine hguniq i _ ?_
    have hrangeA : Set.range (jA i.1).base ⊆ Set.range (jA j.1).base := by
      show Set.range (Spec.map
          (CommRingCat.ofHom (algebraMap A (Localization.Away (ι i.1))))).base
        ⊆ Set.range (Spec.map
          (CommRingCat.ofHom (algebraMap A (Localization.Away (ι j.1))))).base
      rw [range_specMap_localizationAway, range_specMap_localizationAway]
      intro P hP
      have h3 : PrimeSpectrum.comap ι P ∈ PrimeSpectrum.basicOpen i.1 := hP
      exact (leOfHom hij : PrimeSpectrum.basicOpen i.1 ≤ PrimeSpectrum.basicOpen j.1) h3
    have ht : IsOpenImmersion.lift (jA j.1) (jA i.1) hrangeA ≫ jA j.1 = jA i.1 :=
      IsOpenImmersion.lift_fac _ _ _
    have hcomm : πb i.1 ≫ 𝒰.trans hij
        = IsOpenImmersion.lift (jA j.1) (jA i.1) hrangeA ≫ πb j.1 := by
      rw [← cancel_mono (𝒰.f j), Category.assoc, Category.assoc, 𝒰.trans_map hij]
      show πb i.1 ≫ jB i.1
        = IsOpenImmersion.lift (jA j.1) (jA i.1) hrangeA ≫ πb j.1 ≫ jB j.1
      rw [specMap_awayMap_comm, specMap_awayMap_comm, ← Category.assoc, ht]
    show πb i.1 ≫ (𝒰.trans hij ≫ g j) = jA i.1 ≫ φ
    rw [← Category.assoc, hcomm, Category.assoc, hg j, ← Category.assoc, ht]
  refine ⟨𝒰.glueMorphismsOfLocallyDirected g htrans, ?_, ?_⟩
  · refine 𝒱.hom_ext _ _ (fun i => ?_)
    show jA i.1 ≫ Spec.map (CommRingCat.ofHom ι) ≫ 𝒰.glueMorphismsOfLocallyDirected g htrans
      = jA i.1 ≫ φ
    rw [← Category.assoc, ← specMap_awayMap_comm, Category.assoc]
    show πb i.1 ≫ 𝒰.f i ≫ 𝒰.glueMorphismsOfLocallyDirected g htrans = jA i.1 ≫ φ
    rw [Scheme.OpenCover.map_glueMorphismsOfLocallyDirected, hg i]
  · intro ψ' hψ'
    refine 𝒰.hom_ext _ _ (fun i => ?_)
    rw [Scheme.OpenCover.map_glueMorphismsOfLocallyDirected]
    refine hguniq i _ ?_
    show πb i.1 ≫ 𝒰.f i ≫ ψ' = jA i.1 ≫ φ
    show πb i.1 ≫ jB i.1 ≫ ψ' = jA i.1 ≫ φ
    rw [← Category.assoc, specMap_awayMap_comm, Category.assoc, hψ']

end Fermat.InvariantQuotient
