/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.DualNumber
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Data.Rat.Lemmas

/-!
# The formal-immersion principle

**A morphism of schemes over a LOCAL base that is injective on tangent vectors at a
point of the closed fibre is injective on the sections through that point.**

This is the general principle behind Mazur's method (IHÉS 47 (1977), §III.1) and
Kamienny's criterion (Invent. Math. 109 (1992)), with the modular curve, the level,
the Eisenstein ideal and the cusp all removed.  `Fermat/FLT/FreyCurve/MazurTorsion.lean`
consumes it as `eq_of_formalImmersionAt`.

## The proof, and what it does NOT need

The classical account runs through completions: tangent injectivity dualises to
surjectivity of the cotangent map, Nakayama makes `𝒪̂_{A,ā} ↠ 𝒪̂_{X,c̄}`, and two
`ℤ_(q)`-points agreeing on the image of `𝒪̂_{A,ā}` therefore agree.  That route needs
`𝒪_{X,c̄}` NOETHERIAN (hence smoothness or local finite type) and finite-dimensionality
of the cotangent space.

The proof here needs **neither**, and that is why `eq_of_formalImmersionAt`'s `_hsm`
(smoothness of `xstr`) and `_abZ` (the abelian-scheme structure on `astrZ`) are BOTH
unused.  Instead of completing, it runs the `q`-adic induction directly:

* a section `Spec ℤ_(q) ⟶ X` whose closed point lands at `c̄` IS a local homomorphism
  `φ : 𝒪_{X,c̄} → ℤ_(q)` (`AlgebraicGeometry.SpecToEquivOfLocalRing`);
* if `φ ≡ ψ mod qⁿ` (`n ≥ 0`) then `D := (φ − ψ)/qⁿ` is an honest `ψ`-derivation
  `𝒪_{X,c̄} → ℤ_(q)`, because `φa·φb − ψa·ψb = φa(φb − ψb) + (φa − ψa)ψb` and
  `q^{2n} ∣ q^{n+1}` for `n ≥ 1` is not even needed — the identity is EXACT in `ℤ_(q)`;
* `toF ∘ D` is then an `𝔽_q`-valued derivation, i.e. an `𝔽_q[ε]`-point of `X` over
  `ℤ_(q)` lying over `c̄` (`ofDeriv`), and it has the SAME image under `fmor` as the
  zero derivation, because `φ` and `ψ` already agree on the image of `𝒪_{A,ā}`;
* tangent injectivity kills it, so `q ∣ D`, i.e. `φ ≡ ψ mod q^{n+1}`;
* `⋂ₙ qⁿ ℤ_(q) = 0` finishes.

No duality, no Nakayama, no completion, no noetherian hypothesis.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace Fermat.FormalImmersion

/-! ### Dual numbers -/

section Dual

variable {k : Type*} [CommRing k] [IsLocalRing k]

instance : IsLocalRing (DualNumber k) := by
  haveI : Nontrivial (DualNumber k) :=
    ⟨⟨0, 1, fun h => zero_ne_one (congrArg TrivSqZeroExt.fst h)⟩⟩
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self ?_
  intro a
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (TrivSqZeroExt.fst a) with h | h
  · left; rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]; exact h
  · right
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa using h

instance : IsLocalHom (algebraMap k (DualNumber k)) :=
  ⟨fun a h => by
    rw [show algebraMap k (DualNumber k) a = TrivSqZeroExt.inl a from rfl,
      TrivSqZeroExt.isUnit_inl_iff] at h
    exact h⟩

instance : IsLocalHom (TrivSqZeroExt.fstHom k k k : DualNumber k →ₐ[k] k).toRingHom :=
  ⟨fun a h => by rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]; exact h⟩

variable {O : Type*} [CommRing O]

/-- A ring hom `f : O →+* k` together with an `f`-derivation `d` assembles into a
ring hom `O →+* k[ε]`. -/
def ofDeriv (f : O →+* k) (d : O →+ k) (h1 : d 1 = 0)
    (hmul : ∀ a b, d (a * b) = f a * d b + f b * d a) : O →+* DualNumber k where
  toFun a := TrivSqZeroExt.inl (f a) + TrivSqZeroExt.inr (d a)
  map_one' := by refine TrivSqZeroExt.ext ?_ ?_ <;> simp [h1]
  map_mul' a b := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [TrivSqZeroExt.fst_mul]
    · simp [TrivSqZeroExt.snd_mul, hmul a b, smul_eq_mul]
      ring
  map_zero' := by refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_add' a b := by refine TrivSqZeroExt.ext ?_ ?_ <;> simp

omit [IsLocalRing k] in
@[simp] theorem ofDeriv_fst (f : O →+* k) (d : O →+ k) (h1 hmul) (a : O) :
    TrivSqZeroExt.fst (ofDeriv f d h1 hmul a) = f a := by
  simp [ofDeriv]

omit [IsLocalRing k] in
@[simp] theorem ofDeriv_snd (f : O →+* k) (d : O →+ k) (h1 hmul) (a : O) :
    TrivSqZeroExt.snd (ofDeriv f d h1 hmul a) = d a := by
  simp [ofDeriv]

end Dual

/-! ### The `q`-adic induction -/

section Core

variable {q : ℕ} {R : Type*} [CommRing R] [IsDomain R] {k : Type*} [CommRing k]

/-- **The `q`-adic induction at the heart of the formal-immersion principle.** -/
theorem eq_of_deriv_vanishing (toF : R →+* k) (hq : (q : R) ≠ 0)
    (hdvd : ∀ r : R, toF r = 0 → ∃ s, r = (q : R) * s)
    (hsep : ∀ r : R, (∀ n : ℕ, ∃ s, r = (q : R) ^ n * s) → r = 0)
    {O : Type*} [CommRing O] {O' : Type*} [CommRing O']
    (φ ψ : O →+* R) (g : O' →+* O) (β : R →+* O)
    (hres : ∀ a, toF (φ a) = toF (ψ a))
    (himg : ∀ b, φ (g b) = ψ (g b))
    (hβφ : ∀ r, φ (β r) = r) (hβψ : ∀ r, ψ (β r) = r)
    (H : ∀ d : O →+ k, d 1 = 0 →
        (∀ a b, d (a * b) = toF (ψ a) * d b + toF (ψ b) * d a) →
        (∀ b, d (g b) = 0) → (∀ r, d (β r) = 0) → ∀ a, d a = 0) :
    φ = ψ := by
  have key : ∀ n : ℕ, ∀ a : O, ∃ s : R, φ a - ψ a = (q : R) ^ n * s := by
    intro n
    induction n with
    | zero => intro a; exact ⟨φ a - ψ a, by simp⟩
    | succ n ih =>
      choose D hD using ih
      have hqn : ((q : R) ^ n) ≠ 0 := pow_ne_zero _ hq
      have hD0 : D 0 = 0 := by
        have h := hD 0
        simp only [map_zero, sub_zero] at h
        exact (mul_eq_zero.mp h.symm).resolve_left hqn
      have hDadd : ∀ a b, D (a + b) = D a + D b := by
        intro a b
        refine mul_left_cancel₀ hqn ?_
        rw [← hD (a + b), mul_add, ← hD a, ← hD b, map_add, map_add]
        ring
      have hD1 : D 1 = 0 := by
        have h := hD 1
        simp only [map_one, sub_self] at h
        exact (mul_eq_zero.mp h.symm).resolve_left hqn
      have hDmul : ∀ a b, D (a * b) = φ a * D b + ψ b * D a := by
        intro a b
        refine mul_left_cancel₀ hqn ?_
        rw [← hD (a * b), map_mul, map_mul]
        linear_combination φ a * hD b + ψ b * hD a
      have hDg : ∀ b, D (g b) = 0 := by
        intro b
        have h := hD (g b)
        rw [himg b, sub_self] at h
        exact (mul_eq_zero.mp h.symm).resolve_left hqn
      have hDβ : ∀ r, D (β r) = 0 := by
        intro r
        have h := hD (β r)
        rw [hβφ r, hβψ r, sub_self] at h
        exact (mul_eq_zero.mp h.symm).resolve_left hqn
      set δ : O →+ k :=
        { toFun := fun a => toF (D a)
          map_zero' := by simp [hD0]
          map_add' := fun a b => by simp [hDadd a b] } with hδdef
      have hδ : ∀ a, δ a = 0 := by
        refine H δ (by simp [hδdef, hD1]) (fun a b => ?_) (fun b => by simp [hδdef, hDg b])
          (fun r => by simp [hδdef, hDβ r])
        show toF (D (a * b)) = toF (ψ a) * toF (D b) + toF (ψ b) * toF (D a)
        rw [hDmul a b, map_add, map_mul, map_mul, hres a]
      intro a
      obtain ⟨s, hs⟩ := hdvd (D a) (hδ a)
      exact ⟨s, by rw [hD a, hs]; ring⟩
  ext a
  exact sub_eq_zero.mp (hsep (φ a - ψ a) (fun n => key n a))

end Core

/-! ### Scheme-level plumbing -/

section SchemeHelpers

variable {S : Type} [CommRing S] [IsLocalRing S] {X : Scheme.{0}}

theorem exists_stalkHom (f : Spec (CommRingCat.of S) ⟶ X) {p : X}
    (hp : f.base (closedPoint S) = p) :
    ∃ θ : X.presheaf.stalk p ⟶ CommRingCat.of S, IsLocalHom θ.hom ∧
      Spec.map θ ≫ X.fromSpecStalk p = f := by
  subst hp
  exact ⟨Scheme.stalkClosedPointTo f, inferInstance,
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk f⟩

theorem stalkHom_injective {p : X} {θ₁ θ₂ : X.presheaf.stalk p ⟶ CommRingCat.of S}
    (h₁ : IsLocalHom θ₁.hom) (h₂ : IsLocalHom θ₂.hom)
    (h : Spec.map θ₁ ≫ X.fromSpecStalk p = Spec.map θ₂ ≫ X.fromSpecStalk p) : θ₁ = θ₂ := by
  have h3 := (SpecToEquivOfLocalRing X (CommRingCat.of S)).symm.injective
    (a₁ := ⟨p, θ₁, h₁⟩) (a₂ := ⟨p, θ₂, h₂⟩) h
  simpa using h3

end SchemeHelpers

/-! ### The formal-immersion principle -/

section Main

open TrivSqZeroExt

variable {q : ℕ} {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
  {k : Type} [CommRing k] [IsLocalRing k]

theorem isLocalHom_comp' {A B C : CommRingCat} (f : A ⟶ B) (g : B ⟶ C)
    (hf : IsLocalHom f.hom) (hg : IsLocalHom g.hom) : IsLocalHom (f ≫ g).hom :=
  ⟨fun a h => hf.map_nonunit _ (hg.map_nonunit _ (by simpa using h))⟩

theorem eq_of_formalImmersion (toF : R →+* k) (htoFloc : IsLocalHom toF)
    (hq : (q : R) ≠ 0)
    (hdvd : ∀ r : R, toF r = 0 → ∃ s, r = (q : R) * s)
    (hsep : ∀ r : R, (∀ n : ℕ, ∃ s, r = (q : R) ^ n * s) → r = 0)
    {XZ AZ : Scheme.{0}} {xstr : XZ ⟶ Spec (CommRingCat.of R)} {fmor : XZ ⟶ AZ}
    {c x : Spec (CommRingCat.of R) ⟶ XZ}
    (hcsec : c ≫ xstr = 𝟙 _) (hxsec : x ≫ xstr = 𝟙 _)
    (htan : ∀ v w : Spec (CommRingCat.of (DualNumber k)) ⟶ XZ,
      v ≫ xstr = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫
        Spec.map (CommRingCat.ofHom toF) →
      w ≫ xstr = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫
        Spec.map (CommRingCat.ofHom toF) →
      Spec.map (CommRingCat.ofHom (fstHom k k k : DualNumber k →ₐ[k] k).toRingHom) ≫ v
        = Spec.map (CommRingCat.ofHom toF) ≫ c →
      Spec.map (CommRingCat.ofHom (fstHom k k k : DualNumber k →ₐ[k] k).toRingHom) ≫ w
        = Spec.map (CommRingCat.ofHom toF) ≫ c →
      v ≫ fmor = w ≫ fmor → v = w)
    (hred : Spec.map (CommRingCat.ofHom toF) ≫ x = Spec.map (CommRingCat.ofHom toF) ≫ c)
    (himg : x ≫ fmor = c ≫ fmor) :
    x = c := by
  haveI : IsLocalHom (CommRingCat.ofHom toF).hom := by rwa [CommRingCat.hom_ofHom]
  -- the two sections hit the same point of `XZ`
  have hpt : x.base (closedPoint R) = c.base (closedPoint R) := by
    rw [← Spec_closedPoint (f := CommRingCat.ofHom toF)]
    exact congrArg (fun m : Spec (CommRingCat.of k) ⟶ XZ => m.base (closedPoint k)) hred
  obtain ⟨p, hpc⟩ : ∃ p : XZ, c.base (closedPoint R) = p := ⟨_, rfl⟩
  obtain ⟨ψ, hψloc, hψ⟩ := exists_stalkHom c hpc
  obtain ⟨φ, hφloc, hφ⟩ := exists_stalkHom x (hpt.trans hpc)
  -- the structure morphism, read on the stalk
  obtain ⟨β, hβ⟩ := Spec.map_surjective (XZ.fromSpecStalk p ≫ xstr)
  have hβsec : ∀ (θ : XZ.presheaf.stalk p ⟶ CommRingCat.of R)
      (m : Spec (CommRingCat.of R) ⟶ XZ), Spec.map θ ≫ XZ.fromSpecStalk p = m →
      m ≫ xstr = 𝟙 _ → β ≫ θ = 𝟙 _ := by
    intro θ m hm hsec
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_id, hβ, ← Category.assoc, hm, hsec]
  have hβψ := hβsec ψ c hψ hcsec
  have hβφ := hβsec φ x hφ hxsec
  -- reduce to an equality of stalk homomorphisms
  suffices hstalk : φ = ψ by rw [← hφ, ← hψ, hstalk]
  -- residues agree
  have hresid : φ ≫ CommRingCat.ofHom toF = ψ ≫ CommRingCat.ofHom toF := by
    refine stalkHom_injective (isLocalHom_comp' _ _ hφloc inferInstance)
      (isLocalHom_comp' _ _ hψloc inferInstance) ?_
    rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc, hφ, hψ]
    exact hred
  -- the images under `fmor` agree
  have himgst : fmor.stalkMap p ≫ φ = fmor.stalkMap p ≫ ψ := by
    refine stalkHom_injective (isLocalHom_comp' _ _ inferInstance hφloc)
      (isLocalHom_comp' _ _ inferInstance hψloc) ?_
    rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc, ← Category.assoc, hφ, hψ]
    exact himg
  have hβψ' : ∀ r, ψ.hom (β.hom r) = r := fun r =>
    congrArg (fun m : CommRingCat.of R ⟶ CommRingCat.of R => m.hom r) hβψ
  have hβφ' : ∀ r, φ.hom (β.hom r) = r := fun r =>
    congrArg (fun m : CommRingCat.of R ⟶ CommRingCat.of R => m.hom r) hβφ
  -- the tangent hypothesis, read as "every derivation killing the image vanishes"
  have H : ∀ d : (XZ.presheaf.stalk p) →+ k, d 1 = 0 →
      (∀ a b, d (a * b) = toF (ψ.hom a) * d b + toF (ψ.hom b) * d a) →
      (∀ b, d ((fmor.stalkMap p).hom b) = 0) → (∀ r, d (β.hom r) = 0) → ∀ a, d a = 0 := by
    intro d hd1 hdmul hdg hdβ
    -- the tangent vector attached to `d`, and the zero tangent vector, made opaque
    have mk : ∀ (dd : (XZ.presheaf.stalk p) →+ k), dd 1 = 0 →
        (∀ a b, dd (a * b) = toF (ψ.hom a) * dd b + toF (ψ.hom b) * dd a) →
        ∃ t : XZ.presheaf.stalk p ⟶ CommRingCat.of (DualNumber k), IsLocalHom t.hom ∧
          (∀ a, TrivSqZeroExt.fst (t.hom a) = toF (ψ.hom a)) ∧
          (∀ a, TrivSqZeroExt.snd (t.hom a) = dd a) := by
      intro dd h1 hm
      refine ⟨CommRingCat.ofHom (ofDeriv (toF.comp ψ.hom) dd h1 hm), ⟨fun a ha => ?_⟩,
        fun a => ?_, fun a => ?_⟩
      · have ha' : IsUnit (ofDeriv (toF.comp ψ.hom) dd h1 hm a) := ha
        rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, ofDeriv_fst] at ha'
        exact hψloc.map_nonunit _ (htoFloc.map_nonunit _ ha')
      · show TrivSqZeroExt.fst (ofDeriv (toF.comp ψ.hom) dd h1 hm a) = _
        rw [ofDeriv_fst]; rfl
      · show TrivSqZeroExt.snd (ofDeriv (toF.comp ψ.hom) dd h1 hm a) = _
        rw [ofDeriv_snd]
    obtain ⟨τ, hτloc, hτfst, hτsnd⟩ := mk d hd1 hdmul
    obtain ⟨τ₀, hτ₀loc, hτ₀fst, hτ₀snd⟩ := mk 0 rfl (by intro a b; simp)
    -- the three conditions of `htan`
    have hfst : ∀ (t : XZ.presheaf.stalk p ⟶ CommRingCat.of (DualNumber k)),
        (∀ a, TrivSqZeroExt.fst (t.hom a) = toF (ψ.hom a)) →
        t ≫ CommRingCat.ofHom (fstHom k k k : DualNumber k →ₐ[k] k).toRingHom
          = ψ ≫ CommRingCat.ofHom toF :=
      fun t ht => CommRingCat.hom_ext (RingHom.ext fun a => ht a)
    have hoverbase : ∀ (t : XZ.presheaf.stalk p ⟶ CommRingCat.of (DualNumber k)),
        (∀ a, TrivSqZeroExt.fst (t.hom a) = toF (ψ.hom a)) →
        (∀ r, TrivSqZeroExt.snd (t.hom (β.hom r)) = 0) →
        β ≫ t = CommRingCat.ofHom toF ≫ CommRingCat.ofHom (algebraMap k (DualNumber k)) :=
      fun t ht1 ht2 => CommRingCat.hom_ext (RingHom.ext fun r =>
        TrivSqZeroExt.ext (by
            show TrivSqZeroExt.fst (t.hom (β.hom r)) = _
            rw [ht1 (β.hom r), hβψ' r]
            simp [TrivSqZeroExt.algebraMap_eq_inl])
          (by
            show TrivSqZeroExt.snd (t.hom (β.hom r)) = _
            rw [ht2 r]
            simp [TrivSqZeroExt.algebraMap_eq_inl]))
    have hg : fmor.stalkMap p ≫ τ = fmor.stalkMap p ≫ τ₀ :=
      CommRingCat.hom_ext (RingHom.ext fun b => TrivSqZeroExt.ext
        (by show TrivSqZeroExt.fst (τ.hom _) = TrivSqZeroExt.fst (τ₀.hom _)
            rw [hτfst, hτ₀fst])
        (by show TrivSqZeroExt.snd (τ.hom _) = TrivSqZeroExt.snd (τ₀.hom _)
            rw [hτsnd, hτ₀snd]
            exact (hdg b).trans (by simp)))
    have key := htan (Spec.map τ ≫ XZ.fromSpecStalk p) (Spec.map τ₀ ≫ XZ.fromSpecStalk p)
      (by rw [Category.assoc, ← hβ, ← Spec.map_comp, ← Spec.map_comp,
            hoverbase τ hτfst (fun r => by rw [hτsnd]; exact hdβ r)])
      (by rw [Category.assoc, ← hβ, ← Spec.map_comp, ← Spec.map_comp,
            hoverbase τ₀ hτ₀fst (fun r => by rw [hτ₀snd]; simp)])
      (by rw [← Category.assoc, ← Spec.map_comp, hfst τ hτfst, Spec.map_comp,
            Category.assoc, hψ])
      (by rw [← Category.assoc, ← Spec.map_comp, hfst τ₀ hτ₀fst, Spec.map_comp,
            Category.assoc, hψ])
      (by rw [Category.assoc, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
            ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, hg])
    have hττ := stalkHom_injective hτloc hτ₀loc key
    intro a
    rw [← hτsnd a, hττ, hτ₀snd a]
    simp
  -- and the algebra closes it
  have hfin := eq_of_deriv_vanishing toF hq hdvd hsep φ.hom ψ.hom (fmor.stalkMap p).hom β.hom
    (fun a => congrArg (fun m : XZ.presheaf.stalk p ⟶ CommRingCat.of k => m.hom a) hresid)
    (fun b => congrArg
      (fun m : AZ.presheaf.stalk (fmor.base p) ⟶ CommRingCat.of R => m.hom b) himgst)
    hβφ' hβψ' H
  exact CommRingCat.hom_ext hfin

end Main


/-! ### The base ring `ℤ_(q)`, from the two axioms of `IsReductionBase`

`Fermat/FLT/ModularCurve/X0.lean`'s `IsReductionBase q R toF` says exactly two
things about a subring `R ⊆ ℚ` and a ring map `toF : R →+* ZMod q`: that `toF` is
SURJECTIVE, and that its kernel is the set of NON-UNITS.  Everything the
formal-immersion principle needs about the base is derived here from those two
clauses alone, so that this module does not have to import `X0.lean`.
-/

section Base

variable {q : ℕ} {R : Subring ℚ} {toF : ↥R →+* ZMod q}

/-- **The denominator of an element of `R` is invertible in `R`.**  Bézout: with
`u·num + v·den = 1` one has `1/den = u·r + v`, visibly an element of `R`. -/
theorem inv_den_mem (r : ↥R) : ((((r : ℚ)).den : ℚ))⁻¹ ∈ R := by
  obtain ⟨u, v, huv⟩ : IsCoprime ((r : ℚ).num) (((r : ℚ).den : ℤ)) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact (r : ℚ).reduced
  have hrd : (r : ℚ) * (((r : ℚ)).den : ℚ) = (((r : ℚ)).num : ℚ) := Rat.mul_den_eq_num _
  have h1 : ((u : ℚ) * (r : ℚ) + (v : ℚ)) * ((((r : ℚ)).den : ℚ)) = 1 := by
    rw [add_mul, mul_assoc, hrd]
    exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) huv
  rw [← eq_inv_of_mul_eq_one_left h1]
  exact R.add_mem (R.mul_mem (intCast_mem R u) r.2) (intCast_mem R v)

/-- **The denominator, as an element of `R`, is a unit.** -/
theorem isUnit_den (r : ↥R) : IsUnit ((((r : ℚ)).den : ℕ) : ↥R) := by
  refine IsUnit.of_mul_eq_one ⟨((((r : ℚ)).den : ℚ))⁻¹, inv_den_mem r⟩ (Subtype.ext ?_)
  have : (((r : ℚ)).den : ℚ) ≠ 0 := by
    exact_mod_cast (r : ℚ).den_ne_zero
  push_cast
  field_simp

/-- **`q` does not divide the denominator of an element of `R`** — i.e. `R ⊆ ℤ_(q)`. -/
theorem not_dvd_den (hker : ∀ r : ↥R, toF r = 0 ↔ ¬ IsUnit r) (r : ↥R) :
    ¬ q ∣ (((r : ℚ))).den := by
  intro hc
  have h0 : toF ((((r : ℚ)).den : ℕ) : ↥R) = 0 := by
    rw [map_natCast]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr hc
  exact ((hker _).mp h0) (isUnit_den r)

/-- **The residue ring is nontrivial**: at `q = 1` the map `toF` kills `1`. -/
theorem residue_nontrivial (hker : ∀ r : ↥R, toF r = 0 ↔ ¬ IsUnit r) : Nontrivial (ZMod q) := by
  rcases subsingleton_or_nontrivial (ZMod q) with hs | hn
  · exact absurd ((hker 1).mp (Subsingleton.elim _ _)) (not_not.mpr isUnit_one)
  · exact hn

/-- **`R` is local**, its maximal ideal being `ker toF`. -/
theorem base_isLocalRing (hker : ∀ r : ↥R, toF r = 0 ↔ ¬ IsUnit r) : IsLocalRing ↥R := by
  haveI := residue_nontrivial hker
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self (fun a => ?_)
  by_cases ha : IsUnit a
  · exact Or.inl ha
  · refine Or.inr ?_
    by_contra hb
    have h1 : toF a = 0 := (hker a).mpr ha
    have h2 : toF (1 - a) = 0 := (hker _).mpr hb
    rw [map_sub, map_one, h1, sub_zero] at h2
    exact one_ne_zero h2

/-- **`toF` is a local homomorphism.** -/
theorem base_isLocalHom (hker : ∀ r : ↥R, toF r = 0 ↔ ¬ IsUnit r) : IsLocalHom toF := by
  haveI := residue_nontrivial hker
  refine ⟨fun a ha => ?_⟩
  by_contra hu
  rw [(hker a).mpr hu] at ha
  exact zero_ne_one (isUnit_zero_iff.mp ha)

/-- **The residue ring is local** (indeed a field). -/
theorem residue_isLocalRing (hsurj : Function.Surjective toF)
    (hker : ∀ r : ↥R, toF r = 0 ↔ ¬ IsUnit r) : IsLocalRing (ZMod q) := by
  haveI := residue_nontrivial hker
  haveI := base_isLocalRing hker
  exact IsLocalRing.of_surjective' toF hsurj

/-- **`q ≠ 0`**: at `q = 0` the residue ring is `ℤ`, in which `2` is neither `0` nor a unit. -/
theorem base_ne_zero (hsurj : Function.Surjective toF)
    (hker : ∀ r : ↥R, toF r = 0 ↔ ¬ IsUnit r) : q ≠ 0 := by
  rintro rfl
  obtain ⟨r, hr⟩ := hsurj (2 : ZMod 0)
  have h2 : (2 : ZMod 0) ≠ 0 := by decide
  have hu : IsUnit r := by
    by_contra hnu
    exact h2 (hr ▸ (hker r).mpr hnu)
  have hz : IsUnit (2 : ℤ) := hr ▸ hu.map toF
  rcases Int.isUnit_iff.mp hz with h1 | h1 <;> omega

/-- **`q` is PRIME** — a consequence of the two axioms, not a hypothesis: every non-zero
element of `ZMod q` is a unit, which fails at a proper divisor of a composite `q`. -/
theorem base_prime (hsurj : Function.Surjective toF)
    (hker : ∀ r : ↥R, toF r = 0 ↔ ¬ IsUnit r) : q.Prime := by
  have hq0 := base_ne_zero hsurj hker
  haveI : NeZero q := ⟨hq0⟩
  have hne1 : q ≠ 1 := by
    rintro rfl
    exact ((hker 1).mp (Subsingleton.elim _ _)) isUnit_one
  have hfield : ∀ z : ZMod q, z ≠ 0 → IsUnit z := by
    intro z hz
    obtain ⟨r, rfl⟩ := hsurj z
    exact (not_not.mp (fun hu => hz ((hker r).mpr hu))).map toF
  rw [Nat.prime_def_lt]
  refine ⟨by omega, fun m hm hmdvd => ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · exact absurd (Nat.eq_zero_of_zero_dvd hmdvd) hq0
  have hne : ((m : ℕ) : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hc
    exact absurd (Nat.le_of_dvd hmpos hc) (by omega)
  have hu := hfield _ hne
  rw [ZMod.isUnit_iff_coprime] at hu
  exact (Nat.gcd_eq_left hmdvd).symm.trans hu

/-- **`q ≠ 0` in `R`.** -/
theorem base_natCast_ne_zero (hsurj : Function.Surjective toF)
    (hker : ∀ r : ↥R, toF r = 0 ↔ ¬ IsUnit r) : ((q : ℕ) : ↥R) ≠ 0 := by
  intro hc
  have h1 : ((q : ℕ) : ℚ) = 0 := by
    have := congrArg (fun t : ↥R => (t : ℚ)) hc
    push_cast at this
    exact this
  exact base_ne_zero hsurj hker (by exact_mod_cast h1)

/-- **The maximal ideal is `q·R`.** -/
theorem base_exists_mul (r : ↥R) (hr : toF r = 0) :
    ∃ s : ↥R, r = ((q : ℕ) : ↥R) * s := by
  have hnum : ((((r : ℚ)).num : ℤ) : ↥R) = r * ((((r : ℚ)).den : ℕ) : ↥R) := by
    apply Subtype.ext; push_cast; exact (Rat.mul_den_eq_num _).symm
  have hz : toF ((((r : ℚ)).num : ℤ) : ↥R) = 0 := by rw [hnum, map_mul, hr, zero_mul]
  rw [map_intCast] at hz
  obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
  refine ⟨⟨(m : ℚ) * ((((r : ℚ)).den : ℚ))⁻¹,
    R.mul_mem (intCast_mem R m) (inv_den_mem r)⟩, ?_⟩
  apply Subtype.ext
  push_cast
  have hd : ((((r : ℚ)).den : ℚ)) ≠ 0 := by exact_mod_cast (r : ℚ).den_ne_zero
  have hrd : (r : ℚ) * ((((r : ℚ)).den : ℚ)) = ((((r : ℚ)).num : ℤ) : ℚ) := Rat.mul_den_eq_num _
  field_simp
  rw [hrd]
  exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) hm

/-- **Every element of `R` has non-negative `q`-adic valuation.** -/
theorem base_padicValRat_nonneg (hker : ∀ r : ↥R, toF r = 0 ↔ ¬ IsUnit r) (r : ↥R) :
    0 ≤ padicValRat q ((r : ℚ)) := by
  have hz : padicValNat q ((r : ℚ)).den = 0 :=
    padicValNat.eq_zero_of_not_dvd (not_dvd_den hker r)
  simp only [padicValRat, hz]
  simp

/-- **`⋂ₙ qⁿ R = 0`**: `R` is `q`-adically separated. -/
theorem base_eq_zero_of_forall_pow (hsurj : Function.Surjective toF)
    (hker : ∀ r : ↥R, toF r = 0 ↔ ¬ IsUnit r) (r : ↥R)
    (H : ∀ n : ℕ, ∃ s : ↥R, r = ((q : ℕ) : ↥R) ^ n * s) : r = 0 := by
  haveI : Fact q.Prime := ⟨base_prime hsurj hker⟩
  by_contra hr0
  have hrQ : (r : ℚ) ≠ 0 := fun hc => hr0 (Subtype.ext hc)
  have hqQ : ((q : ℚ)) ≠ 0 := by exact_mod_cast base_ne_zero hsurj hker
  have key : ∀ n : ℕ, (n : ℤ) ≤ padicValRat q ((r : ℚ)) := by
    intro n
    obtain ⟨s, hs⟩ := H n
    have hrs : (r : ℚ) = (q : ℚ) ^ n * (s : ℚ) := by
      have := congrArg (fun t : ↥R => (t : ℚ)) hs
      push_cast at this
      exact this
    have hsQ : (s : ℚ) ≠ 0 := by
      intro hc
      exact hrQ (by rw [hrs, hc, mul_zero])
    rw [hrs, padicValRat.mul (pow_ne_zero _ hqQ) hsQ, padicValRat.pow,
      padicValRat.self (base_prime hsurj hker).one_lt]
    have := base_padicValRat_nonneg hker s
    omega
  have h1 := key ((padicValRat q ((r : ℚ))).toNat + 1)
  omega

end Base

/-! ### The principle over a subring of `ℚ` -/

/-- **THE FORMAL-IMMERSION PRINCIPLE, in the form `MazurTorsion.lean` consumes.**

The base is a subring `R ⊆ ℚ` together with a surjection `toF : R →+* ZMod q` whose
kernel is the set of non-units — i.e. exactly the two clauses of
`Fermat.IsReductionBase q R toF`, which force `R = ℤ_(q)` and `q` prime.

Note what is NOT asked for: no smoothness of `xstr`, no abelian-scheme structure on the
target, no properness, no noetherian hypothesis, no `q ≠ 2`.  See the module docstring. -/
theorem eq_of_formalImmersion_subringRat {q : ℕ} {R : Subring ℚ} {toF : ↥R →+* ZMod q}
    (hsurj : Function.Surjective toF) (hker : ∀ r : ↥R, toF r = 0 ↔ ¬ IsUnit r)
    {XZ AZ : Scheme.{0}} {xstr : XZ ⟶ Spec (CommRingCat.of ↥R)} {fmor : XZ ⟶ AZ}
    {c x : Spec (CommRingCat.of ↥R) ⟶ XZ}
    (hcsec : c ≫ xstr = 𝟙 _) (hxsec : x ≫ xstr = 𝟙 _)
    (htan : ∀ v w : Spec (CommRingCat.of (DualNumber (ZMod q))) ⟶ XZ,
      v ≫ xstr = Spec.map (CommRingCat.ofHom (algebraMap (ZMod q) (DualNumber (ZMod q)))) ≫
        Spec.map (CommRingCat.ofHom toF) →
      w ≫ xstr = Spec.map (CommRingCat.ofHom (algebraMap (ZMod q) (DualNumber (ZMod q)))) ≫
        Spec.map (CommRingCat.ofHom toF) →
      Spec.map (CommRingCat.ofHom
          (TrivSqZeroExt.fstHom (ZMod q) (ZMod q) (ZMod q) :
            DualNumber (ZMod q) →ₐ[ZMod q] ZMod q).toRingHom) ≫ v
        = Spec.map (CommRingCat.ofHom toF) ≫ c →
      Spec.map (CommRingCat.ofHom
          (TrivSqZeroExt.fstHom (ZMod q) (ZMod q) (ZMod q) :
            DualNumber (ZMod q) →ₐ[ZMod q] ZMod q).toRingHom) ≫ w
        = Spec.map (CommRingCat.ofHom toF) ≫ c →
      v ≫ fmor = w ≫ fmor → v = w)
    (hred : Spec.map (CommRingCat.ofHom toF) ≫ x = Spec.map (CommRingCat.ofHom toF) ≫ c)
    (himg : x ≫ fmor = c ≫ fmor) :
    x = c := by
  haveI := base_isLocalRing hker
  haveI := residue_isLocalRing hsurj hker
  exact eq_of_formalImmersion toF (base_isLocalHom hker) (base_natCast_ne_zero hsurj hker)
    (fun r hr => base_exists_mul r hr) (fun r H => base_eq_zero_of_forall_pow hsurj hker r H)
    hcsec hxsec htan hred himg

end Fermat.FormalImmersion
