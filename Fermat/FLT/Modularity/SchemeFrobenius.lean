/-
Modularity/SchemeFrobenius.lean — own work for the Fermat project (not
vendored from the FLT project).

# The absolute Frobenius endomorphism of a scheme of characteristic `p`

This module supplies a piece of scheme theory that **the mathlib pin does
not have at all**: the absolute Frobenius morphism of a scheme.  The check
that established the absence, re-run 2026-07-27 in this worktree, is

    grep -rli frobenius .lake/packages/mathlib/Mathlib/AlgebraicGeometry/

which is EMPTY; `~/cs/FLT` has no abelian-variety or Frobenius material
either.  What the pin does have is the *ring-level* Frobenius
(`frobenius`, `iterateFrobenius` in `Mathlib/Algebra/CharP/Frobenius.lean`),
and that is all this module needs: the geometric Frobenius is built here
directly as a morphism of locally ringed spaces.

## What is here

For a scheme `X` in which the prime `p` is zero on every section
(`hchar : ∀ U, (p : Γ(X, U)) = 0` — the hypothesis is stated in this
elementary form rather than as `CharP Γ(X, U) p` because `Γ(X, ⊥)` is the
TRIVIAL ring, which has no `CharP` and no `ExpChar` instance at all):

* `absFrobScheme X p a hp hchar : X ⟶ X` — the absolute `p ^ a`-power
  Frobenius.  It is the IDENTITY on the underlying topological space and
  `s ↦ s ^ p ^ a` on the structure sheaf.
* `absFrobScheme_naturality` — it is a natural endomorphism of the identity
  functor: `Fr_X ≫ g = g ≫ Fr_Y` for every morphism `g : X ⟶ Y`.  This is
  the only substantive statement in the module, and it is the one every
  consumer actually uses: it is what makes "arithmetic Frobenius = Frobenius
  endomorphism" an identity of morphisms rather than of point maps.
* `absFrobScheme_spec` — on an affine scheme it is `Spec` of the power map.
* `exists_absFrobenius_of_finiteBase` — the packaged form over a FINITE base
  field `k` with `N` elements: a natural endomorphism `Φ` of the identity
  functor on `k`-schemes which is a `k`-morphism (`Φ ≫ a = a`) and which on
  `Spec` of a `k`-algebra is `Spec` of the `N`-power map.  Being a
  `k`-morphism is exactly where finiteness of `k` is consumed: the
  `N`-power Frobenius of `Spec k` is the IDENTITY because `z ^ N = z` on a
  field with `N` elements, and over an infinite base it is not, so `Φ`
  would not lie over `Spec k` at all.

## Why the sheaf-level construction and not a gluing argument

The absolute Frobenius is the identity on the space, so the pushforward
`(𝟙 X) _* 𝒪_X` is *definitionally* `𝒪_X`
(`TopCat.Presheaf.Pushforward.id_eq` is `rfl`), and the whole datum reduces
to one natural transformation `𝒪_X ⟶ 𝒪_X`.  Naturality of that transformation
is `RingHom.map_pow` for the restriction maps; the local-ring condition on
stalks is `IsUnit (g ^ n) → IsUnit g`, which holds in any monoid.  A gluing
argument over an affine cover would have needed the compatibility on
overlaps, which is the naturality statement it was supposed to produce.
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

noncomputable section

namespace Fermat

/-! ### The `p ^ a`-power map of a ring in which `p` vanishes

The hypothesis is `(p : R) = 0` and NOT `CharP R p`, because the sections of
a scheme over the empty open set form the trivial ring, and the trivial ring
carries neither a `CharP` nor an `ExpChar` instance (`CharP R p` forces
`p = 1`, `ExpChar R 1` forces `CharZero R`).  Every ring of sections of a
scheme over `Spec 𝔽_p` satisfies `(p : R) = 0`; a uniform `CharP` hypothesis
would be FALSE. -/

/-- **`x ↦ x ^ (p ^ a)` as a ring endomorphism** of a commutative ring in
which the prime `p` vanishes.  Additivity is `add_pow_char_pow` after
discarding the trivial ring, where every equation holds. -/
def powFrobHom (R : Type*) [CommRing R] (p a : ℕ) (hp : p.Prime) (h : (p : R) = 0) : R →+* R where
  toFun x := x ^ p ^ a
  map_one' := one_pow _
  map_mul' x y := mul_pow x y _
  map_zero' := zero_pow (pow_ne_zero a hp.ne_zero)
  map_add' x y := by
    rcases subsingleton_or_nontrivial R with hs | hn
    · exact Subsingleton.elim _ _
    · haveI : Fact p.Prime := ⟨hp⟩
      haveI : CharP R p := by
        have hd : ringChar R ∣ p := ringChar.dvd h
        rcases Nat.Prime.eq_one_or_self_of_dvd hp _ hd with h1 | h1
        · exfalso
          have h0 : ((ringChar R : ℕ) : R) = 0 := CharP.cast_eq_zero R (ringChar R)
          rw [h1] at h0
          simp at h0
        · exact h1 ▸ ringChar.charP R
      exact add_pow_char_pow x y p a

/-- **A power of an element is a unit only if the element is.**  The
local-ring condition for the Frobenius on stalks. -/
theorem isUnit_of_isUnit_pow {M : Type*} [CommMonoid M] {y : M} {n : ℕ} (hn : n ≠ 0)
    (h : IsUnit (y ^ n)) : IsUnit y := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [pow_succ'] at h
  exact isUnit_of_mul_isUnit_left h

/-! ### The Frobenius as a morphism of schemes -/

section

variable (X : Scheme.{u}) (p a : ℕ) (hp : p.Prime) (hchar : ∀ U : X.Opens, (p : Γ(X, U)) = 0)

/-- **The `p ^ a`-power map on the structure sheaf**, as an endomorphism of
the presheaf of rings.  Naturality is `RingHom.map_pow` for the restriction
maps. -/
def absFrobC : X.presheaf ⟶ X.presheaf where
  app U := CommRingCat.ofHom (powFrobHom Γ(X, U.unop) p a hp (hchar _))
  naturality := by
    intro U V f
    ext x
    exact (map_pow (X.presheaf.map f).hom x (p ^ a)).symm

/-- **The absolute `p ^ a`-power Frobenius as a morphism of presheafed
spaces**: the identity on the space, the power map on the sheaf.  The
pushforward along `𝟙` is definitionally the presheaf itself, which is why
the `c` field is literally `absFrobC`. -/
def absFrobPsh : X.toPresheafedSpace.Hom X.toPresheafedSpace where
  base := 𝟙 _
  c := absFrobC X p a hp hchar

/-- **The Frobenius acts on every stalk as the `p ^ a`-power map.**  Proved
by writing an element of the stalk as a germ and applying
`PresheafedSpace.stalkMap_germ`. -/
theorem absFrobPsh_stalkMap (x : X) (g : X.presheaf.stalk x) :
    ((absFrobPsh X p a hp hchar).stalkMap x).hom g = g ^ p ^ a := by
  obtain ⟨U, m, s, rfl⟩ := X.presheaf.exists_germ_eq g
  have h := PresheafedSpace.stalkMap_germ_apply (absFrobPsh X p a hp hchar) U x m s
  exact h.trans (map_pow (X.presheaf.germ U x m).hom s (p ^ a))

/-- **The absolute Frobenius as a morphism of locally ringed spaces.**  The
local-ring condition is `isUnit_of_isUnit_pow` applied to the stalk map,
which `absFrobPsh_stalkMap` identifies as the power map. -/
def absFrobLRS : X.toLocallyRingedSpace.Hom X.toLocallyRingedSpace where
  toHom := absFrobPsh X p a hp hchar
  prop := fun x => by
    constructor
    intro y hy
    rw [absFrobPsh_stalkMap] at hy
    exact isUnit_of_isUnit_pow (pow_ne_zero a hp.ne_zero) hy

/-- **THE ABSOLUTE `p ^ a`-POWER FROBENIUS ENDOMORPHISM OF A SCHEME** in
which the prime `p` vanishes on sections.  It is the identity on the
underlying topological space and `s ↦ s ^ p ^ a` on the structure sheaf. -/
def absFrobScheme : X ⟶ X := ⟨absFrobLRS X p a hp hchar⟩

end

/-- **NATURALITY OF THE ABSOLUTE FROBENIUS**: it is an endomorphism of the
IDENTITY FUNCTOR on schemes of characteristic `p`.

This is the whole point of the construction.  On points the Frobenius says
nothing that the `p`-power map on a ring does not already say; what it adds
is that the square

    X --Fr_X--> X
    |           |
    g           g
    v           v
    Y --Fr_Y--> Y

commutes for EVERY morphism `g`, so that a Galois element realised as a
Frobenius acts on the whole functor of points at once and not merely on one
fibre.  The proof is `RingHom.map_pow` for `g`'s sheaf map: both bases are
`g.base`, and both `c`-components send `s` to `g^{\#}(s) ^ (p ^ a)`. -/
theorem absFrobScheme_naturality {X Y : Scheme.{u}} (p a : ℕ) (hp : p.Prime)
    (hX : ∀ U : X.Opens, (p : Γ(X, U)) = 0) (hY : ∀ U : Y.Opens, (p : Γ(Y, U)) = 0)
    (g : X ⟶ Y) :
    absFrobScheme X p a hp hX ≫ g = g ≫ absFrobScheme Y p a hp hY := by
  apply Scheme.Hom.ext'
  apply LocallyRingedSpace.Hom.ext'
  refine PresheafedSpace.hext _ _ rfl (heq_of_eq ?_)
  refine NatTrans.ext ?_
  funext U
  ext s
  exact (map_pow (g.c.app U).hom s (p ^ a)).symm

/-- **The absolute Frobenius of an AFFINE scheme is `Spec` of the power
map.**  Two morphisms into an affine scheme agree as soon as their global
sections do (`AlgebraicGeometry.ext_of_isAffine`), and on global sections
both sides are `s ↦ s ^ p ^ a` transported along `Scheme.ΓSpecIso`. -/
theorem absFrobScheme_spec {R : Type u} [CommRing R] (p a : ℕ) (hp : p.Prime)
    (h : ∀ U : (Spec (CommRingCat.of R)).Opens, (p : Γ(Spec (CommRingCat.of R), U)) = 0)
    (ψ : R →+* R) (hψ : ∀ z : R, ψ z = z ^ p ^ a) :
    absFrobScheme (Spec (CommRingCat.of R)) p a hp h = Spec.map (CommRingCat.ofHom ψ) := by
  apply AlgebraicGeometry.ext_of_isAffine
  rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of R)).hom, Scheme.ΓSpecIso_naturality]
  ext s
  show (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (s ^ p ^ a) =
    ψ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom s)
  rw [map_pow, hψ]

/-- **A scheme over `Spec k` inherits `p = 0` on every ring of sections.**
The composite `k → Γ(Spec k, ⊤) → Γ(X, ⊤) → Γ(X, U)` is a ring
homomorphism, and a ring homomorphism preserves `(p : ·)`. -/
theorem natCast_sections_eq_zero_of_over {k : Type u} [CommRing k] {X : Scheme.{u}}
    (aX : X ⟶ Spec (CommRingCat.of k)) (p : ℕ) (hk : (p : k) = 0) (U : X.Opens) :
    (p : Γ(X, U)) = 0 := by
  have h := map_natCast ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ aX.appTop ≫
    X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom p
  rw [← h, hk, map_zero]

/-- **THE ABSOLUTE `N`-POWER FROBENIUS OF A SCHEME OVER A FINITE FIELD**
(PROVEN 2026-07-27).

For `k` a finite field with `N` elements there is an endomorphism `Φ` of the
identity functor on `k`-schemes with three properties:

* `Φ X a ≫ a = a` — each `Φ X a` is a morphism **over `Spec k`**.  This is
  the only clause that uses finiteness of `k`, and it uses it through
  `z ^ N = z` (`FiniteField.pow_card`): the `N`-power Frobenius of `Spec k`
  is the IDENTITY, so `Φ` descends to the category of `k`-schemes.  Over an
  infinite base of characteristic `p` the same construction exists but is
  NOT a `k`-morphism, and the statement would be false.
* naturality in `X`;
* on `Spec` of a `k`-algebra `R`, `Φ` is `Spec` of any ring endomorphism
  `ψ` of `R` with `ψ z = z ^ N`.  Applied to `R = k̄` and `ψ` the arithmetic
  Frobenius, this is what identifies the Galois action on geometric points
  with composition with `Φ`.

The witness does not depend on the structure morphism `a` at all (the
absolute Frobenius is intrinsic); `a` appears only so that the
characteristic hypothesis can be derived from it, and by proof irrelevance
`Φ X a = Φ X a'` for any two of them. -/
theorem exists_absFrobenius_of_finiteBase {k : Type u} [Field k] (hfin : Finite k)
    (N : ℕ) (hN : Nat.card k = N) :
    ∃ Φ : (X : Scheme.{u}) → (X ⟶ Spec (CommRingCat.of k)) → (X ⟶ X),
      (∀ (X : Scheme.{u}) (aX : X ⟶ Spec (CommRingCat.of k)), Φ X aX ≫ aX = aX) ∧
      (∀ (X Y : Scheme.{u}) (aX : X ⟶ Spec (CommRingCat.of k))
          (aY : Y ⟶ Spec (CommRingCat.of k)) (g : X ⟶ Y), Φ X aX ≫ g = g ≫ Φ Y aY) ∧
      (∀ (R : Type u) [CommRing R] (aR : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of k))
          (ψ : R →+* R), (∀ z : R, ψ z = z ^ N) →
          Φ (Spec (CommRingCat.of R)) aR = Spec.map (CommRingCat.ofHom ψ)) := by
  classical
  haveI : Fintype k := Fintype.ofFinite k
  obtain ⟨n, hpp, hcard⟩ := FiniteField.card k (ringChar k)
  have hpN : (ringChar k) ^ (n : ℕ) = N := by
    rw [← hcard, ← Nat.card_eq_fintype_card, hN]
  have hk0 : ((ringChar k : ℕ) : k) = 0 := (ringChar.spec k _).mpr dvd_rfl
  have hchar : ∀ (X : Scheme.{u}) (_ : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens),
      ((ringChar k : ℕ) : Γ(X, U)) = 0 := fun _ aX U =>
    natCast_sections_eq_zero_of_over aX _ hk0 U
  refine ⟨fun X aX => absFrobScheme X (ringChar k) (n : ℕ) hpp (hchar X aX), ?_, ?_, ?_⟩
  · intro X aX
    have hpow : ∀ z : k, (RingHom.id k) z = z ^ (ringChar k) ^ (n : ℕ) := by
      intro z
      show z = z ^ (ringChar k) ^ (n : ℕ)
      rw [← hcard]
      exact (FiniteField.pow_card z).symm
    have hoid : CommRingCat.ofHom (RingHom.id k) = 𝟙 (CommRingCat.of k) := rfl
    have hid : absFrobScheme (Spec (CommRingCat.of k)) (ringChar k) (n : ℕ) hpp
        (hchar _ (𝟙 _)) = 𝟙 _ := by
      rw [absFrobScheme_spec (R := k) (ringChar k) (n : ℕ) hpp (hchar _ (𝟙 _)) (RingHom.id k) hpow,
        hoid, Spec.map_id]
    rw [absFrobScheme_naturality (ringChar k) (n : ℕ) hpp (hchar X aX) (hchar _ (𝟙 _)) aX, hid,
      Category.comp_id]
  · intro X Y aX aY g
    exact absFrobScheme_naturality (ringChar k) (n : ℕ) hpp (hchar X aX) (hchar Y aY) g
  · intro R _ aR ψ hψ
    exact absFrobScheme_spec (R := R) (ringChar k) (n : ℕ) hpp (hchar _ aR) ψ
      (fun z => by rw [hψ z, hpN])

end Fermat

end
