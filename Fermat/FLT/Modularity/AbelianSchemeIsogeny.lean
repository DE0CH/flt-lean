/-
Modularity/AbelianSchemeIsogeny.lean — own work for the Fermat project
(not vendored from the FLT project).

# Multiplication by `n` on an abelian scheme, as a morphism, and its surjectivity

This module sits between `Modularity/AbelianScheme.lean` (which gives an
abelian scheme only through its functor of points) and
`Modularity/TateModule.lean` (which consumes divisibility of a geometric
fibre).  It supplies the object that statement is really about — the
MORPHISM `[n] : A ⟶ A` — and reduces

  `exists_nsmul_eq_geomFibrePt` (`A_x̄(F̄)` is `n`-divisible)

to a single statement of the theory of abelian varieties which mentions
no Galois action, no field, and no group of points:

  `flat_locallyOfFinitePresentation_mulByNat` — `[n]` is FLAT and of
  finite presentation, i.e. (with the already-free properness) `[n]` is
  finite locally free.  That is the output of the THEOREM OF THE CUBE.

## Why a separate module

The Yoneda layer below (`RelPoint.self` … `isProper_mulByNat`) previously
lived inside `Modularity/TateModule.lean`, *below* the divisibility leaf
it is needed to prove.  Lean's declaration order therefore made the leaf
unprovable where it stands.  Moving the layer into an upstream module —
rather than reordering a 5000-line file whose other leaves have their own
owners — is the minimal fix, and it also cuts the layer's elaboration out
of that file.  The declarations are moved VERBATIM and keep their names,
so every existing consumer resolves unchanged through the `public import`.

## The reduction, in full

Everything here except the one leaf is PROVEN.  The chain is:

1. **Yoneda.** `mulByNat n : A ⟶ A` is the `n`-fold sum of the
   tautological point `𝟙 A`, and `nsmul_val` says precomposition with it
   computes `n • y` on every relative point.  Hence "`∃ w, n • w = y`" is
   literally "`y.1` factors through `[n]`" (`exists_nsmul_of_exists_comp`).
2. **For free from `ab`.** `[n] ≫ f = f`, so `[n]` is PROPER
   (`isProper_mulByNat`, via `IsProper.of_comp`) and LOCALLY OF FINITE
   TYPE (`locallyOfFiniteType_mulByNat`, via `locallyOfFiniteType_of_comp`).
   Neither uses any abelian-variety input.
3. **The leaf.** `[n]` is flat and locally of finite presentation.
4. **`[n]` is UNIVERSALLY OPEN** (`universallyOpen_mulByNat`), by
   `UniversallyOpen.of_flat`.
5. **`[n]` is SURJECTIVE** (`surjective_mulByNat`).  Its image is open by
   (4) and closed by (2), hence clopen; it meets every fibre of `f`
   because `[n]` fixes the zero section (`zeroSection_comp_mulByNat`); and
   the fibres of `f` are CONNECTED (`ab.connected`).  A clopen set meeting
   a connected set contains it, so the image is everything.  **This is the
   only place `ab.connected` is used, and it is essential**: for a
   disconnected group scheme `[n]` need not be surjective.
6. **`F̄`-points lift** (`exists_comp_eq_of_surjective`).  Base-change `[n]`
   along the point; the pullback is surjective onto `Spec F̄` hence
   nonempty, and locally of finite type over a field, hence a Jacobson
   space; a closed point of it has residue field `F̄` because `F̄` is
   algebraically closed, giving a section.  This is the Nullstellensatz
   step, and it is general scheme theory — no abelian varieties in it.

Step 6 is why the leaf may be stated about the morphism rather than about
points: the passage from "surjective as a map of schemes" to "surjective
on `F̄`-points" is proven here once and for all.
-/
module

public import Fermat.FLT.Modularity.AbelianScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
-- The decomposition of `flat_of_finite_fibres_endo` (miracle flatness) below.
-- `IsFinite` and `LocallyQuasiFinite` occur in the SIGNATURES of its geometric
-- leaves, and `IsRegularLocalRing` / `ringKrullDim` in the signature of its
-- commutative-algebra leaf, so all four are `public import`s and not bare ones.
-- `QuasiFinite` supplies `LocallyQuasiFinite.of_finite_preimage_singleton` and
-- `ZariskisMainTheorem` supplies `IsFinite.of_isProper_of_locallyQuasiFinite`;
-- together they turn the hypothesis "`IsProper u` with finite fibres" into
-- `IsFinite u`, which is the form all three geometric leaves consume.
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.RingTheory.RegularLocalRing.Defs
-- Consumed by the PROOFS of the two leaves below.  `ResidueField.Fiber` supplies
-- `Ideal.Fiber` (the `κ(p) ⊗ S` of `Algebra.QuasiFinite.finite_fiber`) and
-- `TensorProduct.Quotient` the identification of that fibre with `T ⧸ 𝔪T`;
-- `HopkinsLevitzki` / `KrullDimension.Zero` turn "artinian" into
-- `ringKrullDim = 0`; `LocalRing.RingHom.Basic` supplies
-- `IsLocalRing.map_maximalIdeal_lt_top`.  `Regular.RegularSequence` and
-- `RingHom.Flat` occur in the SIGNATURES of the three sub-leaves of
-- `flat_of_isRegularLocalRing_of_ringKrullDim_eq`, so they are `public`.
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.RingHom.Flat

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace Fermat

section MulByNat

variable {A S : Scheme.{u}} {f : A ⟶ S}

/-- **The tautological relative point** of `f : A ⟶ S`: the identity of
`A`, read as an `A`-point of `A` over the base point `f` itself. It is
the universal element of the functor of points, and it is what makes
`AbelianSchemeStruct.mulByNat` below constructible without any Yoneda
apparatus. -/
def RelPoint.self (f : A ⟶ S) : RelPoint f f := ⟨𝟙 A, Category.id_comp f⟩

/-- **Every relative point is the tautological one, pulled back along
itself.** This is the Yoneda lemma for `RelPoint`, in the only form
needed here. -/
theorem RelPoint.pre_self {T : Scheme.{u}} {g : T ⟶ S} (y : RelPoint f g) :
    RelPoint.pre y.1 y.2 (RelPoint.self f) = y :=
  Subtype.ext (Category.comp_id _)

/-! ### Relative points of a base change

The functor of points of the base change `A ×_S T ⟶ T` along `g : T ⟶ S`
is the functor of points of `A ⟶ S` restricted to base points that factor
through `g`.  Concretely, for `h : U ⟶ T`,

  `RelPoint (pullback.snd f g) h  ≃  RelPoint f (h ≫ g)`,

by the universal property of the pullback.  That bijection is
`baseChangeDown`/`baseChangeUp` below, and it is what transports the whole
`AbelianSchemeStruct` — group law, naturality and all — from `f` to its
base change.  Nothing here is specific to abelian schemes.
-/

section BaseChangePoints

open _root_.CategoryTheory.Limits

namespace RelPoint

variable {T : Scheme.{u}} (g : T ⟶ S)

/-- **A relative point of the base change, read as a relative point of `f`**:
compose with the projection `A ×_S T ⟶ A`.  The base point moves from
`h : U ⟶ T` to `h ≫ g : U ⟶ S`. -/
noncomputable def baseChangeDown {U : Scheme.{u}} {h : U ⟶ T}
    (x : RelPoint (pullback.snd f g) h) : RelPoint f (h ≫ g) :=
  ⟨x.1 ≫ pullback.fst f g, by
    rw [Category.assoc, pullback.condition, ← Category.assoc, x.2]⟩

/-- **A relative point of `f` over a base point factoring through `g`, read
as a relative point of the base change**: the universal property of the
pullback.  Inverse to `baseChangeDown`. -/
noncomputable def baseChangeUp {U : Scheme.{u}} {h : U ⟶ T}
    (x : RelPoint f (h ≫ g)) : RelPoint (pullback.snd f g) h :=
  ⟨pullback.lift x.1 h x.2, pullback.lift_snd _ _ _⟩

@[simp] theorem baseChangeDown_val {U : Scheme.{u}} {h : U ⟶ T}
    (x : RelPoint (pullback.snd f g) h) :
    (baseChangeDown g x).1 = x.1 ≫ pullback.fst f g := rfl

@[simp] theorem baseChangeUp_val {U : Scheme.{u}} {h : U ⟶ T} (x : RelPoint f (h ≫ g)) :
    (baseChangeUp g x).1 = pullback.lift x.1 h x.2 := rfl

theorem baseChangeDown_baseChangeUp {U : Scheme.{u}} {h : U ⟶ T} (x : RelPoint f (h ≫ g)) :
    baseChangeDown g (baseChangeUp g x) = x :=
  Subtype.ext (pullback.lift_fst _ _ _)

theorem baseChangeUp_baseChangeDown {U : Scheme.{u}} {h : U ⟶ T}
    (x : RelPoint (pullback.snd f g) h) : baseChangeUp g (baseChangeDown g x) = x := by
  refine Subtype.ext ?_
  refine pullback.hom_ext ?_ ?_
  · simpa using pullback.lift_fst (C := Scheme.{u}) (x.1 ≫ pullback.fst f g) h _
  · simpa [x.2] using pullback.lift_snd (C := Scheme.{u}) (x.1 ≫ pullback.fst f g) h _

theorem baseChangeDown_injective {U : Scheme.{u}} {h : U ⟶ T} :
    Function.Injective (baseChangeDown (f := f) g (U := U) (h := h)) :=
  Function.LeftInverse.injective (baseChangeUp_baseChangeDown g)

/-- **`baseChangeDown` is natural**: it commutes with precomposition of
relative points.  Both sides are `h ≫ x.1 ≫ pullback.fst`, associated
differently. -/
theorem baseChangeDown_pre {U' U : Scheme.{u}} (h : U' ⟶ U) {k : U ⟶ T} {k' : U' ⟶ T}
    (hk : h ≫ k = k') (x : RelPoint (pullback.snd f g) k) :
    baseChangeDown g (RelPoint.pre h hk x) =
      RelPoint.pre h (show h ≫ (k ≫ g) = k' ≫ g by rw [← Category.assoc, hk])
        (baseChangeDown g x) :=
  Subtype.ext (Category.assoc _ _ _)

end RelPoint

end BaseChangePoints

/-- **Cancellation for `LocallyOfFinitePresentation`** (PROVEN 2026-07-26):
if `f ≫ g` is locally of finite presentation and `g` is locally of finite
TYPE, then `f` is locally of finite presentation.  Stacks 0562/01TS.

This is general scheme theory with no abelian-variety content, and it is a
gap in mathlib at this pin: `LocallyOfFiniteType` has
`locallyOfFiniteType_of_comp` and `LocallyQuasiFinite` has
`LocallyQuasiFinite.of_comp`, both via `HasRingHomProperty.of_comp`, but
`LocallyOfFinitePresentation` has neither — and it cannot use
`HasRingHomProperty.of_comp` as it stands, because that helper's
hypothesis `Q (g ∘ f) → Q g` admits no side condition, whereas the ring
statement `RingHom.FinitePresentation.of_comp_finiteType` genuinely needs
`f` of finite type.  (It must: `LocallyOfFinitePresentation` is not
cancellable outright.  A closed immersion `Spec (R/I) ⟶ Spec R` with `I`
not finitely generated is not locally of finite presentation, while its
composite with `Spec R ⟶ Spec (R/I)`'s base need not see that.)

So the proof re-runs `HasRingHomProperty.of_comp`'s four-step reduction —
affine target, affine middle, affine source, then the ring statement —
carrying the auxiliary hypothesis through each step.  `LocallyOfFiniteType`
is Zariski-local at source and target, which is exactly what makes the
extra hypothesis survive the restrictions. -/
theorem locallyOfFinitePresentation_of_comp {X Y Z : Scheme.{u}} {p : X ⟶ Y} {q : Y ⟶ Z}
    (h : LocallyOfFinitePresentation (p ≫ q)) (h' : LocallyOfFiniteType q) :
    LocallyOfFinitePresentation p := by
  wlog hZ : IsAffine Z generalizing X Y Z
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
      (q.iSup_preimage_eq_top (iSup_affineOpens_eq_top Z))]
    intro U
    have H := IsZariskiLocalAtTarget.restrict h U.1
    rw [morphismRestrict_comp] at H
    exact this H (IsZariskiLocalAtTarget.restrict h' U.1) inferInstance
  wlog hY : IsAffine Y generalizing X Y
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
      (iSup_affineOpens_eq_top Y)]
    intro U
    have H := HasRingHomProperty.comp_of_isOpenImmersion @LocallyOfFinitePresentation
      (p ⁻¹ᵁ U.1).ι (p ≫ q) h
    rw [← morphismRestrict_ι_assoc] at H
    exact this H (HasRingHomProperty.comp_of_isOpenImmersion @LocallyOfFiniteType U.1.ι q h')
      inferInstance
  wlog hX : IsAffine X generalizing X
  · rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
      (iSup_affineOpens_eq_top X)]
    intro U
    have H := HasRingHomProperty.comp_of_isOpenImmersion @LocallyOfFinitePresentation
      U.1.ι (p ≫ q) h
    rw [← Category.assoc] at H
    exact this H inferInstance
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)] at h ⊢
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)] at h'
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] at h
  exact RingHom.FinitePresentation.of_comp_finiteType _ h h'

namespace AbelianSchemeStruct

variable (ab : AbelianSchemeStruct f)

/-- **Pullback of relative points commutes with `n`-fold addition.**
This is `pre_add` and `pre_zero` — the naturality axioms of the group
structure — read at the `ℕ`-action of the resulting `AddCommGroup`. -/
theorem pre_nsmul {T' T : Scheme.{u}} (h : T' ⟶ T) {g : T ⟶ S} {g' : T' ⟶ S}
    (hg : h ≫ g = g') (n : ℕ) (y : RelPoint f g) :
    letI := ab.addCommGroup g
    letI := ab.addCommGroup g'
    RelPoint.pre h hg (n • y) = n • RelPoint.pre h hg y := by
  letI := ab.addCommGroup g
  letI := ab.addCommGroup g'
  induction n with
  | zero =>
      show RelPoint.pre h hg (0 • y) = 0 • RelPoint.pre h hg y
      rw [zero_nsmul, zero_nsmul]
      exact ab.pre_zero h hg
  | succ n ih =>
      rw [succ_nsmul, succ_nsmul]
      show RelPoint.pre h hg (ab.add (n • y) y)
          = ab.add (n • RelPoint.pre h hg y) (RelPoint.pre h hg y)
      rw [ab.pre_add h hg, ih]

/-- **Multiplication by `n`, as a MORPHISM of schemes `A ⟶ A`**: the
underlying morphism of the `n`-fold sum of the tautological relative
point `RelPoint.self f`.

By `nsmul_val` this really is `[n]`: precomposition with it computes
`n • y` on every relative point, so it is the Yoneda realization of the
endomorphism `y ↦ n • y` of the functor of points. No fibre products
and no chosen pullbacks are needed to write it down. -/
noncomputable def mulByNat (n : ℕ) : A ⟶ A :=
  letI := ab.addCommGroup f
  (n • RelPoint.self f).1

/-- **`n`-fold addition of relative points IS precomposition with
`mulByNat n`.** -/
theorem nsmul_val {T : Scheme.{u}} {g : T ⟶ S} (n : ℕ) (y : RelPoint f g) :
    letI := ab.addCommGroup g
    (n • y).1 = y.1 ≫ ab.mulByNat n := by
  letI := ab.addCommGroup g
  letI := ab.addCommGroup f
  conv_lhs => rw [← RelPoint.pre_self y]
  rw [← ab.pre_nsmul y.1 y.2 n (RelPoint.self f)]
  rfl

/-- **The zero section** `S ⟶ A`, i.e. the unit of the group scheme. -/
noncomputable def zeroSection : S ⟶ A := (ab.zero (𝟙 S)).1

/-- **Every zero relative point is the zero section, precomposed.** -/
theorem zero_val {T : Scheme.{u}} (g : T ⟶ S) :
    (ab.zero g).1 = g ≫ ab.zeroSection :=
  congrArg Subtype.val (ab.pre_zero (h := g) (g := 𝟙 S) (g' := g) (Category.comp_id g)).symm

/-- **`mulByNat n` is a morphism over `S`.** -/
theorem mulByNat_comp (n : ℕ) : ab.mulByNat n ≫ f = f :=
  letI := ab.addCommGroup f
  (n • RelPoint.self f).2

/-- **`[1]` is the identity** (PROVEN 2026-07-26).  `1 • self = self`, and
the underlying morphism of the tautological point is `𝟙 A` by definition. -/
theorem mulByNat_one : ab.mulByNat 1 = 𝟙 A := by
  letI := ab.addCommGroup f
  show (1 • RelPoint.self f).1 = 𝟙 A
  rw [one_smul]
  rfl

/-- **`[m·n] = [n] ≫ [m]`** (PROVEN 2026-07-26): `n ↦ [n]` is multiplicative,
i.e. `ℕ ⟶ End(A)` is a monoid map (note the order reversal, since `≫` is
diagrammatic composition and `[m]` is applied last).

This is `nsmul_val` read at the relative point `n • RelPoint.self f`:
`(m • (n • self)).1 = (n • self).1 ≫ [m]`, and `smul_smul` rewrites the
left side to `((m * n) • self).1 = [m * n]`.

**Why it matters.**  It is what reduces flatness of `[n]` to flatness of
`[p]` for `p` PRIME (`flat_mulByNat` below), because flatness of scheme
morphisms is stable under composition.  No route to the leaf avoids it. -/
theorem mulByNat_mul (m n : ℕ) :
    ab.mulByNat (m * n) = ab.mulByNat n ≫ ab.mulByNat m := by
  letI := ab.addCommGroup f
  have h := ab.nsmul_val m (n • RelPoint.self f)
  rw [smul_smul] at h
  exact h

/-- **`mulByNat n` is PROPER**, for free: it commutes with the structure
morphism `f`, which is proper by `ab.proper`, and a morphism whose
composite with a SEPARATED morphism is proper is itself proper
(`IsProper.of_comp`). No abelian-variety input whatsoever. -/
theorem isProper_mulByNat (n : ℕ) : IsProper (ab.mulByNat n) := by
  haveI := ab.proper
  haveI : IsProper (ab.mulByNat n ≫ f) := by rw [ab.mulByNat_comp]; exact ab.proper
  exact IsProper.of_comp _ f

/-! ### The zero section, and finite type — both free -/

/-- **The zero section is a section of `f`** — the second component of
the relative point `ab.zero (𝟙 S)`, read out. -/
theorem zeroSection_comp : ab.zeroSection ≫ f = 𝟙 S := (ab.zero (𝟙 S)).2

/-- **`[n]` fixes the zero section**, `[n] ∘ e = e`.  This is `n • 0 = 0`
in the group of `S`-points, transported through `nsmul_val`.  It is what
makes the image of `[n]` meet every fibre of `f`, which is the
nonemptiness half of the connectedness argument in
`surjective_mulByNat`. -/
theorem zeroSection_comp_mulByNat (n : ℕ) :
    ab.zeroSection ≫ ab.mulByNat n = ab.zeroSection := by
  letI := ab.addCommGroup (𝟙 S)
  have hz : (n • (ab.zero (𝟙 S)) : RelPoint f (𝟙 S)) = ab.zero (𝟙 S) := by
    show (n • (0 : RelPoint f (𝟙 S))) = (0 : RelPoint f (𝟙 S))
    exact smul_zero n
  have h := ab.nsmul_val n (ab.zero (𝟙 S))
  rw [hz] at h
  exact h.symm

/-- **`[n]` is LOCALLY OF FINITE TYPE**, for free, exactly as it is
proper: `[n] ≫ f = f` is locally of finite type because `f` is smooth,
and `locallyOfFiniteType_of_comp` cancels the second factor (no
separatedness hypothesis is needed for this one).

No abelian-variety input.  This is what lets the geometric fibre of `[n]`
be a Jacobson space in `exists_comp_eq_of_surjective`, and it is the
reason the leaf below need not assert finiteness of `[n]`. -/
theorem locallyOfFiniteType_mulByNat (n : ℕ) : LocallyOfFiniteType (ab.mulByNat n) := by
  haveI := ab.smooth
  haveI : LocallyOfFiniteType (ab.mulByNat n ≫ f) := by
    rw [ab.mulByNat_comp]; infer_instance
  exact locallyOfFiniteType_of_comp (ab.mulByNat n) f

/-- **`[n]` is LOCALLY OF FINITE PRESENTATION**, also for free (PROVEN
2026-07-26).

`[n] ≫ f = f` is locally of finite presentation because `f` is smooth,
and `f` is locally of finite type, so `locallyOfFinitePresentation_of_comp`
above cancels the second factor.

This matters for the leaf below: it is the reason the theorem of the cube
has to supply only FLATNESS.  Mathlib's `UniversallyOpen.of_flat` wants
`Flat` *and* `LocallyOfFinitePresentation`, and the second of the two is
not an abelian-variety fact at all. -/
theorem locallyOfFinitePresentation_mulByNat (n : ℕ) :
    LocallyOfFinitePresentation (ab.mulByNat n) := by
  haveI := ab.smooth
  haveI : LocallyOfFinitePresentation (ab.mulByNat n ≫ f) := by
    rw [ab.mulByNat_comp]; infer_instance
  exact locallyOfFinitePresentation_of_comp this inferInstance

/-- **The Yoneda translation of divisibility** (PROVEN): a relative point
`y` is `n`-divisible in the group `RelPoint f g` exactly when its
underlying morphism factors through `[n]`.

The factorization automatically lies over `g`: if `w ≫ [n] = y.1` then
`w ≫ f = w ≫ [n] ≫ f = y.1 ≫ f = g`, so no compatibility has to be
supplied by the caller.  That is the whole reason the geometric input can
be a statement about the MORPHISM `[n]` rather than about the group of
points. -/
theorem exists_nsmul_of_exists_comp {T : Scheme.{u}} {g : T ⟶ S} (n : ℕ)
    (y : RelPoint f g) (h : ∃ w : T ⟶ A, w ≫ ab.mulByNat n = y.1) :
    letI := ab.addCommGroup g
    ∃ w : RelPoint f g, n • w = y := by
  letI := ab.addCommGroup g
  obtain ⟨w, hw⟩ := h
  have hwf : w ≫ f = g := by
    have hb : w ≫ (ab.mulByNat n ≫ f) = g := by
      rw [← Category.assoc, hw]; exact y.2
    rwa [ab.mulByNat_comp] at hb
  refine ⟨⟨w, hwf⟩, Subtype.ext ?_⟩
  rw [ab.nsmul_val n ⟨w, hwf⟩]
  exact hw

/-! ### Base change of an abelian scheme

An abelian scheme stays an abelian scheme after any base change `g : T ⟶ S`,
and multiplication by `n` base-changes to multiplication by `n`.  Both are
formal: the group law transports through the bijection of §"Relative points
of a base change", and properness, smoothness and geometric connectedness
are stable under base change in mathlib.

This is what lets the finiteness leaf below be stated over a FIELD: the
fibre `f.fiber s = A ×_S Spec κ(s)` carries an `AbelianSchemeStruct` over
`Spec κ(s)`, i.e. it is an abelian VARIETY, and `[n]` on it is the
restriction of `[n]` on `A`.
-/

section BaseChange

open _root_.CategoryTheory.Limits

/-- **Base change of an abelian scheme structure** along `g : T ⟶ S`.

The group law is transported through the bijection
`RelPoint (pullback.snd f g) h ≃ RelPoint f (h ≫ g)`; properness,
smoothness and geometric connectedness come from mathlib's
`IsStableUnderBaseChange` instances for the three properties. -/
noncomputable def baseChange (ab : AbelianSchemeStruct f) {T : Scheme.{u}} (g : T ⟶ S) :
    AbelianSchemeStruct (pullback.snd f g) where
  add := fun {_} {_} x y =>
    RelPoint.baseChangeUp g (ab.add (RelPoint.baseChangeDown g x) (RelPoint.baseChangeDown g y))
  zero := fun {_} h => RelPoint.baseChangeUp g (ab.zero (h ≫ g))
  neg := fun {_} {_} x => RelPoint.baseChangeUp g (ab.neg (RelPoint.baseChangeDown g x))
  add_assoc := by
    intro U h x y z
    rw [RelPoint.baseChangeDown_baseChangeUp, RelPoint.baseChangeDown_baseChangeUp,
      ab.add_assoc]
  add_comm := by
    intro U h x y
    rw [ab.add_comm]
  zero_add := by
    intro U h x
    rw [RelPoint.baseChangeDown_baseChangeUp, ab.zero_add,
      RelPoint.baseChangeUp_baseChangeDown]
  neg_add := by
    intro U h x
    rw [RelPoint.baseChangeDown_baseChangeUp, ab.neg_add]
  pre_add := by
    intro U' U h k k' hk x y
    apply RelPoint.baseChangeDown_injective g
    simp only [RelPoint.baseChangeDown_pre, RelPoint.baseChangeDown_baseChangeUp]
    exact ab.pre_add h _ _ _
  pre_zero := by
    intro U' U h k k' hk
    apply RelPoint.baseChangeDown_injective g
    simp only [RelPoint.baseChangeDown_pre, RelPoint.baseChangeDown_baseChangeUp]
    exact ab.pre_zero h _
  proper := by haveI := ab.proper; infer_instance
  smooth := by haveI := ab.smooth; infer_instance
  connected := by haveI := ab.connected; infer_instance

@[simp] theorem baseChange_add (ab : AbelianSchemeStruct f) {T : Scheme.{u}} (g : T ⟶ S)
    {U : Scheme.{u}} {h : U ⟶ T} (x y : RelPoint (pullback.snd f g) h) :
    (ab.baseChange g).add x y =
      RelPoint.baseChangeUp g
        (ab.add (RelPoint.baseChangeDown g x) (RelPoint.baseChangeDown g y)) := rfl

@[simp] theorem baseChange_zero (ab : AbelianSchemeStruct f) {T : Scheme.{u}} (g : T ⟶ S)
    {U : Scheme.{u}} (h : U ⟶ T) :
    (ab.baseChange g).zero h = RelPoint.baseChangeUp g (ab.zero (h ≫ g)) := rfl

/-- **`baseChangeDown` is additive**, hence commutes with the `ℕ`-action. -/
theorem baseChangeDown_nsmul (ab : AbelianSchemeStruct f) {T : Scheme.{u}} (g : T ⟶ S)
    {U : Scheme.{u}} {h : U ⟶ T} (n : ℕ) (x : RelPoint (pullback.snd f g) h) :
    letI := (ab.baseChange g).addCommGroup h
    letI := ab.addCommGroup (h ≫ g)
    RelPoint.baseChangeDown g (n • x) = n • RelPoint.baseChangeDown g x := by
  letI := (ab.baseChange g).addCommGroup h
  letI := ab.addCommGroup (h ≫ g)
  induction n with
  | zero =>
      show RelPoint.baseChangeDown g (0 • x) = 0 • RelPoint.baseChangeDown g x
      rw [zero_nsmul, zero_nsmul]
      show RelPoint.baseChangeDown g ((ab.baseChange g).zero h) = ab.zero (h ≫ g)
      rw [baseChange_zero, RelPoint.baseChangeDown_baseChangeUp]
  | succ n ih =>
      rw [succ_nsmul, succ_nsmul]
      show RelPoint.baseChangeDown g ((ab.baseChange g).add (n • x) x)
          = ab.add (n • RelPoint.baseChangeDown g x) (RelPoint.baseChangeDown g x)
      rw [baseChange_add, RelPoint.baseChangeDown_baseChangeUp, ih]

/-- **`[n]` base-changes to `[n]`**: multiplication by `n` on the base
change `A ×_S T` is the base change of multiplication by `n` on `A`,
expressed as the commuting square with the projection `A ×_S T ⟶ A`.

This is the compatibility that makes the reduction to a field base
legitimate: on the fibre `f.fiber s ⟶ A` the morphism `[n]` of the fibre
is the restriction of `[n]` on `A`, so the two have the same point-set
fibres. -/
theorem baseChange_mulByNat (ab : AbelianSchemeStruct f) {T : Scheme.{u}} (g : T ⟶ S) (n : ℕ) :
    (ab.baseChange g).mulByNat n ≫ pullback.fst f g
      = pullback.fst f g ≫ ab.mulByNat n := by
  letI := (ab.baseChange g).addCommGroup (pullback.snd f g)
  letI := ab.addCommGroup (pullback.snd f g ≫ g)
  letI := ab.addCommGroup f
  have hp : pullback.fst f g ≫ f = pullback.snd f g ≫ g := pullback.condition
  have h1 : RelPoint.baseChangeDown g (n • RelPoint.self (pullback.snd f g))
      = n • RelPoint.baseChangeDown g (RelPoint.self (pullback.snd f g)) :=
    ab.baseChangeDown_nsmul g n _
  have h2 : RelPoint.baseChangeDown g (RelPoint.self (pullback.snd f g))
      = RelPoint.pre (pullback.fst f g) hp (RelPoint.self f) :=
    Subtype.ext (by simp [RelPoint.baseChangeDown, RelPoint.self, RelPoint.pre])
  have h3 : n • RelPoint.pre (pullback.fst f g) hp (RelPoint.self f)
      = RelPoint.pre (pullback.fst f g) hp (n • RelPoint.self f) :=
    (ab.pre_nsmul _ hp n _).symm
  exact congrArg Subtype.val (h1.trans (by rw [h2, h3]))

end BaseChange

end AbelianSchemeStruct

/-! ### The fibrewise reduction, and the theorem of the cube on a fibre

`flat_mulByNat` used to be a single leaf over an ARBITRARY base scheme
`S`, and in that form it is not attackable: the classical proof
("miracle flatness") needs `A` to be REGULAR, which is false over a
general base — `A` is smooth over `S`, so it is only as regular as `S`
is, and `S` is arbitrary here.  The classical argument lives on the
FIBRES, where the base is a field and smoothness does give regularity.

So the leaf is now cut in two along exactly that seam:

* `flat_of_flat_fiberMap` — the **fibrewise criterion of flatness**
  (EGA IV 11.3.10, *critère de platitude par fibres*; Stacks 039E).
  Pure scheme theory: no group scheme, no abelian variety, no `[n]`.
* `flat_fiberMap_mulByNat` — `[p]` is flat **on every fibre**, for `p`
  prime.  This was the abelian-variety half; it is **PROVEN since
  2026-07-27** and is no longer a leaf.

`flat_mulByNat` itself is PROVEN over the two, together with
`mulByNat_mul` (which does the reduction from general `n` to primes).

**The second cut, 2026-07-27 — and where the declarations now live.**
`flat_fiberMap_mulByNat` was closed by carrying the split one step
further, along the seam between the group law and the commutative
algebra.  Over a fibre the base is `Spec κ(s)`, and
`AbelianSchemeStruct.baseChange` — which already existed — makes the
fibre a genuine abelian VARIETY, with `baseChange_mulByNat` identifying
`fiberMapOver [p]` as its own `[p]`.  That reduces the fibre statement to
`flat_mulByNat_of_field`, which in turn splits with NO residue into:

* `finite_preimage_mulByNat_of_field` — the theorem of the cube, and now
  the ONLY leaf in this chain carrying abelian-variety content.  It
  already existed, as the input the torsion CARDINALITY arguments need;
  it is untouched.
* `flat_of_finite_fibres_endo` — **miracle flatness** (Matsumura
  *Commutative Ring Theory* Thm 23.1) in endomorphism form: a proper
  endomorphism with finite fibres of a smooth proper geometrically
  connected scheme over a field is flat.  Pure commutative algebra: no
  group scheme, no abelian variety, no `[n]`.  Declared just below, next
  to `flat_of_flat_fiberMap`, because the two are siblings — both are
  general theorems that would be at home in mathlib.

So the abelian-variety input of the whole divisibility chain is now
concentrated in ONE leaf, where it previously appeared twice.

Declaration ORDER changed to make this possible: `flat_fiberMap_mulByNat`
and `flat_mulByNat` now sit BELOW `finite_preimage_mulByNat`, since they
consume the cube leaf.  They moved down rather than the leaf moving up,
deliberately — that leaf had a live owner, and relocating a declaration
out from under the agent proving it is how merge conflicts get
manufactured here.
-/

/-- **The morphism induced on scheme-theoretic fibres** over a point `s`
of the base by a morphism `u` commuting with the two structure
morphisms.

`Scheme.Hom.fiber p s` is `pullback p (S.fromSpecResidueField s)`, the
fibre over the residue field `κ(s)`, so this is `pullback.map` with the
identity on both the base point and the residue field.  It is the object
the fibrewise criterion of flatness talks about. -/
noncomputable def fiberMapOver {X Y S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    (u : X ⟶ Y) (h : u ≫ q = p) (s : S) : p.fiber s ⟶ q.fiber s :=
  Limits.pullback.map p (S.fromSpecResidueField s) q (S.fromSpecResidueField s)
    u (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id]; exact h.symm)
    (by rw [Category.comp_id, Category.id_comp])

/-- **The fibrewise criterion of flatness, AT A POINT** (sorry leaf —
general scheme theory, NO abelian varieties: Stacks 039C = Stacks Theorem
37.16.2, of which the global `flat_of_flat_fiberMap` below is the
specialization Stacks 039E; EGA IV 11.3.10, *critère de platitude par
fibres*).

`Flat` of a morphism is exactly flatness of every stalk map
(`AlgebraicGeometry.Flat.iff_flat_stalkMap`), so this is the statement the
global one reduces to, and it is the form in which the literature actually
proves it.  Fix `x : X`, put `s = p x` and `y = u x`.  Given that `X` is
flat over `S` at `x` and that the fibre morphism `X_s ⟶ Y_s` is flat at
`x`, conclude that `u` is flat at `x`.

**FAITHFULNESS — this is Stacks 039C verbatim, with hypotheses CHECKED
against the source on 2026-07-27** (not reconstructed from memory).  039C
reads: *`X` locally of finite presentation over `S`; `F` an `O_X`-module
of finite presentation; `Y` locally of finite type over `S`.  Let
`x ∈ X`, `y = f x`, `s` the image in `S`.  If `F_x ≠ 0` then (1) `F` flat
over `S` at `x` and `F_s` flat over `Y_s` at `x`, is equivalent to (2) `Y`
flat over `S` at `y` and `F` flat over `Y` at `x`.*  Instantiate
`F = O_X` (finitely presented as a module over itself, and `O_{X,x} ≠ 0`
because a stalk of a scheme is a local ring, hence nontrivial) and take
the direction (1) ⟹ (2), keeping only the second half of (2).  So:

* `hp` is "`F` flat over `S` at `x`";
* `hfib` is "`F_s` flat over `Y_s` at `x`" — the fibre `p.fiber (p x)` is
  `X_s`, `Scheme.Hom.asFiber` is the canonical point of it above `x`, and
  `fiberMapOver` is `f_s`;
* the conclusion is "`F` flat over `Y` at `x`".

Two hypotheses of the CONSUMER are deliberately **not** taken here,
because 039C does not use them: `Flat q` (039C *produces* flatness of `Y`
over `S` at `y` — it is the discarded first half of (2)), and
`LocallyOfFinitePresentation u`.  `LocallyOfFiniteType q` is what 039C
asks for and is weaker than the consumer's
`LocallyOfFinitePresentation q`; mathlib supplies the instance, so the
consumer still applies.  This leaf is therefore strictly STRONGER than
what `flat_of_flat_fiberMap` needs, and correspondingly reusable.

**ROUTE, and what is missing — surveyed 2026-07-27, each claim paired
with the check that would refute it.**  The classical proof has two
layers, and *only the first* is Noetherian:

1. *The Noetherian local engine* is Stacks 00MP, checked verbatim: `R`,
   `S`, `S'` **Noetherian** local, `R → S → S'` local, `M` a finite
   `S'`-module, `M ≠ 0`, `M/𝔪M` flat over `S/𝔪S`, `M` flat over `R`;
   then `S` is flat over `R` and `M` is flat over `S`.  Taking
   `M = S' = O_{X,x}` makes the finiteness hypothesis automatic, so at
   this level the ONLY real hypothesis is Noetherian-ness.  Its proof
   runs through the **local criterion of flatness** (`Tor₁` vanishing).
2. *`S` here is an ARBITRARY scheme*, so layer 1 does not apply directly.
   That is exactly why 039C carries finite-presentation hypotheses
   instead of Noetherian ones, and why its proof needs a **limit /
   spreading-out** argument (absolute Noetherian approximation) to
   descend to the Noetherian case.  Do not plan a proof that stops at
   00MP; it does not reach this statement.

ABSENT from the pin, each with its refuting grep over
`.lake/packages/mathlib`:

* **Tor of modules over a ring.**  `grep -rn "^def Tor"` finds only the
  categorical `CategoryTheory.Monoidal.Tor` and the group-homology
  `Rep k G` version — there is no `Tor R M N` for modules, hence no
  local criterion of flatness.  `grep -rn "local criterion"` returns
  nothing at all.
* **Cohen–Macaulay and depth.**  `grep -rn CohenMacaulay` returns
  literally nothing; `RingTheory/Regular/Depth.lean` is a 10-line stub.
  (Re-verified 2026-07-27.)
* **Generic flatness and openness of the flat locus.**
  `grep -rln flatLocus` returns nothing.
* **Stalks of pullbacks and of fibres.**  `grep -n stalk` over
  `AlgebraicGeometry/Fiber.lean` and over
  `AlgebraicGeometry/PullbackCarrier.lean` each return NOTHING.  This is
  the reason this leaf was not cut further: the natural next seam is
  "the stalk of `p.fiber s` at `p.asFiber x` is `O_{X,x} ⧸ 𝔪_s O_{X,x}`,
  compatibly with `u`", and that identification would have to be built
  from scratch before the local algebra could even be stated over plain
  rings.  A hit on either grep means that seam is now cheap and this
  leaf should be re-cut along it.
* **Essentially of finite presentation.**  `Algebra.EssFiniteType` exists
  (`RingTheory/EssentialFiniteness.lean`) but there is no
  essentially-of-finite-*presentation* notion, which is what
  `LocallyOfFinitePresentation p` becomes at a stalk.  This is the second
  reason the leaf is not stated over abstract local rings: the honest
  ring-level statement cannot currently be written down.  Do **not**
  weaken it to `EssFiniteType` — finite type is strictly weaker than
  finite presentation and the criterion is not known in that generality,
  so that would risk a FALSE leaf.

`~/cs/FLT` has none of this either (checked 2026-07-26: no
`AbelianVariety`, no cube, no `CohenMacaulay`), so there is nothing to
vendor. -/
theorem flat_stalkMap_of_flat_stalkMap_fiberMapOver
    {X Y S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    (u : X ⟶ Y) (h : u ≫ q = p)
    [LocallyOfFinitePresentation p] [LocallyOfFiniteType q]
    (x : X)
    (hp : (p.stalkMap x).hom.Flat)
    (hfib : ((fiberMapOver u h (p x)).stalkMap (p.asFiber x)).hom.Flat) :
    (u.stalkMap x).hom.Flat :=
  sorry

/-! ### The four inputs of miracle flatness

`flat_of_finite_fibres_endo` below is PROVEN over the four leaves in this
block.  The cut is at the stalks: `AlgebraicGeometry.Flat.of_stalkMap` turns
`Flat u` into a statement about each local homomorphism
`𝒪_{X,u x} ⟶ 𝒪_{X,x}`, and Matsumura 23.1 is exactly a criterion for such a
homomorphism to be flat.  Three of the four leaves are geometry (they say what
`u` and `X` do to stalks) and one is pure commutative algebra.

**What the glue itself contributes, and it is not nothing**: the hypothesis
`IsProper u` together with finite fibres is upgraded ONCE, here, to
`IsFinite u` — via `LocallyQuasiFinite.of_finite_preimage_singleton` and
Zariski's main theorem in mathlib's form
`IsFinite.of_isProper_of_locallyQuasiFinite`.  Every geometric leaf below is
therefore stated with `[IsFinite u]`, which is far more usable than "proper
with finite fibres", and no leaf has to redo that step.

**STATUS OF THE FOUR, 2026-07-27 (updated).**

* `isRegularLocalRing_stalk_of_smooth` — OPEN, and it is a **HOIST**, not a
  proof; see its docstring.  It now unblocks TWO leaves, not one (the other is
  `exists_isWeaklyRegular_span_eq_maximalIdeal` below).
* `ringKrullDim_quotient_map_maximalIdeal_stalkMap` — **PROVEN**, over the new
  ring-level lemma `ringKrullDim_quotient_of_quasiFinite`.  The hand-written
  affine descent the survey called for turned out to be already in mathlib as
  `Scheme.Hom.quasiFiniteAt`.
* `ringKrullDim_stalk_eq_of_isFinite_endo` — OPEN, and still the deepest: it
  needs `dim 𝒪_{X,x} + dim closure{x} = dim X`, and mathlib has no scheme-level
  dimension theory at all.
* `flat_of_isRegularLocalRing_of_ringKrullDim_eq` — **PROVEN over three new
  sub-leaves** (`exists_isWeaklyRegular_span_eq_maximalIdeal`,
  `isWeaklyRegular_map_of_ringKrullDim_eq`,
  `flat_of_isWeaklyRegular_span_eq_maximalIdeal`).  Its docstring also corrects
  the previously recorded "`Tor`-free affine route", which is a route to a
  DIFFERENT (module-finite) theorem and not to that leaf. -/

/-- **SMOOTH OVER A FIELD ⟹ THE STALKS ARE REGULAR LOCAL RINGS**
(sorry leaf — but see the next paragraph: **DO NOT PROVE THIS, HOIST IT**).

**THIS IS ALREADY PROVEN IN THIS REPOSITORY, AND ITS SUBTREE IS SORRY-FREE.**
It stands sorried here for one reason only: DECLARATION ORDER.  The proof is
`GaloisRepresentation.Modularity.isRegularLocalRing_stalk_of_smooth_over_field`
in `Fermat/FLT/Modularity/KhareWintenberger.lean`, and that module is strictly
DOWNSTREAM of this one — it `public import`s `Modularity/TateModule.lean`,
which `public import`s this file — so the proof cannot be imported here.

Verified 2026-07-27, and here is the check that would refute it:

    grep -n 'theorem isRegularLocalRing_stalk_of_smooth_over_field' \
         Fermat/FLT/Modularity/KhareWintenberger.lean
    grep -n '^public import Fermat' Fermat/FLT/Modularity/KhareWintenberger.lean

The first must find the declaration; the second must show `TateModule` among
its imports.  Its own two dependencies were checked the same day and BOTH have
sorry-free bodies:
`exists_isRegularLocalRing_quotient_indepList_of_smooth_over_field` and
`isRegularLocalRing_quotient_span_list_aux` (which is a general "a quotient of
a regular local ring by part of a regular system of parameters is regular
local", a genuine mathlib gap), resting in turn on
`isDomain_of_isRegularLocalRing`.  So there is NO open mathematics under this
leaf anywhere in the tree.

**THE CORRECT REPAIR IS A HOIST, NOT A PROOF.**  Move
`isRegularLocalRing_stalk_of_smooth_over_field` together with those
dependencies into a module upstream of `Modularity/AbelianScheme.lean`, then
this leaf closes in one line (the only difference in the statements is
cosmetic: the downstream one takes `{K : Type u} [Field K]` and
`Spec (CommRingCat.of K)`, this one takes the `K : CommRingCat` that the
consumer already has).  Re-proving it here would be the single most expensive
mistake available at this leaf: it would duplicate a large, finished
development.  Whoever performs the hoist owns the import-cone audit that comes
with it — that is the real work, and it is bookkeeping, not mathematics. -/
theorem isRegularLocalRing_stalk_of_smooth {X : Scheme.{u}} {K : CommRingCat.{u}} [Field K]
    (g : X ⟶ Spec K) [Smooth g] (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) :=
  sorry

/-- **THE FIBRE OF A QUASI-FINITE ALGEBRA OVER A LOCAL RING IS ZERO-DIMENSIONAL**
(PROVEN 2026-07-27 — the ring-level core of
`ringKrullDim_quotient_map_maximalIdeal_stalkMap` below).

For `R` local and `T` a quasi-finite `R`-algebra whose fibre ring `T ⧸ 𝔪_R T` is
nonzero, that fibre ring has Krull dimension `0`.

The whole content is that `Algebra.QuasiFinite` is *by definition*
`Module.Finite κ(p) (p.Fiber T)` at every prime `p` of the BASE — so at
`p = 𝔪_R` it says exactly that the fibre is a finite-dimensional algebra over the
residue field, hence artinian.  Mathlib already carries that instance
(`IsArtinianRing (p.Fiber T)`); all this proof does is transport it along the
standard identification `κ(𝔪) ⊗[R] T ≃ₐ T ⧸ 𝔪T` and convert `Ring.KrullDimLE 0`
into `ringKrullDim = 0`, which needs the nontriviality hypothesis `hne`.

**This is where the module-finiteness trap is dodged**, and it is worth saying
how, because the warning on the geometric statement below is real: nothing here
asks `T` to be a finite `R`-MODULE.  `Algebra.QuasiFinite` is a condition on
FIBRES, and it is stable under localisation of the base in exactly the way
module-finiteness is not. -/
theorem ringKrullDim_quotient_of_quasiFinite (R T : Type u) [CommRing R] [CommRing T]
    [IsLocalRing R] [Algebra R T] [Algebra.QuasiFinite R T]
    (hne : Ideal.map (algebraMap R T) (IsLocalRing.maximalIdeal R) ≠ ⊤) :
    ringKrullDim (T ⧸ Ideal.map (algebraMap R T) (IsLocalRing.maximalIdeal R)) = 0 := by
  have _ : Nontrivial (T ⧸ Ideal.map (algebraMap R T) (IsLocalRing.maximalIdeal R)) :=
    Ideal.Quotient.nontrivial_iff.mpr hne
  -- `κ(𝔪_R) ⊗[R] T ≃ₐ[R] T ⧸ 𝔪_R T`, the identification used in mathlib's own
  -- `Algebra.QuasiFinite.finite_of_isArtinianRing_of_isLocalRing`.
  let e : (IsLocalRing.maximalIdeal R).Fiber T ≃ₐ[R]
      T ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R T) :=
    (Algebra.TensorProduct.congr (.symm <| .ofBijective _
      (Ideal.bijective_algebraMap_quotient_residueField
        (IsLocalRing.maximalIdeal R))) .refl).trans <|
    (Algebra.TensorProduct.comm _ _ _).trans
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot T
      (IsLocalRing.maximalIdeal R)).symm.restrictScalars _)
  have _ : Nontrivial ((IsLocalRing.maximalIdeal R).Fiber T) := e.toEquiv.nontrivial
  rw [← ringKrullDim_eq_of_ringEquiv e.toRingEquiv,
    ← ringKrullDimZero_iff_ringKrullDim_eq_zero]
  infer_instance

/-- **THE FIBRE RING OF A FINITE MORPHISM AT A POINT IS ZERO-DIMENSIONAL**
(**PROVEN 2026-07-27**, over `ringKrullDim_quotient_of_quasiFinite` above —
general scheme theory, NO abelian varieties, no smoothness, no field; true for an
arbitrary finite morphism of schemes).

`𝒪_{X,x} ⧸ 𝔪_{u x} 𝒪_{X,x}` is the local ring at `x` of the scheme-theoretic
fibre `u ⁻¹ (u x)`.  For `u` finite that fibre is `Spec` of a finite
`κ(u x)`-algebra, hence artinian, hence zero-dimensional; and localising an
artinian ring keeps it artinian.  This is the hypothesis `dim M/𝔪M = 0` of
Matsumura 23.1, which is what collapses the general dimension identity
`dim M = dim A + dim M/𝔪M` to the equality supplied by
`ringKrullDim_stalk_eq_of_isFinite_endo`.

The quotient is NONTRIVIAL, so `0` is the right value and not `⊥`: the stalk
map of a morphism of schemes is a LOCAL homomorphism
(`AlgebraicGeometry.Scheme.instIsLocalHomStalkMap`), so
`𝔪_{u x} 𝒪_{X,x} ⊆ 𝔪_x ≠ ⊤`.

**ROUTE AS PLANNED, AND THE MUCH SHORTER ONE ACTUALLY TAKEN** (2026-07-27).  The
survey below proposed descending to an affine cover by hand: choose affine
`V ∋ u x`, use that `u` finite is affine so `U = u ⁻¹ᵁ V` is affine and
`B = Γ(U)` is a finite `A = Γ(V)`-module, identify the stalks with `B_q` and
`A_p` through `IsAffineOpen.isLocalization_stalk`, and localise LAST.  That
route is correct and it is also unnecessary: **mathlib has already done exactly
this descent, once, and packaged it as `Scheme.Hom.quasiFiniteAt`.**

    Scheme.Hom.quasiFiniteAt (f) [LocallyQuasiFinite f] (x) : f.QuasiFiniteAt x

i.e. `(u.stalkMap x).hom.QuasiFinite`, and `[IsFinite u]` supplies
`LocallyQuasiFinite u` by a low-priority instance.  Unfolding
`RingHom.QuasiFinite` through `RingHom.quasiFinite_algebraMap` gives
`Algebra.QuasiFinite 𝒪_{Y,ux} 𝒪_{X,x}`, whose field `finite_fiber` at the prime
`𝔪_{ux}` is *verbatim* the "finite `κ(u x)`-algebra" the survey wanted.  From
there `ringKrullDim_quotient_of_quasiFinite` above finishes it.  Total: eleven
lines, and no affine cover is ever mentioned.

The check that would have found this earlier, and it is the one to copy: the
survey's own sentence "`B ⧸ pB` is a finite `κ(p)`-algebra" IS the definition of
a mathlib class (`Algebra.QuasiFinite`, `RingTheory/QuasiFinite/Basic.lean`).
When a route note describes a property in words, grep for a class that has that
property as its DEFINING field before writing the descent by hand.

The quotient is NONTRIVIAL — needed because `ringKrullDim ⊥ = ⊥ ≠ 0` — by
`IsLocalRing.map_maximalIdeal_lt_top`, which needs only that the stalk map is a
LOCAL homomorphism (`AlgebraicGeometry.Scheme.instIsLocalHomStalkMap`).

**A WARNING, STILL LIVE AFTER THE PROOF, because it is the trap that decided
the shape of `flat_of_isRegularLocalRing_of_ringKrullDim_eq` below.**  Do NOT
try to prove this by showing the stalk map is module-finite and quoting a
finiteness argument at the level of stalks: **THE STALK MAP OF A FINITE
MORPHISM IS NOT MODULE-FINITE.**  Counterexample: `u : Spec ℤ[i] ⟶ Spec ℤ` is
finite; take `p = (5)`, which splits, and `q` one of the two primes above it.
Then `A_p = ℤ_(5)` and `B_q` is a DVR with fraction field `ℚ(i)`.  If `B_q`
were a finite `A_p`-module it would be integral over `A_p`, hence contained in
the integral closure `ℤ[i]_(5) = B_p`; but `B_q ⊋ B_p`, since it inverts the
elements of the OTHER prime above `5`.  So `B_q` is not finite over `A_p`.
Finiteness survives only BEFORE localising at `q`.

The proof below respects that: `Algebra.QuasiFinite` is a condition on FIBRES,
not a module-finiteness condition, and it is precisely the property that DOES
survive localisation of the base.  Nowhere does the proof claim
`Module.Finite 𝒪_{Y,ux} 𝒪_{X,x}`, which is false. -/
theorem ringKrullDim_quotient_map_maximalIdeal_stalkMap {X Y : Scheme.{u}}
    (u : X ⟶ Y) [IsFinite u] (x : X) :
    ringKrullDim ((X.presheaf.stalk x) ⧸
      Ideal.map (u.stalkMap x).hom (IsLocalRing.maximalIdeal (Y.presheaf.stalk (u x)))) = 0 := by
  letI : Algebra (Y.presheaf.stalk (u x)) (X.presheaf.stalk x) := (u.stalkMap x).hom.toAlgebra
  have halg : algebraMap (Y.presheaf.stalk (u x)) (X.presheaf.stalk x) = (u.stalkMap x).hom := rfl
  haveI : Algebra.QuasiFinite (Y.presheaf.stalk (u x)) (X.presheaf.stalk x) :=
    RingHom.quasiFinite_algebraMap.mp (halg ▸ u.quasiFiniteAt x)
  rw [← halg]
  refine ringKrullDim_quotient_of_quasiFinite _ _ ?_
  refine ne_of_lt ?_
  rw [halg]
  exact IsLocalRing.map_maximalIdeal_lt_top _

/-- **A FINITE ENDOMORPHISM PRESERVES THE DIMENSION OF EVERY LOCAL RING**
(sorry leaf — general scheme theory over a field, NO abelian varieties, no
group law, no `[n]`.  This is the deepest of the three geometric leaves and
the one that genuinely needs a dimension theory of schemes.)

For `X` smooth, proper and geometrically connected over a field and `u` a
FINITE endomorphism of `X`, `dim 𝒪_{X,x} = dim 𝒪_{X,u x}` for every `x`.

**ROUTE, in the order the hypotheses are used.**

1. *`X` is irreducible.*  `Smooth g` over a field makes every stalk regular
   local, hence a domain, so `X` is locally irreducible;
   `GeometricallyConnected g` makes it connected; a connected, locally
   noetherian, locally irreducible scheme is irreducible.  Only ORDINARY
   connectedness is used, so this hypothesis may be weakened freely — it is
   `GeometricallyConnected` merely because that is what the caller has in hand
   (`AbelianSchemeStruct.connected`).
2. *`u` is surjective.*  `IsProper g` makes `X` quasi-compact and of finite
   type over the field, hence finite-dimensional.  A finite morphism preserves
   the dimension of a closed subset, so `u '' X` is a closed irreducible subset
   of `X` of the full dimension `dim X`; in an irreducible finite-dimensional
   scheme of finite type over a field the only such subset is `X`.
3. *The dimension formula.*  On an irreducible scheme of finite type over a
   field, `dim 𝒪_{X,x} = dim X - dim (closure {x})`.  Since `u` is finite,
   `dim (closure {x}) = dim (closure {u x})`, and the two local dimensions
   agree.

**WHAT IS MISSING, with the greps that would refute it** (re-run 2026-07-27
against `.lake/packages/mathlib`).  Mathlib has the RING-level dimension
theory — `ringKrullDim`, `Ideal.height`, `Module.supportDim`,
`topologicalKrullDim`, and the dimension-drop lemmas in
`RingTheory/KrullDimension/Regular.lean` — but essentially NO scheme-level
dimension theory: `ls Mathlib/AlgebraicGeometry/` shows no `Dimension.lean`,
and `grep -rn "dim" Mathlib/AlgebraicGeometry/` turns up nothing that proves
step 3.  Step 3 is the classical `dim 𝒪_{X,x} + dim closure{x} = dim X`
(Matsumura 5.6 / EGA IV 5.2.3) and it, not steps 1–2, is the real content of
this leaf.  A hit on a scheme-dimension file means this note has gone stale
and the leaf is far cheaper than it looks. -/
theorem ringKrullDim_stalk_eq_of_isFinite_endo {X : Scheme.{u}} {K : CommRingCat.{u}} [Field K]
    (g : X ⟶ Spec K) [Smooth g] [IsProper g] [GeometricallyConnected g]
    (u : X ⟶ X) [IsFinite u] (x : X) :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (X.presheaf.stalk (u x)) :=
  sorry

/-! ### The three sub-leaves of miracle flatness at the ring level

`flat_of_isRegularLocalRing_of_ringKrullDim_eq` below is PROVEN over the three
statements in this block.  See its docstring for why the previously recorded
"`Tor`-free affine route" is NOT a route to it. -/

/-- **A REGULAR LOCAL RING HAS A REGULAR SYSTEM OF PARAMETERS, AND IT IS A
REGULAR SEQUENCE** (sorry leaf — pure commutative algebra; would be at home in
`Mathlib/RingTheory/RegularLocalRing/`).

`𝔪_R` is generated by `dim R` elements *by the definition of
`IsRegularLocalRing`* (`spanFinrank_maximalIdeal`); the CONTENT of this leaf is
that some such generating list is a weakly regular sequence.

**THIS IS BLOCKED BY DECLARATION ORDER, NOT BY MATHEMATICS — DO NOT PROVE IT
FROM SCRATCH.**  The induction is on `n = (𝔪_R).spanFinrank`:

* `n = 0`: `𝔪_R = ⊥`, so `R` is a field and `rs = []` works
  (`IsWeaklyRegular R []` is vacuous).
* `n + 1`: take `t ∈ 𝔪_R \ 𝔪_R²`.  Then `R ⧸ (t)` is regular local of dimension
  `n`, and `t` is a nonzerodivisor because a regular local ring is a DOMAIN and
  `t ≠ 0`.  Recurse in `R ⧸ (t)`, lift the resulting list along
  `Ideal.Quotient.mk`, and prepend `t`; `isWeaklyRegular_cons_iff` plus the
  identification `QuotSMulTop t R ≃ₗ R ⧸ (t)` and
  `isWeaklyRegular_map_algebraMap_iff` assemble the two halves.

Both non-trivial inputs are **already proven in this repository**:
`isDomain_of_isRegularLocalRing` and `isRegularLocalRing_quotient_span_singleton`
in `Fermat/FLT/Modularity/KhareWintenberger.lean`, together with
`exists_finset_card_span_insert_eq_maximalIdeal` there.  That module is strictly
DOWNSTREAM of this one, which is exactly the situation of
`isRegularLocalRing_stalk_of_smooth` above — and the SAME hoist fixes both.

The check that would refute this note:

    grep -n 'theorem isDomain_of_isRegularLocalRing\b' \
         Fermat/FLT/Modularity/KhareWintenberger.lean
    grep -n 'theorem isRegularLocalRing_quotient_span_singleton' \
         Fermat/FLT/Modularity/KhareWintenberger.lean

Mathlib itself has neither: its entire `IsRegularLocalRing` API is three lemmas
in `RingTheory/RegularLocalRing/Defs.lean` (`of_ringEquiv`,
`of_spanFinrank_maximalIdeal_le`, `iff_finrank_cotangentSpace`) plus the PID
instance — re-checked 2026-07-27 with
`grep -rn IsRegularLocalRing .lake/packages/mathlib/Mathlib/`. -/
theorem exists_isWeaklyRegular_span_eq_maximalIdeal (R : Type u) [CommRing R]
    [IsRegularLocalRing R] :
    ∃ rs : List R, Ideal.span {r | r ∈ rs} = IsLocalRing.maximalIdeal R ∧
      (rs.length : WithBot ℕ∞) = ringKrullDim R ∧
      RingTheory.Sequence.IsWeaklyRegular R rs :=
  sorry

/-- **A SYSTEM OF PARAMETERS OF A REGULAR LOCAL RING IS A REGULAR SEQUENCE**
(sorry leaf — pure commutative algebra; this is "regular local ⟹
Cohen–Macaulay" in the only form the assembly needs, and it is the one genuinely
missing piece of commutative algebra under this node).

The hypotheses say exactly that `rs.map φ` is a system of parameters of `T`:
`hspan` makes `Ideal.span (rs.map φ) = Ideal.map φ 𝔪_R`, `hfib` says that ideal
is `𝔪_T`-primary (dimension `0` quotient), and `hlen` with `hdim` says the list
has exactly `dim T` entries.  `T` regular ⟹ `T` Cohen–Macaulay ⟹ every system of
parameters is a regular sequence.

**WHY THIS IS HARD, and why the obvious induction does not work.**  The FIRST
step is easy and uses only that `T` is a domain: `rs.map φ` being a system of
parameters forces `dim T ⧸ (rs.map φ).head = dim T - 1`, so the head lies in no
minimal prime, and a regular local ring has only the zero minimal prime.  What
breaks is the INDUCTION: `T ⧸ (t)` is in general **not regular** — take
`T = k⟦x⟧` and `t = x²`, where `t` is a system of parameters and `T ⧸ (t)` is
not even reduced.  So the induction hypothesis has to be "Cohen–Macaulay", and
carrying it means having depth theory.  A prover must not plan an induction that
keeps `IsRegularLocalRing` on the quotient.

**ABSENT EVERYWHERE, re-checked 2026-07-27 with the refuting greps.**
`grep -rl CohenMacaulay .lake/packages/mathlib/Mathlib/` is empty and
`Mathlib/RingTheory/Regular/Depth.lean` is a 10-line file with ZERO
declarations.  `~/cs/FLT` DOES have a small `Module.depth` development
(`FLT/Patching/Utils/Depth.lean`, 259 lines: `Module.depth`,
`Module.length_le_depth`, `Module.depth_le_dim`, `Module.depth_le_of_free`,
`RingTheory.Sequence.isWeaklyRegular_of_free`), already vendored into this
project and consumed by `Fermat/FLT/Modularity/PatchingVendored/System.lean` —
but it proves only `depth ≤ dim`, which is the wrong inequality here.  What is
needed is `dim ≤ depth` for a regular local ring (that is sub-leaf 1 above) AND
the unmixedness statement that in a Cohen–Macaulay ring every system of
parameters is regular; only the latter is genuinely new. -/
theorem isWeaklyRegular_map_of_ringKrullDim_eq {R T : Type u} [CommRing R] [CommRing T]
    [IsRegularLocalRing R] [IsRegularLocalRing T] (φ : R →+* T) [IsLocalHom φ] (rs : List R)
    (hspan : Ideal.span {r | r ∈ rs} = IsLocalRing.maximalIdeal R)
    (hlen : (rs.length : WithBot ℕ∞) = ringKrullDim R)
    (hdim : ringKrullDim T = ringKrullDim R)
    (hfib : ringKrullDim (T ⧸ Ideal.map φ (IsLocalRing.maximalIdeal R)) = 0) :
    RingTheory.Sequence.IsWeaklyRegular T (rs.map φ) :=
  sorry

/-- **THE LOCAL CRITERION OF FLATNESS** (sorry leaf — pure commutative algebra;
Matsumura *Commutative Ring Theory* 22.3, Stacks 00MK.  Absent from mathlib,
from `~/cs/FLT` and from this project).

If `𝔪_R` is generated by an `R`-regular sequence `rs` — equivalently, `R` is
regular local with regular system of parameters `rs` — and the image of `rs` is
`T`-regular, then `T` is flat over `R`.

**FAITHFULNESS — the separatedness hypothesis is present, disguised as
`[IsNoetherianRing T] [IsLocalRing T] [IsLocalHom φ]`, and it is LOAD-BEARING.**
The classical criterion needs `T` to be `𝔪_R`-adically *ideally separated*; the
statement is false for an arbitrary `R`-module with a regular sequence acting
regularly.  Here it is automatic and the derivation is short enough to record:
`φ` local gives `𝔪_R T ⊆ 𝔪_T`, hence `𝔪_R^n T ⊆ 𝔪_T^n`, so
`⋂ₙ 𝔪_R^n T ⊆ ⋂ₙ 𝔪_T^n = 0` by Krull's intersection theorem; and `T ⧸ I T` for
`I` finitely generated is again a noetherian local ring, so the same applies to
it.  **A prover who weakens `T` to a bare `R`-module produces a FALSE leaf.**

**THE SINGLE ATOMIC LEMMA THIS REDUCES TO.**  The induction along `rs` is
mechanical — pass from `R → T` to `R ⧸ (t) → T ⧸ tT` and shorten the list — so
the whole content is the one-element case:

> `R`, `T` noetherian local, `φ : R → T` a local homomorphism, `t ∈ 𝔪_R` a
> nonzerodivisor on `R` and on `T`, and `T ⧸ tT` flat over `R ⧸ tR`.  Then `T`
> is flat over `R`.

That is the statement to state and dispatch next if this leaf is cut further;
the surrounding induction needs nothing beyond `isWeaklyRegular_cons_iff` and
the fact that quotients of noetherian local rings are noetherian local.

**WHAT MATHLIB HAS THAT A PROVER WILL WANT**, since there is no `Tor`:
`Module.Flat.iff_rTensor_injective` (`RingTheory/Flat/Basic.lean`) expresses
`Tor₁(R ⧸ I, M) = 0` as injectivity of `I ⊗ M → M`, which is enough to run the
argument without ever constructing derived functors;
`Module.Flat.of_isLocalized_maximal` and the equational criterion
(`RingTheory/Flat/EquationalCriterion.lean`) are the other two handles. -/
theorem flat_of_isWeaklyRegular_span_eq_maximalIdeal {R T : Type u} [CommRing R] [CommRing T]
    [IsLocalRing R] [IsNoetherianRing R] [IsLocalRing T] [IsNoetherianRing T]
    (φ : R →+* T) [IsLocalHom φ] (rs : List R)
    (hspan : Ideal.span {r | r ∈ rs} = IsLocalRing.maximalIdeal R)
    (hR : RingTheory.Sequence.IsWeaklyRegular R rs)
    (hT : RingTheory.Sequence.IsWeaklyRegular T (rs.map φ)) :
    φ.Flat :=
  sorry

/-- **MIRACLE FLATNESS, RING LEVEL** (**PROVEN 2026-07-27** over the three
sub-leaves stated immediately above — PURE COMMUTATIVE ALGEBRA,
no schemes at all: Matsumura *Commutative Ring Theory* Theorem 23.1, in the
special case `M = T` of the source ring itself.  It would be at home in
mathlib, which has nothing of it.)

A local homomorphism `φ : R ⟶ T` of regular local rings whose fibre ring
`T ⧸ 𝔪_R T` is zero-dimensional and which does not change the Krull dimension
is FLAT.

**FAITHFULNESS.**  Matsumura 23.1 reads: *let `(A,𝔪) → (B,𝔫)` be a local
homomorphism of noetherian local rings and `M` a finite `B`-module with `A`
regular, `M` Cohen–Macaulay and `dim M = dim A + dim M/𝔪M`; then `M` is flat
over `A`.*  Instantiate `A = R`, `B = M = T`: `T` is a finite `T`-module, and
`T` regular makes it Cohen–Macaulay.  The dimension identity becomes
`hdim` together with `hfib`.  Note there is **no finiteness hypothesis
relating `R` and `T`** and there must not be — see the counterexample in the
docstring of `ringKrullDim_quotient_map_maximalIdeal_stalkMap` above, which is
exactly why this statement is the one that had to be cut here.

**WHAT MATHLIB HAS, AND ONE CLAIM OF THE OLD SURVEY THAT IS NOW REFUTED.**

* PRESENT: `IsRegularLocalRing` (`RingTheory/RegularLocalRing/Defs.lean`,
  defined by `(maximalIdeal R).spanFinrank = ringKrullDim R`), `ringKrullDim`,
  the regular-sequence theory in `RingTheory/Regular/RegularSequence.lean` —
  including the recursor `IsWeaklyRegular.ndrecWithRing`, which does induction
  along a regular sequence while quotienting the BASE RING as well — and the
  dimension-drop lemmas of `RingTheory/KrullDimension/Regular.lean`.
* **REFUTED (2026-07-27).**  Every earlier survey of this node, including the
  one that used to stand in this file, said that the induction step needs the
  **local criterion of flatness** in its `Tor₁` form and that mathlib has no
  `Tor` of modules, so the leaf was hopeless.  The second half is true —
  `grep -rn "^def Tor" Mathlib/` finds only `CategoryTheory.Monoidal.Tor` and
  the group-homology `Rep k G` version — but the first half is FALSE for
  MODULE-FINITE base changes.  `Module.free_quotSMulTop_iff_free`
  (`Mathlib/RingTheory/Regular/Free.lean`) states exactly the induction step:
  for `M` finitely presented over `R` and `x` in the Jacobson radical and
  `M`-regular, `M ⧸ xM` free over `R ⧸ (x)` **iff** `M` free over `R`.  Its
  proof is Nakayama plus a lifting argument, no `Tor` anywhere.  Refuting
  grep: `grep -n free_quotSMulTop_iff_free
  .lake/packages/mathlib/Mathlib/RingTheory/Regular/Free.lean`.
* So the honest statement of the obstruction is much narrower than "no local
  criterion": *with* module-finiteness the criterion is already in the pin,
  and the two remaining gaps are (a) **the fibre-dimension hypothesis has to be
  turned into a regular sequence**, i.e. "regular local ⟹ Cohen–Macaulay", or
  concretely "a system of parameters of a regular local ring is a regular
  sequence" — `grep -rl CohenMacaulay Mathlib/` is still empty and
  `RingTheory/Regular/Depth.lean` is a deprecation stub with ZERO declarations
  — and (b) the passage from the module-finite case to this one.

**THE "ROUTE THAT AVOIDS `Tor` ENTIRELY" DOES NOT APPLY TO *THIS* STATEMENT —
CORRECTED 2026-07-27, and this is the one thing in the survey above that would
have cost a prover a whole task.**  The route recorded here previously read:
"do not attack this leaf at the stalks; go back to an affine cover, where
finiteness survives", and then checked `Module.Flat A B` at the maximal ideals
of `A` (`Module.flat_of_isLocalized_maximal`), used
`Module.free_of_flat_of_isLocalRing` and inducted with
`Module.free_quotSMulTop_iff_free`.  Every step of that is correct — **for the
affine statement.**  It is not a route to the declaration below, because:

* **the declaration below has NO module-finiteness hypothesis**, deliberately
  (see the FAITHFULNESS paragraph above: Matsumura 23.1 with `M = T` needs
  none), and
* `Module.free_quotSMulTop_iff_free` requires `Module.FinitePresentation R M`,
  and `Module.free_of_flat_of_isLocalRing` requires `Module.Finite R P`.

So the affine route is a route to a DIFFERENT theorem — one about
`A → B` with `B` a finite `A`-module — and taking it here means silently adding
a hypothesis that the counterexample in
`ringKrullDim_quotient_map_maximalIdeal_stalkMap` shows is false at stalks.
Anyone who wants that route must first re-cut the CONSUMER
(`flat_of_finite_fibres_endo`) to descend to an affine cover before reaching the
stalks; that is a cut-level change to the glue, not work at this leaf.

**STATUS 2026-07-27 — DECOMPOSED into three sub-leaves, and this node is PROVEN
over them.**  Each is a standard named theorem, and each is stated in exactly
the generality the assembly needs:

1. `exists_isWeaklyRegular_span_eq_maximalIdeal` — a regular local ring has a
   regular system of parameters, and it is a regular sequence.  **This is the
   cheapest of the three and it is blocked only by DECLARATION ORDER**, exactly
   like `isRegularLocalRing_stalk_of_smooth` above: its two inputs,
   `isDomain_of_isRegularLocalRing` and `isRegularLocalRing_quotient_span_singleton`,
   are both PROVEN in `Fermat/FLT/Modularity/KhareWintenberger.lean` (lines 3071
   and 3109 as of this writing), which is strictly downstream of this module.
   **The hoist that closes `isRegularLocalRing_stalk_of_smooth` closes this one
   too** — that is a second reason to do it, and it was not previously recorded.
2. `isWeaklyRegular_map_of_ringKrullDim_eq` — "regular local ⟹
   Cohen–Macaulay", in the only form needed: a system of parameters of a regular
   local ring is a regular sequence.  This is gap (a) above and it is genuinely
   absent from mathlib, from `~/cs/FLT` and from this project.
3. `flat_of_isWeaklyRegular_span_eq_maximalIdeal` — the **local criterion of
   flatness**.  Genuinely absent, and see its own docstring for the single
   one-element lemma it reduces to.

The assembly is three lines and uses each sub-leaf exactly once. -/
theorem flat_of_isRegularLocalRing_of_ringKrullDim_eq {R T : Type u} [CommRing R] [CommRing T]
    [IsRegularLocalRing R] [IsRegularLocalRing T] (φ : R →+* T) [IsLocalHom φ]
    (hdim : ringKrullDim T = ringKrullDim R)
    (hfib : ringKrullDim (T ⧸ Ideal.map φ (IsLocalRing.maximalIdeal R)) = 0) :
    φ.Flat := by
  obtain ⟨rs, hspan, hlen, hR⟩ := exists_isWeaklyRegular_span_eq_maximalIdeal R
  exact flat_of_isWeaklyRegular_span_eq_maximalIdeal φ rs hspan hR
    (isWeaklyRegular_map_of_ringKrullDim_eq φ rs hspan hlen hdim hfib)

/-- **MIRACLE FLATNESS, endomorphism form** (**PROVEN 2026-07-27** over the
four leaves stated immediately above — PURE COMMUTATIVE
ALGEBRA / general scheme theory, NO abelian varieties, no group law, no
`[n]`: Matsumura *Commutative Ring Theory* Theorem 23.1, the theorem
usually called *miracle flatness*; also in the Stacks Project under that
name, and in EGA IV §6.  Tag numbers deliberately not quoted — they were
not checked against the Stacks Project, and a wrong tag is worse than
none.)

*A proper endomorphism with finite fibres of a smooth proper
geometrically connected scheme over a field is FLAT.*

**Why this shape** (2026-07-27).  It is exactly the residue of
`flat_fiberMap_mulByNat` after the abelian-variety input has been isolated
into `finite_preimage_mulByNat_of_field` below.  Everything specific to
abelian varieties — the group law, the theorem of the cube, the degree
`n^{2g}` — is consumed by that leaf; what is left is a statement about an
arbitrary endomorphism of an arbitrary smooth proper connected variety,
which is where the classical "miracle flatness" theorem lives.  Whoever
proves this proves a general theorem, and it has no group scheme in it at
all — the same division of labour as `flat_of_flat_fiberMap` below.

**The classical proof, in the order the hypotheses are used.**

1. *`u` is FINITE.*  `IsProper u` supplies `LocallyOfFiniteType u`, and
   `hu` supplies finite fibres, so
   `LocallyQuasiFinite.of_finite_preimage_singleton` gives
   `LocallyQuasiFinite u`, and then Zariski's main theorem in mathlib's
   form, `IsFinite.of_isProper_of_locallyQuasiFinite`, gives `IsFinite u`.
   Both lemmas EXIST at this pin — `Morphisms/QuasiFinite.lean:296` and
   `ZariskisMainTheorem.lean:371`, located by name 2026-07-27 — but
   neither module is imported here, so a prover closing this leaf should
   add `Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite` and
   `Mathlib.AlgebraicGeometry.ZariskisMainTheorem` to the header.  That
   missing import is exactly why the hypothesis is phrased as `IsProper`
   plus finite fibres rather than as `[IsFinite u]`: in this form the
   statement needs no import this module does not already have, and the
   caller can discharge it from material that is free here.
2. *`X` is REGULAR and IRREDUCIBLE.*  `Smooth g` over a field gives
   geometric regularity, hence regularity, hence normality, hence local
   irreducibility; `GeometricallyConnected g` gives connectedness; and a
   connected, locally noetherian, locally irreducible scheme is
   irreducible.  Only ORDINARY connectedness is used, so a prover may
   weaken that hypothesis freely — `GeometricallyConnected` is merely what
   the caller has in hand (`AbelianSchemeStruct.connected`).
3. *`u` is SURJECTIVE.*  `IsProper g` makes `X` quasi-compact and of
   finite type over the field, hence finite-dimensional.  A finite
   morphism preserves dimension, so `u '' X` is a closed irreducible
   subset of `X` of the full dimension `dim X`, and in an irreducible
   finite-dimensional scheme of finite type over a field the only such
   subset is `X` itself.
4. *Miracle flatness, pointwise.*  Fix `x` and put `y = u x`.  Then
   `𝒪_{X,y} → 𝒪_{X,x}` is a local homomorphism of REGULAR local rings,
   module-finite because `u` is finite, whose fibre ring
   `𝒪_{X,x} / m_y 𝒪_{X,x}` is a localisation of a finite `κ(y)`-algebra
   and so has dimension `0`.  Since `u` is finite,
   `dim closure {x} = dim closure {u x}`, and on a finite-dimensional
   irreducible scheme of finite type over a field
   `dim 𝒪_{X,x} = dim X - dim closure {x}`; hence
   `dim 𝒪_{X,x} = dim 𝒪_{X,y} + dim (𝒪_{X,x} / m_y 𝒪_{X,x})`.  A regular
   local ring is Cohen–Macaulay, so Matsumura 23.1 applies and `𝒪_{X,x}`
   is flat over `𝒪_{X,y}`.  Conclude with
   `AlgebraicGeometry.Flat.iff_flat_stalkMap`
   (`Morphisms/Flat.lean:102`, located by name 2026-07-27).

**BOTH GLOBAL HYPOTHESES ARE LOAD-BEARING — an explicit counterexample.**
Drop connectedness and the statement is FALSE.  Take `X = 𝔸¹_K ⊔ Spec K`
and let `u` be the identity on `𝔸¹` and send the isolated point to the
origin of `𝔸¹`.  Every fibre is finite, yet on stalks `u` is
`𝒪_{𝔸¹,0} → K`, the quotient by the maximal ideal, which is not flat.
(This `X` is smooth over `K` but neither connected nor proper, so it is
excluded twice over — which is the point: neither hypothesis is
decorative.)

**WHAT IS PRESENT AND WHAT IS MISSING at this pin (checked 2026-07-27, not
inherited).**

* PRESENT: `ringKrullDim` (`RingTheory/KrullDimension/Basic.lean`),
  `Module.supportDim`, `topologicalKrullDim`, `Ideal.height`,
  `IsRegularLocalRing` (`RingTheory/RegularLocalRing/Defs.lean`), the
  regular-sequence theory in `RingTheory/Regular/RegularSequence.lean`,
  and the dimension-drop lemmas Stacks 00KW / 0B52 in
  `RingTheory/KrullDimension/Regular.lean` — which are the induction step
  of miracle flatness.  At scheme level, `Flat.iff_flat_stalkMap`,
  `Scheme.Hom.fiber`, and Zariski's main theorem.
* MISSING: **Cohen–Macaulay and depth**.  `grep -rl CohenMacaulay Mathlib/`
  returns nothing, and `RingTheory/Regular/Depth.lean` is 10 lines with
  ZERO declarations (both re-run 2026-07-27).  Also missing: the local
  criterion of flatness (the `Tor₁` statement), generic flatness, and
  openness of the flat locus —
  `grep -rln "genericFlat\|flatLocus" Mathlib/RingTheory/` is empty.
  `~/cs/FLT` has none of it either.

**To refute this survey**, re-run those three greps; a hit on any of them
means this note has gone stale and the leaf may be far cheaper than it
looks.  Note that a prover does NOT need the whole of CM theory: only
"regular local ⟹ Cohen–Macaulay" plus Matsumura 23.1 in the special case
where BOTH rings are regular, which is the classical dimension count and
does not need depth in its full generality.

**STATUS 2026-07-27 — DECOMPOSED, and the survey above is now out of date in
two places that matter.**  The four steps are separated into the four leaves
stated immediately above this docstring, and this node is proven over them:

* step 1 (`u` is FINITE) is **PROVEN HERE**, in the two `haveI` lines below,
  exactly as the survey predicted — `LocallyQuasiFinite.of_finite_preimage_singleton`
  followed by `IsFinite.of_isProper_of_locallyQuasiFinite`, with the two
  modules added to this file's header.  Nothing else in the chain has to
  re-derive it: all three geometric leaves take `[IsFinite u]`.
* steps 2 and 3 (regularity, irreducibility, surjectivity) and the dimension
  count of step 4 are `isRegularLocalRing_stalk_of_smooth` and
  `ringKrullDim_stalk_eq_of_isFinite_endo`;
* the finiteness of the fibres becomes
  `ringKrullDim_quotient_map_maximalIdeal_stalkMap`;
* and the local algebra is `flat_of_isRegularLocalRing_of_ringKrullDim_eq`.

**FIRST CORRECTION.**  The survey says regularity of the stalks has to be
proven.  It does not: it is ALREADY PROVEN in this repository, sorry-free, as
`GaloisRepresentation.Modularity.isRegularLocalRing_stalk_of_smooth_over_field`
in `Modularity/KhareWintenberger.lean`, which is DOWNSTREAM of this module.
See the leaf's own docstring — the repair is a hoist, not a proof.

**SECOND CORRECTION.**  The survey says the local criterion of flatness (the
`Tor₁` statement) is missing and therefore blocking.  Missing, yes; blocking,
no — for MODULE-FINITE base changes `Module.free_quotSMulTop_iff_free`
(`Mathlib/RingTheory/Regular/Free.lean`) already IS the induction step, with no
`Tor` in its proof.  The one genuinely missing piece of commutative algebra
under this node is "a system of parameters of a regular local ring is a
regular sequence" (regular ⟹ Cohen–Macaulay).  The ring leaf's docstring
writes out the four-step route that consumes it.

**THIRD CORRECTION (2026-07-27, and it partly walks the second one back).**  The
`Module.free_quotSMulTop_iff_free` route is real, but it is a route to a
MODULE-FINITE statement, and `flat_of_isRegularLocalRing_of_ringKrullDim_eq`
carries no finiteness hypothesis and must not — the stalk map of a finite
morphism is not module-finite.  So that route cannot be executed *at that leaf*;
it could only be reached by re-cutting THIS glue to descend to an affine cover
before taking stalks.  The leaf's honest decomposition is the three sub-leaves
listed in its docstring, of which the local criterion of flatness is one.  Two
further facts landed the same day: the fibre-dimension leaf is now PROVEN (the
descent it wanted is mathlib's `Scheme.Hom.quasiFiniteAt`), and the hoist that
closes `isRegularLocalRing_stalk_of_smooth` also closes
`exists_isWeaklyRegular_span_eq_maximalIdeal`.

**Two routes considered and REJECTED for this leaf**, recorded so they are
not re-attempted: the *theorem of the cube* route needs ample line
bundles, absent as above; the *homogeneity/translation* route needs
openness of the flat locus AND generic flatness, both absent, and its
translation layer would have been free-floating since nothing could
consume it. -/
theorem flat_of_finite_fibres_endo {X : Scheme.{u}} {K : CommRingCat.{u}} [Field K]
    (g : X ⟶ Spec K) [Smooth g] [IsProper g] [GeometricallyConnected g]
    (u : X ⟶ X) [IsProper u] (hu : ∀ a : X, (⇑u ⁻¹' {a}).Finite) : Flat u := by
  -- Zariski's main theorem: proper with finite fibres ⟹ FINITE.
  haveI : LocallyQuasiFinite u := LocallyQuasiFinite.of_finite_preimage_singleton u hu
  haveI : IsFinite u := IsFinite.of_isProper_of_locallyQuasiFinite u
  -- Flatness of a morphism is flatness of every stalk map.
  refine AlgebraicGeometry.Flat.of_stalkMap u fun x => ?_
  -- Both stalks are regular local, `X` being smooth over a field.
  haveI := isRegularLocalRing_stalk_of_smooth g x
  haveI := isRegularLocalRing_stalk_of_smooth g (u x)
  -- Matsumura 23.1, with the two dimension inputs supplied by the geometry.
  exact flat_of_isRegularLocalRing_of_ringKrullDim_eq (u.stalkMap x).hom
    (ringKrullDim_stalk_eq_of_isFinite_endo g u x)
    (ringKrullDim_quotient_map_maximalIdeal_stalkMap u x)

/-- **The fibrewise criterion of flatness** (PROVEN 2026-07-27 over the
single pointwise leaf `flat_stalkMap_of_flat_stalkMap_fiberMapOver` above
— general scheme theory, NO abelian varieties: EGA IV 11.3.10, *critère
de platitude par fibres*; Stacks 039E; Matsumura *Commutative Ring
Theory* §23 for the local-algebra form).
Let `u : X ⟶ Y` be a morphism over a base `S`, with both `X` and `Y`
flat and locally of finite presentation over `S`.  If the induced map on
the fibre over every point of `S` is flat, then `u` is flat.

**This is the exact statement being asked for.**  The full criterion is
an "iff at a point": with `Y` flat over `S` at `y = u x`, `u` is flat at
`x` **iff** `X` is flat over `S` at `x` and `u_s` is flat at `x`.  Only
the `⟸` direction, globalized over all points, is stated here — a
strictly weaker statement, so it cannot be false, and it is the whole of
what the abelian-scheme application needs.

**Why it is a separate leaf.**  It is the step that moves the problem
from an arbitrary base to a field, and it has no group-scheme content
whatsoever.  Whoever proves it proves a general theorem, and the
abelian-variety work in `flat_fiberMap_mulByNat` then happens over
`κ(s)`, where a smooth scheme really is regular.

**HOW IT IS PROVEN, and why the cut is where it is.**  Flatness of a
morphism is flatness of every stalk map
(`AlgebraicGeometry.Flat.of_stalkMap`), so the global statement follows
from the statement AT A POINT.  At `x : X` the fibre hypothesis is
consumed at exactly ONE fibre, `p.fiber (p x)`, and at exactly one point
of it, `Scheme.Hom.asFiber p x` — flatness of that fibre morphism gives
flatness of its stalk map there (`AlgebraicGeometry.Flat.stalkMap`).
Nothing is lost: Stacks 039C, the theorem the literature actually proves,
IS pointwise, and 039E is its global specialization.  All the remaining
mathematics is in
`flat_stalkMap_of_flat_stalkMap_fiberMapOver`, whose docstring carries
the route survey and the refuting greps.

**Checked against the source 2026-07-27: Stacks 039E does NOT require `Y`
flat over `S`** — its hypotheses are `X` locally of finite presentation
over `S`, `X` flat over `S`, `f_s` flat for every `s`, and `Y` locally of
finite **type** over `S`; flatness of `Y` over `S` is part of the
*conclusion*.  So the `[Flat q]` and `[LocallyOfFinitePresentation u]`
instances here are redundant, and the pointwise leaf drops them.  They
are harmless: extra hypotheses only weaken this statement, and the
consumer `flat_mulByNat` supplies them anyway.

**What the pin gives a prover, checked 2026-07-26** (this corrects the
survey that used to stand in `flat_mulByNat`'s docstring, which said
mathlib had "no notion of the dimension of a scheme" and that miracle
flatness had to be built from nothing — the RING-level half of that is
false):

* PRESENT.  `ringKrullDim` (`RingTheory/KrullDimension/Basic.lean`),
  `Module.supportDim` and `topologicalKrullDim`
  (`Topology/KrullDimension.lean`), `Ideal.height` / `Ideal.primeHeight`
  and `FiniteRingKrullDim` (`RingTheory/Ideal/Height.lean`), and — the
  induction step of miracle flatness itself — the dimension-drop lemmas
  `ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors`
  (Stacks 00KW) and `supportDim_le_supportDim_quotSMulTop_succ`
  (Stacks 0B52) in `RingTheory/KrullDimension/Regular.lean`.  Also
  `IsRegularLocalRing` / `IsRegularRing`
  (`RingTheory/RegularLocalRing/Defs.lean`), the regular-sequence theory
  `IsWeaklyRegular` / `IsRegular` (`RingTheory/Regular/RegularSequence.lean`,
  `RingTheory/Regular/Flat.lean`), `Module.free_of_flat_of_isLocalRing`
  (`RingTheory/LocalRing/Module.lean`), and, at scheme level,
  `Flat.iff_flat_stalkMap`, stability of `Flat` under base change and
  composition, and `Scheme.Hom.fiber` (`AlgebraicGeometry/Fiber.lean`).
* ABSENT.  **Cohen–Macaulay and depth** — `grep CohenMacaulay` over
  mathlib returns nothing at all, and `RingTheory/Regular/Depth.lean` is
  a 10-line stub with no declarations.  Also absent: the **local
  criterion of flatness** (the `Tor₁` statement), **generic flatness**,
  **openness of the flat locus**, and this criterion itself.  `~/cs/FLT`
  has none of it either (checked 2026-07-26: no `AbelianVariety`, no
  cube, no `CohenMacaulay`), so there is nothing to vendor.

To refute this survey, `grep -rn CohenMacaulay` and
`grep -rln "generic.*[Ff]lat\|flatLocus"` over `.lake/packages/mathlib`;
a hit on either means the note has gone stale. -/
theorem flat_of_flat_fiberMap {X Y S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    (u : X ⟶ Y) (h : u ≫ q = p) [Flat p] [Flat q]
    [LocallyOfFinitePresentation p] [LocallyOfFinitePresentation q]
    [LocallyOfFinitePresentation u]
    (H : ∀ s : S, Flat (fiberMapOver u h s)) : Flat u := by
  refine Flat.of_stalkMap u fun x => ?_
  haveI := H (p x)
  exact flat_stalkMap_of_flat_stalkMap_fiberMapOver u h x (Flat.stalkMap p x)
    (Flat.stalkMap (fiberMapOver u h (p x)) (p.asFiber x))

/-! **`flat_fiberMap_mulByNat` and `flat_mulByNat` used to stand here.**
They moved DOWN, below `finite_preimage_mulByNat` (2026-07-27), because
`flat_fiberMap_mulByNat` is now PROVEN over the theorem-of-the-cube leaf
`finite_preimage_mulByNat_of_field`, which is declared below this point.
Moving the two consumers down was preferred to hoisting that leaf up: the
leaf had a live owner at the time, and relocating a declaration out from
under the agent proving it is how this fleet manufactures merge
conflicts.  Nothing else changed, and `flat_mulByNat` is byte-identical
to its previous form.
-/

/-- **Finite point-fibres COMPOSE**: if every point-fibre of `g` and every
point-fibre of `h` is finite, then so is every point-fibre of `g ≫ h`.

Pure set theory over `Scheme.Hom.comp_apply`: `(g ≫ h) ⁻¹' {c}` is contained
in `⋃ b ∈ h ⁻¹' {c}, g ⁻¹' {b}`, a finite union of finite sets.  Stated for
arbitrary schemes because it is used to split `[n]` along a factorization
`n = p · c` (`mulByNat_mul`), which is what reduces the abelian-variety leaf
below to its two genuinely different cases. -/
theorem finite_preimage_comp {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    (hg : ∀ b : Y, (⇑g ⁻¹' {b}).Finite) (hh : ∀ c : Z, (⇑h ⁻¹' {c}).Finite)
    (c : Z) : (⇑(g ≫ h) ⁻¹' {c}).Finite := by
  refine ((hh c).biUnion (fun b _ => hg b)).subset ?_
  intro x hx
  refine Set.mem_biUnion (show g x ∈ ⇑h ⁻¹' {c} from ?_) (show x ∈ ⇑g ⁻¹' {g x} from rfl)
  show h (g x) = c
  rw [← Scheme.Hom.comp_apply]
  exact hx

/-- **`[n]` has finite fibres when `n` is invertible in the base field**
(sorry leaf — the Lie algebra of a smooth group scheme).

One half of the old `finite_preimage_mulByNat_of_field`, split out
2026-07-27.  Since `K` is a field, `(n : K) ≠ 0` says exactly that `n` is
prime to the characteristic.

**THE ROUTE, AND IT DOES NOT GO THROUGH THE THEOREM OF THE CUBE.**  `[n]`
is FORMALLY UNRAMIFIED, and formally unramified plus locally of finite type
is quasi-finite.  Unramifiedness is immediate from the functor of points,
with no line bundles anywhere: let `T ↪ T'` be a square-zero thickening and
`h₁ h₂ : T' ⟶ A` two lifts with `h₁ ≫ [n] = h₂ ≫ [n]` that agree on `T`.
By `nsmul_val` that says `n • h₁ = n • h₂` in the group `RelPoint f (T' ⟶ S)`,
i.e. `n • (h₁ - h₂) = 0`, and `h₁ - h₂` lies in the kernel of
`RelPoint f (T' ⟶ S) → RelPoint f (T ⟶ S)`.  For a SMOOTH group scheme that
kernel is a module over `Γ(T, 𝒪_T)`, which is a `K`-algebra; so `n` acts
invertibly on it as soon as `(n : K) ≠ 0`, forcing `h₁ = h₂`.  This is the
classical "`d[n] = n · id` on the Lie algebra", and it is exactly why the
prime-to-characteristic case is cheap while the characteristic case
(`finite_preimage_mulByNat_of_field_char`) is not: there `d[p] = 0`.

**What IS present at this pin** (each claim refutable by one grep).
`AlgebraicGeometry.FormallyUnramified`
(`Mathlib/AlgebraicGeometry/Morphisms/FormallyUnramified.lean:54`),
`LocallyQuasiFinite` (`Morphisms/QuasiFinite.lean:71`) with
`locallyQuasiFinite_iff_finite_preimage_singleton`, and — for spreading
quasi-finiteness at the origin over all of `A` — `Scheme.Hom.quasiFiniteLocus`
and `Scheme.Hom.isOpen_quasiFiniteAt`
(`Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean:314`, `:290`), which say
the quasi-finite locus is OPEN.  Mathlib has also STARTED abelian varieties:
`Mathlib/AlgebraicGeometry/Group/{Abelian,Smooth}.lean` exist and carry
`isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed` and
`smooth_of_grpObj`.  Re-check that directory at every pin bump.

**What is MISSING — these are the two obligations, and neither is the cube.**
1. The `Γ(T, 𝒪_T)`-module structure on the kernel above, i.e. the Lie algebra
   / tangent space of a smooth group scheme.  Mathlib has NO scheme tangent
   space at all: `grep -rni "tangentSpace\|DualNumber"
   Mathlib/AlgebraicGeometry/` returns NOTHING.
2. `FormallyUnramified f → LocallyOfFiniteType f → LocallyQuasiFinite f`.
   Absent: `grep -rn "Unramified"
   Mathlib/AlgebraicGeometry/Morphisms/QuasiFinite.lean` returns NOTHING.
   The pieces are present (`FormallyUnramified.stalkMap` and the
   residue-field separability instance at `Morphisms/FormallyUnramified.lean:149`
   and `:156`), so this is ordinary scheme theory, not missing theory.

References: Mumford *Abelian Varieties* §6; Milne *Abelian Varieties* I.7. -/
theorem finite_preimage_mulByNat_of_field_prime_to_char {X : Scheme.{u}}
    (K : CommRingCat.{u}) [Field K] {fK : X ⟶ Spec K} (ab : AbelianSchemeStruct fK)
    (n : ℕ) (hn : (n : K) ≠ 0) (a : X) : (⇑(ab.mulByNat n) ⁻¹' {a}).Finite :=
  sorry

/-- **`[p]` has finite fibres in characteristic `p`** (sorry leaf — the
theorem of the cube; this is the irreducible residue).

The other half of the old `finite_preimage_mulByNat_of_field`, split out
2026-07-27, and the ONLY place in this file where ample line bundles are
genuinely needed.

**Why the cheap route dies here.**  The Lie-algebra argument that proves
`finite_preimage_mulByNat_of_field_prime_to_char` computes `d[n] = n · id`;
at `n = p = ringChar K` that is ZERO, so `[p]` is not unramified and the
argument says nothing.  `[p]` really is inseparable — its kernel contains
`ker F` for the relative Frobenius `F`, an infinitesimal group scheme — so
this is a limitation of the mathematics, not of the write-up.

**What a prover has to supply.**  Fibrewise this is "`ker[p]` is a finite
group scheme", classically "`[p]` is an isogeny", of degree `p^{2g}`.  Two
classical proofs, both blocked at this pin:

* Mumford *Abelian Varieties* §6, Application 2 of the theorem of the cube:
  take a symmetric ample `L`, use `[p]^* L ≅ L^{p²}`, again ample for
  `p ≠ 0`, and conclude that a morphism pulling an ample bundle back to an
  ample bundle is quasi-finite.
* `[p] = V ∘ F`, with `F` the relative Frobenius (finite, and a
  homeomorphism on underlying spaces) and `V` the Verschiebung.  `V` is
  constructed by duality, so this route needs `Pic⁰` and the dual abelian
  variety.

**MISSING MACHINERY at this pin, each claim refutable by one grep.**
`grep -rl Ample Mathlib/AlgebraicGeometry/` returns NOTHING: there are no
ample line bundles (the only `Ample` in mathlib is
`Analysis/Convex/AmpleSet.lean`), no Picard scheme or functor
(`grep -rli picard Mathlib/AlgebraicGeometry/` is empty — the only `Picard`
in mathlib is `RingTheory/PicardGroup.lean`, which is about modules), and no
theorem of the cube.  There is also no Cohen–Macaulay theory
(`grep -rl CohenMacaulay Mathlib/` is empty), which is what blocks the
miracle-flatness route used by the sibling `flat_mulByNat`.  The claim that
mathlib has "no notion of the dimension of a scheme" is STALE in one
respect: `topologicalKrullDim` applies to a scheme's space and
`Mathlib/AlgebraicGeometry/Artinian.lean` carries
`IsLocallyArtinian.of_topologicalKrullDim_le_zero`, so "`ker[p]` is
zero-dimensional" IS expressible; what is missing is any way to PROVE it.

**`hchar` is deliberately carried even though the statement is true without
it** — `[p]` has finite fibres for every `p` — because without it this leaf
would silently duplicate `finite_preimage_mulByNat_of_field_prime_to_char`.
Carrying it records that this leaf is exactly the residue the Lie-algebra
route cannot reach, and makes the leaf VACUOUS in characteristic zero. -/
theorem finite_preimage_mulByNat_of_field_char {X : Scheme.{u}}
    (K : CommRingCat.{u}) [Field K] {fK : X ⟶ Spec K} (ab : AbelianSchemeStruct fK)
    (p : ℕ) (hp : p.Prime) (hchar : ringChar K = p) (a : X) :
    (⇑(ab.mulByNat p) ⁻¹' {a}).Finite :=
  sorry

/-- **The fibres of `[n]` on an abelian VARIETY are FINITE** (PROVEN
2026-07-27 over the two leaves just above).

This is the SECOND cube input, and it is the one the torsion CARDINALITY
arguments need.  It says exactly that `ker[n]` is a finite group scheme:
the fibre of `[n]` over a point `a` is a torsor under the kernel taken in
the fibre of `f` through `a`, so all the fibres are finite as soon as one
of them is.

**Why it is stated on point-set fibres rather than as `LocallyQuasiFinite`.**
Its consumer, `locallyQuasiFinite_mulByNat` in `Modularity/TateModule.lean`,
used to BE the leaf.  But `LocallyQuasiFinite` is (locally of finite type)
+ (quasi-finite fibres), and the first half is already free here
(`locallyOfFiniteType_mulByNat`), so the old leaf was redundantly asking a
prover for something already proven.  Mathlib's
`LocallyQuasiFinite.of_finite_preimage_singleton` needs only
`[LocallyOfFiniteType]` plus this statement, so this is the exact residue.

**Independent of `flat_mulByNat`.**  Neither leaf implies the other at this
pin: flatness would follow from finite fibres only via miracle flatness
(absent — mathlib has NO Cohen–Macaulay or depth theory at all, though it
does have `ringKrullDim` and the dimension-drop lemmas; see the survey in
`flat_of_flat_fiberMap` above), and finite fibres
do not follow from flatness at all (`f` itself is flat with positive
dimensional fibres).  Both are outputs of the theorem of the cube, and a
prover who has the cube discharges both at once.

**THE BASE IS A FIELD** (2026-07-26).  This is the residue of
`finite_preimage_mulByNat` after base change to the residue field of a
point, so it is a statement about an abelian VARIETY over `K` — the setting
of every textbook treatment — rather than about an abelian scheme over an
arbitrary base.  Nothing else was removed: the reduction below is formal.

**THE SPLIT (2026-07-27), replacing the previous "atomic at this pin"
verdict.**  This is no longer a leaf.  It is proven by strong induction on
`n` over the two leaves above, which are genuinely different mathematical
problems and want different provers.  Writing `p = ringChar K`, the step is:

* `(n : K) ≠ 0` — pass to `finite_preimage_mulByNat_of_field_prime_to_char`;
* `(n : K) = 0` — then `p ≠ 0` (else `K` has characteristic zero and `n = 0`),
  so `p` is prime and `p ∣ n`, say `n = p · c` with `c ≠ 0` and `c < n`.
  `mulByNat_mul` gives `[p · c] = [c] ≫ [p]`, and `finite_preimage_comp`
  combines the induction hypothesis at `c` with
  `finite_preimage_mulByNat_of_field_char` at `p`.

The old docstring said "closing it means building ample line bundles and the
theorem of the cube".  That is now known to be true of ONLY ONE of the two
halves.  The prime-to-characteristic half has a completely different and much
cheaper classical proof (the Lie algebra — see its docstring), needing no line
bundles, no `Pic` and no cube; the ample/cube machinery is confined to
`finite_preimage_mulByNat_of_field_char`.

**A caution about the characteristic-zero reading.**
`finite_preimage_mulByNat_of_field_char` is VACUOUS over a field of
characteristic zero, since `ringChar K = p` with `p` prime is then
unsatisfiable — so over such a base this statement rests on the first leaf
alone.  That does NOT retire the second leaf for this development: the
consumer `finite_preimage_mulByNat` applies this theorem to
`S.residueField (f a)`, whose characteristic is positive at the finite
places, which is precisely where the Frey curve's torsion is studied. -/
theorem finite_preimage_mulByNat_of_field {X : Scheme.{u}} (K : CommRingCat.{u}) [Field K]
    {fK : X ⟶ Spec K} (ab : AbelianSchemeStruct fK) (n : ℕ) (hn : n ≠ 0)
    (a : X) : (⇑(ab.mulByNat n) ⁻¹' {a}).Finite := by
  haveI : CharP K (ringChar K) := ringChar.charP K
  suffices h : ∀ (m : ℕ), m ≠ 0 → ∀ (b : X), (⇑(ab.mulByNat m) ⁻¹' {b}).Finite from h n hn a
  clear hn a
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm b
    by_cases hmK : ((m : ℕ) : K) = 0
    · have hp0 : ringChar K ≠ 0 := by
        intro h0
        haveI : CharP K 0 := h0 ▸ (inferInstance : CharP K (ringChar K))
        haveI : CharZero K := CharP.charP_to_charZero K
        exact hm (Nat.cast_eq_zero.mp hmK)
      have hp : (ringChar K).Prime :=
        (CharP.char_is_prime_or_zero K (ringChar K)).resolve_right hp0
      obtain ⟨c, rfl⟩ : ringChar K ∣ m := (CharP.cast_eq_zero_iff K _ m).mp hmK
      have hc0 : c ≠ 0 := by rintro rfl; exact hm (Nat.mul_zero _)
      have hclt : c < ringChar K * c := by
        have h1 : 1 * c < ringChar K * c :=
          (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero hc0)).mpr hp.one_lt
        rwa [one_mul] at h1
      rw [ab.mulByNat_mul]
      exact finite_preimage_comp _ _ (ih c hclt hc0)
        (finite_preimage_mulByNat_of_field_char K ab _ hp rfl) b
    · exact finite_preimage_mulByNat_of_field_prime_to_char K ab _ hmK b

open _root_.CategoryTheory.Limits in
/-- **The fibres of `[n]` are FINITE** (PROVEN 2026-07-26 over the
field-base leaf `finite_preimage_mulByNat_of_field`).

Statement unchanged — its consumer `locallyQuasiFinite_mulByNat` in
`Modularity/TateModule.lean` resolves exactly as before.

**The reduction.**  Every point of `[n] ⁻¹' {a}` lies in the fibre of `f`
through `a`, because `[n] ≫ f = f`.  That fibre is
`f.fiber (f a) = A ×_S Spec κ(f a)`, which by
`AbelianSchemeStruct.baseChange` is again an abelian scheme — now over a
FIELD — and by `AbelianSchemeStruct.baseChange_mulByNat` its `[n]` is the
restriction of `[n]` along the immersion `f.fiberι (f a)`.  So

  `[n] ⁻¹' {a} = f.fiberι (f a) '' ([n]_{fibre} ⁻¹' {a as a point of the fibre})`,

and the right-hand side is the image of a finite set.  `Scheme.Hom.asFiber`
supplies `a` as a point of its own fibre and `Scheme.Hom.range_fiberι`
identifies the range of the immersion with `f ⁻¹' {f a}`.

No abelian-variety input is used here: `hn` is passed straight through to
the field-base leaf. -/
theorem finite_preimage_mulByNat (ab : AbelianSchemeStruct f) (n : ℕ) (hn : n ≠ 0)
    (a : A) : (⇑(ab.mulByNat n) ⁻¹' {a}).Finite := by
  have hinj : Function.Injective (f.fiberι (f a)) := (f.fiberι (f a)).isEmbedding.injective
  have hcomm : ∀ x : ↥(pullback f (S.fromSpecResidueField (f a)) : Scheme.{u}),
      pullback.fst f (S.fromSpecResidueField (f a))
          ((ab.baseChange (S.fromSpecResidueField (f a))).mulByNat n x)
        = ab.mulByNat n (pullback.fst f (S.fromSpecResidueField (f a)) x) := by
    intro x
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ab.baseChange_mulByNat]
  have hfin := finite_preimage_mulByNat_of_field (S.residueField (f a))
      (ab.baseChange (S.fromSpecResidueField (f a))) n hn (f.asFiber a)
  refine (hfin.image (f.fiberι (f a))).subset ?_
  rintro x (hx : ab.mulByNat n x = a)
  have hfx : f x = f a := by
    have hcm : (ab.mulByNat n ≫ f).base x = f.base x := by rw [ab.mulByNat_comp]
    simpa [hx] using hcm.symm
  obtain ⟨x₀, hx₀⟩ : x ∈ Set.range (f.fiberι (f a)) := by
    rw [Scheme.Hom.range_fiberι]; exact hfx
  refine ⟨x₀, ?_, hx₀⟩
  show (ab.baseChange (S.fromSpecResidueField (f a))).mulByNat n x₀ = f.asFiber a
  apply hinj
  have e1 : f.fiberι (f a) ((ab.baseChange (S.fromSpecResidueField (f a))).mulByNat n x₀)
      = ab.mulByNat n (f.fiberι (f a) x₀) := hcomm x₀
  rw [e1, hx₀, hx, Scheme.Hom.fiberι_asFiber]

/-- **`[n]` is FLAT on an abelian scheme OVER A FIELD** (PROVEN
2026-07-27 over two leaves, with no residue).

This is the whole of the abelian-variety flatness statement, in the only
setting where the classical proof applies: the base is `Spec K` for a
field `K`, so `ab.smooth` really does make `X` regular — which is exactly
what fails over the arbitrary base `S` of `f`.

**The proof.**  `ab.proper`, `ab.smooth` and `ab.connected` are precisely
the three hypotheses that `flat_of_finite_fibres_endo` asks of the
structure morphism `fK`.  Properness of `[n]` itself is FREE
(`isProper_mulByNat`, via `IsProper.of_comp` applied to `[n] ≫ fK = fK`),
and finiteness of the fibres of `[n]` is exactly
`finite_preimage_mulByNat_of_field`.  So the two leaves meet with nothing
left over, and `hn` is passed straight through to the cube leaf — this
assembly introduces no hypothesis of its own and no mathematics of its
own.

**Where the content went.**  All abelian-variety input is in
`finite_preimage_mulByNat_of_field` (the theorem of the cube); all
commutative algebra is in `flat_of_finite_fibres_endo` (miracle
flatness).  Since 2026-07-27 the cube leaf is therefore the ONLY leaf in
the divisibility chain carrying abelian-variety content — it used to be
needed twice over, once here and once for the torsion cardinality
arguments.

`hn : n ≠ 0` is load-bearing downstream rather than here; see the
discussion in `flat_mulByNat` below. -/
theorem flat_mulByNat_of_field {X : Scheme.{u}} (K : CommRingCat.{u}) [Field K]
    {fK : X ⟶ Spec K} (ab : AbelianSchemeStruct fK) (n : ℕ) (hn : n ≠ 0) :
    Flat (ab.mulByNat n) :=
  haveI := ab.smooth
  haveI := ab.proper
  haveI := ab.connected
  haveI := ab.isProper_mulByNat n
  flat_of_finite_fibres_endo fK (ab.mulByNat n)
    (finite_preimage_mulByNat_of_field K ab n hn)

/-- **`[p]` is FLAT ON EVERY FIBRE, for `p` prime** (PROVEN 2026-07-27;
abelian varieties — Mumford *Abelian Varieties* §6 (Application 2 of the
theorem of the cube) and §18, Milne *Abelian Varieties* I.7, Silverman
*AEC* III.6).

This is the abelian-variety half of the old `flat_mulByNat`, and the
point of the cut is that it is a statement **over a field**: the fibre
`f.fiber s` is an abelian variety over the residue field `κ(s)`, and
`fiberMapOver (ab.mulByNat p) _ s` is `[p]` on it.

**THE OLD DOCSTRING'S CLOSING NOTE WAS STALE, AND IT WAS THE WHOLE
OBSTACLE** (corrected 2026-07-27).  It read: "the fibre carries an
abelian-variety structure, but this module does not hand you one:
`AbelianSchemeStruct` is not currently known to base-change", and it
named constructing that structure as the natural first step.
**`AbelianSchemeStruct.baseChange` has existed in this very module since
2026-07-26**, together with `AbelianSchemeStruct.baseChange_mulByNat`,
which says precisely that `[n]` commutes with the projection; the sibling
`finite_preimage_mulByNat` was already proven by exactly that route.
Refute the note in one grep:
`grep -n "def baseChange" Fermat/FLT/Modularity/AbelianSchemeIsogeny.lean`.

**The proof, in one move.**  `Scheme.Hom.fiber f s` is by definition
`pullback f (S.fromSpecResidueField s)`, so
`ab.baseChange (S.fromSpecResidueField s)` is an `AbelianSchemeStruct` on
`pullback.snd f (S.fromSpecResidueField s)` — an abelian scheme over
`Spec κ(s)`, i.e. an abelian VARIETY.  Its multiplication morphism IS the
fibre map:

  `fiberMapOver [p] _ s = (ab.baseChange (S.fromSpecResidueField s)).mulByNat p`,

which `pullback.hom_ext` reduces to two identities: `baseChange_mulByNat`
after composing with `pullback.fst`, and `mulByNat_comp` for the
base-changed structure after composing with `pullback.snd` (`fiberMapOver`
carries the identity in that slot).  Then `flat_mulByNat_of_field`
applies with `K := S.residueField s`, and `hp.pos.ne'` supplies its
`n ≠ 0`.

**`p.Prime` is unused by this proof, and that is deliberate.**  Only
`p ≠ 0` is needed, since `flat_mulByNat_of_field` holds for every nonzero
`n`.  The hypothesis is kept because the statement is consumed by
`flat_mulByNat`'s reduction to primes, and because — as the old note
observed — a prover attacking the cube directly may want to split on
whether `p` equals the residue characteristic, the case `p ≠ ℓ` being
where `[p]` is étale.  It is a genuine hypothesis of the STATEMENT that
this particular proof happens not to need, not a hidden weakening. -/
theorem flat_fiberMap_mulByNat (ab : AbelianSchemeStruct f) (p : ℕ) (hp : p.Prime)
    (s : S) : Flat (fiberMapOver (ab.mulByNat p) (ab.mulByNat_comp p) s) := by
  have hkey : fiberMapOver (ab.mulByNat p) (ab.mulByNat_comp p) s
      = show (f.fiber s : Scheme.{u}) ⟶ f.fiber s from
          (ab.baseChange (S.fromSpecResidueField s)).mulByNat p := by
    refine Limits.pullback.hom_ext ?_ ?_
    · calc fiberMapOver (ab.mulByNat p) (ab.mulByNat_comp p) s
              ≫ Limits.pullback.fst f (S.fromSpecResidueField s)
          = Limits.pullback.fst f (S.fromSpecResidueField s) ≫ ab.mulByNat p :=
            Limits.pullback.lift_fst _ _ _
        _ = (ab.baseChange (S.fromSpecResidueField s)).mulByNat p
              ≫ Limits.pullback.fst f (S.fromSpecResidueField s) :=
            (ab.baseChange_mulByNat (S.fromSpecResidueField s) p).symm
    · calc fiberMapOver (ab.mulByNat p) (ab.mulByNat_comp p) s
              ≫ Limits.pullback.snd f (S.fromSpecResidueField s)
          = Limits.pullback.snd f (S.fromSpecResidueField s) ≫ 𝟙 _ :=
            Limits.pullback.lift_snd _ _ _
        _ = Limits.pullback.snd f (S.fromSpecResidueField s) := Category.comp_id _
        _ = (ab.baseChange (S.fromSpecResidueField s)).mulByNat p
              ≫ Limits.pullback.snd f (S.fromSpecResidueField s) :=
            ((ab.baseChange (S.fromSpecResidueField s)).mulByNat_comp p).symm
  rw [hkey]
  exact flat_mulByNat_of_field (S.residueField s) (ab.baseChange _) p hp.pos.ne'

/-- **Multiplication by a nonzero `n` on an abelian scheme is FLAT**
(abelian varieties; Mumford *Abelian Varieties* §6 (Application 2 of the
theorem of the cube) and §18, Milne *Abelian Varieties* I.7, Silverman
*AEC* III.6).

**PROVEN 2026-07-26**, over the two leaves above plus `mulByNat_mul`.
It used to be the sorry itself; the abelian-variety content is now in
`flat_fiberMap_mulByNat` and the scheme theory in
`flat_of_flat_fiberMap`.  (Statement and proof unchanged since;
the declaration merely MOVED here on 2026-07-27, below
`finite_preimage_mulByNat_of_field`, so that `flat_fiberMap_mulByNat`
could be proven over it.)

Together with `isProper_mulByNat` and `locallyOfFinitePresentation_mulByNat`
(both free) this says `[n]` is **finite locally free**, of degree `n^{2g}`
on each fibre of `f` — the classical statement that `[n]` is an isogeny.
Only the flatness was ever asked for here, because properness and finite
presentation are already available without any abelian-variety input.

**The proof, in three moves.**

1. *Reduce to primes.*  `[1] = 𝟙` (`mulByNat_one`) is flat, and
   `[p·m] = [m] ≫ [p]` (`mulByNat_mul`), so a strong induction on `n`
   using `Nat.exists_prime_and_dvd` and the fact that `Flat` is stable
   under composition reduces everything to `n` prime.  `hn : n ≠ 0` is
   what makes the induction start: it rules out the one value of `n`
   with no prime factorization to descend along.
2. *Descend to the fibres.*  `f` is smooth, hence flat and locally of
   finite presentation, and `[p]` is locally of finite presentation for
   free (`locallyOfFinitePresentation_mulByNat`).  So
   `flat_of_flat_fiberMap` applies to `[p]` as a morphism over `S`.
3. *The fibre statement* is `flat_fiberMap_mulByNat`.

**`hn` is LOAD-BEARING** — it is a genuine hypothesis, not bookkeeping.
`mulByNat 0 = f ≫ zeroSection` factors through the base, so for relative
dimension `g ≥ 1` it is not flat: its fibre over a point of the zero
section is a whole fibre of `f`, of dimension `g`, while its fibre over
any other point is empty, and flatness would force those to have the
same dimension.

**Relation to the sibling leaf.**  `Modularity/TateModule.lean` carries
`locallyQuasiFinite_mulByNat`, which asks for the QUASI-FINITENESS of the
same morphism and is the same theorem-of-the-cube input; over it that file
derives `IsFinite (mulByNat n)` by Zariski's main theorem.  The two are
deliberately *not* merged: quasi-finiteness is what the torsion
CARDINALITY arguments need, flatness is what DIVISIBILITY needs, and a
prover who has the cube gets both at once.  Neither consumes the other.
(Since 2026-07-27 they share their one leaf,
`finite_preimage_mulByNat_of_field`, so "a prover who has the cube gets
both at once" is now literally true of this file.) -/
theorem flat_mulByNat (ab : AbelianSchemeStruct f) (n : ℕ) (hn : n ≠ 0) :
    Flat (ab.mulByNat n) := by
  haveI := ab.smooth
  haveI : LocallyOfFinitePresentation f := inferInstance
  haveI : Flat f := inferInstance
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases eq_or_ne n 1 with rfl | hn1
    · rw [ab.mulByNat_one]; infer_instance
    · obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hn1
      obtain ⟨m, rfl⟩ := hpd
      have hm0 : m ≠ 0 := by rintro rfl; simp at hn
      have hmlt : m < p * m := by
        have h1 : 1 * m < p * m :=
          (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero hm0)).mpr hp.one_lt
        simpa using h1
      haveI := ih m hmlt hm0
      haveI : LocallyOfFinitePresentation (ab.mulByNat p) :=
        ab.locallyOfFinitePresentation_mulByNat p
      haveI : Flat (ab.mulByNat p) :=
        flat_of_flat_fiberMap (ab.mulByNat p) (ab.mulByNat_comp p)
          (flat_fiberMap_mulByNat ab p hp)
      rw [ab.mulByNat_mul]
      infer_instance

/-- **`[n]` is flat and locally of finite presentation** (PROVEN
2026-07-26 over `flat_mulByNat`; the finite presentation is free).

Retained with its original name and statement so that every existing
consumer resolves unchanged; the abelian-variety content is now entirely
in `flat_mulByNat`. -/
theorem flat_locallyOfFinitePresentation_mulByNat (ab : AbelianSchemeStruct f)
    (n : ℕ) (hn : n ≠ 0) :
    Flat (ab.mulByNat n) ∧ LocallyOfFinitePresentation (ab.mulByNat n) :=
  ⟨flat_mulByNat ab n hn, ab.locallyOfFinitePresentation_mulByNat n⟩

/-- **`[n]` is UNIVERSALLY OPEN** (PROVEN over the leaf): a flat morphism
locally of finite presentation is universally open,
`AlgebraicGeometry.UniversallyOpen.of_flat` (Stacks 01UA). -/
theorem universallyOpen_mulByNat (ab : AbelianSchemeStruct f) (n : ℕ) (hn : n ≠ 0) :
    UniversallyOpen (ab.mulByNat n) := by
  obtain ⟨h1, h2⟩ := flat_locallyOfFinitePresentation_mulByNat ab n hn
  haveI := h1
  haveI := h2
  exact UniversallyOpen.of_flat _

/-- **`[n]` is SURJECTIVE** (PROVEN over the leaf).

The image of `[n]` is OPEN because `[n]` is universally open, and CLOSED
because `[n]` is proper — and properness is free, so the leaf supplies
only the openness.  So the image is a clopen subset of `A`.

`A` itself need not be connected, so the argument is fibrewise: given
`a : A`, the fibre `f ⁻¹' {f a}` is CONNECTED (`ab.connected`, through
`Scheme.Hom.isConnected_preimage_singleton`), and it meets the image
because `[n]` fixes the zero section, whose value at `f a` lies in that
fibre.  A connected set meeting a clopen set is contained in it
(`IsPreconnected.subset_isClopen`), so `a` is in the image.

This is the only use of `ab.connected` in the divisibility chain, and it
cannot be dropped: on a disconnected commutative group scheme — say the
constant group scheme `ℤ/n` over a field — `[n]` is the zero map and is
very far from surjective. -/
theorem surjective_mulByNat (ab : AbelianSchemeStruct f) (n : ℕ) (hn : n ≠ 0) :
    Surjective (ab.mulByNat n) := by
  haveI := ab.proper
  haveI := ab.connected
  haveI := ab.isProper_mulByNat n
  haveI := universallyOpen_mulByNat ab n hn
  have hop : IsOpen (Set.range ⇑(ab.mulByNat n)) :=
    ((ab.mulByNat n).isOpenMap).isOpen_range
  have hcl : IsClosed (Set.range ⇑(ab.mulByNat n)) :=
    ((ab.mulByNat n).isClosedMap).isClosed_range
  refine ⟨fun a => ?_⟩
  have hconn : _root_.IsConnected (⇑f ⁻¹' {f a}) := f.isConnected_preimage_singleton (f a)
  have hz : (ab.mulByNat n) (ab.zeroSection (f a)) = ab.zeroSection (f a) := by
    have h := ab.zeroSection_comp_mulByNat n
    have h2 := congrArg (fun φ : S ⟶ A => φ (f a)) h
    simpa using h2
  have hfz : f (ab.zeroSection (f a)) = f a := by
    have h := ab.zeroSection_comp
    have h2 := congrArg (fun φ : S ⟶ S => φ (f a)) h
    simpa using h2
  have hsub := hconn.isPreconnected.subset_isClopen ⟨hcl, hop⟩
    ⟨ab.zeroSection (f a), hfz, ⟨_, hz⟩⟩
  exact hsub rfl

open _root_.CategoryTheory.Limits in
/-- **A `K`-point lifts along a surjective morphism locally of finite
type, `K` algebraically closed** (PROVEN 2026-07-26).

This is the Nullstellensatz step, and it contains no abelian-variety
input at all — it is general scheme theory and would be at home in
mathlib.

Given `w : Spec K ⟶ Y`, base-change `φ` along `w`.  Surjectivity of `φ`
gives `Set.range (pullback.snd φ w) = w ⁻¹' Set.range φ = univ`
(`Scheme.Pullback.range_snd`), so `pullback.snd` is surjective and in
particular `pullback φ w` is NONEMPTY.  It is locally of finite type over
`Spec K`, and `K` is a field hence a Jacobson ring, so the pullback is a
JACOBSON SPACE and therefore has a closed point
(`nonempty_inter_closedPoints`).  Because `K` is algebraically closed, the
residue field at a closed point of a `K`-scheme locally of finite type is
`K` itself, so that closed point IS a `K`-point
(`AlgebraicGeometry.pointOfClosedPoint`), i.e. a section of
`pullback.snd`.  Composing it with `pullback.fst` and using
`pullback.condition` gives the required factorization.

Note what is NOT needed: no finiteness of `φ`, no flatness, no
properness. -/
theorem exists_comp_eq_of_surjective {X Y : Scheme.{u}} (φ : X ⟶ Y)
    [Surjective φ] [LocallyOfFiniteType φ] {K : Type u} [Field K] [IsAlgClosed K]
    (w : Spec (CommRingCat.of K) ⟶ Y) :
    ∃ u : Spec (CommRingCat.of K) ⟶ X, u ≫ φ = w := by
  haveI hsurj : Surjective (pullback.snd φ w) := by
    refine ⟨?_⟩
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd, range_eq_univ, Set.preimage_univ]
  obtain ⟨q, -⟩ := hsurj.surj (IsLocalRing.closedPoint K)
  haveI : JacobsonSpace ↥(pullback φ w) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd φ w)
  obtain ⟨p, -, hp⟩ := nonempty_inter_closedPoints
    (Z := (Set.univ : Set ↥(pullback φ w))) ⟨q, trivial⟩ isClosed_univ.isLocallyClosed
  refine ⟨pointOfClosedPoint (pullback.snd φ w) p hp ≫ pullback.fst φ w, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc,
    pointOfClosedPoint_comp, Category.id_comp]

/-- **Every `F̄`-point of `A` is `[n]` of another one** (PROVEN over the
single leaf `flat_locallyOfFinitePresentation_mulByNat`).

This is the scheme-level form of divisibility, and it is what
`exists_nsmul_eq_geomFibrePt` consumes.  Note that no compatibility with
the base is imposed on `w` or asserted of `u`: `u ≫ [n] = w` forces
`u ≫ f = w ≫ f` automatically, so the statement is about `A` alone. -/
theorem exists_comp_mulByNat_eq (ab : AbelianSchemeStruct f) (n : ℕ) (hn : n ≠ 0)
    {K : Type u} [Field K] [IsAlgClosed K] (w : Spec (CommRingCat.of K) ⟶ A) :
    ∃ u : Spec (CommRingCat.of K) ⟶ A, u ≫ ab.mulByNat n = w := by
  haveI := surjective_mulByNat ab n hn
  haveI := ab.locallyOfFiniteType_mulByNat n
  exact exists_comp_eq_of_surjective (ab.mulByNat n) w

end MulByNat

end Fermat
