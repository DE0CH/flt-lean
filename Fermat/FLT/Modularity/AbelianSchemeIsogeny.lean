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
  prime.  This is the abelian-variety content, now stated over a field.

`flat_mulByNat` itself is PROVEN over the two, together with
`mulByNat_mul` (which does the reduction from general `n` to primes).
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

/-- **`[p]` is FLAT ON EVERY FIBRE, for `p` prime** (sorry leaf — abelian
varieties; Mumford *Abelian Varieties* §6 (Application 2 of the theorem
of the cube) and §18, Milne *Abelian Varieties* I.7, Silverman *AEC*
III.6).

This is the abelian-variety half of the old `flat_mulByNat`, and the
point of the cut is that it is now a statement **over a field**: the
fibre `f.fiber s` is an abelian variety over the residue field `κ(s)`,
and `fiberMapOver (ab.mulByNat p) _ s` is `[p]` on it.

**The argument, which now actually applies.**  `f.fiber s` is smooth
over `κ(s)` (smoothness is stable under base change), hence REGULAR —
this is the step that is simply false for `A` itself over a general base
`S`, and it is why the fibrewise criterion had to be split off.  Fix a
symmetric ample line bundle `L` on the fibre; the theorem of the cube
gives `[p]^* L ≅ L^{p²}`, again ample for `p ≠ 0`, so `[p]` has finite
fibres, and being also proper it is finite.  A finite morphism between
regular schemes of the same dimension is flat ("miracle flatness",
Matsumura *Commutative Ring Theory* Theorem 23.1).

**`p.Prime` is a convenience, not a restriction.**  The consumer
`flat_mulByNat` derives the statement for every `n ≠ 0` from this one by
multiplicativity (`mulByNat_mul`) and stability of `Flat` under
composition, so a prover only has to handle primes.  Nothing is lost:
a prover holding the cube gets every `n` at once and may ignore `hp`.
The reason to keep the hypothesis is that over a fibre of
characteristic `ℓ` the two cases `p ≠ ℓ` (where `[p]` is étale) and
`p = ℓ` (where it is not) are genuinely different arguments, and this is
the form in which that split can be made.

**MISSING MACHINERY at this pin, restricted to what this leaf needs**
(surveyed 2026-07-26; the general-purpose half of the survey is in
`flat_of_flat_fiberMap` above).  Mathlib has group schemes as `GrpObj`
objects of `Over (Spec K)`
(`Mathlib/AlgebraicGeometry/Group/{Abelian,Smooth}.lean`), but **no**
`AbelianVariety`, no isogeny theory, no `[n]`, no theorem of the cube,
no degree, and no ample line bundles (the only `Ample` in mathlib is
`Analysis/Convex/AmpleSet.lean`, which is about convexity).  Supplying
an isogeny package is what this leaf asks for.

**A note for whoever takes it.**  The fibre carries an abelian-variety
structure, but this module does not hand you one: `AbelianSchemeStruct`
is not currently known to base-change.  Constructing
`AbelianSchemeStruct (f.fiberOverSpecResidueField s)` from `ab` is
therefore the natural first step, and it is pure Yoneda — a relative
point of the fibre over `T ⟶ Spec κ(s)` is, by the universal property of
the pullback, a relative point of `f` over the composite `T ⟶ S`. -/
theorem flat_fiberMap_mulByNat (ab : AbelianSchemeStruct f) (p : ℕ) (hp : p.Prime)
    (s : S) : Flat (fiberMapOver (ab.mulByNat p) (ab.mulByNat_comp p) s) :=
  sorry

/-- **Multiplication by a nonzero `n` on an abelian scheme is FLAT**
(sorry leaf — abelian varieties; Mumford *Abelian Varieties* §6
(Application 2 of the theorem of the cube) and §18, Milne *Abelian
Varieties* I.7, Silverman *AEC* III.6).

**PROVEN 2026-07-26**, over the two leaves above plus `mulByNat_mul`.
It used to be the sorry itself; the abelian-variety content is now in
`flat_fiberMap_mulByNat` and the scheme theory in
`flat_of_flat_fiberMap`.

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
prover who has the cube gets both at once.  Neither consumes the other. -/
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

/-- **The fibres of `[n]` on an abelian VARIETY are FINITE** (sorry leaf —
abelian varieties; same references as `flat_mulByNat`).

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

**What a prover has to supply.**  Fibrewise this is "`ker[n]` is a finite
group scheme", classically the statement that `[n]` is an isogeny, of degree
`n^{2g}`.  The standard proof (Mumford *Abelian Varieties* §6, Application 2
of the theorem of the cube; Milne *Abelian Varieties* I.7) takes a symmetric
ample `L` on `A`, uses `[n]^* L ≅ L^{n²}` — which is again ample for
`n ≠ 0` — and concludes that `[n]` has finite fibres because a morphism
pulling an ample bundle back to an ample bundle is quasi-finite.

**MISSING MACHINERY at this pin, checked 2026-07-26 rather than inherited.**
`grep -rl Ample Mathlib/AlgebraicGeometry/` returns NOTHING: there are no
ample line bundles (the only `Ample` in mathlib is
`Analysis/Convex/AmpleSet.lean`), no `Proj`, no Picard scheme or functor,
and no theorem of the cube.  There is also no Cohen–Macaulay theory
(`grep -rl CohenMacaulay Mathlib/` is empty), which is what blocks the
miracle-flatness route used by the sibling `flat_mulByNat`.  The claim
that mathlib has "no notion of the dimension of a scheme" is however now
STALE in one respect: `topologicalKrullDim` applies to a scheme's space and
`Mathlib/AlgebraicGeometry/Artinian.lean` carries
`IsLocallyArtinian.of_topologicalKrullDim_le_zero`, so "`ker[n]` is
zero-dimensional" IS expressible; what is missing is any way to PROVE it.
Each of these is refuted by a one-line grep if it goes stale.

So this leaf is atomic at this pin: closing it means building ample line
bundles and the theorem of the cube, not finding a lemma. -/
theorem finite_preimage_mulByNat_of_field {X : Scheme.{u}} (K : CommRingCat.{u}) [Field K]
    {fK : X ⟶ Spec K} (ab : AbelianSchemeStruct fK) (n : ℕ) (hn : n ≠ 0)
    (a : X) : (⇑(ab.mulByNat n) ⁻¹' {a}).Finite :=
  sorry

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
