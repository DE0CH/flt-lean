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
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Pullbacks
-- `IsFinite`, `LocallyQuasiFinite` and `IsFinite.of_isProper_of_locallyQuasiFinite`
-- (Zariski's main theorem), for the shearing reduction below.  These add NOTHING to
-- any downstream cone: the module's only consumer, `Modularity/TateModule.lean`,
-- already `public import`s all three (checked 2026-07-27,
-- `grep -rn "import Fermat.FLT.Modularity.AbelianSchemeIsogeny" Fermat/`).
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
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
-- (Those three AlgebraicGeometry modules are already `public import`ed above.)
public import Mathlib.RingTheory.RegularLocalRing.Defs
-- `flat_stalkMap_of_flat_stalkMap_fiberMapOver` and its three-leaf cut.
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.Quotient.Operations

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

/-! ### The pointwise fibre criterion, cut into ring theory + two transports

`flat_stalkMap_of_flat_stalkMap_fiberMapOver` (Stacks 039C) used to be a
single opaque leaf, and its docstring recorded that it **could not honestly
be restated over abstract local rings** because "essentially of finite
presentation" does not exist in the pin.  That inference is the standard
one this fleet's doctrine warns about — *stating* a notion is not *proving*
anything about it.  The notion is a five-line definition
(`EssFinitePresentation` below), and once it is written the leaf decomposes
with **no residue** into

* `flat_of_flat_of_flat_quotientMap` — the ring-level *critère de platitude
  par fibres*, **Stacks 05UV verbatim**, over abstract local rings.  This is
  where all the missing mathematics now lives (Tor, the local criterion,
  and the limit argument);
* `essFinitePresentation_stalkMap` — the stalk of a morphism locally of
  finite presentation is essentially of finite presentation.  The exact
  analogue of mathlib's `AlgebraicGeometry.LocallyOfFiniteType.stalkMap`
  (`Morphisms/FiniteType.lean:99`), which supplies the OTHER finiteness
  hypothesis (`EssFiniteType`) for free;
* `flat_quotientMap_of_flat_stalkMap_fiberMapOver` — "the stalk of the
  fibre is the base change of the stalk", in the flatness form the criterion
  consumes.

**Why 05UV and not 00MP.**  The Noetherian local engine 00MP cannot be used
here: `S` is an arbitrary scheme, so its stalks are arbitrary local rings.
05UV (= Algebra Lemma 10.128.9) is the non-Noetherian local-ring form, and
its hypotheses were checked against the source on 2026-07-27:

> Let `R`, `S`, `S'` be local rings and let `R → S → S'` be local ring
> homomorphisms.  Let `M` be an `S'`-module and `𝔪` the maximal ideal of
> `R`.  Assume (1) `R → S'` is essentially of finite presentation, (2)
> `R → S` is essentially of finite type, (3) `M` is of finite presentation
> over `S'`, (4) `M` is not zero, (5) `M/𝔪M` is a flat `S/𝔪S`-module, (6)
> `M` is a flat `R`-module.  Then `S` is essentially of finite presentation
> and flat over `R` and `M` is a flat `S`-module.

Note (2) is *finite type*, not presentation — that is exactly why this is
the right form to cut along, since `LocallyOfFiniteType.stalkMap` already
delivers it.  Its sibling 00R7 (10.128.8) demands essential finite
presentation on BOTH maps and is therefore the wrong one to reach for.

Instantiating `M = S' = 𝒪_{X,x}`, `S = 𝒪_{Y,y}`, `R = 𝒪_{S,s}` makes (3)
automatic (a ring is finitely presented over itself) and (4) automatic (a
local ring is nontrivial), which is why neither appears below.
-/

/-- **Essentially of finite presentation**, for a ring homomorphism: `φ`
factors as a finitely presented ring map followed by a localization.

This is the exact analogue of mathlib's `Algebra.EssFiniteType` — whose
docstring reads "an `R`-algebra is essentially of finite type if it is the
localization of an algebra of finite type" — with *finite type* replaced by
*finite presentation*, and it is the standard definition (Stacks; EGA IV
1.4).  It is stated for ring homs rather than algebras because that is the
shape the stalk maps come in.

**Why it is not a `Subalgebra`.**  Mathlib's `EssFiniteType` is equivalently
witnessed by a sub*algebra* of the target
(`essFiniteType_iff_exists_subalgebra`), because the image of a finite-type
algebra is again of finite type.  **That equivalence FAILS for finite
presentation** — the image of a finitely presented algebra need not be
finitely presented — so the intermediate ring `T` here genuinely has to be
abstract, and copying the `EssFiniteType` idiom would have produced a
strictly stronger, and hence possibly FALSE, notion.

Belongs in mathlib next to `Algebra.EssFiniteType`; it is declared here only
to avoid a new module.  `grep -rn "EssFinitePresentation"
.lake/packages/mathlib ~/cs/FLT` returned nothing on 2026-07-27. -/
def EssFinitePresentation {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) : Prop :=
  ∃ (T : Type u) (_ : CommRing T) (g : R →+* T) (v : T →+* S) (M : Submonoid T),
    g.FinitePresentation ∧ v.comp g = φ ∧ @IsLocalization T _ M S _ v.toAlgebra

/-- Ideal bookkeeping: `I·B` lands in the contraction of `I·A` along `B → A`.
This exists only to give the fibre hypothesis of
`flat_of_flat_of_flat_quotientMap` a stable, nameable proof term, so that the
statement below elaborates the same way at every use site. -/
theorem map_le_comap_map_comp {R B A : Type u} [CommRing R] [CommRing B] [CommRing A]
    (g : R →+* B) (v : B →+* A) (I : Ideal R) :
    I.map g ≤ (I.map (v.comp g)).comap v := by
  rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap]
  exact Ideal.le_comap_map

/-- **CRITÈRE DE PLATITUDE PAR FIBRES, ring level** (sorry leaf — PURE
COMMUTATIVE ALGEBRA, no schemes, no group schemes: **Stacks 05UV** = Algebra
Lemma 10.128.9, the non-Noetherian local-ring form; Noetherian case Stacks
00MP; Matsumura *Commutative Ring Theory* §23 and EGA IV 11.3.10 for the
classical account).

*Let `R → B → A` be local homomorphisms of local rings, with `R → A`
essentially of finite presentation and `R → B` essentially of finite type.
If `A` is flat over `R` and `A/𝔪_R A` is flat over `B/𝔪_R B`, then `A` is
flat over `B`.*

**FAITHFULNESS — this is 05UV instantiated at `M = S' = A`, with the source
quoted in the section note above.**  Hypotheses (3) `M` of finite
presentation over `S'` and (4) `M ≠ 0` are omitted because at `M = S' = A`
they are theorems, not assumptions: `A` is finitely presented over itself,
and `[IsLocalRing A]` already gives `Nontrivial A`.  The conclusion is
likewise *weaker* than 05UV's, which also asserts that `B` is essentially of
finite presentation and flat over `R`; only `A` flat over `B` is kept,
because only that is consumed.  A weaker conclusion and fewer hypotheses
cannot turn a true statement false, so this leaf is safe in both directions.

**This is where ALL the missing mathematics now is**, and the survey below
is what a prover faces (each claim paired with the grep that refutes it if
it goes stale; all re-run against the pin on 2026-07-27):

* **Tor of modules over a ring is ABSENT.**  `grep -rn "^def Tor" Mathlib/`
  finds only the abstract monoidal `CategoryTheory.Monoidal.Tor` — whose own
  file carries `assert_not_exists ModuleCat.abelian`, i.e. it is
  *deliberately* disconnected from modules — and the group-homology
  `Rep k G` version.  `Mathlib/RingTheory/Flat/CategoryTheory.lean:27`
  carries the literal TODO `- Relate flatness with Tor`.  **`Ext` for
  modules DOES exist** (`HasExt (ModuleCat.{v} R)`), so the asymmetry is
  real and worth knowing: the derived-functor apparatus is present, only the
  `Tor` half is unbuilt.
* **The local criterion of flatness is ABSENT.**  `grep -rin "local
  criterion" Mathlib/` returns nothing.  But note two ingredients that ARE
  present and that a naive survey misses:
  `Module.Flat.iff_rTensor_injective'` (`Flat/Tensor.lean:67`) is exactly
  "`Tor₁(R/I, M) = 0` for every ideal `I`" written without Tor, and
  `Module.free_of_maximalIdeal_rTensor_injective`
  (`LocalRing/Module.lean:248`) is the local criterion itself in the
  finitely-*presented* case: `𝔪 ⊗ M → M` injective plus `FinitePresentation`
  gives `Free`.

**ROUTE AUDIT, 2026-07-27 — a CORRECTION to the sentence that used to end
that bullet.**  It read: "The gap is precisely that a stalk is essentially,
not actually, of finite presentation."  That is **wrong**, and it is wrong in
the direction that sends a prover at a non-existent one-line weakening, so it
is corrected rather than merely qualified.  The check that refutes it is to
read the mathlib statement:

    theorem free_of_maximalIdeal_rTensor_injective [Module.FinitePresentation R M]
        (H : Function.Injective ((𝔪).subtype.rTensor M)) : Module.Free R M

Its hypothesis is `Module.FinitePresentation R M` — finite presentation of a
**module**.  What this leaf has is `EssFinitePresentation` of a ring
**homomorphism** `B →+* A`.  Those are not comparable notions and neither
implies the other: a stalk `A` of a smooth morphism of positive relative
dimension is essentially of finite presentation over `B` as an algebra while
being nowhere near finitely generated as a `B`-module.  So the step from
*finitely* to *essentially* finitely presented is **not** the missing step,
and "weaken `FinitePresentation` to `EssFinitePresentation` in
`free_of_maximalIdeal_rTensor_injective`" is not a task that can be
dispatched — it does not typecheck as a task.

**A second hazard on the same route, flagged rather than asserted.**  Before
cutting this leaf along a local criterion at all, check the criterion's
hypotheses in the NON-Noetherian setting: the classical statement (Matsumura
*Commutative Ring Theory* Thm 22.3; Bourbaki) requires the module to be
*ideally separated*, which Noetherianness supplies for free and which this
leaf's setting — `S` an arbitrary scheme, so `R` an arbitrary local ring —
does not.  A sub-leaf of the shape "`𝔫 ⊗_B A → A` injective ⟹ `A` flat over
`B`", stated with no separatedness hypothesis, is exactly the sort of leaf
that can be FALSE, and a false sub-leaf is worse than the open node it
replaces.  Verify against the source before writing one.  That this is a
real distinction and not pedantry is visible in the Stacks project itself:
05UV is stated separately from the Noetherian 00MP precisely because the
Noetherian engine does not reach it.

**AXIS SEARCHED** (so the next reader knows what this audit did NOT look
at): routes that cut this leaf along ring-theoretic machinery — Tor, the
local criterion of flatness, and Noetherian approximation/spreading out.
All three are absent from the pin, by the greps above and below, re-run
2026-07-27.  Not searched: whether the CONSUMER can be re-cut so that this
ring-level statement is never needed — e.g. whether the abelian-scheme
application always supplies a Noetherian base, in which case the far cheaper
Noetherian form 00MP would suffice and this leaf could be replaced by a
weaker one.  That is a question about `flat_of_flat_fiberMap`'s call sites,
not about commutative algebra, and it is the first thing to check before
anyone commits to building Tor.
* **Spreading out / absolute Noetherian approximation is ABSENT.**
  `grep -rni "noetherian approximation" Mathlib/` returns nothing.
  `AffineTransitionLimit.lean` descends *morphisms* along cofiltered limits
  (`Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation:1230`) but
  not the *property*, so EGA IV 8.8.2 is not available.
* **Cohen–Macaulay, depth, generic flatness, openness of the flat locus are
  ABSENT.**  `grep -rn CohenMacaulay Mathlib/` is empty,
  `RingTheory/Regular/Depth.lean` is a 10-line stub with zero declarations,
  and `grep -rln "flatLocus\|genericFlat" Mathlib/` is empty.
* `~/cs/FLT` has none of it either.

A hit on any of those greps means this note has gone stale and the leaf is
cheaper than it looks. -/
theorem flat_of_flat_of_flat_quotientMap {R B A : Type u}
    [CommRing R] [CommRing B] [CommRing A]
    [IsLocalRing R] [IsLocalRing B] [IsLocalRing A]
    {g : R →+* B} {v : B →+* A} [IsLocalHom g] [IsLocalHom v]
    (hfp : EssFinitePresentation (v.comp g))
    (hft : g.EssFiniteType)
    (hflat : (v.comp g).Flat)
    (hfib : (Ideal.quotientMap ((IsLocalRing.maximalIdeal R).map (v.comp g)) v
        (map_le_comap_map_comp g v (IsLocalRing.maximalIdeal R))).Flat) :
    v.Flat :=
  sorry

/-- **A finitely presented ring map followed by a localization is essentially
of finite presentation.**  This is `EssFinitePresentation` read off its own
definition, with the one piece of friction the definition creates handled
once and for all: the definition demands
`@IsLocalization T _ M S _ v.toAlgebra`, i.e. the localization statement for
the algebra structure *built from* `v`, whereas at a use site the ambient
`Algebra T S` instance is the one in scope.  The two are equal by
`Algebra.algebra_ext` (their `algebraMap`s are literally the same function),
and every construction of an `EssFinitePresentation` below goes through this
lemma rather than repeating that transport. -/
theorem essFinitePresentation_of_isLocalization {R T S : Type u} [CommRing R] [CommRing T]
    [CommRing S] [Algebra T S] (M : Submonoid T) [IsLocalization M S]
    {g : R →+* T} (hg : g.FinitePresentation) :
    EssFinitePresentation ((algebraMap T S).comp g) := by
  refine ⟨T, ‹_›, g, algebraMap T S, M, hg, rfl, ?_⟩
  have h : (algebraMap T S).toAlgebra = ‹Algebra T S› :=
    Algebra.algebra_ext _ _ (fun _ => rfl)
  rw [h]
  infer_instance

/-- **The localization of a finitely presented map is essentially of finite
presentation.**  This is the `EssFinitePresentation` analogue of mathlib's
`RingHom.HoldsForLocalization.isLocalizationMap`, and the proof is that
proof's factorization specialized to a finitely presented `f`:
`IsLocalization.map S' f` factors as the `M`-localized map
`R' → (M.map f)⁻¹S`, which is finitely presented by
`RingHom.finitePresentation_localizationPreserves`, followed by the further
localization `(M.map f)⁻¹S → S'`.

Stating it directly, rather than deriving it from the generic
`isLocalizationMap`, is what lets the whole stalk leaf avoid
`StableUnderComposition` for `EssFinitePresentation` — which is the only one
of the four meta-properties with real content, since a finitely presented
algebra over a localization descends to a finitely presented algebra only
after clearing denominators in the *relations*. -/
theorem essFinitePresentation_isLocalizationMap
    {R S : Type u} [CommRing R] [CommRing S]
    {M : Submonoid R} {T : Submonoid S}
    {R' : Type u} [CommRing R'] [Algebra R R'] [IsLocalization M R']
    (S' : Type u) [CommRing S'] [Algebra S S'] [IsLocalization T S']
    {f : R →+* S} (hy : M ≤ Submonoid.comap f T) (hf : f.FinitePresentation) :
    EssFinitePresentation (IsLocalization.map (S := R') S' f hy) := by
  have hle : Submonoid.map f M ≤ T := by simpa [Submonoid.map_le_iff_le_comap]
  letI : Algebra (Localization (M.map f)) S' :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (M.map f) T hle
  have : IsScalarTower S (Localization (Submonoid.map f M)) S' :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ _
  have : IsLocalization (T.map (algebraMap S (Localization (M.map f)))) S' :=
    IsLocalization.isLocalization_of_submonoid_le _ _ (M.map f) T hle
  have heq : IsLocalization.map (S := R') S' f hy =
      (algebraMap (Localization (M.map f)) S').comp
        (IsLocalization.map (M := M) (T := M.map f) (S := R') (Localization (M.map f)) f
          (M.le_comap_map)) := by
    apply IsLocalization.ringHom_ext M
    ext
    simp [← IsScalarTower.algebraMap_apply]
  rw [heq]
  exact essFinitePresentation_of_isLocalization
    (T.map (algebraMap S (Localization (M.map f))))
    (RingHom.finitePresentation_localizationPreserves f M R' _ hf)

/-- **`EssFinitePresentation` respects isomorphisms.**  Post-composition
transports the witnessing localization along the equivalence
(`IsLocalization.isLocalization_of_algEquiv`); pre-composition is absorbed
into the finitely presented half, using
`RingHom.finitePresentation_respectsIso`. -/
theorem essFinitePresentation_respectsIso :
    RingHom.RespectsIso @EssFinitePresentation := by
  constructor
  · rintro R S T' _ _ _ f e ⟨T₀, _, g, v, M, hg, hv, hloc⟩
    refine ⟨T₀, ‹_›, g, e.toRingHom.comp v, M, hg, by rw [RingHom.comp_assoc, hv], ?_⟩
    letI : Algebra T₀ S := v.toAlgebra
    letI : Algebra T₀ T' := (e.toRingHom.comp v).toAlgebra
    exact IsLocalization.isLocalization_of_algEquiv (S := S) M
      (AlgEquiv.ofRingEquiv (f := e) (fun _ => rfl))
  · rintro R S T' _ _ _ f e ⟨T₀, _, g, v, M, hg, hv, hloc⟩
    exact ⟨T₀, ‹_›, g.comp e.toRingHom, v, M,
      RingHom.finitePresentation_respectsIso.2 g e hg,
      by rw [← RingHom.comp_assoc, hv], hloc⟩

/-- **The stalk of a morphism locally of finite presentation is essentially
of finite presentation** (PROVEN 2026-07-27 — general scheme theory, no
abelian varieties).

This is the exact analogue of mathlib's
`AlgebraicGeometry.LocallyOfFiniteType.stalkMap`
(`Mathlib/AlgebraicGeometry/Morphisms/FiniteType.lean:99`), which proves
`(f.stalkMap x).hom.EssFiniteType` for `f` locally of finite type.  Mathlib
has NO finite-presentation counterpart: `grep -rln stalkMap
Mathlib/AlgebraicGeometry/` does not list
`Morphisms/FinitePresentation.lean`, and that file contains no `stalkMap` at
all.  A hit there refutes this note.

**Why it is true**, and why the route is the same as mathlib's: on affine
opens `f` is a finitely presented `R → S`, and the stalk map is
`R_𝔭 → S_𝔮`.  Now `S ⊗_R R_𝔭` is finitely presented over `R_𝔭` (finite
presentation is stable under base change) and `S_𝔮` is a localization of it,
so the composite is a localization of a finitely presented `R_𝔭`-algebra —
which is `EssFinitePresentation` by definition.

**HOW IT IS PROVEN, and the ONE STALE CLAIM this replaces.**  The route is
`HasRingHomProperty.stalkMap_of_respectsIso`, exactly as for the finite-type
one.  The previous version of this docstring predicted that this would need
**four** closure properties for `EssFinitePresentation` (`respectsIso`,
`stableUnderComposition`, `isStableUnderBaseChange`/`localizationPreserves`,
`holdsForLocalization`), and called `stableUnderComposition` "the only one
with any content".  That was right about the content and wrong about the
requirement: `stalkMap_of_respectsIso` asks only for

* `RespectsIso` of the *target* property — `essFinitePresentation_respectsIso`
  above, which needs no composition lemma at all; and
* the localized-map statement **for a finitely presented `f` only** —
  `essFinitePresentation_isLocalizationMap` above.

`stableUnderComposition` for `EssFinitePresentation` is therefore **not
needed here and is not proven**.  That matters, because it is the one with
the real mathematics in it: a finitely presented algebra over a localization
`M⁻¹T` descends to a finitely presented `T`-algebra only after clearing
denominators in the *relations*, and unlike the finite-type case the
subalgebra idiom is unavailable (see `EssFinitePresentation`'s own
docstring).  Anyone who later wants `EssFinitePresentation` as a genuine
meta-property should expect that lemma to be the whole cost. -/
theorem essFinitePresentation_stalkMap {X Y : Scheme.{u}} (φ : X ⟶ Y)
    [LocallyOfFinitePresentation φ] (x : X) :
    EssFinitePresentation (φ.stalkMap x).hom :=
  HasRingHomProperty.stalkMap_of_respectsIso essFinitePresentation_respectsIso
    (fun _ hf _ _ ↦ essFinitePresentation_isLocalizationMap _ _ hf) ‹_› x

/-- **The stalk of the fibre is the quotient of the stalk, compatibly with
`u`** (sorry leaf — general scheme theory, no abelian varieties: this is the
whole mathematical content of
`flat_quotientMap_of_flat_stalkMap_fiberMapOver` below, which is PROVEN over
it with no residue).

Two canonical identifications
`𝒪_{Y,y} ⧸ 𝔪_s 𝒪_{Y,y} ≅ 𝒪_{Y_s, y_s}` and
`𝒪_{X_s, x_s} ≅ 𝒪_{X,x} ⧸ 𝔪_s 𝒪_{X,x}`, and the square saying they carry the
stalk map of `fiberMapOver u rfl s` to `Ideal.quotientMap`.

**Why the two equivalences point in OPPOSITE directions.**  A `RingEquiv` in
either direction is the same data, and these two are chosen so that the
square composes with no `.symm` anywhere: the conclusion is literally
`quotientMap = eX ∘ stalkMap ∘ eY`.  That is not cosmetic — the `.symm` form
of the same statement cost a full verify cycle in coercion bookkeeping
(`RingEquiv.toRingHom` vs the `RingEquiv` coercion do not simp into each
other inside `RingHom.comp`), and this form makes the consumer a two-line
application of `RingHom.Flat.comp` and `RingHom.Flat.of_bijective`.

**Why the point of `q.fiber s` is written
`fiberMapOver u rfl s ((u ≫ q).asFiber x)` and not `q.asFiber (u x)`.**
Those two points ARE equal — both lie over `u x` and `q.fiberι` is injective
(`Scheme.Hom.fiberHomeo`) — but proving it is a separate obligation, and
`stalkMap` forces the former.  Writing the former keeps this leaf free of
that obligation; a prover who wants the latter should prove the point
equality first and transport.  The statement is faithful either way: the
point named does lie over `u x`, since
`fiberι ≫ fiberMapOver = u ≫ fiberι`.

**A SIMPLIFICATION the old note missed.**  The old text justified "the
further localization is trivial" by `Scheme.Hom.fiberι` being injective on
points.  That is true but is not the reason, and the real reason is much
cheaper: `𝔪_s·𝒪_{X,x} ⊆ 𝔪_x` because `p.stalkMap x` is a LOCAL homomorphism,
so `𝒪_{X,x} ⧸ 𝔪_s 𝒪_{X,x}` is already a local ring and localizing it at its
own maximal ideal does nothing.  No point-set input is needed.

Concretely: `𝒪_{X_s, x_s} = 𝒪_{X,x} ⧸ 𝔪_s 𝒪_{X,x}` and
`𝒪_{Y_s, y_s} = 𝒪_{Y,y} ⧸ 𝔪_s 𝒪_{Y,y}`, compatibly with `u`, so flatness of
the stalk map of `fiberMapOver u h s` at `p.asFiber x` IS flatness of
`𝒪_{Y,y}/𝔪_s 𝒪_{Y,y} → 𝒪_{X,x}/𝔪_s 𝒪_{X,x}`.  The statement is phrased as
that flatness rather than as the isomorphism, so that it plugs straight into
hypothesis (5) of `flat_of_flat_of_flat_quotientMap`.

**Why it is true, and why the special feature matters.**  For a general
fibre product the local ring at a point is a *localization* of a tensor
product of local rings, not the tensor product itself.  Here it is on the
nose, because `Scheme.Hom.fiberι` is injective on points (it is a
homeomorphism onto `p ⁻¹' {s}` — `Scheme.Hom.fiberHomeo`), so the prime of
`𝒪_{X,x} ⊗_{𝒪_{S,s}} κ(s)` corresponding to `x_s` is already its unique
maximal ideal and the further localization is trivial.  Concretely on
affines, with `𝔭 ↔ x` and `𝔯 ↔ s` and `𝔭 ∩ R = 𝔯`, both sides are
`(A/𝔯A)_𝔭`.

**ABSENT from the pin, with the refuting greps** (re-run 2026-07-27):
`grep -n stalk Mathlib/AlgebraicGeometry/Fiber.lean` and the same over
`PullbackCarrier.lean` and `Pullbacks.lean` each return NOTHING, and
`grep -rn "stalkMap_pullback\|pullback_stalk" Mathlib/` is empty.  Mathlib
computes the **residue field** of a point of a fibre product
(`PullbackCarrier.Triplet.tensor`) and the **sections** of one
(the `pushoutSection` block, `Morphisms/Flat.lean:183–509`), but never the
stalk.  A hit on any of those means this leaf is cheap.

**FAITHFULNESS — the intermediate map is PINNED, deliberately.**  An earlier
draft of this leaf took the map `𝒪_{S,s} ⟶ 𝒪_{Y,y}` as an arbitrary
parameter `g` with `g ≫ u.stalkMap x = p.stalkMap x`.  That is **not safe**:
`u.stalkMap x` need not be injective, so `g` is not determined by that
equation, while the conclusion depends on `g` through the ideal `𝔪_s·𝒪_{Y,y}`
— i.e. the leaf would have quantified over data the statement is not
invariant under, and could have been FALSE.  It is therefore stated in the
substituted form `p = u ≫ q`, with the map fixed to `q.stalkMap (u x)`; the
consumer reaches it by `subst h`, which costs nothing. -/
theorem exists_ringEquiv_stalkMap_fiberMapOver
    {X Y S : Scheme.{u}} {q : Y ⟶ S} (u : X ⟶ Y) (x : X) :
    ∃ (eY : (Y.presheaf.stalk (u x) ⧸
              (IsLocalRing.maximalIdeal (S.presheaf.stalk ((u ≫ q) x))).map
                (q.stalkMap (u x)).hom) ≃+*
            ((q.fiber ((u ≫ q) x)).presheaf.stalk
              (fiberMapOver u rfl ((u ≫ q) x) ((u ≫ q).asFiber x))))
      (eX : (((u ≫ q).fiber ((u ≫ q) x)).presheaf.stalk ((u ≫ q).asFiber x)) ≃+*
            (X.presheaf.stalk x ⧸
              (IsLocalRing.maximalIdeal (S.presheaf.stalk ((u ≫ q) x))).map
                ((u.stalkMap x).hom.comp (q.stalkMap (u x)).hom))),
      Ideal.quotientMap
          ((IsLocalRing.maximalIdeal (S.presheaf.stalk ((u ≫ q) x))).map
            ((u.stalkMap x).hom.comp (q.stalkMap (u x)).hom))
          (u.stalkMap x).hom
          (map_le_comap_map_comp (q.stalkMap (u x)).hom (u.stalkMap x).hom
            (IsLocalRing.maximalIdeal (S.presheaf.stalk ((u ≫ q) x))))
        = eX.toRingHom.comp
            (((fiberMapOver u rfl ((u ≫ q) x)).stalkMap ((u ≫ q).asFiber x)).hom.comp
              eY.toRingHom) :=
  sorry

/-- **The stalk of the fibre is the base change of the stalk**, in the
flatness form the fibre criterion consumes (PROVEN 2026-07-27 over
`exists_ringEquiv_stalkMap_fiberMapOver` above, with NO residue — the whole
of what remains open is that one statement).

The statement is phrased as this flatness rather than as the isomorphism, so
that it plugs straight into hypothesis (5) of
`flat_of_flat_of_flat_quotientMap`; the isomorphism itself is the leaf above.

**What this cut buys.**  All the commutative-algebra bookkeeping —
`Ideal.quotientMap`, the ideal inclusion `map_le_comap_map_comp`, and the
transport of `RingHom.Flat` across the two identifications — is discharged
here by `RingHom.Flat.comp` and `RingHom.Flat.of_bijective`, so what remains
open is a statement of pure scheme theory that mentions flatness nowhere.
It is also strictly more reusable than the flatness form: any property of
ring maps that respects isomorphisms transports across the same square.

**FAITHFULNESS — the intermediate map is PINNED, deliberately**, exactly as
recorded on the leaf above: `p` is substituted as `u ≫ q` and the map
`𝒪_{S,s} ⟶ 𝒪_{Y,y}` is fixed to `q.stalkMap (u x)` rather than quantified
over, because `u.stalkMap x` need not be injective and the conclusion
depends on that map through the ideal `𝔪_s·𝒪_{Y,y}`. -/
theorem flat_quotientMap_of_flat_stalkMap_fiberMapOver
    {X Y S : Scheme.{u}} {q : Y ⟶ S} (u : X ⟶ Y) (x : X)
    (hfib : ((fiberMapOver u rfl ((u ≫ q) x)).stalkMap ((u ≫ q).asFiber x)).hom.Flat) :
    (Ideal.quotientMap
        ((IsLocalRing.maximalIdeal (S.presheaf.stalk ((u ≫ q) x))).map
          ((u.stalkMap x).hom.comp (q.stalkMap (u x)).hom))
        (u.stalkMap x).hom
        (map_le_comap_map_comp (q.stalkMap (u x)).hom (u.stalkMap x).hom
          (IsLocalRing.maximalIdeal (S.presheaf.stalk ((u ≫ q) x))))).Flat := by
  obtain ⟨eY, eX, heq⟩ := exists_ringEquiv_stalkMap_fiberMapOver (q := q) u x
  rw [heq]
  exact RingHom.Flat.comp
    (RingHom.Flat.comp (RingHom.Flat.of_bijective eY.bijective) hfib)
    (RingHom.Flat.of_bijective eX.bijective)

/-- **The fibrewise criterion of flatness, AT A POINT** (PROVEN 2026-07-27
over the three leaves above —
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

**HOW IT IS PROVEN, and the TWO STALE CLAIMS this replaces.**  The proof
is `subst h`, then `flat_of_flat_of_flat_quotientMap` — Stacks 05UV over
abstract local rings — fed by the three transports declared above:
`essFinitePresentation_stalkMap` for hypothesis (1),
`LocallyOfFiniteType.stalkMap` (mathlib, FREE) for hypothesis (2), `hp`
for hypothesis (6), and `flat_quotientMap_of_flat_stalkMap_fiberMapOver`
for hypothesis (5).  `subst h` is what lets `p.stalkMap x` factor as
`q.stalkMap (u x) ≫ u.stalkMap x` by `Scheme.Hom.stalkMap_comp` with no
`eqToHom` anywhere.

The previous version of this docstring recorded two reasons the leaf could
NOT be cut further.  **Both were wrong, and both are the same error** —
treating a missing *definition* as a missing *theory*:

1. *"Essentially of finite presentation does not exist, so the honest
   ring-level statement cannot be written down."*  It is a five-line
   definition (`EssFinitePresentation` above), and writing it is what makes
   the cut possible.  Nothing about it has to be *proven* for the cut; the
   proof obligations land on the named leaves instead.
2. *"The natural seam — the stalk of the fibre — is not available, so the
   local algebra cannot even be stated over plain rings."*  The seam does
   not need mathlib's stalk-of-pullback theory to be *stated*; it needs it
   to be *proven*, and that obligation is now
   `flat_quotientMap_of_flat_stalkMap_fiberMapOver`, isolated from the
   commutative algebra it was entangled with.

The old note's positive content survives and has been moved to the leaf it
actually describes: the Tor / local-criterion / spreading-out survey is on
`flat_of_flat_of_flat_quotientMap`, and the stalk-of-pullback survey is on
`flat_quotientMap_of_flat_stalkMap_fiberMapOver`.

**STATUS of the three leaves, 2026-07-27.**  Two of the three are now closed:

* `essFinitePresentation_stalkMap` — **PROVEN**, and its docstring records
  that `stableUnderComposition` for `EssFinitePresentation` turned out not to
  be needed at all.
* `flat_quotientMap_of_flat_stalkMap_fiberMapOver` — **PROVEN** over the
  single new leaf `exists_ringEquiv_stalkMap_fiberMapOver`, which carries all
  of its content and none of its flatness bookkeeping.
* `flat_of_flat_of_flat_quotientMap` — still open, and still where all the
  depth is.

An earlier version of this paragraph carried a "correction" claiming that
mathlib's `Module.free_of_maximalIdeal_rTensor_injective` narrows the gap to
"exactly the step from *finitely* to *essentially* finitely presented".
**That claim is false and has been retracted**; the refutation, which is a
one-line read of the mathlib statement (its hypothesis is finite presentation
of a MODULE, whereas this leaf has essential finite presentation of a ring
HOMOMORPHISM — incomparable notions), is written out in full on
`flat_of_flat_of_flat_quotientMap` itself, together with the axis that audit
searched and the one it did not.

**Route note that remains true and load-bearing**: `S` is an ARBITRARY
scheme, so the Noetherian engine 00MP does not reach this statement.  05UV
is the non-Noetherian local-ring form and is what the cut uses; a plan that
stops at 00MP is still incomplete. -/
theorem flat_stalkMap_of_flat_stalkMap_fiberMapOver
    {X Y S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    (u : X ⟶ Y) (h : u ≫ q = p)
    [LocallyOfFinitePresentation p] [LocallyOfFiniteType q]
    (x : X)
    (hp : (p.stalkMap x).hom.Flat)
    (hfib : ((fiberMapOver u h (p x)).stalkMap (p.asFiber x)).hom.Flat) :
    (u.stalkMap x).hom.Flat := by
  subst h
  have hcomp : (u.stalkMap x).hom.comp (q.stalkMap (u x)).hom = ((u ≫ q).stalkMap x).hom := by
    rw [← CommRingCat.hom_comp, ← Scheme.Hom.stalkMap_comp]
    rfl
  have := q.prop (u x)
  exact flat_of_flat_of_flat_quotientMap (g := (q.stalkMap (u x)).hom)
    (v := (u.stalkMap x).hom)
    (hcomp ▸ essFinitePresentation_stalkMap (u ≫ q) x)
    (LocallyOfFiniteType.stalkMap (f := q) (u x)) (hcomp ▸ hp)
    (flat_quotientMap_of_flat_stalkMap_fiberMapOver u x hfib)

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
with finite fibres", and no leaf has to redo that step. -/

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

/-- **THE FIBRE RING OF A FINITE MORPHISM AT A POINT IS ZERO-DIMENSIONAL**
(sorry leaf — general scheme theory, NO abelian varieties, no smoothness, no
field; true for an arbitrary finite morphism of schemes).

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

**ROUTE.**  Purely affine-local bookkeeping.  Choose an affine open `V ∋ u x`;
`u` finite is affine, so `U = u ⁻¹ᵁ V` is affine, and `B = Γ(U)` is a FINITE
`A = Γ(V)`-module.  With `p ⊆ A` and `q ⊆ B` the primes of `x` and `u x`,
`IsAffineOpen.isLocalization_stalk` identifies the two stalks with `B_q` and
`A_p`, and the fibre ring with `(B ⧸ pB)_q`.  Now `B ⧸ pB` is a finite
`κ(p)`-algebra, so it is artinian, so its localisation is artinian and
`ringKrullDim = 0`.

**A WARNING FOR WHOEVER TAKES THIS LEAF, because it is the trap that decided
the shape of `flat_of_isRegularLocalRing_of_ringKrullDim_eq` below.**  Do NOT
try to prove this by showing the stalk map is module-finite and quoting a
finiteness argument at the level of stalks: **THE STALK MAP OF A FINITE
MORPHISM IS NOT MODULE-FINITE.**  Counterexample: `u : Spec ℤ[i] ⟶ Spec ℤ` is
finite; take `p = (5)`, which splits, and `q` one of the two primes above it.
Then `A_p = ℤ_(5)` and `B_q` is a DVR with fraction field `ℚ(i)`.  If `B_q`
were a finite `A_p`-module it would be integral over `A_p`, hence contained in
the integral closure `ℤ[i]_(5) = B_p`; but `B_q ⊋ B_p`, since it inverts the
elements of the OTHER prime above `5`.  So `B_q` is not finite over `A_p`.
Finiteness survives only BEFORE localising at `q`, which is why the route
above localises last. -/
theorem ringKrullDim_quotient_map_maximalIdeal_stalkMap {X Y : Scheme.{u}}
    (u : X ⟶ Y) [IsFinite u] (x : X) :
    ringKrullDim ((X.presheaf.stalk x) ⧸
      Ideal.map (u.stalkMap x).hom (IsLocalRing.maximalIdeal (Y.presheaf.stalk (u x)))) = 0 :=
  sorry

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

/-- **MIRACLE FLATNESS, RING LEVEL** (sorry leaf — PURE COMMUTATIVE ALGEBRA,
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

**THE ROUTE THAT AVOIDS `Tor` ENTIRELY, and it is worth taking.**  Do not
attack this leaf at the stalks; go back to an affine cover, where finiteness
survives.  For `u` finite and `V ⊆ Y` affine, `U = u ⁻¹ᵁ V` is affine and
`B = Γ(U)` is a FINITE `A = Γ(V)`-module.  Then:

1. `Module.Flat A B` may be checked at the maximal ideals of `A`
   (`Module.flat_of_isLocalized_maximal`, `RingTheory/Flat/Localization.lean`),
   and `B_p := B ⊗_A A_p` is still a FINITE `A_p`-module — the localisation is
   at a prime of `A`, not of `B`, which is precisely what dodges the
   counterexample above.
2. A finite module over a local ring is flat iff free
   (`Module.free_of_flat_of_isLocalRing`).
3. Freeness follows by induction along a regular system of parameters
   `t₁, …, t_d` of `A_p` using `Module.free_quotSMulTop_iff_free` at each step,
   with `IsWeaklyRegular.ndrecWithRing` as the recursor; the base case is
   `𝔪 = ⊥`, i.e. `A_p` a field, where every module is free.
4. The ONLY remaining input is that `t₁, …, t_d` is a `B_p`-regular sequence.
   That is gap (a): `B_p` is Cohen–Macaulay because `B` is regular, and
   `𝔪_p B_p` is `𝔪`-primary because the fibre is finite.

So a prover who first proves "a system of parameters of a regular local ring is
a regular sequence" gets the rest from the pin.  That statement — not `Tor`,
not depth in its full generality, not generic flatness, not openness of the
flat locus (`grep -rln "flatLocus\|genericFlat" Mathlib/` is empty) — is the
one genuinely missing piece of commutative algebra under this node. -/
theorem flat_of_isRegularLocalRing_of_ringKrullDim_eq {R T : Type u} [CommRing R] [CommRing T]
    [IsRegularLocalRing R] [IsRegularLocalRing T] (φ : R →+* T) [IsLocalHom φ]
    (hdim : ringKrullDim T = ringKrullDim R)
    (hfib : ringKrullDim (T ⧸ Ideal.map φ (IsLocalRing.maximalIdeal R)) = 0) :
    φ.Flat :=
  sorry

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
pointwise statement `flat_stalkMap_of_flat_stalkMap_fiberMapOver` above,
itself PROVEN the same day over the three leaves
`flat_of_flat_of_flat_quotientMap` (Stacks 05UV, ring level),
`essFinitePresentation_stalkMap` and
`flat_quotientMap_of_flat_stalkMap_fiberMapOver`
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
IS pointwise, and 039E is its global specialization.  The pointwise
statement is in turn PROVEN, so the remaining mathematics is now in its
three leaves: `flat_of_flat_of_flat_quotientMap` carries the Tor /
local-criterion / spreading-out survey (that is where the depth is),
`essFinitePresentation_stalkMap` is the finite-presentation analogue of a
lemma mathlib already has for finite type, and
`flat_quotientMap_of_flat_stalkMap_fiberMapOver` carries the
stalk-of-pullback survey.  Each docstring carries its own refuting greps.

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

/-! ### `[n]` is UNRAMIFIED when `n` is prime to the characteristic

The four declarations below carry the whole of
`finite_preimage_mulByNat_of_field_prime_to_char` except one leaf.  Three
of them are general scheme theory with no abelian-variety content at all;
the fourth (`eq_zero_of_nsmul_eq_zero_of_squareZero`) is the single
genuinely missing input, the Lie algebra of a smooth group scheme. -/

namespace AbelianSchemeStruct

/-- **Precomposition of relative points is SUBTRACTIVE** (PROVEN 2026-07-27).

`RelPoint.pre` preserves `+` and `0` by the structure's own naturality
axioms `pre_add` and `pre_zero`; the inversion step is proven inline from
`neg_add` and cancellation.

**Why inline rather than by reusing `AbelianSchemeStruct.pre_neg`.**  That
lemma exists — `Fermat/FLT/ModularCurve/X0.lean:1352`, same namespace, same
statement — but in a SIBLING module which is not in this import cone (X0
imports `Modularity/AbelianScheme`, not this file).  Re-declaring
`Fermat.AbelianSchemeStruct.pre_neg` here would give two declarations of one
name and break any module that ever imports both, so the two lines are
duplicated instead of the name.  If the two modules are ever merged into one
cone, delete this `have` and use `ab.pre_neg`.

Used once, in `formallyUnramified_mulByNat`, to turn "two points agree
modulo a square-zero ideal" into "their difference lies in the kernel of the
restriction map". -/
theorem pre_sub (ab : AbelianSchemeStruct f) {T' T : Scheme.{u}} (h : T' ⟶ T)
    {g : T ⟶ S} {g' : T' ⟶ S} (hg : h ≫ g = g') (x y : RelPoint f g) :
    letI := ab.addCommGroup g
    letI := ab.addCommGroup g'
    RelPoint.pre h hg (x - y) = RelPoint.pre h hg x - RelPoint.pre h hg y := by
  letI := ab.addCommGroup g
  letI := ab.addCommGroup g'
  have hneg : RelPoint.pre h hg (-y) = -(RelPoint.pre h hg y) := by
    refine eq_neg_of_add_eq_zero_left ?_
    show ab.add (RelPoint.pre h hg (ab.neg y)) (RelPoint.pre h hg y) = ab.zero g'
    rw [← ab.pre_add h hg]
    show RelPoint.pre h hg (ab.add (ab.neg y) y) = ab.zero g'
    rw [ab.neg_add]
    exact ab.pre_zero h hg
  simp only [sub_eq_add_neg]
  rw [← hneg]
  exact ab.pre_add h hg x (-y)

end AbelianSchemeStruct

/-- **Formally unramified + finite type ⟹ quasi-finite, at RING level**
(PROVEN 2026-07-27, and it is two lines).

**This REFUTES a survey that stood in this file.**  The docstring of
`finite_preimage_mulByNat_of_field_prime_to_char` recorded
`FormallyUnramified f → LocallyOfFiniteType f → LocallyQuasiFinite f` as
ABSENT from the pin, on the strength of
`grep -rn "Unramified" Mathlib/AlgebraicGeometry/Morphisms/QuasiFinite.lean`
returning nothing.  That grep is correct and the conclusion drawn from it is
not: the implication holds at ring level as a mathlib INSTANCE,

    Mathlib/RingTheory/Unramified/LocalStructure.lean:333
    instance (priority := low) [EssFiniteType R S] [FormallyUnramified R S] :
      Algebra.QuasiFinite R S

(located by name 2026-07-27), with `Algebra.EssFiniteType.of_finiteType`
supplying `EssFiniteType` from `FiniteType`.  Only the *scheme-level*
packaging was missing, and that is `locallyQuasiFinite_of_formallyUnramified`
below.  **To refute THIS note in turn**, re-run
`grep -rn "EssFiniteType R S. .FormallyUnramified R S" Mathlib/RingTheory/Unramified/`;
an empty result means the instance has been removed or renamed.

The one non-obvious point is that `RingHom.QuasiFinite` is a `def`, not a
class, so `inferInstance` cannot close the goal directly — the `Algebra`-side
instance has to be produced with the ring types NAMED, which is exactly what
this wrapper does. -/
theorem quasiFinite_of_formallyUnramified_of_finiteType {R S : Type*} [CommRing R] [CommRing S]
    (ψ : R →+* S) (h₁ : ψ.FormallyUnramified) (h₂ : ψ.FiniteType) : ψ.QuasiFinite := by
  algebraize [ψ]
  exact (inferInstance : Algebra.QuasiFinite R S)

/-- **Formally unramified + locally of finite type ⟹ locally quasi-finite**
(PROVEN 2026-07-27).  General scheme theory, no abelian varieties.

Both `FormallyUnramified` and `LocallyOfFiniteType` are
`HasRingHomProperty`s, and so is `LocallyQuasiFinite`; `iff_appLE` turns all
three into statements about the same affine-local maps `Γ(Y, U) ⟶ Γ(X, V)`,
where `quasiFinite_of_formallyUnramified_of_finiteType` applies pointwise.
No Zariski gluing is needed because the three characterisations quantify over
the *same* pairs of affine opens.

This is the piece of `Mathlib/AlgebraicGeometry/Morphisms/QuasiFinite.lean`
that is genuinely absent upstream, and it is a mathlib-facing lemma: it
mentions nothing from this development. -/
theorem locallyQuasiFinite_of_formallyUnramified {X Y : Scheme.{u}} (u : X ⟶ Y)
    [FormallyUnramified u] [LocallyOfFiniteType u] : LocallyQuasiFinite u := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite) (f := u)]
  intro U V e
  exact quasiFinite_of_formallyUnramified_of_finiteType _
    ((HasRingHomProperty.iff_appLE (P := @FormallyUnramified) (f := u)).mp ‹_› U V e)
    ((HasRingHomProperty.iff_appLE (P := @LocallyOfFiniteType) (f := u)).mp ‹_› U V e)

/-- **THE LIE ALGEBRA OF A SMOOTH GROUP SCHEME** (sorry leaf, created
2026-07-27 — the ONE remaining input of
`finite_preimage_mulByNat_of_field_prime_to_char`, and the only thing in
that half of the old cube leaf that mathlib does not already have).

*The infinitesimal kernel of an abelian scheme is torsion free at every `n`
invertible in the base field.*  Concretely: `Spec R₀ ⟶ Spec R` is a
square-zero thickening (`φ` surjective, `ker φ ^ 2 = ⊥`), `d` is an
`R`-point of `A` over the base point `q`, `d` restricts to the identity
element on `Spec R₀`, and `n · d = 0`.  Then `d = 0`.

**WHY IT IS TRUE, and why it needs no line bundles.**  Write `I = ker φ`, so
`I ^ 2 = 0` and `I` is a module over `R₀ = R ⧸ I`.  For any `S`-group scheme
`G` and any square-zero thickening there is a natural isomorphism

    ker (G(R) ⟶ G(R₀))  ≅  Hom_{R₀} (e^* Ω_{G/S} ⊗ R₀, I)

(SGA 3, Exp. II; Mumford *Abelian Varieties* §11; Milne *Abelian Varieties*
I.7) — the "Lie algebra" of `G`, tensored with the ideal.  The right-hand
side is an `R₀`-MODULE, and `R₀` is a `K`-algebra because `q : Spec R ⟶
Spec K` makes `R` one.  Under that isomorphism the group's `ℕ`-action is the
module action of `(n : R₀)`, which is a unit as soon as `(n : K) ≠ 0`.
Hence `n • d = 0` forces `d = 0`.  Nothing in this argument mentions ample
line bundles, `Pic`, or the theorem of the cube.

**IT IS EXACTLY THE `d[n] = n · id` STATEMENT.**  That is why this leaf
closes the prime-to-characteristic half and says nothing about the other
half: at `n = p = ringChar K` the scalar `(n : R₀)` is zero, the argument
gives no information, and `finite_preimage_mulByNat_of_field_char` really
does need the cube.

**WHAT IS MISSING AT THIS PIN** (each claim refutable by one grep, all
re-run 2026-07-27 on this worktree's `.lake/packages/mathlib`).

* A scheme-level tangent space or Lie algebra:
  `grep -rni "tangentSpace\|DualNumber" Mathlib/AlgebraicGeometry/` returns
  NOTHING.  A hit means this leaf may now be cheap and should be re-attacked.
* Consequently there is no `e^* Ω_{G/S}` for a group scheme and no
  identification of the infinitesimal kernel with it.  `Ω` itself exists at
  ring level (`KaehlerDifferential`) and as a sheaf, so what is missing is
  the group-scheme half, not differentials.

**A GENERALISATION THAT IS ALSO TRUE**, recorded so a prover is not misled
into thinking the field is essential: the same statement holds over an
arbitrary base with `n` invertible in `Γ(T, 𝒪_T)`, and does not need
`ab.smooth` either (the displayed isomorphism is valid for every group
scheme).  It is stated over a field here because that is the shape the
consumer needs, and a prover may freely prove the stronger form and
specialise. -/
theorem eq_zero_of_nsmul_eq_zero_of_squareZero {X : Scheme.{u}} (K : CommRingCat.{u}) [Field K]
    {fK : X ⟶ Spec K} (ab : AbelianSchemeStruct fK) (n : ℕ) (hn : (n : K) ≠ 0)
    {R R₀ : CommRingCat.{u}} (φ : R ⟶ R₀) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ.hom ^ 2 = ⊥)
    {q : Spec R ⟶ Spec K} (d : RelPoint fK q)
    (hres : letI := ab.addCommGroup (Spec.map φ ≫ q)
      RelPoint.pre (Spec.map φ) rfl d = 0)
    (hnd : letI := ab.addCommGroup q; n • d = 0) :
    letI := ab.addCommGroup q; d = 0 :=
  sorry

/-- **`[n]` is FORMALLY UNRAMIFIED when `n` is prime to the characteristic**
(PROVEN 2026-07-27 over the single leaf
`eq_zero_of_nsmul_eq_zero_of_squareZero` above).

This is the functor-of-points argument in full, and it uses no geometry
beyond the group structure.  Mathlib's `FormallyUnramified.of_hom_ext`
reduces formal unramifiedness to: for every surjection `φ : R ⟶ R₀` with
`ker φ ^ 2 = ⊥` and every pair `g₁ g₂ : Spec R ⟶ A` with
`Spec.map φ ≫ g₁ = Spec.map φ ≫ g₂` and `g₁ ≫ [n] = g₂ ≫ [n]`, one has
`g₁ = g₂`.

The proof:

1. *Both are relative points over the SAME base point.*  `[n] ≫ f = f`
   (`mulByNat_comp`) turns `g₁ ≫ [n] = g₂ ≫ [n]` into `g₂ ≫ f = g₁ ≫ f`,
   so `g₁` and `g₂` are two elements of the group `RelPoint f (g₁ ≫ f)`.
2. *The hypotheses become group statements.*  `nsmul_val` says precomposition
   with `[n]` IS multiplication by `n`, so `g₁ ≫ [n] = g₂ ≫ [n]` reads
   `n • y₁ = n • y₂`, i.e. `n • (y₁ - y₂) = 0`; and `pre_sub` turns the
   agreement over `Spec R₀` into `RelPoint.pre _ _ (y₁ - y₂) = 0`.
3. *Apply the leaf* to `d = y₁ - y₂` and conclude `y₁ = y₂`, hence
   `g₁ = g₂`.

No line bundles, no `Pic`, no theorem of the cube, and no smoothness is used
HERE — smoothness is consumed inside the leaf. -/
theorem formallyUnramified_mulByNat {X : Scheme.{u}} (K : CommRingCat.{u}) [Field K]
    {fK : X ⟶ Spec K} (ab : AbelianSchemeStruct fK) (n : ℕ) (hn : (n : K) ≠ 0) :
    FormallyUnramified (ab.mulByNat n) := by
  refine FormallyUnramified.of_hom_ext _ ?_
  intro R R₀ φ hφ hker g₁ g₂ hres hcomp
  have hq₂ : g₂ ≫ fK = g₁ ≫ fK := by
    conv_lhs => rw [← ab.mulByNat_comp n]
    rw [← Category.assoc, ← hcomp, Category.assoc, ab.mulByNat_comp]
  letI := ab.addCommGroup (g₁ ≫ fK)
  letI := ab.addCommGroup (Spec.map φ ≫ (g₁ ≫ fK))
  set y₁ : RelPoint fK (g₁ ≫ fK) := ⟨g₁, rfl⟩ with hy₁
  set y₂ : RelPoint fK (g₁ ≫ fK) := ⟨g₂, hq₂⟩ with hy₂
  have hsub : y₁ - y₂ = 0 := by
    refine eq_zero_of_nsmul_eq_zero_of_squareZero K ab n hn φ hφ hker _ ?_ ?_
    · rw [ab.pre_sub, sub_eq_zero]
      exact Subtype.ext hres
    · rw [smul_sub, sub_eq_zero]
      refine Subtype.ext ?_
      rw [ab.nsmul_val, ab.nsmul_val]
      exact hcomp
  exact congrArg Subtype.val (sub_eq_zero.mp hsub)

/-- **`[n]` has finite fibres when `n` is invertible in the base field**
(PROVEN 2026-07-27 over the single leaf
`eq_zero_of_nsmul_eq_zero_of_squareZero`; this used to be a sorry leaf).

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

**THE TWO OBLIGATIONS THIS DOCSTRING USED TO RECORD: one is now PROVEN, one
is now the single leaf.**  Neither was ever the cube.

1. The `Γ(T, 𝒪_T)`-module structure on the kernel above, i.e. the Lie algebra
   / tangent space of a smooth group scheme.  **Still missing, and it is now
   the leaf `eq_zero_of_nsmul_eq_zero_of_squareZero` above**, where the
   argument, the references and the refuting greps are recorded.  Mathlib
   still has NO scheme tangent space: `grep -rni "tangentSpace\|DualNumber"
   Mathlib/AlgebraicGeometry/` returns NOTHING (re-run 2026-07-27).
2. `FormallyUnramified f → LocallyOfFiniteType f → LocallyQuasiFinite f`.
   **This was recorded as ABSENT and that was WRONG** — the grep it rested on
   (`grep -rn "Unramified" Morphisms/QuasiFinite.lean` → nothing) is true but
   does not support the conclusion, because the implication lives at RING
   level as the mathlib instance
   `[EssFiniteType R S] [FormallyUnramified R S] : Algebra.QuasiFinite R S`
   (`Mathlib/RingTheory/Unramified/LocalStructure.lean:333`).  It is now
   PROVEN here as `locallyQuasiFinite_of_formallyUnramified`, in four lines.

**The `quasiFiniteLocus` spreading tool is NOT needed** — and recording that
saves the next reader a detour.  `Scheme.Hom.quasiFiniteLocus` /
`isOpen_quasiFiniteAt` were suggested for propagating quasi-finiteness from
the origin over all of `A`, but the functor-of-points argument proves
`FormallyUnramified` at EVERY affine test scheme at once, so there is nothing
to spread.  (Openness of the quasi-finite locus would not have sufficed
anyway: spreading from one point needs homogeneity, i.e. translations, not
just an open locus.)

References: Mumford *Abelian Varieties* §6, §11; Milne *Abelian Varieties*
I.7; SGA 3, Exp. II. -/
theorem finite_preimage_mulByNat_of_field_prime_to_char {X : Scheme.{u}}
    (K : CommRingCat.{u}) [Field K] {fK : X ⟶ Spec K} (ab : AbelianSchemeStruct fK)
    (n : ℕ) (hn : (n : K) ≠ 0) (a : X) : (⇑(ab.mulByNat n) ⁻¹' {a}).Finite := by
  haveI : LocallyOfFiniteType (ab.mulByNat n) := ab.locallyOfFiniteType_mulByNat n
  haveI : IsProper (ab.mulByNat n) := ab.isProper_mulByNat n
  haveI : QuasiCompact (ab.mulByNat n) := inferInstance
  haveI : FormallyUnramified (ab.mulByNat n) := formallyUnramified_mulByNat K ab n hn
  haveI : LocallyQuasiFinite (ab.mulByNat n) :=
    locallyQuasiFinite_of_formallyUnramified (ab.mulByNat n)
  exact (ab.mulByNat n).finite_preimage_singleton a

section ShearReduction

-- `_root_.` is not optional: a bare `open Limits` inside `namespace Fermat` would
-- bind to a nested `Fermat.Limits` if one is ever declared.  The file already
-- opens `Limits` this way in its two earlier sections.
open _root_.CategoryTheory.Limits

/-! ### The shearing reduction: ALL fibres of `[n]` from the ONE fibre `ker[n]`

(Added 2026-07-27, while proving `finite_preimage_mulByNat_of_field_char`.)

Everything in this block is PROVEN and **cube-free**, and it is stated for an
arbitrary base `S` — there is no field, no characteristic and no smoothness in
it.  It replaces the "all fibres of `[n]`" problem by the ONE statement the
literature actually proves, namely that `[n]` is an ISOGENY:

  `ker[n] ⟶ S` is a FINITE morphism.

The argument is the classical one, and it is worth recording because it is
*not* the theorem of the cube:

1. `finite_preimage_of_finite_preimage_pullback_fst` — pure scheme theory.
   For ANY `h : X ⟶ Y`, finite fibres of `pullback.fst h h` give finite fibres
   of `h`.  Reason: given `u, v` with `h u = h v`, `Scheme.Pullback.exists_preimage_pullback`
   produces a point of `X ×_Y X` over the pair `(u, v)` — the map from the
   carrier of a fibre product ONTO the set-theoretic fibre product is
   surjective, because `κ(u) ⊗_{κ(h u)} κ(v)` is a nonzero ring.  So
   `pullback.snd` maps the (finite) fibre of `pullback.fst` over `u` ONTO
   `h ⁻¹' {h u}`.

2. `kerShear` — the shearing morphism `A ×_{[n], A, [n]} A ⟶ A ×_S ker[n]`,
   `(u, v) ↦ (u, v - u)`, written directly on relative points: `v - u` is a
   relative point of `f` over `A ×_{[n]} A`, and `nsmul_val` turns
   `[n] ∘ v = [n] ∘ u` into `n • (v - u) = 0`, i.e. `v - u` factors through
   `ker[n]`.  `kerUnshear` is `(u, k) ↦ (u, u + k)` and
   `kerShear_unshear` says `kerShear ≫ kerUnshear = 𝟙`, so `kerShear` is
   injective on points — which is all that is needed.  Only ONE round trip is
   proven; the other is not required and is not claimed.

3. `pullback.fst f (ker[n] ⟶ S)` is the base change of `ker[n] ⟶ S`, hence
   finite when that is, hence has finite fibres.  Composing (2) and (1) gives
   `finite_preimage_mulByNat_of_isFinite_ker`.

`isFinite_ker_mulByNat_of_finite_preimage` is a convenience bridge in the other
direction: since `[n]` is proper (`isProper_mulByNat`) and locally of finite
type (`locallyOfFiniteType_mulByNat`), so is `ker[n] ⟶ S`, and Zariski's main
theorem (`IsFinite.of_isProper_of_locallyQuasiFinite`) upgrades "every fibre of
`ker[n] ⟶ S` is a finite SET" to "`ker[n] ⟶ S` is a finite MORPHISM".  A prover
of the residual leaf therefore only ever has to exhibit a finite point set —
over a field, a single one.

**This block is `n`-generic and characteristic-blind.**  It applies verbatim to
the prime-to-characteristic sibling `finite_preimage_mulByNat_of_field_prime_to_char`
and to the arbitrary-base `finite_preimage_mulByNat`.  Those have their own
owners and are deliberately NOT touched here; this note is so the next owner
sees the shared route.
-/

/-- **Finite fibres descend from `pullback.fst h h` to `h`** (PROVEN
2026-07-27).  General scheme theory, no group structure and no hypotheses on
`h` whatever.

The point is that the carrier of `X ×_Y X` surjects onto the set-theoretic
fibre product of the carriers (`Scheme.Pullback.exists_preimage_pullback`,
which is where the nonvanishing of `κ(u) ⊗_{κ(s)} κ(v)` is used).  So for `u`
in the fibre of `h` over `y`, the whole fibre `h ⁻¹' {y}` is the image under
`pullback.snd h h` of the fibre of `pullback.fst h h` over `u`. -/
theorem finite_preimage_of_finite_preimage_pullback_fst {X Y : Scheme.{u}} (h : X ⟶ Y)
    (H : ∀ x : X, (⇑(pullback.fst h h) ⁻¹' {x}).Finite) (y : Y) :
    (⇑h ⁻¹' {y}).Finite := by
  rcases Set.eq_empty_or_nonempty (⇑h ⁻¹' {y}) with he | ⟨u, hu⟩
  · rw [he]; exact Set.finite_empty
  · refine ((H u).image ⇑(pullback.snd h h)).subset ?_
    intro v hv
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hu hv
    obtain ⟨z, hz1, hz2⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := h) (g := h) u v (hu.trans hv.symm)
    exact ⟨z, by simpa using hz1, hz2⟩

namespace AbelianSchemeStruct

variable (ab : AbelianSchemeStruct f) (n : ℕ)

/-- Both projections of `A ×_{[n], A, [n]} A` lie over the same point of `S`,
because `[n]` is a morphism over `S`. -/
theorem pullbackSnd_comp_structure :
    pullback.snd (ab.mulByNat n) (ab.mulByNat n) ≫ f
      = pullback.fst (ab.mulByNat n) (ab.mulByNat n) ≫ f := by
  calc pullback.snd (ab.mulByNat n) (ab.mulByNat n) ≫ f
      = pullback.snd (ab.mulByNat n) (ab.mulByNat n) ≫ (ab.mulByNat n ≫ f) := by
        rw [ab.mulByNat_comp]
    _ = (pullback.snd (ab.mulByNat n) (ab.mulByNat n) ≫ ab.mulByNat n) ≫ f :=
        (Category.assoc _ _ _).symm
    _ = (pullback.fst (ab.mulByNat n) (ab.mulByNat n) ≫ ab.mulByNat n) ≫ f := by
        rw [pullback.condition]
    _ = pullback.fst (ab.mulByNat n) (ab.mulByNat n) ≫ (ab.mulByNat n ≫ f) :=
        Category.assoc _ _ _
    _ = pullback.fst (ab.mulByNat n) (ab.mulByNat n) ≫ f := by rw [ab.mulByNat_comp]

/-- **The structure morphism of `ker[n] = A ×_{[n], A, e} S`**: the inclusion
`ker[n] ⟶ A` followed by `f` is the second projection.  Uses only
`mulByNat_comp` and `zeroSection_comp`. -/
theorem kerι_comp_structure :
    pullback.fst (ab.mulByNat n) ab.zeroSection ≫ f
      = pullback.snd (ab.mulByNat n) ab.zeroSection := by
  calc pullback.fst (ab.mulByNat n) ab.zeroSection ≫ f
      = pullback.fst (ab.mulByNat n) ab.zeroSection ≫ (ab.mulByNat n ≫ f) := by
        rw [ab.mulByNat_comp]
    _ = (pullback.fst (ab.mulByNat n) ab.zeroSection ≫ ab.mulByNat n) ≫ f :=
        (Category.assoc _ _ _).symm
    _ = (pullback.snd (ab.mulByNat n) ab.zeroSection ≫ ab.zeroSection) ≫ f := by
        rw [pullback.condition]
    _ = pullback.snd (ab.mulByNat n) ab.zeroSection ≫ (ab.zeroSection ≫ f) :=
        Category.assoc _ _ _
    _ = pullback.snd (ab.mulByNat n) ab.zeroSection := by
        rw [ab.zeroSection_comp, Category.comp_id]

/-- The first projection of `A ×_{[n], A, [n]} A`, read as a relative point. -/
noncomputable def shearFst :
    RelPoint f (pullback.fst (ab.mulByNat n) (ab.mulByNat n) ≫ f) :=
  ⟨pullback.fst (ab.mulByNat n) (ab.mulByNat n), rfl⟩

/-- The second projection of `A ×_{[n], A, [n]} A`, read as a relative point. -/
noncomputable def shearSnd :
    RelPoint f (pullback.fst (ab.mulByNat n) (ab.mulByNat n) ≫ f) :=
  ⟨pullback.snd (ab.mulByNat n) (ab.mulByNat n), ab.pullbackSnd_comp_structure n⟩

/-- The difference `q₂ - q₁` of the two projections, as a relative point.
Written with `ab.add`/`ab.neg` rather than `-` so that the definition carries
no `letI`. -/
noncomputable def shearDiff :
    RelPoint f (pullback.fst (ab.mulByNat n) (ab.mulByNat n) ≫ f) :=
  ab.add (ab.shearSnd n) (ab.neg (ab.shearFst n))

theorem shearDiff_eq_sub :
    letI := ab.addCommGroup (pullback.fst (ab.mulByNat n) (ab.mulByNat n) ≫ f)
    ab.shearDiff n = ab.shearSnd n - ab.shearFst n := rfl

/-- **`n • (q₂ - q₁) = 0`**: this is `pullback.condition` read through
`nsmul_val`, and it is the whole reason the shearing lands in `ker[n]`. -/
theorem nsmul_shearDiff_eq_zero :
    letI := ab.addCommGroup (pullback.fst (ab.mulByNat n) (ab.mulByNat n) ≫ f)
    n • ab.shearDiff n = 0 := by
  letI := ab.addCommGroup (pullback.fst (ab.mulByNat n) (ab.mulByNat n) ≫ f)
  rw [ab.shearDiff_eq_sub n, smul_sub, sub_eq_zero]
  refine Subtype.ext ?_
  rw [ab.nsmul_val, ab.nsmul_val]
  exact pullback.condition.symm

/-- `(q₂ - q₁) ≫ [n]` is the zero section: the difference factors through
`ker[n]`. -/
theorem shearDiff_comp_mulByNat :
    (ab.shearDiff n).1 ≫ ab.mulByNat n
      = (pullback.fst (ab.mulByNat n) (ab.mulByNat n) ≫ f) ≫ ab.zeroSection := by
  letI := ab.addCommGroup (pullback.fst (ab.mulByNat n) (ab.mulByNat n) ≫ f)
  rw [← ab.nsmul_val n (ab.shearDiff n), ab.nsmul_shearDiff_eq_zero n]
  exact ab.zero_val _

/-- **The shearing morphism** `A ×_{[n], A, [n]} A ⟶ A ×_S ker[n]`,
`(u, v) ↦ (u, v - u)`. -/
noncomputable def kerShear :
    pullback (ab.mulByNat n) (ab.mulByNat n) ⟶
      pullback f (pullback.snd (ab.mulByNat n) ab.zeroSection) :=
  pullback.lift (pullback.fst (ab.mulByNat n) (ab.mulByNat n))
    (pullback.lift (ab.shearDiff n).1 (pullback.fst (ab.mulByNat n) (ab.mulByNat n) ≫ f)
      (ab.shearDiff_comp_mulByNat n))
    (pullback.lift_snd _ _ _).symm

/-- The shearing is the identity in the `A`-coordinate — the fact that makes
it useful for comparing fibres of the two first projections. -/
theorem kerShear_fst :
    ab.kerShear n ≫ pullback.fst f (pullback.snd (ab.mulByNat n) ab.zeroSection)
      = pullback.fst (ab.mulByNat n) (ab.mulByNat n) := by
  simp only [kerShear]
  exact pullback.lift_fst _ _ _

theorem kerShear_snd_fst :
    ab.kerShear n ≫ pullback.snd f (pullback.snd (ab.mulByNat n) ab.zeroSection)
        ≫ pullback.fst (ab.mulByNat n) ab.zeroSection
      = (ab.shearDiff n).1 := by
  rw [← Category.assoc]
  simp only [kerShear]
  rw [pullback.lift_snd]
  exact pullback.lift_fst _ _ _

/-- The first projection of `A ×_S ker[n]`, as a relative point. -/
noncomputable def unshearFst :
    RelPoint f (pullback.fst f (pullback.snd (ab.mulByNat n) ab.zeroSection) ≫ f) :=
  ⟨pullback.fst f (pullback.snd (ab.mulByNat n) ab.zeroSection), rfl⟩

/-- The `ker[n]`-component of `A ×_S ker[n]`, read as a relative point of `A`. -/
noncomputable def unshearSnd :
    RelPoint f (pullback.fst f (pullback.snd (ab.mulByNat n) ab.zeroSection) ≫ f) :=
  ⟨pullback.snd f (pullback.snd (ab.mulByNat n) ab.zeroSection)
      ≫ pullback.fst (ab.mulByNat n) ab.zeroSection, by
    rw [Category.assoc, ab.kerι_comp_structure n]
    exact pullback.condition.symm⟩

/-- **A point of `ker[n]` is killed by `n`** — by construction, but this is
the form the shearing needs. -/
theorem nsmul_unshearSnd_eq_zero :
    letI := ab.addCommGroup (pullback.fst f (pullback.snd (ab.mulByNat n) ab.zeroSection) ≫ f)
    n • ab.unshearSnd n = 0 := by
  letI := ab.addCommGroup (pullback.fst f (pullback.snd (ab.mulByNat n) ab.zeroSection) ≫ f)
  refine Subtype.ext ?_
  rw [ab.nsmul_val]
  have hz : ((0 : RelPoint f
      (pullback.fst f (pullback.snd (ab.mulByNat n) ab.zeroSection) ≫ f))).1
      = (pullback.fst f (pullback.snd (ab.mulByNat n) ab.zeroSection) ≫ f) ≫ ab.zeroSection :=
    ab.zero_val _
  rw [hz]
  show (pullback.snd f (pullback.snd (ab.mulByNat n) ab.zeroSection)
      ≫ pullback.fst (ab.mulByNat n) ab.zeroSection) ≫ ab.mulByNat n = _
  rw [Category.assoc, pullback.condition (f := ab.mulByNat n) (g := ab.zeroSection),
    ← Category.assoc, ← pullback.condition, Category.assoc]

/-- **The inverse shearing** `A ×_S ker[n] ⟶ A ×_{[n], A, [n]} A`,
`(u, k) ↦ (u, u + k)`.  It lands in the fibre product because `n • k = 0`. -/
noncomputable def kerUnshear :
    pullback f (pullback.snd (ab.mulByNat n) ab.zeroSection) ⟶
      pullback (ab.mulByNat n) (ab.mulByNat n) :=
  pullback.lift (ab.unshearFst n).1 (ab.add (ab.unshearFst n) (ab.unshearSnd n)).1 (by
    letI := ab.addCommGroup (pullback.fst f (pullback.snd (ab.mulByNat n) ab.zeroSection) ≫ f)
    have h : n • (ab.unshearFst n) = n • (ab.unshearFst n + ab.unshearSnd n) := by
      rw [smul_add, ab.nsmul_unshearSnd_eq_zero, add_zero]
    have h2 := congrArg Subtype.val h
    rwa [ab.nsmul_val, ab.nsmul_val] at h2)

theorem kerUnshear_fst :
    ab.kerUnshear n ≫ pullback.fst (ab.mulByNat n) (ab.mulByNat n) = (ab.unshearFst n).1 := by
  simp only [kerUnshear]
  exact pullback.lift_fst _ _ _

theorem kerUnshear_snd :
    ab.kerUnshear n ≫ pullback.snd (ab.mulByNat n) (ab.mulByNat n)
      = (ab.add (ab.unshearFst n) (ab.unshearSnd n)).1 := by
  simp only [kerUnshear]
  exact pullback.lift_snd _ _ _

/-- **`kerShear` is a split monomorphism**: `(u, v) ↦ (u, v - u) ↦ (u, u + (v - u))`
is the identity.  Only this round trip is proven — injectivity on points is all
the fibre comparison needs — and the naturality axiom `pre_add` is what turns
the computation into the group identity `u + (v - u) = v`. -/
theorem kerShear_kerUnshear : ab.kerShear n ≫ ab.kerUnshear n = 𝟙 _ := by
  letI := ab.addCommGroup (pullback.fst (ab.mulByNat n) (ab.mulByNat n) ≫ f)
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, ab.kerUnshear_fst n, Category.id_comp]
    show ab.kerShear n ≫ pullback.fst f _ = _
    exact ab.kerShear_fst n
  · rw [Category.assoc, ab.kerUnshear_snd n, Category.id_comp]
    have hg : ab.kerShear n ≫ (pullback.fst f (pullback.snd (ab.mulByNat n) ab.zeroSection) ≫ f)
        = pullback.fst (ab.mulByNat n) (ab.mulByNat n) ≫ f := by
      rw [← Category.assoc, ab.kerShear_fst n]
    have key := ab.pre_add (ab.kerShear n) hg (ab.unshearFst n) (ab.unshearSnd n)
    have h1 : RelPoint.pre (ab.kerShear n) hg (ab.unshearFst n) = ab.shearFst n :=
      Subtype.ext (ab.kerShear_fst n)
    have h2 : RelPoint.pre (ab.kerShear n) hg (ab.unshearSnd n) = ab.shearDiff n :=
      Subtype.ext (by
        show ab.kerShear n ≫ (pullback.snd f (pullback.snd (ab.mulByNat n) ab.zeroSection)
            ≫ pullback.fst (ab.mulByNat n) ab.zeroSection) = _
        exact ab.kerShear_snd_fst n)
    rw [h1, h2] at key
    have h3 : ab.add (ab.shearFst n) (ab.shearDiff n) = ab.shearSnd n := by
      show ab.shearFst n + ab.shearDiff n = ab.shearSnd n
      rw [ab.shearDiff_eq_sub n, add_sub_cancel]
    exact congrArg Subtype.val (key.trans h3)

/-- **ZMT bridge**: `ker[n] ⟶ S` is a FINITE MORPHISM as soon as each of its
fibres is a finite SET (PROVEN 2026-07-27).

`[n]` is proper and locally of finite type, hence so is its base change
`ker[n] ⟶ S`; `LocallyQuasiFinite.of_finite_preimage_singleton` then gives
quasi-finiteness and `IsFinite.of_isProper_of_locallyQuasiFinite` (Zariski's
main theorem) upgrades it.  Over a field the hypothesis is a single finite
point set — the classical "`ker[n]` is zero-dimensional". -/
theorem isFinite_ker_mulByNat_of_finite_preimage
    (H : ∀ s : S, (⇑(pullback.snd (ab.mulByNat n) ab.zeroSection) ⁻¹' {s}).Finite) :
    IsFinite (pullback.snd (ab.mulByNat n) ab.zeroSection) := by
  haveI : IsProper (ab.mulByNat n) := ab.isProper_mulByNat n
  haveI : LocallyOfFiniteType (ab.mulByNat n) := ab.locallyOfFiniteType_mulByNat n
  haveI : LocallyQuasiFinite (pullback.snd (ab.mulByNat n) ab.zeroSection) :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ H
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

/-- **EVERY fibre of `[n]` is finite as soon as `ker[n] ⟶ S` is a finite
morphism** (PROVEN 2026-07-27) — i.e. as soon as `[n]` is an ISOGENY.

Cube-free, `n`-generic, characteristic-blind, and stated over an ARBITRARY
base `S`.  This is the reduction described in the section header: shear
`A ×_{[n], A, [n]} A` onto `A ×_S ker[n]`, note that the first projection of
the latter is a base change of `ker[n] ⟶ S` and so has finite fibres, and then
descend along `finite_preimage_of_finite_preimage_pullback_fst`. -/
theorem finite_preimage_mulByNat_of_isFinite_ker
    (hker : IsFinite (pullback.snd (ab.mulByNat n) ab.zeroSection)) (a : A) :
    (⇑(ab.mulByNat n) ⁻¹' {a}).Finite := by
  haveI := hker
  refine finite_preimage_of_finite_preimage_pullback_fst (ab.mulByNat n) (fun x => ?_) a
  have hQ : (⇑(pullback.fst f (pullback.snd (ab.mulByNat n) ab.zeroSection)) ⁻¹' {x}).Finite :=
    Scheme.Hom.finite_preimage_singleton _ x
  have hinj : Function.Injective ⇑(ab.kerShear n) := by
    intro c d hcd
    have h1 : (ab.kerShear n ≫ ab.kerUnshear n) c = (ab.kerShear n ≫ ab.kerUnshear n) d := by
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hcd]
    rw [ab.kerShear_kerUnshear n] at h1
    simpa using h1
  have hset : (⇑(pullback.fst (ab.mulByNat n) (ab.mulByNat n)) ⁻¹' {x})
      = ⇑(ab.kerShear n) ⁻¹'
        (⇑(pullback.fst f (pullback.snd (ab.mulByNat n) ab.zeroSection)) ⁻¹' {x}) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [← ab.kerShear_fst n, Scheme.Hom.comp_apply]
  rw [hset]
  exact hQ.preimage hinj.injOn

end AbelianSchemeStruct

/-- **`ker[p]` has FINITELY MANY POINTS in characteristic `p`** (sorry leaf —
the theorem of the cube; this is the irreducible residue, cut down 2026-07-27
from `finite_preimage_mulByNat_of_field_char`).

`Spec K` has a single point, so this is one finite set: the underlying space of
`ker[p]` is finite, i.e. `ker[p]` is zero-dimensional.  That is the weakest
form the residue can be put in, and it is deliberately the form the leaf is
stated in — everything else on the route (properness, Zariski's main theorem,
the shearing) is proven above, so a prover here owes ONLY the dimension
statement.

For the mathematics — why `d[p] = 0` kills the cheap route, the two classical
cube proofs, and the verified survey of what is missing from the pin — see
`isFinite_ker_mulByNat_of_field_char` just below, which is the consumer. -/
theorem finite_ker_mulByNat_of_field_char {X : Scheme.{u}}
    (K : CommRingCat.{u}) [Field K] {fK : X ⟶ Spec K} (ab : AbelianSchemeStruct fK)
    (p : ℕ) (hp : p.Prime) (hchar : ringChar K = p) :
    ∀ s : Spec K, (⇑(pullback.snd (ab.mulByNat p) ab.zeroSection) ⁻¹' {s}).Finite :=
  sorry

/-- **`ker[p]` is a finite group scheme in characteristic `p`** — equivalently,
`[p]` is an ISOGENY (PROVEN 2026-07-27 over `finite_ker_mulByNat_of_field_char`,
through the Zariski's-main-theorem bridge `isFinite_ker_mulByNat_of_finite_preimage`).

**What changed.**  The old leaf asked for finiteness of EVERY fibre of `[p]`.
The shearing block above proves — cube-free and over an arbitrary base — that
all fibres are finite as soon as this ONE fibre is
(`finite_preimage_mulByNat_of_isFinite_ker`).  So the whole residue became the
single statement every textbook actually proves: `ker[p]` is finite, of order
`p^{2g}`; and by `isFinite_ker_mulByNat_of_finite_preimage` even that is
reduced to a bare POINT SET being finite, which is the leaf
`finite_ker_mulByNat_of_field_char` above.  The chain from there to
`finite_preimage_mulByNat_of_field_char` is entirely proven.

**So the honest remaining content is "`ker[p]` is zero-dimensional"** —
properness, Zariski's main theorem and the shearing supply everything else.

**Why this is still the cube, and why the cheap route dies here.**  The
Lie-algebra argument that proves the sibling
`finite_preimage_mulByNat_of_field_prime_to_char` computes `d[n] = n · id`; at
`n = p = ringChar K` that is ZERO, so `[p]` is not unramified and the argument
says nothing.  `[p]` really is inseparable — its kernel contains `ker F` for the
relative Frobenius `F`, an infinitesimal group scheme — so this is a limitation
of the mathematics, not of the write-up.  Two classical proofs, both blocked at
this pin:

* Mumford *Abelian Varieties* §6, Application 2 of the theorem of the cube:
  take a symmetric ample `L`, use `[p]^* L ≅ L^{p²}`, again ample for `p ≠ 0`;
  then `[p]^* L` is ample and trivial on `ker[p]`, which forces `ker[p]` to be
  zero-dimensional.
* `[p] = V ∘ F`, with `F` the relative Frobenius (finite, and a homeomorphism
  on underlying spaces) and `V` the Verschiebung.  `V` is constructed by
  duality, so this route needs `Pic⁰` and the dual abelian variety.

**MISSING MACHINERY at this pin, each claim refutable by one grep** (re-verified
2026-07-27 against the worktree's own `.lake/packages/mathlib`).
`grep -rl Ample Mathlib/AlgebraicGeometry/` returns NOTHING: there are no ample
line bundles (the only `Ample` in mathlib is `Analysis/Convex/AmpleSet.lean`).
`grep -rli picard Mathlib/AlgebraicGeometry/` returns only
`EllipticCurve/Weierstrass.lean`: there is no Picard scheme or functor
(`RingTheory/PicardGroup.lean` is about modules).
`grep -rlie "line bundle\|invertible sheaf\|InvertibleSheaf" Mathlib/AlgebraicGeometry/`
returns NOTHING, and `Mathlib/AlgebraicGeometry/Modules/` contains only
`Presheaf.lean`, `Sheaf.lean`, `Tilde.lean` — so there is no invertible-sheaf
theory to build `Pic` on.  There is no theorem of the cube
(`grep -rli "theoremOfTheCube" Mathlib/` is empty), no relative Frobenius
(`grep -rli frobenius Mathlib/AlgebraicGeometry/` is empty) and no
Cohen–Macaulay theory (`grep -rl CohenMacaulay Mathlib/` is empty).
`~/cs/FLT` has none of it either: its only `Ample`/`Picard` matches are
`import Mathlib.RingTheory.PicardGroup`.
What mathlib HAS started is abelian varieties themselves —
`Mathlib/AlgebraicGeometry/Group/{Abelian,Smooth}.lean`, carrying
`isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed`,
`isCommMonObj_of_isProper_of_geometricallyIntegral` and `smooth_of_grpObj`.
Re-check that directory at every pin bump.

**`hp` and `hchar` are deliberately carried even though the statement is true
without them** — `ker[n]` is finite for every `n ≠ 0` — because without them
this leaf would silently duplicate the content the sibling needs.  Carrying
them records that this is exactly the residue the Lie-algebra route cannot
reach, and makes the leaf VACUOUS in characteristic zero. -/
theorem isFinite_ker_mulByNat_of_field_char {X : Scheme.{u}}
    (K : CommRingCat.{u}) [Field K] {fK : X ⟶ Spec K} (ab : AbelianSchemeStruct fK)
    (p : ℕ) (hp : p.Prime) (hchar : ringChar K = p) :
    IsFinite (pullback.snd (ab.mulByNat p) ab.zeroSection) :=
  ab.isFinite_ker_mulByNat_of_finite_preimage p
    (finite_ker_mulByNat_of_field_char K ab p hp hchar)

end ShearReduction

/-- **`[p]` has finite fibres in characteristic `p`** (PROVEN 2026-07-27 over
`isFinite_ker_mulByNat_of_field_char`, via the cube-free shearing reduction).

The other half of the old `finite_preimage_mulByNat_of_field`, split out
2026-07-27.  **It is no longer a leaf**: the shearing block above reduces it,
cube-free, to the single fibre `ker[p]`, and the residue now lives in
`isFinite_ker_mulByNat_of_field_char`.

The statement is UNCHANGED — same name, same hypotheses, same conclusion — so
every consumer (`finite_preimage_mulByNat_of_field` below) resolves exactly as
before.  `hp` and `hchar` are not used by this assembly; they are passed
through to the residual leaf, which is where they are recorded as marking the
Lie-algebra route's blind spot.  The leaf remains VACUOUS in characteristic
zero, and so does this theorem's route through it.

For the mathematics — why `d[p] = 0` kills the cheap route, the two classical
cube proofs, and the verified survey of what is missing from the pin — see
`isFinite_ker_mulByNat_of_field_char` above.  It is not repeated here, so that
there is exactly one place to update when mathlib grows ample bundles. -/
theorem finite_preimage_mulByNat_of_field_char {X : Scheme.{u}}
    (K : CommRingCat.{u}) [Field K] {fK : X ⟶ Spec K} (ab : AbelianSchemeStruct fK)
    (p : ℕ) (hp : p.Prime) (hchar : ringChar K = p) (a : X) :
    (⇑(ab.mulByNat p) ⁻¹' {a}).Finite :=
  ab.finite_preimage_mulByNat_of_isFinite_ker p
    (isFinite_ker_mulByNat_of_field_char K ab p hp hchar) a

/-- **The fibres of `[n]` on an abelian VARIETY are FINITE** (PROVEN
2026-07-27 over the two declarations just above).

**Status update 2026-07-27, later the same day.**  Of those two,
`finite_preimage_mulByNat_of_field_prime_to_char` is now itself PROVEN, over
the single new leaf `eq_zero_of_nsmul_eq_zero_of_squareZero` (the Lie algebra
of a smooth group scheme).  So the two open leaves under this declaration are
now that one and `finite_preimage_mulByNat_of_field_char`, and only the
SECOND of them needs the theorem of the cube.

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
`n` over the two declarations above, which are genuinely different
mathematical problems and want different provers (and the first of them has
since been PROVEN, over the Lie-algebra leaf
`eq_zero_of_nsmul_eq_zero_of_squareZero`).  Writing `p = ringChar K`, the
step is:

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
