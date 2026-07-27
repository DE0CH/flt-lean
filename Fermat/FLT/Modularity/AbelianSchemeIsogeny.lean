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
public import Mathlib.AlgebraicGeometry.QuasiAffine
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
-- Consumed by the PROOFS of the two leaves below.  `ResidueField.Fiber` supplies
-- `Ideal.Fiber` (the `κ(p) ⊗ S` of `Algebra.QuasiFinite.finite_fiber`) and
-- `TensorProduct.Quotient` the identification of that fibre with `T ⧸ 𝔪T`;
-- `HopkinsLevitzki` / `KrullDimension.Zero` turn "artinian" into
-- `ringKrullDim = 0`; `LocalRing.RingHom.Basic` supplies
-- `IsLocalRing.map_maximalIdeal_lt_top`.  `Regular.RegularSequence` and
-- `RingHom.Flat` (already imported just above) occur in the SIGNATURES of the
-- three sub-leaves of `flat_of_isRegularLocalRing_of_ringKrullDim_eq`, so they
-- are `public`.
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
-- `QuotSMulTop` appears in the `isWeaklyRegular_cons_iff` step of
-- `exists_isWeaklyRegular_span_eq_maximalIdeal_aux`.  It arrives transitively
-- through `Regular.RegularSequence`, but named explicitly so that a proof-body
-- use cannot be broken by a private import upstream.
public import Mathlib.RingTheory.QuotSMulTop
-- `Ideal.Quotient.isNoetherianRing`, the instance that lets the induction of
-- `flat_of_isWeaklyRegular_span_eq_maximalIdeal_aux` re-enter itself at
-- `R ⧸ (t) → T ⧸ (φ t)`.  Nothing else in the file needs it.
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
-- `isRegularLocalRing_stalk_of_smooth` below is a one-line corollary of
-- `isRegularLocalRing_stalk_of_smooth_over_field`, which was PROVEN in
-- `Modularity/KhareWintenberger.lean` — a module strictly DOWNSTREAM of this
-- one — and was HOISTED into `Modularity/RegularStalks.lean` on 2026-07-27
-- precisely so that it could be consumed here.
public import Fermat.FLT.Modularity.RegularStalks

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
delivers it.

**A CORRECTION about 00R7 (2026-07-27).**  The previous version of this
paragraph ended "Its sibling 00R7 (10.128.8) demands essential finite
presentation on BOTH maps and is therefore the wrong one to reach for."  The
first half is true and the conclusion is backwards: **05UV's own Stacks proof
is an application of 00R7.**  Read verbatim, it writes `S` as `B/J` with
`R → B` essentially of finite presentation, proves `J` finitely generated by
applying **00R7** to `R → B/J' → S'` for finitely generated `J' ⊆ J` and then
**046Y (10.128.4)** to see that any two such `J'` agree, and finishes: "Thus
we may apply Lemma 10.128.8 to `R → S → S'` and we win."

So 00R7 is not a wrong turn — it is the engine, and the extra content of 05UV
over it is exactly the finite-generation argument for `J`.  A prover should
NOT attack 05UV directly.

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

**THE ACTUAL DEPENDENCY CHAIN, read off the Stacks proofs on 2026-07-27.**
This replaces the guess that the missing pieces are "Tor, the local criterion
and a limit argument", which is right in outline and wrong in the one place
that decides how to attack this:

    05UV (10.128.9)  =  00R7  +  "J is finitely generated"  +  046Y (10.128.4)
    00R7 (10.128.8)  =  Noetherian approximation (10.127.13, 10.128.3)
                        +  00MP (10.99.15)
    046Y (10.128.4)  =  the same approximation  +  10.99.1

Two consequences, both of which change the plan:

* **The local criterion is only ever needed in the NOETHERIAN setting.**
  00MP is 10.99.15 verbatim: *"Let `R`, `S`, `S'` be **Noetherian** local
  rings and `R → S → S'` local homomorphisms, `M` an `S'`-module, `𝔪 ⊂ R` the
  maximal ideal.  Assume (1) `M` finite over `S'`, (2) `M ≠ 0`, (3) `M/𝔪M`
  flat over `S/𝔪S`, (4) `M` flat over `R`.  Then `S` is flat over `R` and `M`
  is a flat `S`-module."*  Note `M` **finite**, not finitely presented, and
  every ring Noetherian.  Its own proof cites only Nakayama (10.20.1) and the
  local-criterion family 10.99.7 / 10.99.10 / 10.39.15.
* **Therefore the "ideally separated" hazard flagged above is real but
  AVOIDABLE.**  The Stacks route never proves a non-Noetherian local
  criterion; it approximates down to the Noetherian case where ideal
  separatedness is free.  So the whole non-Noetherian content of this leaf is
  the **approximation/limit machinery**, not the criterion.  Anyone planning
  to build a non-Noetherian local criterion for this leaf is building
  something the source does not use.

**What a safe cut would therefore need**, in increasing order of cost:
`00MP` (a self-contained Noetherian statement, writable today over
`IsNoetherianRing` and `IsLocalRing` with no new definitions); `10.99.1`
(likewise); and the approximation half — writing an essentially-of-finite-type
local ring map as a filtered colimit of such maps of **Noetherian** local
rings (10.127.13), plus descent of flatness along that colimit (10.128.3).
The last two are the ones that need a design decision about how to state a
filtered system of rings in this development, and getting that wrong
manufactures a useless or false leaf, so they are deliberately NOT cut here.

**AXIS SEARCHED** (so the next reader knows what this audit did NOT look
at): routes that cut this leaf along ring-theoretic machinery — Tor, the
local criterion of flatness, and Noetherian approximation/spreading out.
All three are absent from the pin, by the greps above and below, re-run
2026-07-27.

**THE ONE UNSEARCHED AXIS HAS NOW BEEN SEARCHED, AND IT IS A DEAD END**
(2026-07-27).  The previous version of this paragraph named it as "the first
thing to check before anyone commits to building Tor": whether the CONSUMER
always supplies a Noetherian base, in which case the far cheaper Noetherian
form 00MP would suffice.  **It does not.**  The chain is
`flat_of_flat_of_flat_quotientMap` → `flat_stalkMap_of_flat_stalkMap_fiberMapOver`
→ `flat_of_flat_fiberMap` → `flat_mulByNat` → `AbelianSchemeStruct`, and
`AbelianSchemeStruct f` is declared in `Modularity/AbelianScheme.lean` for an
arbitrary `f : A ⟶ S` with `S : Scheme.{u}` and NO finiteness hypothesis on
`S` whatever — that file contains zero occurrences of the string
"Noetherian".  Every consumer above it quantifies over arbitrary `S` too:
`Modularity/TateModule.lean` (`exists_nsmul_eq_geomFibrePt` and the whole
`TatePt` development), `ModularCurve/X0.lean`, and
`Modularity/KhareWintenberger.lean`.  The refuting check is one line:
`grep -rn "Noetherian" Fermat/FLT/Modularity/AbelianScheme.lean`; a hit means
this note has gone stale.

So 00MP does not reach the consumer either, and replacing this leaf by the
Noetherian form would require adding a Noetherian hypothesis to
`AbelianSchemeStruct` and propagating it through four owned files — a
cut-level restatement, not a simplification of this leaf.  05UV stands.
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

/-! ### The stalk of a scheme-theoretic fibre

The three-line summary of this block: `Scheme.Hom.fiberι` is a
**preimmersion** (mathlib, `AlgebraicGeometry/Fiber.lean`), so its stalk maps
are surjective; the pullback square defining the fibre forces `𝔪_s` into the
kernel; and the reverse inclusion is supplied by the universal property of
`Spec` of a LOCAL ring (`AlgebraicGeometry.SpecToEquivOfLocalRing`), which
produces a morphism `Spec (𝒪_{X,x}/𝔪_s𝒪_{X,x}) ⟶ X_s` splitting it.

That third step is the whole trick, and it is why this needed no
stalk-of-pullback theory (which mathlib indeed does not have — the greps on
`exists_ringEquiv_stalkMap_fiberMapOver` below were re-run 2026-07-27 and are
still empty).  `Scheme.stalkClosedPointTo` turns the morphism into a ring map
`𝒪_{X_s,z} ⟶ 𝒪_{X,x}/𝔪_s𝒪_{X,x}` which is a LEFT INVERSE of the surjection, so
the surjection is injective as well.
-/

section FiberStalk

/-- Every stalk of `Spec κ(s)` has trivial maximal ideal: `Spec` of a field has
one point and its stalk there is that field. -/
theorem maximalIdeal_stalk_residueField_eq_bot {S : Scheme.{u}} (s : S)
    (w : Spec (S.residueField s)) :
    IsLocalRing.maximalIdeal ((Spec (S.residueField s)).presheaf.stalk w) = ⊥ := by
  obtain rfl : w = IsLocalRing.closedPoint _ := Subsingleton.elim (α := PrimeSpectrum _) _ _
  have hbij := ConcreteCategory.bijective_of_isIso
    (AlgebraicGeometry.stalkClosedPointIso (S.residueField s)).hom
  haveI : IsLocalHom (AlgebraicGeometry.stalkClosedPointIso (S.residueField s)).hom.hom :=
    _root_.IsLocalHom.of_surjective _ hbij.2
  rw [← IsLocalRing.maximalIdeal_comap
      (AlgebraicGeometry.stalkClosedPointIso (S.residueField s)).hom.hom,
    IsLocalRing.maximalIdeal_eq_bot, Ideal.comap_bot_of_injective _ hbij.1]

/-- A `stalkCongr` isomorphism maps the maximal ideal into the maximal ideal —
it is an isomorphism, hence surjective, hence local. -/
theorem stalkCongr_mem_maximalIdeal {Y : Scheme.{u}} {y y' : Y} (h : Inseparable y y')
    {a : Y.presheaf.stalk y} (ha : a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) :
    (Y.presheaf.stalkCongr h).hom.hom a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y') := by
  haveI : IsLocalHom (Y.presheaf.stalkCongr h).hom.hom :=
    _root_.IsLocalHom.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2
  exact _root_.map_nonunit _ _ ha

/-- The stalk map of `Spec κ(s) ⟶ S` kills the maximal ideal: it is a local
homomorphism into a ring whose maximal ideal is `⊥`. -/
theorem stalkMap_fromSpecResidueField_eq_zero {S : Scheme.{u}} (s : S)
    (w : Spec (S.residueField s)) {a : S.presheaf.stalk (S.fromSpecResidueField s w)}
    (ha : a ∈ IsLocalRing.maximalIdeal (S.presheaf.stalk (S.fromSpecResidueField s w))) :
    ((S.fromSpecResidueField s).stalkMap w).hom a = 0 := by
  have h := _root_.map_nonunit ((S.fromSpecResidueField s).stalkMap w).hom a ha
  rw [maximalIdeal_stalk_residueField_eq_bot] at h
  simpa using h

variable {X S : Scheme.{u}} (p : X ⟶ S) (s : S) (z : p.fiber s)

/-- The ideal `𝔪_s · 𝒪_{X,x}` at the point `x = fiberι z`. -/
noncomputable abbrev fiberStalkIdeal : Ideal (X.presheaf.stalk (p.fiberι s z)) :=
  (IsLocalRing.maximalIdeal (S.presheaf.stalk (p (p.fiberι s z)))).map
    (p.stalkMap (p.fiberι s z)).hom

/-- `p` sends a point of the fibre to the image of the residue-field point;
this is `Scheme.Hom.fiber_fac` read on points. -/
theorem map_fiberι_eq_fromSpecResidueField :
    p (p.fiberι s z) = S.fromSpecResidueField s (p.fiberToSpecResidueField s z) := by
  rw [← Scheme.Hom.comp_apply, p.fiber_fac s, Scheme.Hom.comp_apply]

/-- **`𝔪_s · 𝒪_{X,x}` dies in the stalk of the fibre.**  The composite
`𝒪_{S,s} → 𝒪_{X,x} → 𝒪_{X_s,z}` factors through `κ(s)` by the pullback square,
and `κ(s)` has trivial maximal ideal. -/
theorem fiberStalkIdeal_le_ker :
    fiberStalkIdeal p s z ≤ RingHom.ker ((p.fiberι s).stalkMap z).hom := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, RingHom.mem_ker]
  have hc : ((p.fiberι s).stalkMap z).hom ((p.stalkMap (p.fiberι s z)).hom a)
      = ((p.fiberι s ≫ p).stalkMap z).hom a := by
    rw [Scheme.Hom.stalkMap_comp]; rfl
  rw [hc, Scheme.Hom.stalkMap_congr_hom _ _ (p.fiber_fac s) z, Scheme.Hom.stalkMap_comp]
  show ((p.fiberToSpecResidueField s).stalkMap z).hom
      (((S.fromSpecResidueField s).stalkMap (p.fiberToSpecResidueField s z)).hom
        ((S.presheaf.stalkCongr
          (Inseparable.of_eq (map_fiberι_eq_fromSpecResidueField p s z))).hom.hom a)) = 0
  rw [stalkMap_fromSpecResidueField_eq_zero s _ (stalkCongr_mem_maximalIdeal _ ha), map_zero]

/-- `fiberι` is a preimmersion, so it is surjective on stalks. -/
theorem surjective_fiberι_stalkMap :
    Function.Surjective ((p.fiberι s).stalkMap z).hom :=
  (p.fiberι s).stalkMap_surjective z

/-- A point of `p.fiber s` lies over `s`. -/
theorem map_fiberι_eq_base : p (p.fiberι s z) = s := by
  rw [map_fiberι_eq_fromSpecResidueField, Scheme.fromSpecResidueField_apply]

/-- **THE STALK OF THE FIBRE IS THE QUOTIENT OF THE STALK** (PROVEN
2026-07-27): `𝒪_{X_s, z} ≅ 𝒪_{X,x} ⧸ 𝔪_s·𝒪_{X,x}` where `x = fiberι z`, and the
isomorphism carries the quotient map to the stalk map of `fiberι`.

*Surjectivity* is `IsPreimmersion (p.fiberι s)`, *`𝔪_s ⊆ ker`* is
`fiberStalkIdeal_le_ker`, and *`ker ⊆ 𝔪_s`* is the interesting half: write
`A = 𝒪_{X,x} ⧸ 𝔪_s·𝒪_{X,x}`, a LOCAL ring because `p.stalkMap x` is a local
homomorphism, and build `ψ : Spec A ⟶ X_s` out of the two legs
`Spec A ⟶ Spec 𝒪_{X,x} ⟶ X` and `Spec A ⟶ Spec κ(s)` — the second exists
precisely because `𝔪_s` dies in `A` by construction.  Then
`Scheme.stalkClosedPointTo ψ` is a left inverse of the surjection, by the
universal property `AlgebraicGeometry.SpecToEquivOfLocalRing` (morphisms out of
`Spec` of a local ring = a point plus a local homomorphism on the stalk).  A
left inverse makes the surjection injective, so it is an isomorphism. -/
theorem exists_ringEquiv_stalk_fiber :
    ∃ e : (X.presheaf.stalk (p.fiberι s z) ⧸ fiberStalkIdeal p s z) ≃+*
          ((p.fiber s).presheaf.stalk z),
      e.toRingHom.comp (Ideal.Quotient.mk _) = ((p.fiberι s).stalkMap z).hom := by
  haveI hnt : Nontrivial (X.presheaf.stalk (p.fiberι s z) ⧸ fiberStalkIdeal p s z) :=
    Ideal.Quotient.nontrivial_iff.mpr (IsLocalRing.map_maximalIdeal_lt_top _).ne
  haveI hlr : IsLocalRing (X.presheaf.stalk (p.fiberι s z) ⧸ fiberStalkIdeal p s z) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  set A : CommRingCat.{u} :=
    CommRingCat.of (X.presheaf.stalk (p.fiberι s z) ⧸ fiberStalkIdeal p s z) with hA
  set mk0 : X.presheaf.stalk (p.fiberι s z) ⟶ A :=
    CommRingCat.ofHom (Ideal.Quotient.mk (fiberStalkIdeal p s z)) with hmk0
  haveI : IsLocalHom mk0.hom := _root_.IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hps : p (p.fiberι s z) = s := map_fiberι_eq_base p s z
  set cg : S.presheaf.stalk s ⟶ S.presheaf.stalk (p (p.fiberι s z)) :=
    (S.presheaf.stalkCongr (Inseparable.of_eq hps.symm)).hom with hcg
  set f0 : S.presheaf.stalk s ⟶ A := cg ≫ p.stalkMap (p.fiberι s z) ≫ mk0 with hf0def
  have hf0 : ∀ a ∈ IsLocalRing.maximalIdeal (S.presheaf.stalk s), f0.hom a = 0 := by
    intro a ha
    have h1 : cg.hom a ∈ IsLocalRing.maximalIdeal (S.presheaf.stalk (p (p.fiberι s z))) :=
      stalkCongr_mem_maximalIdeal _ ha
    have h2 : (p.stalkMap (p.fiberι s z)).hom (cg.hom a) ∈ fiberStalkIdeal p s z :=
      Ideal.mem_map_of_mem _ h1
    show mk0.hom ((p.stalkMap (p.fiberι s z)).hom (cg.hom a)) = 0
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr h2
  set lif : S.residueField s ⟶ A :=
    CommRingCat.ofHom (Ideal.Quotient.lift _ f0.hom hf0) with hlifdef
  have hlif : S.residue s ≫ lif = f0 := by
    ext a
    rfl
  set α : Spec A ⟶ X := Spec.map mk0 ≫ X.fromSpecStalk (p.fiberι s z) with hα
  set β : Spec A ⟶ Spec (S.residueField s) := Spec.map lif with hβ
  have hLHS : α ≫ p = Spec.map (p.stalkMap (p.fiberι s z) ≫ mk0) ≫
      S.fromSpecStalk (p (p.fiberι s z)) := by
    rw [hα, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc]
  have hRHS : β ≫ S.fromSpecResidueField s = Spec.map (p.stalkMap (p.fiberι s z) ≫ mk0) ≫
      S.fromSpecStalk (p (p.fiberι s z)) := by
    rw [hβ, Scheme.fromSpecResidueField, ← Spec.map_comp_assoc, hlif, hf0def, hcg,
      TopCat.Presheaf.stalkCongr_hom, Spec.map_comp_assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hsq : α ≫ p = β ≫ S.fromSpecResidueField s := by rw [hLHS, hRHS]
  set ψ : Spec A ⟶ p.fiber s := Limits.pullback.lift α β hsq with hψ
  have hψ1 : ψ ≫ p.fiberι s = α := Limits.pullback.lift_fst _ _ _
  have hψ1' : ψ ≫ p.fiberι s =
      (SpecToEquivOfLocalRing X A).symm ⟨p.fiberι s z, mk0, inferInstance⟩ := by
    rw [hψ1, hα]; rfl
  have hEq : (SpecToEquivOfLocalRing X A) (ψ ≫ p.fiberι s) =
      ⟨p.fiberι s z, mk0, inferInstance⟩ := by
    rw [hψ1']; exact Equiv.apply_symm_apply _ _
  obtain ⟨h₁, h₂⟩ := SpecToEquivOfLocalRing_eq_iff.mp hEq
  have hcp : ψ (IsLocalRing.closedPoint A) = z :=
    (p.fiberι s).isEmbedding.injective (by simpa [Scheme.Hom.comp_apply] using h₁)
  set θ : (p.fiber s).presheaf.stalk z ⟶ A :=
    ((p.fiber s).presheaf.stalkCongr (Inseparable.of_eq hcp.symm)).hom ≫
      Scheme.stalkClosedPointTo ψ with hθdef
  have h₁' : p.fiberι s (ψ (IsLocalRing.closedPoint A)) = p.fiberι s z := h₁
  have hstar : (p.fiberι s).stalkMap (ψ (IsLocalRing.closedPoint A)) ≫
      Scheme.stalkClosedPointTo ψ =
      (X.presheaf.stalkCongr (Inseparable.of_eq h₁')).hom ≫ mk0 := by
    rw [← Scheme.stalkClosedPointTo_comp]
    exact h₂
  have hθ : (p.fiberι s).stalkMap z ≫ θ = mk0 := by
    rw [hθdef, Scheme.Hom.stalkMap_congr_point_assoc (p.fiberι s) z
      (ψ (IsLocalRing.closedPoint A)) hcp.symm, hstar]
    simp only [TopCat.Presheaf.stalkCongr_hom,
      TopCat.Presheaf.stalkSpecializes_comp_assoc,
      TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
  have hker : RingHom.ker ((p.fiberι s).stalkMap z).hom ≤ fiberStalkIdeal p s z := by
    intro a ha
    have h0 : mk0.hom a = θ.hom (((p.fiberι s).stalkMap z).hom a) := by
      rw [← hθ]; rfl
    rw [RingHom.mem_ker] at ha
    rw [ha, map_zero] at h0
    exact (Ideal.Quotient.eq_zero_iff_mem).mp h0
  refine ⟨RingEquiv.ofBijective (Ideal.Quotient.lift _ ((p.fiberι s).stalkMap z).hom
    (fun a ha => RingHom.mem_ker.mp (fiberStalkIdeal_le_ker p s z ha))) ⟨?_, ?_⟩, ?_⟩
  · intro u v huv
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective v
    simp only [Ideal.Quotient.lift_mk] at huv
    rw [Ideal.Quotient.eq]
    apply hker
    rw [RingHom.mem_ker, map_sub, huv, sub_self]
  · intro w
    obtain ⟨a, rfl⟩ := surjective_fiberι_stalkMap p s z w
    exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  · ext a
    rfl

/-- `exists_ringEquiv_stalk_fiber` with the point of `X` named separately, so
that a consumer does not have to reduce `fiberι z` to it. -/
theorem exists_ringEquiv_stalk_fiber' (x : X) (hz : p.fiberι s z = x) :
    ∃ e : (X.presheaf.stalk x ⧸
            (IsLocalRing.maximalIdeal (S.presheaf.stalk (p x))).map (p.stalkMap x).hom) ≃+*
          ((p.fiber s).presheaf.stalk z),
      e.toRingHom.comp (Ideal.Quotient.mk _) =
        ((X.presheaf.stalkCongr (Inseparable.of_eq hz.symm)).hom ≫
          (p.fiberι s).stalkMap z).hom := by
  subst hz
  obtain ⟨e, he⟩ := exists_ringEquiv_stalk_fiber p s z
  refine ⟨e, ?_⟩
  rw [he]
  simp

end FiberStalk

/-- `fiberMapOver` commutes with the two embeddings of the fibres: this is
`pullback.lift_fst` for the map defining it. -/
theorem fiberMapOver_fiberι {X Y S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    (u : X ⟶ Y) (h : u ≫ q = p) (s : S) :
    fiberMapOver u h s ≫ q.fiberι s = p.fiberι s ≫ u :=
  Limits.pullback.lift_fst _ _ _

/-- `fiberMapOver_fiberι` read on points. -/
theorem fiberι_fiberMapOver_apply {X Y S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    (u : X ⟶ Y) (h : u ≫ q = p) (s : S) (w : p.fiber s) :
    q.fiberι s (fiberMapOver u h s w) = u (p.fiberι s w) := by
  rw [← Scheme.Hom.comp_apply, fiberMapOver_fiberι, Scheme.Hom.comp_apply]

/-- The stalk-level square attached to `fiberMapOver`, i.e. `fiberMapOver_fiberι`
after `Scheme.Hom.stalkMap`. -/
theorem stalkMap_fiberMapOver_square {X Y S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    (u : X ⟶ Y) (h : u ≫ q = p) (s : S) (w : p.fiber s) :
    (q.fiberι s).stalkMap (fiberMapOver u h s w) ≫ (fiberMapOver u h s).stalkMap w
      = (Y.presheaf.stalkCongr
          (Inseparable.of_eq (fiberι_fiberMapOver_apply u h s w))).hom ≫
        u.stalkMap (p.fiberι s w) ≫ (p.fiberι s).stalkMap w := by
  rw [← Scheme.Hom.stalkMap_comp, ← Scheme.Hom.stalkMap_comp,
    Scheme.Hom.stalkMap_congr_hom _ _ (fiberMapOver_fiberι u h s) w]
  rfl

/-- **The stalk of the fibre is the quotient of the stalk, compatibly with
`u`** (PROVEN 2026-07-27 — general scheme theory, no abelian varieties: this
is the whole mathematical content of
`flat_quotientMap_of_flat_stalkMap_fiberMapOver` below, which is PROVEN over
it with no residue).

**HOW IT IS PROVEN, and the survey below that it CORRECTS.**  Everything the
old survey said about mathlib is still true — there is no stalk of a fibre and
no stalk of a pullback anywhere in the pin, and all four of its greps were
re-run empty on 2026-07-27.  What the survey got wrong was the inference:
*this leaf does not need stalk-of-pullback theory at all.*  The input it needs
is the universal property of `Spec` of a LOCAL ring,
`AlgebraicGeometry.SpecToEquivOfLocalRing` (`AlgebraicGeometry/Stalk.lean`),
which says morphisms `Spec R ⟶ X` out of a local ring are exactly a point of
`X` plus a local homomorphism on its stalk.

With that, `exists_ringEquiv_stalk_fiber` above does the whole job in three
moves: `Scheme.Hom.fiberι` is a PREIMMERSION, so it is surjective on stalks;
the pullback square puts `𝔪_s` in the kernel (`fiberStalkIdeal_le_ker`); and
the reverse inclusion comes from building `ψ : Spec (𝒪_{X,x}/𝔪_s𝒪_{X,x}) ⟶ X_s`
— which exists precisely because `𝔪_s` dies in that quotient — and reading
`Scheme.stalkClosedPointTo ψ` as a LEFT INVERSE of the surjection.  A left
inverse forces injectivity, so the surjection is an isomorphism.

The reusable moral, and the reason this is worth recording rather than just
deleting: an "absent from the pin" survey ranged over the wrong axis.  It
searched for the OBJECT (a stalk of a pullback) and concluded correctly that
mathlib has none; it never asked whether the object could be avoided by a
UNIVERSAL PROPERTY, which is where the pin was in fact rich.

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

**The point-equality obligation flagged below never had to be paid.**  The
general lemma `exists_ringEquiv_stalk_fiber'` is stated for an ARBITRARY point
`z` of the fibre together with a hypothesis `p.fiberι s z = x`, so it applies
directly at `fiberMapOver u rfl s ((u ≫ q).asFiber x)` and the identification
of that point with `q.asFiber (u x)` is simply never needed.  The note below
is kept because its warning is still correct for anyone who states the leaf
the other way round.

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

**STILL ABSENT from the pin, with the refuting greps** (re-run 2026-07-27,
all still empty — but see the correction at the top: their absence turned out
not to matter):
`grep -n stalk Mathlib/AlgebraicGeometry/Fiber.lean` and the same over
`PullbackCarrier.lean` and `Pullbacks.lean` each return NOTHING, and
`grep -rn "stalkMap_pullback\|pullback_stalk" Mathlib/` is empty.  Mathlib
computes the **residue field** of a point of a fibre product
(`PullbackCarrier.Triplet.tensor`) and the **sections** of one
(the `pushoutSection` block, `Morphisms/Flat.lean:183–509`), but never the
stalk.

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
              eY.toRingHom)
    := by
  have hzx : (u ≫ q).fiberι ((u ≫ q) x) ((u ≫ q).asFiber x) = x :=
    Scheme.Hom.fiberι_asFiber (u ≫ q) x
  have hzy : q.fiberι ((u ≫ q) x)
      (fiberMapOver u rfl ((u ≫ q) x) ((u ≫ q).asFiber x)) = u x := by
    rw [fiberι_fiberMapOver_apply, hzx]
  have hcomp : ((u ≫ q).stalkMap x).hom
      = (u.stalkMap x).hom.comp (q.stalkMap (u x)).hom := by
    rw [Scheme.Hom.stalkMap_comp]; rfl
  obtain ⟨ep, hep⟩ :=
    exists_ringEquiv_stalk_fiber' (u ≫ q) ((u ≫ q) x) ((u ≫ q).asFiber x) x hzx
  obtain ⟨eq0, heq0⟩ :=
    exists_ringEquiv_stalk_fiber' q ((u ≫ q) x)
      (fiberMapOver u rfl ((u ≫ q) x) ((u ≫ q).asFiber x)) (u x) hzy
  have hI : (IsLocalRing.maximalIdeal (S.presheaf.stalk ((u ≫ q) x))).map
        ((u ≫ q).stalkMap x).hom
      = (IsLocalRing.maximalIdeal (S.presheaf.stalk ((u ≫ q) x))).map
        ((u.stalkMap x).hom.comp (q.stalkMap (u x)).hom) :=
    congrArg (fun f => Ideal.map f (IsLocalRing.maximalIdeal
      (S.presheaf.stalk ((u ≫ q) x)))) hcomp
  have hSQ : u.stalkMap x ≫ ((X.presheaf.stalkCongr (Inseparable.of_eq hzx.symm)).hom ≫
        ((u ≫ q).fiberι ((u ≫ q) x)).stalkMap ((u ≫ q).asFiber x))
      = ((Y.presheaf.stalkCongr (Inseparable.of_eq hzy.symm)).hom ≫
          (q.fiberι ((u ≫ q) x)).stalkMap
            (fiberMapOver u rfl ((u ≫ q) x) ((u ≫ q).asFiber x))) ≫
        (fiberMapOver u rfl ((u ≫ q) x)).stalkMap ((u ≫ q).asFiber x) := by
    rw [Category.assoc, Scheme.Hom.stalkMap_congr_point_assoc u x
      ((u ≫ q).fiberι ((u ≫ q) x) ((u ≫ q).asFiber x)) hzx.symm,
      stalkMap_fiberMapOver_square u rfl ((u ≫ q) x) ((u ≫ q).asFiber x)]
    simp only [TopCat.Presheaf.stalkCongr_hom,
      TopCat.Presheaf.stalkSpecializes_comp_assoc]
  refine ⟨eq0, ep.symm.trans (Ideal.quotEquivOfEq hI), ?_⟩
  refine RingHom.ext fun w => ?_
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective w
  have hY : eq0 (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal (S.presheaf.stalk ((u ≫ q) x))).map
          (q.stalkMap (u x)).hom) b)
      = ((Y.presheaf.stalkCongr (Inseparable.of_eq hzy.symm)).hom ≫
          (q.fiberι ((u ≫ q) x)).stalkMap
            (fiberMapOver u rfl ((u ≫ q) x) ((u ≫ q).asFiber x))).hom b :=
    DFunLike.congr_fun heq0 b
  have hX : ep (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal (S.presheaf.stalk ((u ≫ q) x))).map
          ((u ≫ q).stalkMap x).hom) ((u.stalkMap x).hom b))
      = ((X.presheaf.stalkCongr (Inseparable.of_eq hzx.symm)).hom ≫
          ((u ≫ q).fiberι ((u ≫ q) x)).stalkMap ((u ≫ q).asFiber x)).hom
            ((u.stalkMap x).hom b) :=
    DFunLike.congr_fun hep ((u.stalkMap x).hom b)
  have hsq' := DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp hSQ) b
  have key : ep (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal (S.presheaf.stalk ((u ≫ q) x))).map
          ((u ≫ q).stalkMap x).hom) ((u.stalkMap x).hom b))
      = ((fiberMapOver u rfl ((u ≫ q) x)).stalkMap ((u ≫ q).asFiber x)).hom
          (eq0 (Ideal.Quotient.mk
            ((IsLocalRing.maximalIdeal (S.presheaf.stalk ((u ≫ q) x))).map
              (q.stalkMap (u x)).hom) b)) := by
    rw [hX, hY]
    exact hsq'
  rw [Ideal.quotientMap_mk]
  show Ideal.Quotient.mk _ ((u.stalkMap x).hom b)
      = (ep.symm.trans (Ideal.quotEquivOfEq hI))
          (((fiberMapOver u rfl ((u ≫ q) x)).stalkMap ((u ≫ q).asFiber x)).hom
            (eq0 (Ideal.Quotient.mk
              ((IsLocalRing.maximalIdeal (S.presheaf.stalk ((u ≫ q) x))).map
                (q.stalkMap (u x)).hom) b)))
  rw [RingEquiv.trans_apply, ← key, RingEquiv.symm_apply_apply, Ideal.quotEquivOfEq_mk]

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

**STATUS of the three leaves, 2026-07-27 (updated).**  Two of the three are
closed OUTRIGHT, and the third is the only thing left in this whole cut:

* `essFinitePresentation_stalkMap` — **PROVEN**, and its docstring records
  that `stableUnderComposition` for `EssFinitePresentation` turned out not to
  be needed at all.
* `flat_quotientMap_of_flat_stalkMap_fiberMapOver` — **PROVEN**, and now
  axiom-clean all the way down: its one-time leaf
  `exists_ringEquiv_stalkMap_fiberMapOver` is itself **PROVEN**, over the
  general `exists_ringEquiv_stalk_fiber` (the stalk of a scheme-theoretic
  fibre is the stalk modulo `𝔪_s`).  That closes the entire scheme-theoretic
  half of the fibre criterion.
* `flat_of_flat_of_flat_quotientMap` — still open, and now the SOLE remaining
  input of `flat_of_flat_fiberMap`.  It is pure commutative algebra; nothing
  above it mentions schemes any more.

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
(sorry leaf — **FALSE AS STATED**; see the FALSITY AUDIT below.  The
mathematics is finished and sitting one line away; what blocks this leaf is
its own SIGNATURE, and repairing it is a CLUSTER-LEVEL change that this
declaration cannot make alone.)

**THE HOIST THIS LEAF ASKED FOR IS DONE (2026-07-27).**  The earlier version
of this docstring said the proof —
`GaloisRepresentation.Modularity.isRegularLocalRing_stalk_of_smooth_over_field`
— was unreachable because it lived in `Modularity/KhareWintenberger.lean`,
strictly DOWNSTREAM of this module.  It has been HOISTED, with its entire
nine-declaration dependency cone, into `Fermat/FLT/Modularity/RegularStalks.lean`,
which this file now `public import`s (see the import block) and which
`KhareWintenberger.lean` imports in turn.  Nothing was restated or reproved:
the declarations moved byte-identically, in the same namespace, and all nine
are sorry-free.  So there is NO open mathematics under this leaf anywhere in
the tree, and the `public import` above is deliberate and load-bearing for the
repair below even though nothing in THIS file consumes it yet.

**FALSITY AUDIT (2026-07-27).**  The hypothesis `[Field K]` does not say what
it looks like it says.  `K : CommRingCat` is a BUNDLED object, carrying its own
ring structure `K.str`; `Spec K` is built from `K.str`.  But `[Field K]`
elaborates to `Field ↥K` — a class on the CARRIER TYPE — and its `CommRing`
is `Field.toCommRing`, which is a DIFFERENT instance.  Lean says so itself:
attempting to close this leaf from the hoisted theorem produces

    X ⟶ Spec (@CommRingCat.of ↑K CommRingCat.instCommRingObjForgetRingHomCarrier)
    X ⟶ Spec (@CommRingCat.of ↑K Field.toCommRing)

as two non-unifiable types.  They are not a defeq nuisance; they are two
genuinely different schemes, because nothing ties the two ring structures
together.  `[Field K]` therefore asserts only that the carrier TYPE of `K`
happens to admit SOME field structure, which constrains `K.str` not at all.

THE COUNTEREXAMPLE.  Take `K := CommRingCat.of (ZMod 4)`, so `↥K = ZMod 4`, a
four-element type.  A `Field ↥K` instance exists — transport the field
structure of `GaloisField 2 2` along any bijection `ZMod 4 ≃ GaloisField 2 2`
— so the hypothesis `[Field K]` is satisfied while `K.str` is the ordinary
`ZMod 4`.  Take `X := Spec K` and `g := 𝟙`, which is smooth.  `ZMod 4` is
local with maximal ideal `(2)`, so the stalk at the unique point is `ZMod 4`
itself, which is not even a domain — and a regular local ring IS a domain
(`GaloisRepresentation.Modularity.isDomain_of_isRegularLocalRing`, PROVEN in
`KhareWintenberger.lean`).  So the conclusion fails.  The same counterexample
refutes the sibling `ringKrullDim_stalk_eq_of_isFinite_endo` below.

**THE REPAIR, AND WHY IT IS NOT MADE HERE.**  Replace `{K : CommRingCat.{u}}
[Field K]` with `{K : Type u} [Field K]` and `Spec K` with
`Spec (CommRingCat.of K)` — the idiom `Modularity/AbelianScheme.lean` uses
everywhere and the one mathlib uses.  Under that signature this leaf closes in
ONE LINE,

    GaloisRepresentation.Modularity.isRegularLocalRing_stalk_of_smooth_over_field
      g ‹Smooth g› x

with no mathematics left to do.  But the signature is shared by a CLUSTER of
seven declarations in this file, which pass `K` to one another:
`isRegularLocalRing_stalk_of_smooth`, `ringKrullDim_stalk_eq_of_isFinite_endo`,
`flat_of_finite_fibres_endo`, `finite_preimage_mulByNat_of_field_prime_to_char`,
`finite_preimage_mulByNat_of_field_char`, `finite_preimage_mulByNat_of_field`
and `flat_mulByNat_of_field`.  Changing one forces changing all: this leaf's
only consumer, `flat_of_finite_fibres_endo`, also calls
`ringKrullDim_stalk_eq_of_isFinite_endo`, which had a live owner in another
worktree when this was found, so a unilateral restatement here would collide
head-on with theirs.  Nothing OUTSIDE this file consumes any of the seven, so
the repair is contained — it just needs ONE owner for the whole cluster. -/
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
and the leaf is far cheaper than it looks.

**THAT SURVEY IS NOW REFUTED, ON EXACTLY THE TERMS IT SET (2026-07-27).  STEP 3
IS NOT NEEDED AT ALL, AND THE ROUTE BELOW USES NO SCHEME DIMENSION THEORY.**
The grep that missed it was `grep -rn "dim" Mathlib/AlgebraicGeometry/`: the
scheme-level statement is stated in terms of `Order.coheight`, and `coheight`
does not contain the substring `dim`.  Every name below was located and read on
2026-07-27; each line ends with the check that would refute it.

1. **`ringKrullDim (X.presheaf.stalk x) = Order.coheight x`** — this exists, as
   `AlgebraicGeometry.ringKrullDim_stalk_eq_coheight`, `@[stacks 02IZ]`, in
   `Mathlib/AlgebraicGeometry/Properties.lean` (with the affine case
   `idealHeight_eq_coheight` just above it).  So both sides of this leaf are
   ideal HEIGHTS, and the whole question is a statement about heights of primes
   under a module-finite ring extension.
   *Refute with:* `grep -n ringKrullDim_stalk_eq_coheight
   .lake/packages/mathlib/Mathlib/AlgebraicGeometry/Properties.lean`.
2. **`height q ≤ height p + height (q in the fibre)`** is FREE — no going-down,
   no normality: `Ideal.height_le_height_add_of_liesOver`, `@[stacks 00OM]`,
   `Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean`.  Combined with the fibre
   being zero-dimensional — which is now PROVEN, as
   `ringKrullDim_quotient_map_maximalIdeal_stalkMap` above — this gives
   `dim 𝒪_{X,x} ≤ dim 𝒪_{X,u x}` outright.  **Half of this leaf costs nothing.**
3. **The reverse inequality is `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`**,
   `@[stacks 00ON]`, Matsumura 13.B Th. 19(2), same file, which upgrades step 2
   to an EQUALITY given `[Algebra.HasGoingDown A B]`.
4. **Going-down is available from NORMALITY, not from flatness** (using flatness
   would be circular — this leaf exists to prove flatness).  Krull's going-down
   theorem is in the pin as an INSTANCE:
   `Mathlib/RingTheory/IntegralClosure/GoingDown.lean:48`, `@[stacks 00H8]`,
   `[IsDomain S] [FaithfulSMul R S] [Algebra.IsIntegral R S] [IsIntegrallyClosed R] →
   Algebra.HasGoingDown R S`.  `u` finite gives `Algebra.IsIntegral`; `X`
   integral gives `IsDomain` and injectivity.
   *Refute with:* `grep -n "stacks 00H8"
   .lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/GoingDown.lean`.

**SO THE WHOLE LEAF NOW RESTS ON ONE PIECE OF COMMUTATIVE ALGEBRA:**

> **a regular local ring is integrally closed** (regular ⟹ normal),

which is what supplies `[IsIntegrallyClosed A]` for `A = Γ(V)` on an affine
chart of the smooth `X`.  That is absent from mathlib — `grep -rn
IsIntegrallyClosed Mathlib/ | grep -i "regular\|smooth\|normal"` returns only
prose in `IntegralClosure/IntegrallyClosed.lean`, and there is no `IsNormalRing`
class at all — and absent from this project and from `~/cs/FLT`.  But it is a
STANDARD, SELF-CONTAINED, MATHLIB-SHAPED statement, and it is enormously smaller
than "a dimension theory of schemes".  Mathlib even provides the localisation
step for it: `Mathlib/RingTheory/LocalProperties/IntegrallyClosed.lean` lets
`IsIntegrallyClosed A` be checked at the localisations of `A`.

Note this route ALSO discards steps 1–3 of the survey above: irreducibility is
still wanted (to make the charts domains), but SURJECTIVITY of `u` is not used,
and neither is `dim 𝒪_{X,x} + dim closure{x} = dim X`.

**Whoever takes this leaf should read the docstring of
`exists_isWeaklyRegular_span_eq_maximalIdeal` below first**: the same hoist of
`Modularity/KhareWintenberger.lean`'s regular-local-ring material that closes
`isRegularLocalRing_stalk_of_smooth` is what would put `IsRegularLocalRing` on
the charts' localisations here, so all three leaves share one piece of
bookkeeping. -/
theorem ringKrullDim_stalk_eq_of_isFinite_endo {X : Scheme.{u}} {K : CommRingCat.{u}} [Field K]
    (g : X ⟶ Spec K) [Smooth g] [IsProper g] [GeometricallyConnected g]
    (u : X ⟶ X) [IsFinite u] (x : X) :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (X.presheaf.stalk (u x)) :=
  sorry

/-! ### The three sub-leaves of miracle flatness at the ring level

`flat_of_isRegularLocalRing_of_ringKrullDim_eq` below is PROVEN over the three
statements in this block.  See its docstring for why the previously recorded
"`Tor`-free affine route" is NOT a route to it. -/

/-- **THE EMBEDDING DIMENSION DROPS BY EXACTLY ONE ON QUOTIENTING BY
`x ∈ 𝔪 ∖ 𝔪²`** (**PROVEN 2026-07-27**).

`isRegularLocalRing_quotient_span_singleton` (in `Modularity/RegularStalks.lean`)
says `R ⧸ (x)` is again regular local; this records the numerical half its
statement drops, namely that its embedding dimension is `m` when that of `R` is
`m + 1`.  That is what lets the induction of
`exists_isWeaklyRegular_span_eq_maximalIdeal_aux` below descend.

The `≤` half is the exchange lemma `exists_finset_card_span_insert_eq_maximalIdeal`
(a generating set of `𝔪` of size `m + 1` containing `x`, whose image without `x`
generates `𝔪 (R ⧸ (x))`).  The `≥` half is Krull's height theorem in the form
`ringKrullDim_le_ringKrullDim_quotient_add_encard`, transported across
regularity of `R ⧸ (x)` — which is exactly why that instance is a hypothesis
here rather than being derived: the caller already has it in hand. -/
theorem spanFinrank_maximalIdeal_quotient_span_singleton {R : Type u} [CommRing R]
    [IsRegularLocalRing R] {x : R}
    (hxm : x ∈ IsLocalRing.maximalIdeal R)
    (hx2 : x ∉ (IsLocalRing.maximalIdeal R) ^ 2) (m : ℕ)
    (hn : (IsLocalRing.maximalIdeal R).spanFinrank = m + 1)
    [IsRegularLocalRing (R ⧸ Ideal.span {x})] :
    (IsLocalRing.maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank = m := by
  classical
  have hdim : ringKrullDim R = ((m + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R), hn]
  obtain ⟨T, hTcard, hTspan⟩ :=
    GaloisRepresentation.Modularity.exists_finset_card_span_insert_eq_maximalIdeal hxm hx2 hn
  set I : Ideal R := Ideal.span {x} with hI
  have hIm : I ≤ IsLocalRing.maximalIdeal R := by rw [hI, Ideal.span_le]; simpa using hxm
  have hInt : I ≠ ⊤ := fun h =>
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (h ▸ hIm))
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hInt
  have hmapmax : (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk I)
      = IsLocalRing.maximalIdeal (R ⧸ I) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hsr : (IsLocalRing.maximalIdeal (R ⧸ I)).spanFinrank ≤ m := by
    have himg : IsLocalRing.maximalIdeal (R ⧸ I)
        = Ideal.span ((Ideal.Quotient.mk I) '' (T : Set R)) := by
      rw [← hmapmax, ← hTspan, Ideal.map_span, Set.image_insert_eq]
      have hx0 : (Ideal.Quotient.mk I) x = 0 := by
        rw [Ideal.Quotient.eq_zero_iff_mem, hI]; exact Ideal.subset_span rfl
      rw [hx0, Ideal.span_insert_zero]
    rw [himg]
    refine le_trans (Submodule.spanFinrank_span_le_ncard_of_finite
      ((T : Set R).toFinite.image _)) ?_
    exact le_trans (Set.ncard_image_le (T : Set R).toFinite) (by simp [hTcard])
  have hjac : ({x} : Set R) ⊆ Ring.jacobson R := by
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    show y ∈ Ring.jacobson R
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
    exact hxm
  have hkey : ringKrullDim R ≤ ringKrullDim (R ⧸ I) + 1 := by
    have h := ringKrullDim_le_ringKrullDim_quotient_add_encard ({x} : Set R) hjac
    simpa [hI] using h
  have hdimq : ((m : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ I) := by
    rw [hdim] at hkey
    push_cast at hkey
    exact ENat.WithBot.add_le_add_one_right_iff.mp hkey
  refine le_antisymm hsr ?_
  have hfr := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R ⧸ I)
  have h2 : ((m : ℕ) : WithBot ℕ∞)
      ≤ (((IsLocalRing.maximalIdeal (R ⧸ I)).spanFinrank : ℕ) : WithBot ℕ∞) := by
    rw [hfr]; exact hdimq
  exact_mod_cast h2

/-- **THE INDUCTION CARRIER OF `exists_isWeaklyRegular_span_eq_maximalIdeal`**
(**PROVEN 2026-07-27**) — the same statement with the length measured against
the embedding dimension `n` rather than against `ringKrullDim R`, so that the
strong induction on `n` can be stated at all.  The two agree by
`IsRegularLocalRing.spanFinrank_maximalIdeal`, which is the DEFINITION of
`IsRegularLocalRing`. -/
theorem exists_isWeaklyRegular_span_eq_maximalIdeal_aux (n : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R],
      (IsLocalRing.maximalIdeal R).spanFinrank = n →
      ∃ rs : List R, Ideal.span {r | r ∈ rs} = IsLocalRing.maximalIdeal R ∧
        rs.length = n ∧ RingTheory.Sequence.IsWeaklyRegular R rs := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro R _ _ hn
    match n, hn, ih with
    | 0, hn, _ =>
      refine ⟨[], ?_, rfl, RingTheory.Sequence.IsWeaklyRegular.nil R R⟩
      have hbot : IsLocalRing.maximalIdeal R = ⊥ :=
        (Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).1 hn
      rw [hbot]
      simp
    | (m + 1), hn, ih =>
      -- `𝔪 ⊄ 𝔪²`, else Nakayama forces `𝔪 = ⊥` and the embedding dimension is `0`.
      have hm2 : ¬ (IsLocalRing.maximalIdeal R ≤ (IsLocalRing.maximalIdeal R) ^ 2) := by
        intro hle
        have hb : IsLocalRing.maximalIdeal R = ⊥ := by
          refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R) _
            (IsNoetherian.noetherian _) ?_ ?_
          · rwa [smul_eq_mul, ← pow_two]
          · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
        rw [hb] at hn
        simp at hn
      obtain ⟨x, hxm, hx2⟩ := Set.not_subset.1 hm2
      set I : Ideal R := Ideal.span {x} with hI
      have hIm : I ≤ IsLocalRing.maximalIdeal R := by rw [hI, Ideal.span_le]; simpa using hxm
      have hInt : I ≠ ⊤ := fun h =>
        (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (h ▸ hIm))
      haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hInt
      haveI : IsLocalRing (R ⧸ I) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
      haveI hreg : IsRegularLocalRing (R ⧸ I) :=
        GaloisRepresentation.Modularity.isRegularLocalRing_quotient_span_singleton hxm hx2
      have hsrq : (IsLocalRing.maximalIdeal (R ⧸ I)).spanFinrank = m :=
        spanFinrank_maximalIdeal_quotient_span_singleton hxm hx2 m hn
      obtain ⟨rs', hspan', hlen', hreg'⟩ := ih m (Nat.lt_succ_self m) (R ⧸ I) hsrq
      -- lift `rs'` along the surjection `R → R ⧸ I`
      obtain ⟨rs, hrs⟩ : ∃ rs : List R, rs.map (Ideal.Quotient.mk I) = rs' := by
        clear hspan' hlen' hreg'
        induction rs' with
        | nil => exact ⟨[], rfl⟩
        | cons a l ihl =>
          obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective a
          obtain ⟨l', hl'⟩ := ihl
          exact ⟨b :: l', by simp [hb, hl']⟩
      refine ⟨x :: rs, ?_, ?_, ?_⟩
      · -- `(x) + (rs) = 𝔪`, read off by taking `comap` of the corresponding
        -- identity in `R ⧸ (x)`, where `ker (mk) = (x) ≤ 𝔪` absorbs the join.
        have hmapofl : (Ideal.span {r | r ∈ rs}).map (Ideal.Quotient.mk I)
            = IsLocalRing.maximalIdeal (R ⧸ I) := by
          rw [show (Ideal.span {r | r ∈ rs}) = Ideal.ofList rs from rfl,
            Ideal.map_ofList, hrs]
          exact hspan'
        have hcm : Ideal.comap (Ideal.Quotient.mk I)
            (IsLocalRing.maximalIdeal (R ⧸ I)) = IsLocalRing.maximalIdeal R := by
          rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
            Ideal.Quotient.mk_surjective,
            Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
            ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
          exact sup_eq_left.2 hIm
        have hsup : Ideal.span {r | r ∈ rs} ⊔ I = IsLocalRing.maximalIdeal R := by
          rw [← hcm, ← hmapofl,
            Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
            ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
        rw [show (Ideal.span {r | r ∈ (x :: rs)}) =
            Ideal.ofList (x :: rs) from rfl,
          Ideal.ofList_cons, ← hI, sup_comm]
        exact hsup
      · have hlrs : rs.length = m := by rw [← hlen', ← hrs, List.length_map]
        simp [hlrs]
      · -- `x` is a nonzerodivisor because `R` is a DOMAIN; the tail is the
        -- induction hypothesis transported along `R ⧸ (x) ≃ₗ QuotSMulTop x R`.
        have hx0 : x ≠ 0 := by
          intro h
          exact hx2 (h ▸ Ideal.zero_mem _)
        haveI : IsDomain R := GaloisRepresentation.Modularity.isDomain_of_isRegularLocalRing R
        have hxreg : IsSMulRegular R x := mul_right_injective₀ hx0
        have hstep : RingTheory.Sequence.IsWeaklyRegular (QuotSMulTop x R) rs := by
          have hquot : RingTheory.Sequence.IsWeaklyRegular (R := R) (R ⧸ I) rs := by
            rw [← RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff (R ⧸ I) (R ⧸ I) rs]
            rw [show (rs.map (algebraMap R (R ⧸ I))) = rs' from hrs]
            exact hreg'
          have he : (R ⧸ I) ≃ₗ[R] QuotSMulTop x R :=
            Submodule.quotEquivOfEq _ _ (by
              rw [hI, ← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top])
          exact (he.isWeaklyRegular_congr rs).1 hquot
        exact (RingTheory.Sequence.isWeaklyRegular_cons_iff R x rs).2 ⟨hxreg, hstep⟩

/-- **A REGULAR LOCAL RING HAS A REGULAR SYSTEM OF PARAMETERS, AND IT IS A
REGULAR SEQUENCE** (**PROVEN 2026-07-27** — pure commutative algebra; would be
at home in `Mathlib/RingTheory/RegularLocalRing/`).

`𝔪_R` is generated by `dim R` elements *by the definition of
`IsRegularLocalRing`* (`spanFinrank_maximalIdeal`); the CONTENT of this leaf is
that some such generating list is a weakly regular sequence.

**IT WAS BLOCKED BY DECLARATION ORDER, NOT BY MATHEMATICS, AND THE HOIST THAT
UNBLOCKED IT LANDED ON 2026-07-27.**  The induction is on `n = (𝔪_R).spanFinrank`
and lives in `exists_isWeaklyRegular_span_eq_maximalIdeal_aux` above:

* `n = 0`: `𝔪_R = ⊥`, so `R` is a field and `rs = []` works
  (`IsWeaklyRegular R []` is vacuous).
* `n + 1`: take `t ∈ 𝔪_R \ 𝔪_R²`.  Then `R ⧸ (t)` is regular local of dimension
  `n`, and `t` is a nonzerodivisor because a regular local ring is a DOMAIN and
  `t ≠ 0`.  Recurse in `R ⧸ (t)`, lift the resulting list along
  `Ideal.Quotient.mk`, and prepend `t`; `isWeaklyRegular_cons_iff` plus the
  identification `QuotSMulTop t R ≃ₗ R ⧸ (t)` and
  `isWeaklyRegular_map_algebraMap_iff` assemble the two halves.

All three non-trivial inputs now live in `Modularity/RegularStalks.lean`, which
is UPSTREAM of this module and which this file `public import`s:
`isRegularLocalRing_quotient_span_singleton` and the exchange lemma
`exists_finset_card_span_insert_eq_maximalIdeal` were hoisted there out of
`Modularity/KhareWintenberger.lean` with the cone of
`isRegularLocalRing_stalk_of_smooth_over_field`, and
`isDomain_of_isRegularLocalRing` — which that hoist deliberately left behind, as
a sibling consumer of the exchange lemma rather than a member of the cone — was
hoisted after it on 2026-07-27, byte-identical, precisely for this leaf.

The check that would refute this note:

    grep -n 'theorem isDomain_of_isRegularLocalRing\b' \
         Fermat/FLT/Modularity/RegularStalks.lean
    grep -n 'theorem isRegularLocalRing_quotient_span_singleton' \
         Fermat/FLT/Modularity/RegularStalks.lean

Mathlib itself has neither: its entire `IsRegularLocalRing` API is three lemmas
in `RingTheory/RegularLocalRing/Defs.lean` (`of_ringEquiv`,
`of_spanFinrank_maximalIdeal_le`, `iff_finrank_cotangentSpace`) plus the PID
instance — re-checked 2026-07-27 with
`grep -rn IsRegularLocalRing .lake/packages/mathlib/Mathlib/`. -/
theorem exists_isWeaklyRegular_span_eq_maximalIdeal (R : Type u) [CommRing R]
    [IsRegularLocalRing R] :
    ∃ rs : List R, Ideal.span {r | r ∈ rs} = IsLocalRing.maximalIdeal R ∧
      (rs.length : WithBot ℕ∞) = ringKrullDim R ∧
      RingTheory.Sequence.IsWeaklyRegular R rs := by
  obtain ⟨rs, hspan, hlen, hreg⟩ := exists_isWeaklyRegular_span_eq_maximalIdeal_aux _ R rfl
  exact ⟨rs, hspan, by rw [hlen, IsRegularLocalRing.spanFinrank_maximalIdeal], hreg⟩

/-- **UNMIXEDNESS: IN A COHEN–MACAULAY LOCAL RING EVERY SYSTEM OF PARAMETERS IS
A REGULAR SEQUENCE** (sorry leaf — pure commutative algebra, Matsumura
*Commutative Ring Theory* 17.4 / Stacks 00N7.  **This is the single genuinely
missing statement under this node**, and it is the ONLY thing
`isWeaklyRegular_map_of_ringKrullDim_eq` below now rests on.)

**COHEN–MACAULAYNESS IS SPELLED OUT, DELIBERATELY, RATHER THAN NAMED.**  `hCM`
says verbatim: some weakly regular sequence of length `dim T` generates `𝔪_T`.
That is `depth T = dim T` written without a `depth` predicate, and writing it
this way is what makes the leaf stateable at all — **there is no depth or
Cohen–Macaulay layer anywhere in this repository**, and mathlib's
`RingTheory/Regular/Depth.lean` is a 10-line file with zero declarations.  A
prover who would rather have the predicate should vendor
`~/cs/FLT/FLT/Patching/Utils/Depth.lean` (259 lines, UNVENDORED — see the
correction in the docstring below) and restate this in terms of `Module.depth`;
the mathematics is unaffected.

**WHY THIS SHAPE AND NOT `[IsRegularLocalRing T]`.**  The previous cut demanded
the conclusion for a regular local `T`, which conflates two different facts:
that `T` is Cohen–Macaulay, and that a Cohen–Macaulay ring has this unmixedness
property.  The FIRST is no longer open — `exists_isWeaklyRegular_span_eq_maximalIdeal`
above (**PROVEN 2026-07-27**) produces exactly the sequence `hCM` asks for — so
carrying `IsRegularLocalRing T` here would make a prover re-derive something
already available.  Note also that `φ` and `R` have disappeared entirely: this
is a statement about ONE local ring.

**WHY THE OBVIOUS INDUCTION FAILS, and it is the trap to avoid.**  The first
step is easy and needs only that `T` is a domain: `ys` being a system of
parameters forces `dim T ⧸ (ys.head) = dim T - 1`, so the head lies in no
minimal prime.  What breaks is the INDUCTION, because `T ⧸ (t)` is in general
**not regular** — take `T = k⟦x⟧` and `t = x²`, a system of parameters whose
quotient is not even reduced.  So the induction hypothesis must be
Cohen–Macaulayness, which is precisely why this leaf is stated with `hCM`
rather than with regularity: `hCM` is a hypothesis that SURVIVES the quotient,
and `IsRegularLocalRing` is not.  A prover must not plan an induction that keeps
`IsRegularLocalRing` on the quotient. -/
theorem isWeaklyRegular_of_ringKrullDim_quotient_eq_zero {T : Type u} [CommRing T]
    [IsLocalRing T] [IsNoetherianRing T] (ys : List T)
    (hCM : ∃ zs : List T, Ideal.span {z | z ∈ zs} = IsLocalRing.maximalIdeal T ∧
      (zs.length : WithBot ℕ∞) = ringKrullDim T ∧ RingTheory.Sequence.IsWeaklyRegular T zs)
    (hlen : (ys.length : WithBot ℕ∞) = ringKrullDim T)
    (hfib : ringKrullDim (T ⧸ Ideal.span {y | y ∈ ys}) = 0) :
    RingTheory.Sequence.IsWeaklyRegular T ys :=
  sorry

/-- **A SYSTEM OF PARAMETERS OF A REGULAR LOCAL RING IS A REGULAR SEQUENCE**
(**PROVEN 2026-07-27** over the unmixedness leaf
`isWeaklyRegular_of_ringKrullDim_quotient_eq_zero` immediately above, into which
all of its remaining content has been moved).

The hypotheses say exactly that `rs.map φ` is a system of parameters of `T`:
`hspan` makes `Ideal.span (rs.map φ) = Ideal.map φ 𝔪_R`, `hfib` says that ideal
is `𝔪_T`-primary (dimension `0` quotient), and `hlen` with `hdim` says the list
has exactly `dim T` entries.  The classical chain is `T` regular ⟹ `T`
Cohen–Macaulay ⟹ every system of parameters is a regular sequence, and the CUT
made here is exactly at the arrow in the middle:

* `T` regular ⟹ `T` Cohen–Macaulay is **PROVEN**, as
  `exists_isWeaklyRegular_span_eq_maximalIdeal` above — the sequence it produces
  is precisely the `hCM` witness the unmixedness leaf asks for.
* Cohen–Macaulay ⟹ unmixedness is the open leaf
  `isWeaklyRegular_of_ringKrullDim_quotient_eq_zero` above, where the discussion
  of why the naive induction fails now lives.

All this declaration still does is match the two up: `Ideal.map_ofList` turns
`Ideal.span (rs.map φ)` into `Ideal.map φ 𝔪_R`, so `hfib` is literally the
zero-dimensionality hypothesis, and `hlen` with `hdim` is literally the length
hypothesis.

**ABSENT EVERYWHERE, re-checked 2026-07-27 with the refuting greps.**
`grep -rl CohenMacaulay .lake/packages/mathlib/Mathlib/` is empty and
`Mathlib/RingTheory/Regular/Depth.lean` is a 10-line file with ZERO
declarations.

**CORRECTION (2026-07-27) — `Module.depth` IS NOT VENDORED INTO THIS PROJECT.**
The previous version of this paragraph said `~/cs/FLT`'s
`FLT/Patching/Utils/Depth.lean` was "already vendored into this project and
consumed by `Fermat/FLT/Modularity/PatchingVendored/System.lean`".  That is
FALSE, and a prover who believed it would go looking for an API that is not
there.  The refuting greps, both run on 2026-07-27:

    ls Fermat/FLT/Modularity/PatchingVendored/          # no Depth.lean
    grep -rn "Module.depth" Fermat/                     # only PROSE, no code

`PatchingVendored/System.lean:258-261` names `Module.depth` in a COMMENT
explaining what it did *instead* of vendoring it, and
`Modularity/Patching.lean:6749` says outright that the depth endgame was
"deliberately not vendored".  So there is **no depth layer anywhere in this
repository**, and `~/cs/FLT`'s file remains an unvendored external reference.

That file (259 lines) does contain `Module.depth`, `Module.length_le_depth`,
`Module.depth_le_dim`, `Module.depth_le_of_free` and
`RingTheory.Sequence.isWeaklyRegular_of_free`, and it is the natural thing to
vendor first — but note it proves only `depth ≤ dim`, which is the WRONG
inequality here.

**SO THE ROUTE, IN THE ORDER THE PIECES ARE NEEDED** — and this is why the cut
above is where it is.  What is required is `dim ≤ depth` for a regular local
ring, and that half is now **available, not missing**:
`exists_isWeaklyRegular_span_eq_maximalIdeal` above (**PROVEN 2026-07-27**)
produces a weakly regular sequence generating `𝔪_T` of length exactly `dim T`,
which is precisely a witness that `depth T ≥ dim T`, i.e. that a regular local
ring is Cohen–Macaulay.  What remained genuinely new was only the UNMIXEDNESS
half, and that is now the separate leaf
`isWeaklyRegular_of_ringKrullDim_quotient_eq_zero` above — stated WITHOUT a
depth predicate, by writing Cohen–Macaulayness out as "some weakly regular
sequence of length `dim` generates `𝔪`", so that no `Depth.lean` vendoring is
needed merely to state it.  Proving it is the real work, and it is all that is
left under this node. -/
theorem isWeaklyRegular_map_of_ringKrullDim_eq {R T : Type u} [CommRing R] [CommRing T]
    [IsRegularLocalRing R] [IsRegularLocalRing T] (φ : R →+* T) [IsLocalHom φ] (rs : List R)
    (hspan : Ideal.span {r | r ∈ rs} = IsLocalRing.maximalIdeal R)
    (hlen : (rs.length : WithBot ℕ∞) = ringKrullDim R)
    (hdim : ringKrullDim T = ringKrullDim R)
    (hfib : ringKrullDim (T ⧸ Ideal.map φ (IsLocalRing.maximalIdeal R)) = 0) :
    RingTheory.Sequence.IsWeaklyRegular T (rs.map φ) := by
  -- the image list spans exactly the extended ideal, so `hfib` IS the
  -- zero-dimensionality hypothesis of the unmixedness leaf
  have himg : Ideal.span {y | y ∈ rs.map φ} = Ideal.map φ (IsLocalRing.maximalIdeal R) := by
    rw [show (Ideal.span {y | y ∈ rs.map φ}) = Ideal.ofList (rs.map φ) from rfl,
      ← Ideal.map_ofList]
    exact congrArg (Ideal.map φ) hspan
  refine isWeaklyRegular_of_ringKrullDim_quotient_eq_zero (rs.map φ)
    (exists_isWeaklyRegular_span_eq_maximalIdeal T) ?_ ?_
  · rw [List.length_map, hlen, hdim]
  · rw [himg]; exact hfib

section LocalCriterionOfFlatness

open scoped TensorProduct

variable {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]

/-- **THE POWER STEP OF THE LOCAL CRITERION OF FLATNESS** (sorry leaf — pure
commutative algebra; Stacks 051C + 00MK in the NILPOTENT case, Matsumura
*Commutative Ring Theory* 22.1/22.2).

`t` a nonzerodivisor on `R` and on `T` with `T ⧸ (φ t)` flat over `R ⧸ (t)`;
then `T ⧸ (φ t)^n` is flat over `R ⧸ (t)^n` for every `n`.

**WHY THIS IS ONE OF THE TWO HALVES.**  Together with
`mem_baseChange_sup_of_flat_quotientMap_pow` below it proves the atom
`flat_of_flat_quotient_isSMulRegular`.  It is the half that needs NO
separatedness and NO Artin–Rees: inside `A := R ⧸ (t^n)` the ideal
`(t)/(t^n)` is NILPOTENT, and for a nilpotent ideal the local criterion of
flatness is unconditional.

**THE ROUTE.**  Induct on `n`.  The classical formulation is: for `A` a ring,
`J ⊆ A` nilpotent and `M` an `A`-module, `M` is `A`-flat as soon as `M ⧸ JM`
is `A ⧸ J`-flat and `Tor₁^A(A ⧸ J, M) = 0`.  Instantiated at `A = R ⧸ (t^n)`,
`J = (t)/(t^n)`, `M = T ⧸ (φ t)^n`:

* `M ⧸ JM = T ⧸ (φ t)` is flat over `A ⧸ J = R ⧸ (t)` — that is `hflat`;
* the `Tor₁` vanishing is exactly regularity.  Over `A` the module `A ⧸ J`
  has the periodic-style presentation `A --(t^{n-1})--> A --t--> A → A ⧸ J → 0`,
  so `Tor₁^A(A ⧸ J, M) = (0 :ₘ t) / t^{n-1} M`; and `φ t` being a
  nonzerodivisor on `T` gives `(0 :_{T ⧸ (φ t)^n} φ t) = (φ t)^{n-1} T ⧸ (φ t)^n`,
  which is precisely `t^{n-1} M`.  So the quotient is `0`.

**THERE IS NO `Tor` TO USE.**  Mathlib has no `Tor` long exact sequence for
modules (checked 2026-07-27: `Mathlib/RingTheory/Flat/` has no `Tor` at all,
and there is no `LocalCriterion` file anywhere in the library).  So a prover
must run the argument through `Module.Flat.iff_rTensor_injective` /
`iff_lTensor_injective`, which expresses `Tor₁(R ⧸ I, M) = 0` as injectivity
of `I ⊗ M → M`, exactly as the atom's original docstring already advised.
`Mathlib/RingTheory/TensorProduct/Quotient.lean` (already in this file's import
cone) supplies the identifications that replace the change-of-rings
isomorphisms: `Algebra.TensorProduct.quotIdealMapEquivQuotTensor`,
`quotientTensorEquiv`, `tensorQuotientEquiv`, `Ideal.subtype_rTensor_range`.

**FAITHFULNESS.**  `ψn` is passed as DATA together with its intertwining
`hψn`, for the same reason `ψ` is in the atom: the map is
`Ideal.quotientMap (Ideal.span {(algebraMap R T t)^n}) (algebraMap R T) _`, and
taking it as data keeps the (one-line) construction of its side condition at
the call site.  Since `Ideal.Quotient.mk` is surjective, `hψn` determines `ψn`
uniquely, so this is not a weakening. -/
theorem flat_quotientMap_pow_of_flat_quotientMap
    [IsNoetherianRing R] [IsNoetherianRing T]
    {t : R} (hRt : IsSMulRegular R t) (hTt : IsSMulRegular T (algebraMap R T t))
    (ψ : R ⧸ Ideal.span {t} →+* T ⧸ Ideal.span {algebraMap R T t})
    (hψ : ψ.comp (Ideal.Quotient.mk (Ideal.span {t}))
      = (Ideal.Quotient.mk (Ideal.span {algebraMap R T t})).comp (algebraMap R T))
    (hflat : ψ.Flat) (n : ℕ)
    (ψn : R ⧸ Ideal.span {t ^ n} →+* T ⧸ Ideal.span {(algebraMap R T t) ^ n})
    (hψn : ψn.comp (Ideal.Quotient.mk (Ideal.span {t ^ n}))
      = (Ideal.Quotient.mk (Ideal.span {(algebraMap R T t) ^ n})).comp (algebraMap R T)) :
    ψn.Flat :=
  sorry

/-- **THE DESCENT MODULO `t ^ n`** (sorry leaf — pure commutative algebra;
the elementwise core of Stacks 00MK / Matsumura 22.3).

Write `I = (t) ⊆ R`, `𝔞 ⊆ R` an ideal, and let `ξ ∈ T ⊗[R] 𝔞` map to `0` in
`T` under `𝔞 ⊗ T → T`.  Given only that `T ⧸ (φ t)^n` is FLAT over
`R ⧸ (t)^n`, this says

  `ξ ∈ baseChange T (𝔞 ⊓ (t^n)) + (φ t)^n · (T ⊗[R] 𝔞)`.

**WHY THIS IS THE OTHER HALF, AND WHY THE STATEMENT LOOKS LIKE THIS.**  The
consumer `mem_pow_smul_of_lTensor_ideal_eq_zero` below feeds Artin–Rees into
the first summand (`𝔞 ⊓ (t^n) ⊆ t^{n-k} 𝔞`) and `n ≥ m` into the second, and
then Krull's intersection theorem kills the kernel.  So this leaf is exactly
"the kernel dies modulo `t^n`, up to the Artin–Rees discrepancy", with the
discrepancy left explicit rather than estimated here — that is what makes the
two halves independent.

**THE ROUTE — a four-term chase, all four maps already in mathlib.**  Put
`J = (t^n) ⊆ R`, `J' = ((φ t)^n) ⊆ T`, `Rₙ = R ⧸ J`, `Tₙ = T ⧸ J'`,
`𝔞ₙ = 𝔞.map (Ideal.Quotient.mk J) ⊆ Rₙ`.  Consider

  `T ⊗[R] 𝔞  --a-->  Tₙ ⊗[R] 𝔞  --b-->  Tₙ ⊗[Rₙ] 𝔞ₙ  --c-->  Tₙ`.

* `c` is injective — this is `hpow` through `Module.Flat.iff_lTensor_injective`;
* `c ∘ b ∘ a` sends `ξ` to the image in `Tₙ` of `lTensor T 𝔞.subtype ξ = 0`,
  so `b (a ξ) = 0`;
* `ker b` is the image of `Tₙ ⊗[R] ↥(𝔞 ⊓ J)`, i.e.
  `Submodule.baseChange Tₙ (comap 𝔞.subtype J)`, by right-exactness of
  `Tₙ ⊗[R] -` applied to `(𝔞 ⊓ J) → 𝔞 → 𝔞ₙ → 0`
  (`Submodule.baseChange` IS that image: `Submodule.baseChange_eq_span`);
* `ker a = J' • ⊤`, by right-exactness of `- ⊗[R] 𝔞` on `J' → T → Tₙ → 0`;
* `a` is surjective and carries `baseChange T P` onto `baseChange Tₙ P`, so
  `a⁻¹ (baseChange Tₙ P) = baseChange T P ⊔ ker a`.  That is the conclusion.

**WHAT MATHLIB SUPPLIES** (all already in this file's import cone):
`Submodule.baseChange`, `baseChange_eq_span`, `baseChange_mono`,
`tmul_mem_baseChange_of_mem`, `toBaseChange_surjective`
(`Mathlib/LinearAlgebra/TensorProduct/Tower.lean`);
`TensorProduct.quotientTensorEquiv`, `tensorQuotientEquiv`,
`quotTensorEquivQuotSMul`, `Ideal.subtype_rTensor_range`
(`Mathlib/{LinearAlgebra,RingTheory}/TensorProduct/Quotient.lean`);
`LinearMap.lTensor_exact` / `rTensor_exact` and the right-exactness API in
`Mathlib/LinearAlgebra/TensorProduct/RightExactness.lean`.

**NO HYPOTHESIS ON `R`, `T` BEYOND COMMUTATIVITY IS NEEDED HERE.**  Noetherian,
local and `IsLocalHom` are used only by the consumer (Artin–Rees needs
noetherian; Krull needs local).  Keeping them off this leaf is deliberate: it
makes clear that the separatedness input enters exactly once, in the
consumer.

**THE CONCRETE LEAN ATTACK — DO NOT TRY TO COMPUTE `ker b` DIRECTLY**
(worked out 2026-07-27; identifying `ker b` as an image is the step that turns
a two-page chase into a two-week one).  Write `N` for the target submodule
(the `⊔` in the conclusion) and `Q := (T ⊗[R] 𝔞) ⧸ N`.  Build TWO maps and
never mention a kernel:

* `F : T ⊗[R] 𝔞 → Tₙ ⊗[Rₙ] 𝔞ₙ`, `y ⊗ a ↦ (mk y) ⊗ (mk a)`.  This is
  `R`-balanced because `mk (r • y) = mk r • mk y` on both sides, so
  `TensorProduct.lift` builds it.
* `G : Tₙ ⊗[Rₙ] 𝔞ₙ → Q`, `ȳ ⊗ ā ↦ ⟦y ⊗ a⟧` for ANY lifts.  Well defined
  exactly because of the two summands of `N`, one each:
  changing the lift of `ȳ` moves the value by `(y - y') ⊗ a ∈ J' • ⊤`;
  changing the lift of `ā` moves it by `y ⊗ (a - a')` with
  `a - a' ∈ 𝔞 ⊓ J`, i.e. into `baseChange T (comap 𝔞.subtype J)`
  (`Submodule.tmul_mem_baseChange_of_mem`).  **This is where the shape of the
  conclusion comes from, and it is why the two summands are exactly these.**

Then `G ∘ F = Submodule.mkQ N` (check on `y ⊗ a`), so `F ξ = 0` gives `ξ ∈ N`
with no kernel computation at all.  And `F ξ = 0` is the only place flatness
is used: `c : Tₙ ⊗[Rₙ] 𝔞ₙ → Tₙ`, the `lift (lsmul ∘ 𝔞ₙ.subtype)` of
`Module.Flat.iff_lift_lsmul_comp_subtype_injective`, is INJECTIVE by `hpow`,
and `c (F ξ)` is the image in `Tₙ` of `lift (lsmul ∘ 𝔞.subtype) ξ`, which is
`0` by `hξ`.

**THE INSTANCE HAZARD ON THIS ROUTE**, since it is what will actually cost
time: `Q` is a `T`-module, and `G`'s source is an `Rₙ`-module, so a bare
`TensorProduct.lift` for `G` needs `Module Rₙ Q` — which is NOT an instance
(`Module Rₙ M` from `Module Tₙ M` and `Algebra Rₙ Tₙ` does not fire on its
own).  Either supply it explicitly from `ψn.toAlgebra` and note `J' • ⊤ ≤ N`
makes `Q` a `Tₙ`-module, or build `F` and `G` as bare `AddMonoidHom`s — only
additivity is used above. -/
theorem mem_baseChange_sup_of_flat_quotientMap_pow
    {t : R} (n : ℕ)
    (hpow : ∀ ψn : R ⧸ Ideal.span {t ^ n} →+* T ⧸ Ideal.span {(algebraMap R T t) ^ n},
      ψn.comp (Ideal.Quotient.mk (Ideal.span {t ^ n}))
          = (Ideal.Quotient.mk (Ideal.span {(algebraMap R T t) ^ n})).comp (algebraMap R T) →
        ψn.Flat)
    {𝔞 : Ideal R} (ξ : T ⊗[R] ↥𝔞) (hξ : LinearMap.lTensor T 𝔞.subtype ξ = 0) :
    ξ ∈ (Submodule.comap 𝔞.subtype (Ideal.span {t ^ n} : Ideal R)).baseChange T
      ⊔ (Ideal.span {(algebraMap R T t) ^ n} • (⊤ : Submodule T (T ⊗[R] ↥𝔞))) :=
  sorry

/-- The base change of `t ^ m · 𝔞` sits inside `(φ t)^m · (T ⊗[R] 𝔞)`
(**PROVEN 2026-07-27**).  Pure bookkeeping: `1 ⊗ (r • x) = φ r • (1 ⊗ x)`,
and `φ` carries `(t^m)` into `(φ t)^m`. -/
theorem baseChange_smul_top_le_pow_smul_top (t : R) (m : ℕ) (𝔞 : Ideal R) :
    ((Ideal.span {t ^ m} : Ideal R) • (⊤ : Submodule R ↥𝔞)).baseChange T
      ≤ (Ideal.span {algebraMap R T t} : Ideal T) ^ m •
        (⊤ : Submodule T (T ⊗[R] ↥𝔞)) := by
  rw [Submodule.baseChange_eq_span, Submodule.span_le]
  rintro _ ⟨q, hq, rfl⟩
  simp only [TensorProduct.mk_apply, SetLike.mem_coe]
  refine Submodule.smul_induction_on hq ?_ ?_
  · intro r hr x _
    have hr' : algebraMap R T r ∈ (Ideal.span {algebraMap R T t} : Ideal T) ^ m := by
      rw [Ideal.span_singleton_pow, ← map_pow]
      rw [Ideal.mem_span_singleton] at hr ⊢
      exact map_dvd _ hr
    have key : (1 : T) ⊗ₜ[R] (r • x) = algebraMap R T r • ((1 : T) ⊗ₜ[R] x) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← TensorProduct.smul_tmul,
        Algebra.algebraMap_eq_smul_one]
    rw [key]
    exact Submodule.smul_mem_smul hr' Submodule.mem_top
  · intro x y hx hy
    rw [TensorProduct.tmul_add]
    exact Submodule.add_mem _ hx hy

/-- **THE KERNEL OF `𝔞 ⊗ T → T` LIES IN EVERY POWER OF `(φ t)`**
(**PROVEN 2026-07-27** over the two leaves above — this is the ARTIN–REES half
of the local criterion of flatness).

Given `ξ ∈ T ⊗[R] 𝔞` killed by `𝔞 ⊗ T → T`, and any `m`, we get
`ξ ∈ (φ t)^m · (T ⊗[R] 𝔞)`.  Together with Krull's intersection theorem (in
`flat_of_flat_quotient_isSMulRegular` below) this forces `ξ = 0`, which is
flatness.

**THE PROOF, and the two mathlib facts it turns on.**  Artin–Rees
(`Ideal.exists_pow_inf_eq_pow_smul`, `Mathlib/RingTheory/Filtration.lean` —
it IS in the pin, contrary to what one might expect) gives `k` with
`(t)^n ⊓ 𝔞 = (t)^{n-k} • ((t)^k ⊓ 𝔞)` for `n ≥ k`; take `n = m + k`, so
`𝔞 ⊓ (t^n) ⊆ t^m 𝔞`.  Feeding that into
`mem_baseChange_sup_of_flat_quotientMap_pow` at this `n`, the first summand
lands in `(φ t)^m · (T ⊗ 𝔞)` by `baseChange_smul_top_le_pow_smul_top`, and the
second does because `n ≥ m`.

`ψ`, `hψ`, `hflat`, `hRt`, `hTt` are threaded through only to supply
`flat_quotientMap_pow_of_flat_quotientMap`. -/
theorem mem_pow_smul_of_lTensor_ideal_eq_zero
    [IsNoetherianRing R] [IsNoetherianRing T]
    {t : R} (hRt : IsSMulRegular R t) (hTt : IsSMulRegular T (algebraMap R T t))
    (ψ : R ⧸ Ideal.span {t} →+* T ⧸ Ideal.span {algebraMap R T t})
    (hψ : ψ.comp (Ideal.Quotient.mk (Ideal.span {t}))
      = (Ideal.Quotient.mk (Ideal.span {algebraMap R T t})).comp (algebraMap R T))
    (hflat : ψ.Flat)
    {𝔞 : Ideal R} (ξ : T ⊗[R] ↥𝔞)
    (hξ : LinearMap.lTensor T 𝔞.subtype ξ = 0) (m : ℕ) :
    ξ ∈ (Ideal.span {algebraMap R T t} : Ideal T) ^ m •
      (⊤ : Submodule T (T ⊗[R] ↥𝔞)) := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (Ideal.span {t} : Ideal R) (M := R) 𝔞
  set n := m + k with hn
  have hAR : ((Ideal.span {t} : Ideal R) ^ n • (⊤ : Submodule R R) ⊓ (𝔞 : Submodule R R))
      ≤ Submodule.map 𝔞.subtype ((Ideal.span {t ^ m} : Ideal R) • (⊤ : Submodule R ↥𝔞)) := by
    rw [hk n (by omega), show n - k = m from by omega]
    refine Submodule.smul_le.2 fun r hr y hy => ?_
    refine Submodule.mem_map.2 ⟨r • ⟨y, hy.2⟩, ?_, rfl⟩
    exact Submodule.smul_mem_smul (by rwa [Ideal.span_singleton_pow] at hr) Submodule.mem_top
  have hcomap : Submodule.comap 𝔞.subtype (Ideal.span {t ^ n} : Ideal R)
      ≤ (Ideal.span {t ^ m} : Ideal R) • (⊤ : Submodule R ↥𝔞) := by
    intro x hx
    have h1 : (x : R) ∈ (Ideal.span {t} : Ideal R) ^ n • (⊤ : Submodule R R)
        ⊓ (𝔞 : Submodule R R) := by
      refine ⟨?_, x.2⟩
      have hsmul : (Ideal.span {t} : Ideal R) ^ n • (⊤ : Submodule R R)
          = ((Ideal.span {t} : Ideal R) ^ n : Submodule R R) := by
        rw [smul_eq_mul, ← Ideal.one_eq_top, mul_one]
      rw [hsmul, Ideal.span_singleton_pow]
      exact hx
    obtain ⟨y, hy, hxy⟩ := Submodule.mem_map.1 (hAR h1)
    have hxy' : y = x := Subtype.ext hxy
    exact hxy' ▸ hy
  have hmem := mem_baseChange_sup_of_flat_quotientMap_pow (T := T) (t := t) n
    (fun ψn hψn => flat_quotientMap_pow_of_flat_quotientMap hRt hTt ψ hψ hflat n ψn hψn) ξ hξ
  have hle : (Submodule.comap 𝔞.subtype (Ideal.span {t ^ n} : Ideal R)).baseChange T
      ⊔ (Ideal.span {(algebraMap R T t) ^ n} • (⊤ : Submodule T (T ⊗[R] ↥𝔞)))
      ≤ (Ideal.span {algebraMap R T t} : Ideal T) ^ m •
        (⊤ : Submodule T (T ⊗[R] ↥𝔞)) := by
    refine sup_le ?_ ?_
    · exact (Submodule.baseChange_mono T hcomap).trans
        (baseChange_smul_top_le_pow_smul_top t m 𝔞)
    · refine Submodule.smul_mono_left ?_
      rw [← Ideal.span_singleton_pow]
      exact Ideal.pow_le_pow_right (by omega)
  exact hle hmem

end LocalCriterionOfFlatness

/-- **THE ONE-ELEMENT LOCAL CRITERION OF FLATNESS — THE ATOM**
(**PROVEN 2026-07-27** over the two leaves
`flat_quotientMap_pow_of_flat_quotientMap` and
`mem_baseChange_sup_of_flat_quotientMap_pow` stated immediately above —
pure commutative algebra; Matsumura *Commutative Ring Theory*
22.3 / Stacks 00MK in the length-one case.  Absent from mathlib, from
`~/cs/FLT` and from this project).

`R`, `T` noetherian local, `φ : R → T` a local homomorphism, `t ∈ 𝔪_R` a
nonzerodivisor on `R` and on `T`, and `T ⧸ tT` flat over `R ⧸ tR`.  Then `T` is
flat over `R`.

**THIS IS THE WHOLE CONTENT OF `flat_of_isWeaklyRegular_span_eq_maximalIdeal`
BELOW, WHICH IS NOW PROVEN OVER IT** (2026-07-27).  The list induction that
lemma's own docstring predicted to be "mechanical" is mechanical, and it is
written out in `flat_of_isWeaklyRegular_span_eq_maximalIdeal_aux` below: nothing
is left there but this statement.

**WHY THE INDUCED MAP IS PASSED AS DATA (`ψ`) RATHER THAN CONSTRUCTED.**  The
map `R ⧸ (t) → T ⧸ (φ t)` is `Ideal.quotientMap (Ideal.span {φ t}) φ h`, whose
`h : Ideal.span {t} ≤ (Ideal.span {φ t}).comap φ` would have to appear inside
this signature.  Taking `ψ` together with the intertwining `hψ` says exactly the
same thing, keeps the proof obligation at the call site where it is one line,
and lets a prover of this leaf use whichever description of `ψ` is convenient.

**FAITHFULNESS — the separatedness hypothesis is present, disguised as
`[IsNoetherianRing T] [IsLocalRing T] [IsLocalHom φ]`, and it is LOAD-BEARING.**
The classical criterion needs `T` to be `𝔪_R`-adically *ideally separated*; the
statement is false for an arbitrary `R`-module with a regular element acting
regularly.  Here it is automatic: `φ` local gives `𝔪_R T ⊆ 𝔪_T`, hence
`𝔪_R^n T ⊆ 𝔪_T^n`, so `⋂ₙ 𝔪_R^n T ⊆ ⋂ₙ 𝔪_T^n = 0` by Krull's intersection
theorem.  **A prover who weakens `T` to a bare `R`-module produces a FALSE
leaf.**

**WHAT MATHLIB HAS THAT A PROVER WILL WANT**, since there is no `Tor`:
`Module.Flat.iff_rTensor_injective` (`RingTheory/Flat/Basic.lean`) expresses
`Tor₁(R ⧸ I, M) = 0` as injectivity of `I ⊗ M → M`, which is enough to run the
argument without ever constructing derived functors;
`Module.Flat.of_isLocalized_maximal` and the equational criterion
(`RingTheory/Flat/EquationalCriterion.lean`) are the other two handles.
`RingHom.flat_algebraMap_iff` moves between `RingHom.Flat` and `Module.Flat`.

**THE CUT (2026-07-27), and what is still open.**  The classical proof splits
at exactly one place, and both halves are stated above:

1. `flat_quotientMap_pow_of_flat_quotientMap` — `T ⧸ (φ t)^n` is flat over
   `R ⧸ (t)^n` for all `n`.  This is the local criterion for a NILPOTENT
   ideal; no separatedness, no Artin–Rees.
2. `mem_baseChange_sup_of_flat_quotientMap_pow` — the elementwise descent of
   `ker(𝔞 ⊗ T → T)` modulo `t^n`, granted (1).

Everything else is now written out and PROVEN:
`mem_pow_smul_of_lTensor_ideal_eq_zero` feeds Artin–Rees
(`Ideal.exists_pow_inf_eq_pow_smul`) into (2), and this declaration closes with
Krull's intersection theorem
(`Ideal.iInf_pow_smul_eq_bot_of_isLocalRing`) applied to the FINITE `T`-module
`T ⊗[R] 𝔞` — finite because `𝔞` is finitely generated, which is why
`Module.Flat.iff_lTensor_injective` (finitely generated ideals only) rather
than `iff_lTensor_injective'` is the right entry point.

**WHERE THE SEPARATEDNESS HYPOTHESIS IS ACTUALLY SPENT.**  Precisely twice in
this proof, and nowhere in leaf (2): `[IsLocalHom φ]` + `htm` give
`(φ t) ≠ ⊤`, and `[IsLocalRing T] [IsNoetherianRing T]` give Krull's theorem
for `T ⊗[R] 𝔞`.  That is the formal counterpart of the classical
`⋂ₙ 𝔪_R^n T ⊆ ⋂ₙ 𝔪_T^n = 0` remark above. -/
theorem flat_of_flat_quotient_isSMulRegular {R T : Type u} [CommRing R] [CommRing T]
    [IsLocalRing R] [IsNoetherianRing R] [IsLocalRing T] [IsNoetherianRing T]
    (φ : R →+* T) [IsLocalHom φ] {t : R} (htm : t ∈ IsLocalRing.maximalIdeal R)
    (hRt : IsSMulRegular R t) (hTt : IsSMulRegular T (φ t))
    (ψ : R ⧸ Ideal.span {t} →+* T ⧸ Ideal.span {φ t})
    (hψ : ψ.comp (Ideal.Quotient.mk (Ideal.span {t}))
      = (Ideal.Quotient.mk (Ideal.span {φ t})).comp φ)
    (hflat : ψ.Flat) :
    φ.Flat := by
  letI : Algebra R T := φ.toAlgebra
  show Module.Flat R T
  rw [Module.Flat.iff_lTensor_injective]
  intro 𝔞 h𝔞
  haveI : Module.Finite R ↥𝔞 := Module.Finite.iff_fg.2 h𝔞
  haveI : Module.Finite T (TensorProduct R T ↥𝔞) := inferInstance
  rw [injective_iff_map_eq_zero]
  intro ξ hξ
  have hIne : (Ideal.span {φ t} : Ideal T) ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    exact ((IsLocalRing.mem_maximalIdeal _).1 htm) (isUnit_of_map_unit φ t hu)
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing
    (M := TensorProduct R T ↥𝔞) (Ideal.span {φ t}) hIne
  have hmem : ξ ∈ (⨅ i : ℕ, (Ideal.span {φ t} : Ideal T) ^ i •
      (⊤ : Submodule T (TensorProduct R T ↥𝔞))) := by
    refine Submodule.mem_iInf _ |>.2 fun i => ?_
    exact mem_pow_smul_of_lTensor_ideal_eq_zero hRt hTt ψ hψ hflat ξ hξ i
  rw [hbot] at hmem
  simpa using hmem

/-- **THE INDUCTION CARRIER OF THE LOCAL CRITERION OF FLATNESS**
(**PROVEN 2026-07-27** over the one-element atom above).

Induction is on the LENGTH of the list rather than on the list itself, because
each step changes the pair of rings (`R, T` becomes `R ⧸ (t), T ⧸ (φ t)`) and a
`List R` cannot be recursed on across a change of `R`.

* Base: `rs = []` forces `𝔪_R = ⊥`, so `R` is a field and `RingHom.Flat.of_isField`
  applies — every ring is flat over a field, so **no hypothesis on `T` is used at
  the bottom of the induction**.
* Step: `isWeaklyRegular_cons_iff` splits both regularity hypotheses at the head;
  the tails transport to the quotient RINGS along `A ⧸ (a) ≃ₗ[A] QuotSMulTop a A`
  followed by `isWeaklyRegular_map_algebraMap_iff`; the span hypothesis descends
  because `t ↦ 0`, so `Ideal.ofList` of the image of `t :: rs₀` is that of the
  image of `rs₀`; and `IsLocalHom ψ` follows from surjectivity of
  `Ideal.Quotient.mk` on the source. -/
theorem flat_of_isWeaklyRegular_span_eq_maximalIdeal_aux (n : ℕ) :
    ∀ (R T : Type u) [CommRing R] [CommRing T] [IsLocalRing R] [IsNoetherianRing R]
      [IsLocalRing T] [IsNoetherianRing T] (φ : R →+* T) [IsLocalHom φ] (rs : List R),
      rs.length = n →
      Ideal.span {r | r ∈ rs} = IsLocalRing.maximalIdeal R →
      RingTheory.Sequence.IsWeaklyRegular R rs →
      RingTheory.Sequence.IsWeaklyRegular T (rs.map φ) →
      φ.Flat := by
  classical
  induction n with
  | zero =>
    intro R T _ _ _ _ _ _ φ _ rs hlen hspan _ _
    -- `rs = []`, so `𝔪_R = ⊥` and `R` is a field; everything is flat over a field.
    have hrs : rs = [] := List.eq_nil_of_length_eq_zero hlen
    subst hrs
    have hbot : IsLocalRing.maximalIdeal R = ⊥ := by
      rw [← hspan]; simp
    exact RingHom.Flat.of_isField (IsLocalRing.isField_iff_maximalIdeal_eq.2 hbot) φ
  | succ n ih =>
    intro R T _ _ _ _ _ _ φ _ rs hlen hspan hR hT
    obtain ⟨t, rs₀, rfl⟩ : ∃ t rs₀, rs = t :: rs₀ := by
      cases rs with
      | nil => simp at hlen
      | cons a l => exact ⟨a, l, rfl⟩
    set I : Ideal R := Ideal.span {t} with hI
    set J : Ideal T := Ideal.span {φ t} with hJ
    have htm : t ∈ IsLocalRing.maximalIdeal R := by
      rw [← hspan]
      exact Ideal.subset_span (by simp)
    have hIm : I ≤ IsLocalRing.maximalIdeal R := by rw [hI, Ideal.span_le]; simpa using htm
    have hJm : J ≤ IsLocalRing.maximalIdeal T := by
      rw [hJ, Ideal.span_le]
      have hnu : φ t ∈ IsLocalRing.maximalIdeal T :=
        (IsLocalRing.mem_maximalIdeal _).2 fun H =>
          ((IsLocalRing.mem_maximalIdeal _).1 htm) (isUnit_of_map_unit φ t H)
      simpa using hnu
    have hInt : I ≠ ⊤ := fun h =>
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (h ▸ hIm))
    have hJnt : J ≠ ⊤ := fun h =>
      (IsLocalRing.maximalIdeal.isMaximal T).ne_top (top_le_iff.mp (h ▸ hJm))
    haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hInt
    haveI : Nontrivial (T ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJnt
    haveI : IsLocalRing (R ⧸ I) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    haveI : IsLocalRing (T ⧸ J) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    haveI : IsLocalHom (Ideal.Quotient.mk J) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    -- the induced map on quotients
    have hIJ : I ≤ J.comap φ := by
      rw [hI, Ideal.span_le]
      intro y hy
      simp only [Set.mem_singleton_iff] at hy
      subst hy
      exact Ideal.mem_comap.2 (Ideal.subset_span rfl)
    set ψ : R ⧸ I →+* T ⧸ J := Ideal.quotientMap J φ hIJ with hψdef
    have hψ : ψ.comp (Ideal.Quotient.mk I) = (Ideal.Quotient.mk J).comp φ := by
      ext r; simp [hψdef, Ideal.quotientMap_mk]
    haveI : IsLocalHom ψ := by
      constructor
      intro a ha
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
      have h1 : IsUnit ((Ideal.Quotient.mk J) (φ r)) := by
        rw [← RingHom.comp_apply, ← hψ, RingHom.comp_apply]; exact ha
      have h2 : IsUnit (φ r) :=
        IsLocalHom.map_nonunit (f := Ideal.Quotient.mk J) _ h1
      exact (IsLocalHom.map_nonunit (f := φ) r h2).map (Ideal.Quotient.mk I)
    -- split both regularity hypotheses at the head
    rw [RingTheory.Sequence.isWeaklyRegular_cons_iff] at hR
    obtain ⟨hRt, hRtail⟩ := hR
    rw [List.map_cons, RingTheory.Sequence.isWeaklyRegular_cons_iff] at hT
    obtain ⟨hTt, hTtail⟩ := hT
    -- the identifications `A ⧸ (a) ≃ₗ[A] QuotSMulTop a A`
    have heR : (R ⧸ I) ≃ₗ[R] QuotSMulTop t R :=
      Submodule.quotEquivOfEq _ _ (by
        rw [hI, ← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top])
    have heT : (T ⧸ J) ≃ₗ[T] QuotSMulTop (φ t) T :=
      Submodule.quotEquivOfEq _ _ (by
        rw [hJ, ← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top])
    -- transport the tails to the quotient rings
    have hRq : RingTheory.Sequence.IsWeaklyRegular (R ⧸ I)
        (rs₀.map (Ideal.Quotient.mk I)) := by
      rw [← Ideal.Quotient.algebraMap_eq I,
        RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff (R ⧸ I) (R ⧸ I) rs₀]
      exact (heR.isWeaklyRegular_congr rs₀).2 hRtail
    have hTq : RingTheory.Sequence.IsWeaklyRegular (T ⧸ J)
        ((rs₀.map φ).map (Ideal.Quotient.mk J)) := by
      rw [← Ideal.Quotient.algebraMap_eq J,
        RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff (T ⧸ J) (T ⧸ J) (rs₀.map φ)]
      exact (heT.isWeaklyRegular_congr (rs₀.map φ)).2 hTtail
    -- the two descriptions of the descended list agree
    have hlists : (rs₀.map (Ideal.Quotient.mk I)).map ψ
        = (rs₀.map φ).map (Ideal.Quotient.mk J) := by
      simp only [List.map_map]
      exact congrArg (fun f : R →+* T ⧸ J => rs₀.map f) hψ
    -- the span condition descends, because `t ↦ 0`
    have hspanq : Ideal.span {r | r ∈ rs₀.map (Ideal.Quotient.mk I)}
        = IsLocalRing.maximalIdeal (R ⧸ I) := by
      have h1 : (Ideal.span {r | r ∈ (t :: rs₀)}).map (Ideal.Quotient.mk I)
          = IsLocalRing.maximalIdeal (R ⧸ I) := by
        rw [hspan]
        exact IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
      rw [show (Ideal.span {r | r ∈ (t :: rs₀)}) = Ideal.ofList (t :: rs₀) from rfl,
        Ideal.map_ofList, List.map_cons] at h1
      have ht0 : (Ideal.Quotient.mk I) t = 0 := by
        rw [Ideal.Quotient.eq_zero_iff_mem, hI]; exact Ideal.subset_span rfl
      rw [ht0, Ideal.ofList_cons, Ideal.span_singleton_eq_bot.2 rfl, bot_sup_eq] at h1
      exact h1
    have hlenq : (rs₀.map (Ideal.Quotient.mk I)).length = n := by
      simp only [List.length_map]
      simpa using hlen
    have hTq' : RingTheory.Sequence.IsWeaklyRegular (T ⧸ J)
        ((rs₀.map (Ideal.Quotient.mk I)).map ψ) := by rw [hlists]; exact hTq
    have hflat : ψ.Flat :=
      ih (R ⧸ I) (T ⧸ J) ψ (rs₀.map (Ideal.Quotient.mk I)) hlenq hspanq hRq hTq'
    exact flat_of_flat_quotient_isSMulRegular φ htm hRt hTt ψ hψ hflat

/-- **THE LOCAL CRITERION OF FLATNESS** (**PROVEN 2026-07-27** over the ONE
atom `flat_of_flat_quotient_isSMulRegular` above — pure commutative algebra;
Matsumura *Commutative Ring Theory* 22.3, Stacks 00MK).

If `𝔪_R` is generated by an `R`-regular sequence `rs` — equivalently, `R` is
regular local with regular system of parameters `rs` — and the image of `rs` is
`T`-regular, then `T` is flat over `R`.

**THE CUT (2026-07-27).**  The previous version of this docstring predicted that
"the induction along `rs` is mechanical … so the whole content is the one-element
case", and named that case as "the statement to state and dispatch next if this
leaf is cut further.  That prediction was correct and has now been carried out:
the one-element case is
`flat_of_flat_quotient_isSMulRegular` above, the induction is
`flat_of_isWeaklyRegular_span_eq_maximalIdeal_aux` above, and this declaration is
their composition.  **Nothing is open here any more — the open leaf is the atom.**

The induction really did need nothing beyond `isWeaklyRegular_cons_iff`,
`isWeaklyRegular_map_algebraMap_iff`, the identification
`A ⧸ (a) ≃ₗ[A] QuotSMulTop a A`, and the fact that quotients of noetherian local
rings are noetherian local.  The one thing worth recording that the prediction
did not mention: the base case is `𝔪_R = ⊥`, i.e. `R` a FIELD, and it discharges
by `RingHom.Flat.of_isField` **without using any hypothesis on `T` at all**.

**FAITHFULNESS — the separatedness hypothesis is present, disguised as
`[IsNoetherianRing T] [IsLocalRing T] [IsLocalHom φ]`, and it is LOAD-BEARING.**
The classical criterion needs `T` to be `𝔪_R`-adically *ideally separated*; the
statement is false for an arbitrary `R`-module with a regular sequence acting
regularly.  Here it is automatic and the derivation is short enough to record:
`φ` local gives `𝔪_R T ⊆ 𝔪_T`, hence `𝔪_R^n T ⊆ 𝔪_T^n`, so
`⋂ₙ 𝔪_R^n T ⊆ ⋂ₙ 𝔪_T^n = 0` by Krull's intersection theorem; and `T ⧸ I T` for
`I` finitely generated is again a noetherian local ring, so the same applies to
it.  **A prover who weakens `T` to a bare `R`-module produces a FALSE leaf.**
That hypothesis is carried, unweakened, into the atom. -/
theorem flat_of_isWeaklyRegular_span_eq_maximalIdeal {R T : Type u} [CommRing R] [CommRing T]
    [IsLocalRing R] [IsNoetherianRing R] [IsLocalRing T] [IsNoetherianRing T]
    (φ : R →+* T) [IsLocalHom φ] (rs : List R)
    (hspan : Ideal.span {r | r ∈ rs} = IsLocalRing.maximalIdeal R)
    (hR : RingTheory.Sequence.IsWeaklyRegular R rs)
    (hT : RingTheory.Sequence.IsWeaklyRegular T (rs.map φ)) :
    φ.Flat :=
  flat_of_isWeaklyRegular_span_eq_maximalIdeal_aux rs.length R T φ rs rfl hspan hR hT

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

The declarations below carry the whole of
`finite_preimage_mulByNat_of_field_prime_to_char` except one leaf.  All
but one of them are general scheme theory or bookkeeping with no
abelian-variety content at all; the exception,
`nonempty_module_infKernel_of_squareZero`, is the single genuinely
missing input — the Lie algebra of a smooth group scheme, in the form
"the infinitesimal kernel is a `K`-vector space".

Note `eq_zero_of_nsmul_eq_zero_of_squareZero`, which was the leaf when
this section was written on 2026-07-27, is now PROVEN over it: the split
moved the arithmetic into a proof and left the geometry as the leaf. -/

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

/-- **Precomposition of relative points, packaged as a GROUP HOMOMORPHISM**
(PROVEN 2026-07-27).

`RelPoint.pre h hg` is additive and unital by the two naturality axioms
`pre_add` and `pre_zero`, so it is an `AddMonoidHom` for the group
structures `ab.addCommGroup` on source and target.  Nothing new is proven
here; the point is to have a bundled map whose KERNEL is an
`AddSubgroup`, which is what `infKernel` below needs.

Used only through `infKernel`. -/
def preAddHom (ab : AbelianSchemeStruct f) {T' T : Scheme.{u}} (h : T' ⟶ T)
    {g : T ⟶ S} {g' : T' ⟶ S} (hg : h ≫ g = g') :
    letI := ab.addCommGroup g
    letI := ab.addCommGroup g'
    RelPoint f g →+ RelPoint f g' :=
  letI := ab.addCommGroup g
  letI := ab.addCommGroup g'
  { toFun := RelPoint.pre h hg
    map_zero' := ab.pre_zero h hg
    map_add' := ab.pre_add h hg }

/-- **THE INFINITESIMAL KERNEL** — `ker (A(T) ⟶ A(T'))` for a change of
test object `h : T' ⟶ T`, as an additive subgroup of `RelPoint f g`.

For `h` a square-zero thickening `Spec R₀ ⟶ Spec R` this is the group
whose classical description is the *Lie algebra of `A` tensored with the
ideal* — see `nonempty_module_infKernel_of_squareZero` below, which is
the one place its structure beyond "subgroup" is asserted.

Membership is definitionally `RelPoint.pre h hg x = 0`, so
`AddMonoidHom.mem_ker` is not needed to enter or leave it. -/
def infKernel (ab : AbelianSchemeStruct f) {T' T : Scheme.{u}} (h : T' ⟶ T)
    {g : T ⟶ S} {g' : T' ⟶ S} (hg : h ≫ g = g') :
    letI := ab.addCommGroup g
    AddSubgroup (RelPoint f g) :=
  letI := ab.addCommGroup g
  letI := ab.addCommGroup g'
  (ab.preAddHom h hg).ker

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
2026-07-27 as `eq_zero_of_nsmul_eq_zero_of_squareZero` and RESTATED
2026-07-27 in its present module-theoretic form — the ONE remaining input
of `finite_preimage_mulByNat_of_field_prime_to_char`, and the only thing
in that half of the old cube leaf that mathlib does not already have).

**FALSITY AUDIT (2026-07-27): THIS LEAF IS FALSE AS STATED, AND SO IS ITS
CONSUMER `eq_zero_of_nsmul_eq_zero_of_squareZero`.  DO NOT ATTEMPT A PROOF
BEFORE THE STATEMENT IS REPAIRED.**  The defect is an INSTANCE DIAMOND in
the binder `(K : CommRingCat.{u}) [Field K]`, and it is invisible to every
reader because the two halves of the statement never meet in any of the
already-proven declarations of this cluster — this leaf is the first place
that needs to bridge them.

*The two structures.*  `set_option pp.explicit` on this very declaration
shows the conclusion's scalars are

    @Module ↑K _ (DivisionSemiring.toSemiring (Semifield.toDivisionSemiring
                    (Field.toSemifield ↑K inst)))

i.e. they come from the `[Field ↑K]` BINDER, while `Spec K` — and hence
`fK`, `ab`, `q`, and all the geometry — uses `K`'s OWN ring structure
`K.commRing`.  Nothing in the statement forces `Field.toCommRing` and
`K.commRing` to agree, and Lean cannot bridge them: mathlib's
`instance {K} [Field K] : Unique (Spec (.of K))` fails to apply to
`Spec K` here for exactly this reason (checked: `Subsingleton ↥(Spec K)`
is not synthesizable, and `Subsingleton (PrimeSpectrum ↑K)` is not even
kernel-defeq to it, the mismatch being
`Field.toSemifield.toCommSemiring` against `CommRing.toCommSemiring`).
Note `CommRingCat.of ↑K = K` is `rfl` and therefore pins NOTHING — the
`CommRing` search picks `K.commRing`, the `Semiring`/`CommSemiring` search
picks the `Field` path.  A pin written that way is vacuous.

*The counterexample.*  Let `↑K = 𝔽_p[t]` (`p > 3`) with `K.commRing` its
usual ring structure, and let the `[Field ↑K]` instance be a field
structure TRANSPORTED FROM `ℚ` along any bijection of the two countably
infinite underlying sets.  Take `X = E₀ ×_{𝔽_p} 𝔽_p[t]` for `E₀` an
elliptic curve over `𝔽_p` with good reduction, so `fK` is a genuine
abelian scheme (proper, smooth, geometrically connected fibres).  Take
`R = 𝔽_p[t][ε]/(ε²)`, `R₀ = 𝔽_p[t]`, `φ` the reduction; `φ` is surjective
and `ker φ = (ε)` satisfies `ker φ ^ 2 = ⊥`.  Then

    ab.infKernel (Spec.map φ) rfl  ≅  Lie(E₀) ⊗ (ε)  ≅  𝔽_p[t] ≠ 0,

which is killed by `p`.  But the conclusion demands a module over the
`[Field ↑K]` structure, which is `ℚ` — and a `ℚ`-vector space is
torsion-free, so a nonzero `p`-torsion group admits no `ℚ`-module
structure.  Conclusion FALSE.

*The same counterexample refutes the consumer.*  In it,
`eq_zero_of_nsmul_eq_zero_of_squareZero` at `n = p` has
`(p : ↑K) = (p : ℚ) ≠ 0` and `p • d = 0` for every `d`, yet `d ≠ 0` for
`d` a nonzero element of the kernel.  That declaration is marked PROVEN
only because it rests on this false leaf; the six-line module argument in
it is correct, and it is the LEAF that is wrong.

*The repair, and it is a CUT-LEVEL repair, not a leaf-level one.*  Pin the
field structure by taking the base field UNBUNDLED, exactly as
`exists_isRegularLocalRing_quotient_indepList_of_smooth_over_field`
(`Fermat/FLT/Modularity/KhareWintenberger.lean:4113`) already does in this
project for the same reason:

    {K : Type u} [Field K] {fK : X ⟶ Spec (CommRingCat.of K)}

Then `Spec (.of K)`'s ring structure IS `Field.toCommRing`, mathlib's
`Unique (Spec (.of K))` applies, and the scalars of the conclusion are the
scalars of the geometry.  The change must be threaded through the five
statements of this cluster — this leaf,
`eq_zero_of_nsmul_eq_zero_of_squareZero`, `formallyUnramified_mulByNat`,
`finite_preimage_mulByNat_of_field_prime_to_char` and
`finite_preimage_mulByNat_of_field` — and it TERMINATES: the top consumer
`finite_preimage_mulByNat` instantiates `K := S.residueField (f a)`, and
`Scheme.residueField` is *defined* as
`CommRingCat.of (IsLocalRing.ResidueField _)`
(`Mathlib/AlgebraicGeometry/ResidueField.lean:45`), so the new form is
discharged there by `rfl`.  No proof body needs to change; only the five
binders.  `finite_preimage_mulByNat_of_field_char` is NOT in the chain and
needs no edit.

*The check that would refute this audit*: `pp.explicit` on this
declaration showing the `Module` instance built from `K.commRing` rather
than from `Field.toSemifield`, or `Subsingleton ↥(Spec K)` becoming
synthesizable from `[Field ↑K]` alone.

*The infinitesimal kernel of an abelian scheme is a `K`-VECTOR SPACE.*
Concretely: `Spec R₀ ⟶ Spec R` is a square-zero thickening (`φ`
surjective, `ker φ ^ 2 = ⊥`), and `ab.infKernel (Spec.map φ) rfl` is the
subgroup of `R`-points of `A` over `q` that restrict to the identity
element on `Spec R₀`.  The claim is that this abelian group carries a
`K`-module structure — necessarily compatible with its own addition,
since `Module K ↥(…)` is stated over the subgroup's own `AddCommGroup`.

**WHY THIS IS THE RIGHT RESIDUE.**  The arithmetic that used to sit on
top of this — "`n • d = 0` and `(n : K) ≠ 0` force `d = 0`" — is now
PROVEN in `eq_zero_of_nsmul_eq_zero_of_squareZero` below, in six lines:
a `K`-module has no `n`-torsion for `(n : K) ≠ 0` because `(n : K)⁻¹`
exists, and `Nat.cast_smul_eq_nsmul` identifies the group's `ℕ`-action
with the module's.  So none of the difficulty was ever arithmetic, and
what remains here is exactly the geometric input and nothing else.

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

**THE TWO-STEP ROUTE A SUCCESSOR SHOULD COST OUT FIRST**, since neither
step exists at this pin and the second is the expensive one.  Write
`P = R ×_{R₀} R`.  For `c : R₀` with any lift `c̃ : R`, the map

    α_c : P ⟶ R,   (a, b) ↦ a + c̃ · (b - a)

is a RING HOMOMORPHISM — the only thing to check is multiplicativity, and
it reduces to `(b - a)(b' - a') = 0`, which holds because both factors lie
in `I` and `I ^ 2 = 0`; independence of the lift `c̃` is the same
computation.  Note `α_0 = pr₁` and `α_1 = pr₂`.  Scaling is then
`c • d := Spec.map (α_c) ≫ w`, where `w : Spec P ⟶ A` is the point
patched together from the compatible pair `(0, d)`.  So the missing input
is **Milnor patching for schemes**: that `Spec (R ×_{R₀} R)` is the
pushout of `Spec R ← Spec R₀ → Spec R`, equivalently that
`A(R ×_{R₀} R) ≅ A(R) ×_{A(R₀)} A(R)`.

That is genuinely absent: `grep -rlin "ferrand\|milnor" Mathlib/` is EMPTY
and `grep -rln "pushout" Mathlib/AlgebraicGeometry/` returns only files
about *pullbacks* (re-run 2026-07-27).  A hit on either means this route
has become cheap.  Be warned that the module AXIOMS are not free once
patching exists — additivity in `c` and `(c c') • d = c • (c' • d)` each
need a further patching diagram and the group law — so "prove Milnor
patching" is a necessary but not sufficient plan.

**ROUTE CORRECTION (2026-07-27).  BOTH HALVES OF THE PARAGRAPH ABOVE ARE
WRONG, AND THE ROUTE IS MUCH CHEAPER THAN IT RECORDS.  This assumes the
FALSITY AUDIT's repair has been applied, since step 1 is exactly what the
unpinned `[Field K]` blocks.**

*1. Milnor patching FOR SCHEMES is not needed — the problem is
AFFINE-LOCAL.*  Once the field structure is pinned, `Spec K` is a ONE-POINT
space, so the unit section `e := (ab.zero (𝟙 (Spec K))).1` has a single
point `x₀` in its image.  Every `d` in the infinitesimal kernel satisfies
`Spec.map φ ≫ d.1 = (Spec.map φ ≫ q) ≫ e` (that is `pre_zero` plus
`d ∈ ker`), and `Spec.map φ` is SURJECTIVE on points because `ker φ ^ 2 = ⊥`
puts `ker φ` inside every prime.  Hence the underlying map of `d.1` is
CONSTANT at `x₀` — for *every* `d` at once.  Choosing an affine open
`U ∋ x₀` (`exists_isAffineOpen_mem_and_subset`), every kernel point factors
through `U` (`IsOpenImmersion.lift`), so with `B := Γ(X, U)` the whole leaf
becomes a statement about RING HOMOMORPHISMS `B ⟶ R`.  Patching is then the
universal property of a fibre product of RINGS — `Hom(B, R ×_{R₀} R) =
Hom(B,R) ×_{Hom(B,R₀)} Hom(B,R)` — and needs no Ferrand pushout, no
scheme-level Milnor patching, and nothing absent from the pin.

These five steps are Lean-verified (worktree `flt-lean-164`, 2026-07-27,
against this pin; they compile with `Subsingleton ↥(Spec K)` supplied as an
argument, which is precisely what the repair makes free):
`(ab.zero g).1 = g ≫ (ab.zero (𝟙 S)).1` from `pre_zero` and
`Category.comp_id`; `ker φ ≤ p.asIdeal` from `Ideal.pow_mem_pow` and
`p.isPrime.mem_of_pow_mem`; surjectivity of `(Spec.map φ).base` from
`range_comap_of_surjective` (ROOT namespace, not `PrimeSpectrum`);
constancy of `⇑d.1`; and the affine open.

*2. The group-law crux DISSOLVES — patching plus naturality is
sufficient, and no differentials are needed.*  Write `Δ(x) := ψ_x − ψ_e`
for the ring hom attached to `x`.  The one hard-looking point is that the
ABELIAN SCHEME's group law agrees with addition of the `Δ`'s, which is
classically proven from `m : A ×_S A ⟶ A` by a Taylor expansion.  It is not
needed.  Put `J := R ×_{R₀} R ×_{R₀} R` with projections `pr₁ pr₂ pr₃`, and
note `σ (a,b,c) := b + c − a` is a RING HOM `J ⟶ R` (multiplicativity is
`(b−a)(b'−a') = 0` from `I ^ 2 = ⊥`, the same computation as for `α_c`).
Affine patching gives points `patch(0,x,0)`, `patch(0,0,y)`,
`patch(0,x,y)` of `A` over `Spec J`, and patching is INJECTIVE on
restrictions.  Now `ab.pre_add` along each `pr_i` gives

    pr₁*(patch(0,x,0) + patch(0,0,y)) = 0 + 0 = 0
    pr₂*(…) = x + 0 = x        pr₃*(…) = 0 + y = y

so by injectivity `patch(0,x,0) + patch(0,0,y) = patch(0,x,y)`.  Applying
`σ*` and `ab.pre_add` once more, and using `σ*(patch(0,x,0)) = x`,
`σ*(patch(0,0,y)) = y`, `σ*(patch(0,x,y)) = ψ_x + ψ_y − ψ_e`, yields
`Δ(x + y) = Δ(x) + Δ(y)` — from the structure's own naturality axioms
alone.  With `Δ` injective (affineness) the remaining module axioms are
then bookkeeping on functions `B → I`: `add_smul` is
`Δ((c + c') • d) = (c + c')Δ(d) = Δ(c • d) + Δ(c' • d)`, and `mul_smul`,
`one_smul`, `zero_smul`, `smul_zero`, `smul_add` likewise.  So the
"necessary but not sufficient" warning above is retired: for THIS leaf
patching is sufficient, and the missing theory is not Milnor patching but
only the affine bookkeeping.

**A GENERALISATION THAT IS ALSO TRUE**, recorded so a prover is not misled
into thinking the field is essential: the kernel is a module over `R₀`
itself (restrict along `K ⟶ R₀` to recover the statement below), over an
arbitrary base, and without `ab.smooth` — the displayed isomorphism is
valid for every group scheme.  It is stated over a field here because
that is exactly what the consumer needs and it is the weakest form that
suffices; a prover may freely prove the stronger form and specialise. -/
theorem nonempty_module_infKernel_of_squareZero {X : Scheme.{u}} (K : CommRingCat.{u}) [Field K]
    {fK : X ⟶ Spec K} (ab : AbelianSchemeStruct fK)
    {R R₀ : CommRingCat.{u}} (φ : R ⟶ R₀) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ.hom ^ 2 = ⊥)
    {q : Spec R ⟶ Spec K} :
    letI := ab.addCommGroup q
    Nonempty (Module K (ab.infKernel (Spec.map φ) (rfl : Spec.map φ ≫ q = Spec.map φ ≫ q))) :=
  sorry

/-- **THE INFINITESIMAL KERNEL IS TORSION FREE AT `n` PRIME TO THE
CHARACTERISTIC** (PROVEN 2026-07-27 over the single leaf
`nonempty_module_infKernel_of_squareZero` above; this used to BE the leaf).

`Spec R₀ ⟶ Spec R` is a square-zero thickening, `d` is an `R`-point of `A`
over the base point `q` restricting to the identity element on `Spec R₀`,
and `n · d = 0` with `(n : K) ≠ 0`.  Then `d = 0`.  This is exactly the
classical `d[n] = n · id` statement, and it is why the
prime-to-characteristic half of `finite_preimage_mulByNat_of_field` is
cheap while the characteristic half needs the theorem of the cube: at
`n = p = ringChar K` the scalar `(n : K)` is zero and the argument below
says nothing.

**The proof is pure module theory, and that is the point of the split.**
`d` lies in `ab.infKernel (Spec.map φ) rfl` by `hres` — definitionally, so
no `AddMonoidHom.mem_ker` step is needed.  On that subgroup the leaf
supplies a `K`-module structure whose addition IS the group's, so
`Nat.cast_smul_eq_nsmul` turns `hnd` into `(n : K) • ⟨d, _⟩ = 0`, and
multiplying by `(n : K)⁻¹` — available because `K` is a field and
`hn : (n : K) ≠ 0` — gives `⟨d, _⟩ = 0`.  `Subtype.val` then returns the
statement about `d`.

No geometry is used HERE; all of it is inside the leaf. -/
theorem eq_zero_of_nsmul_eq_zero_of_squareZero {X : Scheme.{u}} (K : CommRingCat.{u}) [Field K]
    {fK : X ⟶ Spec K} (ab : AbelianSchemeStruct fK) (n : ℕ) (hn : (n : K) ≠ 0)
    {R R₀ : CommRingCat.{u}} (φ : R ⟶ R₀) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ.hom ^ 2 = ⊥)
    {q : Spec R ⟶ Spec K} (d : RelPoint fK q)
    (hres : letI := ab.addCommGroup (Spec.map φ ≫ q)
      RelPoint.pre (Spec.map φ) rfl d = 0)
    (hnd : letI := ab.addCommGroup q; n • d = 0) :
    letI := ab.addCommGroup q; d = 0 := by
  letI := ab.addCommGroup q
  letI := ab.addCommGroup (Spec.map φ ≫ q)
  obtain ⟨inst⟩ := nonempty_module_infKernel_of_squareZero K ab φ hφ hker (q := q)
  letI := inst
  have hd : d ∈ ab.infKernel (Spec.map φ) (rfl : Spec.map φ ≫ q = Spec.map φ ≫ q) := hres
  have hx : (n : K) • (⟨d, hd⟩ :
      ab.infKernel (Spec.map φ) (rfl : Spec.map φ ≫ q = Spec.map φ ≫ q)) = 0 := by
    rw [Nat.cast_smul_eq_nsmul]
    exact Subtype.ext hnd
  have hz : (⟨d, hd⟩ :
      ab.infKernel (Spec.map φ) (rfl : Spec.map φ ≫ q = Spec.map φ ≫ q)) = 0 :=
    calc (⟨d, hd⟩ : ab.infKernel (Spec.map φ) (rfl : Spec.map φ ≫ q = Spec.map φ ≫ q))
        = ((n : K)⁻¹ * (n : K)) • (⟨d, hd⟩ :
            ab.infKernel (Spec.map φ) (rfl : Spec.map φ ≫ q = Spec.map φ ≫ q)) := by
          rw [inv_mul_cancel₀ hn, one_smul]
      _ = (n : K)⁻¹ • ((n : K) • (⟨d, hd⟩ :
            ab.infKernel (Spec.map φ) (rfl : Spec.map φ ≫ q = Spec.map φ ≫ q))) := mul_smul _ _ _
      _ = 0 := by rw [hx, smul_zero]
  exact congrArg Subtype.val hz

/-- **`[n]` is FORMALLY UNRAMIFIED when `n` is prime to the characteristic**
(PROVEN 2026-07-27 over `eq_zero_of_nsmul_eq_zero_of_squareZero` above,
which is itself now proven over the single leaf
`nonempty_module_infKernel_of_squareZero`).

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
`nonempty_module_infKernel_of_squareZero`; this used to be a sorry leaf).

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
   the leaf `nonempty_module_infKernel_of_squareZero` above**, where the
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

/-- **A QUASI-AFFINE scheme that is universally closed over an affine scheme is
AFFINE** (PROVEN 2026-07-27; general scheme theory, nothing abelian in it).

This is EGA II 5.1.6's "quasi-affine + proper ⟹ affine", and it is the last
step of the classical ample-line-bundle proof of
`isQuasiAffine_ker_mulByNat_of_field_char` below.  Proving it here is what lets
that leaf be stated as `IsQuasiAffine` — *literally* the sentence the ample
argument produces — instead of `IsAffine`.

The proof is four lines of mathlib.  `X.toSpecΓ` is an OPEN immersion because
`X` is quasi-affine (mathlib's `Scheme.IsQuasiAffine` instance); it is
UNIVERSALLY CLOSED by cancellation, since `X.toSpecΓ ≫ Spec.map f.appTop` is
`f ≫ Y.toSpecΓ` with `Y.toSpecΓ` an isomorphism (`Y` affine) and
`Spec.map f.appTop` separated (a morphism of affine schemes).  An open immersion
with closed range is a CLOSED immersion (`IsClosedImmersion.of_isPreimmersion`),
closed immersions are affine morphisms, and an affine morphism to the affine
scheme `Spec Γ(X, ⊤)` forces `IsAffine X` (`isAffine_of_isAffineHom`).

Note the hypothesis is `UniversallyClosed`, not `IsProper`: separatedness is
free from `IsQuasiAffine` and finite type is not used at all. -/
theorem isAffine_of_isQuasiAffine_of_universallyClosed {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.IsQuasiAffine] [UniversallyClosed f] [IsAffine Y] :
    IsAffine X := by
  have h₁ : UniversallyClosed (X.toSpecΓ ≫ Spec.map f.appTop) := by
    rwa [← Scheme.toSpecΓ_naturality,
      MorphismProperty.cancel_right_of_respectsIso (P := @UniversallyClosed)]
  have h₂ : UniversallyClosed X.toSpecΓ :=
    .of_comp_of_isSeparated _ (Spec.map f.appTop)
  have h₃ : IsClosedImmersion X.toSpecΓ :=
    IsClosedImmersion.of_isPreimmersion _
      (Set.image_univ ▸ X.toSpecΓ.isClosedMap _ isClosed_univ)
  exact isAffine_of_isAffineHom X.toSpecΓ

/-- **`ker[p]` is a QUASI-AFFINE SCHEME in characteristic `p`** (sorry leaf —
the theorem of the cube; cut 2026-07-27 out of
`isAffine_ker_mulByNat_of_field_char`, which is now PROVEN over it through the
bridge `isAffine_of_isQuasiAffine_of_universallyClosed` immediately above).

**HONESTY FIRST: this is a CHANGE OF SHAPE, NOT a reduction of content.**  For a
scheme proper over a field, *quasi-affine*, *affine* and *finite* are all
equivalent, and both equivalences are now PROVEN here — so a prover at this leaf
owes neither more nor less than a prover owed at
`finite_preimage_mulByNat_of_field_char` two cuts ago.  Nobody should report
this as progress on the mathematics.  What the two cuts together buy, and the
only reason they were made:

* the residue is a property of the SCHEME `ker[p]` alone — no morphism
  bookkeeping, no `∀ s : Spec K` packaging, no Zariski's-main-theorem step;
* and it is *exactly* where the classical argument stops.  The ample-line-bundle
  proof does not produce "the point set is finite" and does not produce
  "affine": it produces "`𝒪_Z` is ample, hence `Z` is quasi-affine"
  (EGA II 5.1.2).  Everything after that is the bridge above, and the bridge is
  no longer owed to anybody.

**The bridges, both PROVEN.**  quasi-affine ⟹ affine is
`isAffine_of_isQuasiAffine_of_universallyClosed` above (`ker[p] ⟶ Spec K` is
proper as a base change of `[p]`, `isProper_mulByNat`).  affine ⟹ finite fibre
is `finite_ker_mulByNat_of_field_char` below (`IsAffineHom` is then free since
`Spec K` is affine, so `IsFinite.iff_isProper_and_isAffineHom` gives a FINITE
morphism and `Scheme.Hom.finite_preimage_singleton` reads off the fibre).

**The classical proof, in the order that produces `IsQuasiAffine`.**  Mumford
*Abelian Varieties* §6, Application 2 of the theorem of the cube:

1. `A` carries a symmetric AMPLE invertible sheaf `L` (`A` is projective — a
   theorem, via the theta divisor).
2. The cube gives `[n]^* L ≅ L^{n²}`.
3. `[p]` is constant on `Z = ker[p]` (it factors through the zero section), so
   `([p]^* L)|_Z ≅ 𝒪_Z`; with 2, `(L|_Z)^{p²} ≅ 𝒪_Z`.
4. `L|_Z` is ample (restriction of an ample sheaf to a closed subscheme), hence
   so is `(L|_Z)^{p²} ≅ 𝒪_Z`; and a scheme whose structure sheaf is ample is
   QUASI-AFFINE.  That is this leaf, and it is where the classical argument
   ends.

The second classical route, `[p] = V ∘ F`, produces finiteness rather than
quasi-affineness and needs the Verschiebung, hence `Pic⁰` and the dual abelian
variety.

**MISSING MACHINERY at this pin — every claim re-run 2026-07-27 against this
worktree's own `.lake/packages/mathlib`.  THE PREVIOUS VERSION OF THIS SURVEY
WAS WRONG ON TWO COUNTS; both corrections are recorded first.**

*Correction 1: mathlib DOES have quasi-affine schemes.*
`Mathlib/AlgebraicGeometry/QuasiAffine.lean` defines `Scheme.IsQuasiAffine`
(quasi-compact + `X.toSpecΓ` an immersion, which it proves is then an OPEN
immersion) with `IsQuasiAffine.of_forall_exists_mem_basicOpen`,
`.of_isAffineHom`, `.of_isImmersion` and `.isBasis_basicOpen`.  That is the
target type of EGA II 5.1.2, and the earlier survey never mentioned it — which
is why the leaf used to be stated one step too late.

*Correction 2: mathlib DOES have zero-dimensionality ⟹ affine, topologically.*
`Mathlib/AlgebraicGeometry/Artinian.lean` has
`IsLocallyArtinian.of_topologicalKrullDim_le_zero`,
`IsLocallyArtinian.of_isLocallyNoetherian_of_discreteTopology`,
`IsLocallyArtinian.discreteTopology` and `IsArtinianScheme.finite`.  So
`topologicalKrullDim (ker[p]) ≤ 0` is an equally valid shape for this leaf.  It
was not chosen because it is *further* from what the cube outputs, not because
it is unavailable.  Also present and useful to a prover:
`isIntegral_appTop_of_universallyClosed` (`Γ(Z, 𝒪)` is integral over `K`) and
`isField_of_universallyClosed`, both in `Morphisms/Proper.lean`.

*Still genuinely absent, each refutable by one grep in
`.lake/packages/mathlib`:*
`grep -rl Ample Mathlib/AlgebraicGeometry/` → EMPTY (mathlib's only `Ample` is
`Analysis/Convex/AmpleSet.lean`).  `grep -rli picard Mathlib/AlgebraicGeometry/`
→ only `EllipticCurve/Weierstrass.lean`.
`grep -rliE "line bundle|invertible sheaf" Mathlib/AlgebraicGeometry/` → EMPTY,
and `Mathlib/AlgebraicGeometry/Modules/` is `Presheaf.lean`, `Sheaf.lean`,
`Tilde.lean` only — there is no invertible-sheaf theory to build `Pic` on.
`grep -rli theoremOfTheCube Mathlib/` → EMPTY.
`grep -rli frobenius Mathlib/AlgebraicGeometry/` → EMPTY.
`grep -rl CohenMacaulay Mathlib/` → EMPTY.
`Mathlib/AlgebraicGeometry/AlgebraicCycle/` exists but is `Basic.lean` alone —
cycles, no intersection numbers and no positivity.
`Mathlib/AlgebraicGeometry/Group/` is `Abelian.lean` + `Smooth.lean` only.
`~/cs/FLT`'s only `Ample`/`Picard` hits are `import Mathlib.RingTheory.PicardGroup`.
**Re-run these before believing the paragraph**; a hit on any of them means the
leaf may be far cheaper than it looks.

**ROUTES SEARCHED AND REFUTED, each with the check that would refute the
refutation** (1–5 recorded 2026-07-27 over the axis *everything cube-free that
is expressible at this pin*; 6–8 added later the same day over two axes the
first sweep did not range over — *dimension counting that does not need
dominance*, and *whether the leaf is needed by its consumers at all*).

1. *Dimension count* — "all fibres of `[p]` are translates of `ker[p]`
   (the shearing above proves exactly this, schematically), so
   `dim A = dim [p](A) + dim ker[p]`; if `[p]` is dominant then
   `dim ker[p] = 0`."  Blocked TWICE: mathlib has no fibre-dimension theorem
   for schemes (`grep -rn "fiber.*dimension\|dim.*fiber" Mathlib/AlgebraicGeometry/`
   → EMPTY), and *dominance of `[p]` is not available here* — in this file
   surjectivity of `[n]` is derived FROM finite fibres
   (`flat_of_finite_fibres_endo` → `flat_mulByNat` → `universallyOpen_mulByNat`
   → `surjective_mulByNat`), so using it would be circular.  Refute by
   exhibiting a cube-free proof that `[p]` is dominant.
2. *Lie algebra*, the sibling's route: `d[p] = p · id = 0` in characteristic
   `p`.  Refute by finding any other differential-geometric invariant that
   separates — note `ker[p] ⊇ ker F` is infinitesimal with
   `Lie(ker[p]) = Lie(A)`, so the tangent space at the origin has FULL
   dimension `g` and no smoothness data can bound `dim ker[p]`.  This is the
   structural reason the leaf is hard, not an accident of the write-up.
3. *Leverage the prime-to-`p` sibling.*  For `ℓ` prime to `p`, `[ℓ]` restricts
   to an AUTOMORPHISM of `ker[p]` (choose `ℓ'` with `ℓℓ' ≡ 1 mod p`; then
   `[ℓ'] ∘ [ℓ] = [1 + p·m] = id` on `ker[p]`), so it carries no dimension
   information about `ker[p]`.  Dually, `[p](A)` contains `A[ℓⁿ]` for every
   `ℓ ≠ p` — but concluding `[p](A) = A` from that needs the prime-to-`p`
   torsion to be dense, i.e. `#A[ℓ] = ℓ^{2g}`, i.e. degree theory, which does
   not exist here either.  Refute by producing that density cube-free.
4. *Specialize to dimension 1* and use this project's division polynomials.
   Refuted by the consumers: `AbelianSchemeStruct` is instantiated in
   `Fermat/FLT/ModularCurve/X0.lean` at the JACOBIAN of a modular curve, so
   `g > 1` is genuinely needed.  Refute by showing every consumer is an
   elliptic curve.
5. *Quasi-finiteness at the origin, spread by `isOpen_quasiFiniteAt`* —
   refuted before dispatch: openness alone does not propagate the locus off the
   origin, and the translations that would do it are not `K`-morphisms at
   non-rational points.
6. *Dimension counting WITHOUT dominance, via the shearing isomorphism.*  Route
   1 was refuted partly because `[p]` is not known to be dominant — but the
   shearing does not need dominance: it identifies the fibre product
   `A ×_{[p], [p]} A` with `A × ker[p]`, so `dim A + dim ker[p]` is computed
   with no reference to the image of `[p]`.  The route dies one step later
   instead: the only upper bound available for that fibre product is the closed
   immersion `A ×_{[p]} A ↪ A × A` (`A` is separated), giving
   `dim A + dim ker[p] ≤ 2 dim A`, i.e. `dim ker[p] ≤ g` — TRUE and vacuous.
   Refute by producing any upper bound for `dim (A ×_{[p]} A)` better than the
   diagonal-based one.
7. *Reduce to a smooth connected subgroup and contradict `[p] = 0` there.*
   Over `K̄`, if `dim ker[p] > 0` then `((ker[p])_red)⁰` is a positive-dimensional
   ABELIAN VARIETY `B` with `[p]|_B = 0`, so the leaf reduces to "no
   positive-dimensional abelian variety is killed by `p`".  Every way of
   contradicting that goes back through degrees or duality: `B(K̄)` is
   `ℓ`-divisible for every `ℓ ≠ p` (the prime-to-`p` sibling gives that) and
   killed by `p`, which is perfectly consistent as an abstract group — an
   infinite `𝔽_p`-vector space is uniquely `ℓ`-divisible — so the contradiction
   needs either `deg[p] = p^{2g} ≠ 1` (the cube) or `V` dual to `F` with `F`
   faithfully flat (duality).  Refute by contradicting "`B` is an abelian
   variety of positive dimension with `pB = 0`" using neither degrees nor
   duality.
8. *Avoid the leaf entirely by restricting to characteristic zero.*  Refuted by
   the consumers, and this is the one axis the first sweep did not range over at
   all: `locallyQuasiFinite_mulByNat`'s assembly below instantiates
   `finite_preimage_mulByNat_of_field` at `S.residueField (f a)` for an
   ARBITRARY point of an arbitrary base scheme `S`, so residue characteristic
   `p > 0` is genuinely in scope even when the generic fibre is over a number
   field.  Refute by
   `grep -n "finite_preimage_mulByNat_of_field (S.residueField" ` in this file
   and showing every consumer's base has characteristic zero residue fields.

**AN ALTERNATIVE CUT, recorded but NOT taken.**  The shearing makes
"`ker[p]` is finite" equivalent to the weaker-*looking*
`∃ x : A, (⇑([p]) ⁻¹' {[p] x}).Finite` — ONE finite fibre anywhere suffices.
`kerShear_kerUnshear` above is one of the two round trips; the other,
`(u,k) ↦ (u,u+k) ↦ (u,k)`, is provable by the same `pre_add` computation, and
together they make `kerShear` an isomorphism, after which a fibre transports
along a base change to `κ(x)` (quasi-finiteness being stable under base change).
It was not taken because the only cube-free way to *produce* one finite fibre is
a generic-point argument, which needs precisely the fibre-dimension theory
refuted in 1 — so the existential form would be more attackable in appearance
only.  A prover who first builds fibre dimension should take this cut instead.

**CORRECTION 3 (2026-07-27): the whole equivalence loop is FREE at this pin, and
the survey above missed the one lemma that makes it so.**
`Mathlib/AlgebraicGeometry/Limits.lean:699` carries
`instance (priority := low) [Finite X] [DiscreteTopology X] : IsAffine X` — a
scheme with finite discrete underlying space is AFFINE.  Together with
`IsArtinianScheme.finite` and `IsLocallyArtinian.discreteTopology` (both in
`Artinian.lean`) that closes the circle: `topologicalKrullDim ≤ 0` ⟹
`IsLocallyArtinian` ⟹ discrete, and with `CompactSpace` ⟹ `Finite` ⟹ `IsAffine`
⟹ `IsQuasiAffine`.  So the ARTINIAN ROUTE IS STRICTLY CHEAPER as a bridge: it
needs no hand-written EGA step at all, where the (correct, and worth keeping)
`isAffine_of_isQuasiAffine_of_universallyClosed` above had to be proved by hand.
Consequence for a prover: all of {`𝒪_Z` ample, `IsQuasiAffine`, `IsAffine`,
`Finite`, `DiscreteTopology`, `topologicalKrullDim ≤ 0`} are interchangeable for
this `Z`, so prove whichever your argument produces — and do NOT spend a cycle
re-cutting the leaf into another of them.  Two shape changes have already been
made here; a third would buy nothing.  Refute by exhibiting a member of that
list that does not reach the others.

**Why "ample line bundles are absent" UNDERSTATES the blocker, and why this leaf
is NOT of the "state the interface and cut" kind** (2026-07-27).  The survey
above is right that `Ample`, `Pic` and invertible sheaves are missing, but the
operative fact is stronger and it is what decides feasibility: **there is no
monoidal structure on sheaves of modules over a scheme, so `L^{⊗n}` cannot even
be WRITTEN.**  `Mathlib/Algebra/Category/ModuleCat/Presheaf/Monoidal.lean` builds
`MonoidalCategoryStruct (PresheafOfModules …)` and it is never transported to
sheaves: `grep -rn 'MonoidalCategory\|tensorObj'
Mathlib/Algebra/Category/ModuleCat/Sheaf/` is EMPTY, and that directory's
`LocallyFree.lean` supplies `IsLocallyFree` with no rank and no tensor product
(`grep -n 'rank\|Rank'` there is EMPTY too).  This matters because the standing
rule "an audit saying *atomic until theory T exists* must be asked whether the
cut needs T PROVEN or only STATED" resolves here in the unusual direction: every
step of Mumford's Application 2 puts `L`, `L^{p²}` and `𝒪_Z` in ONE equation, so
stating the interface faithfully means defining tensor powers of invertible
sheaves — a mathlib-scale build (monoidal `SheafOfModules`, then invertibility,
then ampleness), not a task-scale one.  Refute by exhibiting a faithful
sheaf-FREE encoding of "`L` is ample and `L^{p²} ≅ 𝒪_Z`", or by finding a tensor
product of sheaves of modules at this pin.

**ROUTE 9, searched 2026-07-27 over the axis the first two sweeps never ranged
over — BASE CHANGE — and blocked by a defect in this leaf's own STATEMENT.**
Every classical route (Mumford §6, and refuted route 7's reduction to
`((ker[p])_red)⁰`) is written over an ALGEBRAICALLY CLOSED field, so the missing
step is "WLOG `K` algebraically closed".  That reduction is otherwise entirely
available and needs no new theory: `AbelianSchemeStruct.baseChange` and
`baseChange_mulByNat` already exist above, `ker[p]` of a base change is the base
change of `ker[p]` (pullback pasting), `Surjective` is stable under base change
(`Mathlib/AlgebraicGeometry/PullbackCarrier.lean:431`), and the descent re-enters
through declarations already in this file — `IsQuasiAffine` over `K̄` gives
`IsAffine` (the bridge above) gives `IsFinite` gives a finite point set, which
transports along the surjection into
`isFinite_ker_mulByNat_of_finite_preimage`.

What blocks it is that **`Spec K` is not known to be a ONE-POINT scheme here**, so
`Spec K̄ ⟶ Spec K` is not known to be surjective.  `(K : CommRingCat.{u})
[Field K]` puts a `Field` structure on the CARRIER `↑K` that Lean cannot connect
to `K`'s own `CommRing` instance, and at this pin the two are genuinely
independent: under `[Field K]`, `Subsingleton ↥(Spec K)` and `Unique ↥(Spec K)`
both FAIL to synthesize while `Nonempty ↥(Spec K)` succeeds — whereas all three
succeed for `Spec (CommRingCat.of F)` with `(F : Type u) [Field F]` and for
`Spec (S.residueField s)`, which is how `locallyQuasiFinite_mulByNat` below
actually instantiates this family.  So `hchar : ringChar K = p` constrains a
field structure that need not be the one `Spec K` is built from, and as written
the leaf asks for `ker[p]` over a base not known to be a field at all.

That is a FAITHFULNESS defect that makes the leaf HARDER than the theorem it is
meant to be, so a prover cannot repair it from inside.  The repair is a
cut-level restatement of the whole `_of_field`/`_of_field_char` family
(`finite_preimage_mulByNat_of_field`, this leaf,
`isAffine_ker_mulByNat_of_field_char`, `finite_ker_mulByNat_of_field_char`,
`isFinite_ker_mulByNat_of_field_char`) from `(K : CommRingCat.{u}) [Field K]` to
`(F : Type u) [Field F]` with base `Spec (CommRingCat.of F)`, after which route 9
goes through exactly as described above and this leaf becomes "the cube over an
ALGEBRAICALLY CLOSED field".  Refute by synthesizing `Subsingleton ↥(Spec K)`
from `[Field K]` alone — that is a one-line `example`.

**`hp` and `hchar` are deliberately carried even though the statement is true
without them** (`ker[n]` is quasi-affine for every `n ≠ 0`): without them this
leaf would silently duplicate the content the prime-to-characteristic sibling
needs.  Carrying them records that this is exactly the residue the Lie-algebra
route cannot reach. -/
theorem isQuasiAffine_ker_mulByNat_of_field_char {X : Scheme.{u}}
    (K : CommRingCat.{u}) [Field K] {fK : X ⟶ Spec K} (ab : AbelianSchemeStruct fK)
    (p : ℕ) (hp : p.Prime) (hchar : ringChar K = p) :
    Scheme.IsQuasiAffine (pullback (ab.mulByNat p) ab.zeroSection) :=
  sorry

/-- **`ker[p]` is an AFFINE SCHEME in characteristic `p`** (PROVEN 2026-07-27
over `isQuasiAffine_ker_mulByNat_of_field_char`; it used to be the sorry itself).

`ker[p] ⟶ Spec K` is proper as a base change of `[p]` (`isProper_mulByNat`),
hence universally closed, and `Spec K` is affine — so the general bridge
`isAffine_of_isQuasiAffine_of_universallyClosed` above turns the leaf's
`IsQuasiAffine` into `IsAffine`.

**This is a CHANGE OF SHAPE, NOT a reduction of content**: for a proper
`K`-scheme, quasi-affine, affine and finite are all equivalent.  The reason to
stop at `IsQuasiAffine` upstream is that it is literally what the
ample-line-bundle argument outputs (EGA II 5.1.2); see that leaf's docstring for
the classical proof, the corrected survey of what mathlib does and does not
have, and eight refuted routes with the check that would refute each
refutation. -/
theorem isAffine_ker_mulByNat_of_field_char {X : Scheme.{u}}
    (K : CommRingCat.{u}) [Field K] {fK : X ⟶ Spec K} (ab : AbelianSchemeStruct fK)
    (p : ℕ) (hp : p.Prime) (hchar : ringChar K = p) :
    IsAffine (pullback (ab.mulByNat p) ab.zeroSection) := by
  haveI : IsProper (ab.mulByNat p) := ab.isProper_mulByNat p
  haveI := isQuasiAffine_ker_mulByNat_of_field_char K ab p hp hchar
  exact isAffine_of_isQuasiAffine_of_universallyClosed
    (pullback.snd (ab.mulByNat p) ab.zeroSection)

/-- **`ker[p]` has FINITELY MANY POINTS in characteristic `p`** (PROVEN
2026-07-27 over `isAffine_ker_mulByNat_of_field_char`; it used to be the sorry
itself, cut down 2026-07-27 from `finite_preimage_mulByNat_of_field_char`).

`Spec K` has a single point, so this is one finite set: the underlying space of
`ker[p]` is finite, i.e. `ker[p]` is zero-dimensional.

**The proof is the "proper + affine ⟹ finite" bridge**, and it is pure scheme
theory with no abelian-variety content left in it.  `ker[p] ⟶ Spec K` is a base
change of `[p]`, hence PROPER (`isProper_mulByNat`); the leaf says the source is
an AFFINE scheme, and `Spec K` is affine, so the morphism is an affine morphism
(`isAffineHom_of_isAffine`).  Mathlib's
`IsFinite.iff_isProper_and_isAffineHom` then makes it a FINITE morphism, which
is `LocallyQuasiFinite` and `QuasiCompact`, so
`Scheme.Hom.finite_preimage_singleton` reads off the finite fibre.

Note this is a genuinely *different* route to `IsFinite` from the one
`isFinite_ker_mulByNat_of_field_char` below takes (that one goes through
Zariski's main theorem).  Both are kept: the ZMT bridge
`isFinite_ker_mulByNat_of_finite_preimage` is stated over an arbitrary base and
is what the general-`n` chain uses, while the affine bridge is what makes the
residue match the shape the theorem of the cube produces.

For the mathematics — why `d[p] = 0` kills the cheap route, the two classical
cube proofs, the re-verified survey of what is missing from the pin, and the
eight refuted cube-free routes — see `isQuasiAffine_ker_mulByNat_of_field_char`
above, which is now the leaf (`isAffine_ker_mulByNat_of_field_char` was itself
cut down to it 2026-07-27 and is PROVEN). -/
theorem finite_ker_mulByNat_of_field_char {X : Scheme.{u}}
    (K : CommRingCat.{u}) [Field K] {fK : X ⟶ Spec K} (ab : AbelianSchemeStruct fK)
    (p : ℕ) (hp : p.Prime) (hchar : ringChar K = p) :
    ∀ s : Spec K, (⇑(pullback.snd (ab.mulByNat p) ab.zeroSection) ⁻¹' {s}).Finite := by
  haveI : IsProper (ab.mulByNat p) := ab.isProper_mulByNat p
  haveI := isAffine_ker_mulByNat_of_field_char K ab p hp hchar
  haveI : IsFinite (pullback.snd (ab.mulByNat p) ab.zeroSection) :=
    IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
  exact fun s => Scheme.Hom.finite_preimage_singleton _ s

/-- **`ker[p]` is a finite group scheme in characteristic `p`** — equivalently,
`[p]` is an ISOGENY (PROVEN 2026-07-27 over `finite_ker_mulByNat_of_field_char`,
through the Zariski's-main-theorem bridge `isFinite_ker_mulByNat_of_finite_preimage`).

**What changed.**  The old leaf asked for finiteness of EVERY fibre of `[p]`.
The shearing block above proves — cube-free and over an arbitrary base — that
all fibres are finite as soon as this ONE fibre is
(`finite_preimage_mulByNat_of_isFinite_ker`).  So the whole residue became the
single statement every textbook actually proves: `ker[p]` is finite, of order
`p^{2g}`; and by `isFinite_ker_mulByNat_of_finite_preimage` even that is
reduced to a bare POINT SET being finite, `finite_ker_mulByNat_of_field_char`
above.  The chain from there to `finite_preimage_mulByNat_of_field_char` is
entirely proven.

**Where the leaf is now** (2026-07-27, third cut).
`finite_ker_mulByNat_of_field_char` and `isAffine_ker_mulByNat_of_field_char`
are both PROVEN; the sole remaining leaf on this route is
`isQuasiAffine_ker_mulByNat_of_field_char` — "`ker[p]` is a QUASI-AFFINE
scheme" — which for a proper `K`-scheme is EQUIVALENT to affineness and hence to
finiteness, so both cuts changed the shape and not the content.  They were made
because `IsQuasiAffine` is literally what the ample-line-bundle argument outputs
(EGA II 5.1.2), and the remaining step to `IsAffine` is now the proven bridge
`isAffine_of_isQuasiAffine_of_universallyClosed` rather than an obligation.  The
refuted cube-free routes and the corrected missing-machinery survey live in that
leaf's docstring; read it before attacking anything here.

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
the single new leaf `nonempty_module_infKernel_of_squareZero` (the Lie algebra
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
`nonempty_module_infKernel_of_squareZero`).  Writing `p = ringChar K`, the
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
