/-
CurveDimension.lean — own work for the Fermat project (not vendored).

**THE DIMENSION FORMULA FOR A SMOOTH CURVE OVER A FIELD**, in the one form the
`X_0(N)` group-law chain of `MazurTorsion.lean` consumes: for a scheme `X` smooth of
relative dimension `1` over a field `K` and a point `x` of `X`,

    `ringKrullDim 𝒪_{X,x} = 0  ↔  κ(x) is TRANSCENDENTAL over K`,

i.e. `x` is a maximal point of `X` exactly when its residue field has transcendence
degree `1`.  The classical formula is `dim 𝒪_{X,x} + trdeg_K κ(x) = dim X`; in relative
dimension `1` both sides of that are `0` or `1`, so the numerical content collapses to
the displayed dichotomy and NO transcendence degree has to be defined.

WHY THIS FILE EXISTS.  The consumer is
`ringKrullDim_stalk_eq_zero_of_mono_of_curve_over_field` — "a quasi-finite map of smooth
`K`-curves carries generic points to generic points" — which is the single leaf left of
`X0GenusOne`'s miracle-flatness cut in `MazurTorsion.lean`.  That statement compares TWO
points on TWO different schemes, so it cannot be settled inside one affine chart: the
invariant that travels along `u` is the residue field, not the chart.  Everything here
is therefore stated about `κ(x)`, and the transfer along `u` is mathlib's
`AlgebraicGeometry.FormallyUnramified` instance
`Algebra.IsSeparable (Y.residueField (f x)) (X.residueField x)`.

THE PROOF, and it is short because mathlib now has the local structure theorem.
`Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial` factors an affine
chart `A` of `X` as `K → K[X₁] → A` with the second map ÉTALE.  Write `Q = p ∩ K[X₁]` for
the contraction of the prime `p` of `x`.  Then:

* `p` is a MINIMAL prime of `A` iff `Q = ⊥`.  (⟸) étale is quasi-finite, and a
  quasi-finite algebra has discrete fibres, so two primes with the same contraction and
  `P ≤ p` are equal (`Algebra.QuasiFinite.eq_of_le_of_under_eq`).  (⟹) étale is flat, so
  going-down holds and a prime below `Q` is hit by a prime below `p`.
* `Q = ⊥` iff `κ(p)` is transcendental over `K`.  At `Q = ⊥` the field `κ(p)` contains
  `K[X₁]`, whose variable is transcendental; at `Q ≠ ⊥` the ideal `Q` is maximal
  (`K[X₁]` is a PID), so `κ(Q)` is algebraic over `K` by the Nullstellensatz for Jacobson
  rings, and `κ(p)/κ(Q)` is FINITE because `A` is quasi-finite over `K[X₁]`.

The scheme-level statement is then chart bookkeeping, with one point worth naming: the
`K`-algebra structure on `X.residueField x` must be the CANONICAL one, coming from
`strX.residueFieldMap`, and not the chart's — otherwise the two ends of the comparison
along `u` carry unrelated `K`-structures and `Algebra.IsAlgebraic.trans` does not apply.
`residueFieldAlgebra` is that canonical structure; `ringKrullDim_stalk_eq_zero_iff`
proves the chart's structure equal to it (`Algebra.algebra_ext`), which is exactly the
naturality `germ ∘ appLE = germ ∘ appTop` plus `germ ≫ residue = evaluation`.

FAITHFULNESS.  Both smoothness hypotheses of the consumer are load-bearing and the
docstring on the leaf in `MazurTorsion.lean` gives the counterexample for dropping the
one on the target (a smooth curve inside a smooth surface).  Here that shows up as: the
argument uses `ringKrullDim_stalk_eq_zero_iff` at BOTH points, so both structure
morphisms must be smooth of relative dimension `1`.
-/
module

public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.ResidueField

@[expose] public section

universe u

namespace Fermat

open Algebra

/-! ### The affine line -/

/-- **The affine line over a field is a principal ideal ring.** -/
theorem isPrincipalIdealRing_mvPolynomial_fin_one (K : Type u) [Field K] :
    IsPrincipalIdealRing (MvPolynomial (Fin 1) K) :=
  IsPrincipalIdealRing.of_surjective
    (MvPolynomial.uniqueAlgEquiv K (Fin 1)).symm.toRingEquiv
    (MvPolynomial.uniqueAlgEquiv K (Fin 1)).symm.surjective

/-! ### The dimension dichotomy over an étale chart of the affine line -/

section Etale

variable {K : Type u} [Field K] {A : Type u} [CommRing A] [Algebra K A]
variable [Algebra (MvPolynomial (Fin 1) K) A] [Algebra.Etale (MvPolynomial (Fin 1) K) A]
  [IsScalarTower K (MvPolynomial (Fin 1) K) A]
variable (p : Ideal A) [p.IsPrime]

omit [Algebra K A] [IsScalarTower K (MvPolynomial (Fin 1) K) A] in
/-- **A prime of an étale algebra over the affine line is MINIMAL exactly when it
contracts to `⊥`.**

`⟸` is quasi-finiteness (discrete fibres); `⟹` is going-down, available because étale
algebras are flat. -/
theorem height_eq_zero_iff_comap_eq_bot :
    p.height = 0 ↔ p.comap (algebraMap (MvPolynomial (Fin 1) K) A) = ⊥ := by
  haveI : Algebra.FormallyUnramified (MvPolynomial (Fin 1) K) A := inferInstance
  haveI : Algebra.EssFiniteType (MvPolynomial (Fin 1) K) A := inferInstance
  haveI : Algebra.QuasiFinite (MvPolynomial (Fin 1) K) A := inferInstance
  haveI : Algebra.HasGoingDown (MvPolynomial (Fin 1) K) A := inferInstance
  haveI hQp : (p.comap (algebraMap (MvPolynomial (Fin 1) K) A)).IsPrime :=
    Ideal.comap_isPrime _ _
  haveI hlo : p.LiesOver (p.comap (algebraMap (MvPolynomial (Fin 1) K) A)) := ⟨rfl⟩
  rw [Ideal.height_eq_zero_iff]
  constructor
  · intro h
    obtain ⟨P', hP'le, hP'prime, hP'lo⟩ :=
      Ideal.exists_ideal_le_liesOver_of_le
        (p := (⊥ : Ideal (MvPolynomial (Fin 1) K)))
        (q := p.comap (algebraMap (MvPolynomial (Fin 1) K) A)) p bot_le
    haveI := hP'prime
    haveI := hP'lo
    have hPp : P' = p := le_antisymm hP'le (h.2 ⟨hP'prime, bot_le⟩ hP'le)
    have hover := P'.over_def (⊥ : Ideal (MvPolynomial (Fin 1) K))
    rw [hPp] at hover
    exact hover.symm
  · intro h
    refine ⟨⟨inferInstance, bot_le⟩, fun P' hP'prime hle => ?_⟩
    haveI := hP'prime.1
    refine le_of_eq (Algebra.QuasiFinite.eq_of_le_of_under_eq
      (R := MvPolynomial (Fin 1) K) P' p hle ?_).symm
    have h1 : P'.under (MvPolynomial (Fin 1) K) ≤ p.under (MvPolynomial (Fin 1) K) :=
      Ideal.comap_mono hle
    have h2 : p.under (MvPolynomial (Fin 1) K) = ⊥ := h
    rw [h2] at h1 ⊢
    exact le_bot_iff.mp h1

/-- **The residue field at `p` is TRANSCENDENTAL over `K` exactly when `p` contracts
to `⊥`.**

At `Q = ⊥` the field `κ(p)` receives `K[X₁]` injectively and the variable is
transcendental; at `Q ≠ ⊥` the ideal `Q` is maximal in the PID `K[X₁]`, so `κ(Q)` is
algebraic over `K` (Nullstellensatz for Jacobson rings) and `κ(p)` is FINITE over `κ(Q)`
by quasi-finiteness. -/
theorem comap_eq_bot_iff_not_isAlgebraic :
    p.comap (algebraMap (MvPolynomial (Fin 1) K) A) = ⊥ ↔
      ¬ Algebra.IsAlgebraic K p.ResidueField := by
  haveI : Algebra.FormallyUnramified (MvPolynomial (Fin 1) K) A := inferInstance
  haveI : Algebra.EssFiniteType (MvPolynomial (Fin 1) K) A := inferInstance
  haveI : Algebra.QuasiFinite (MvPolynomial (Fin 1) K) A := inferInstance
  haveI := isPrincipalIdealRing_mvPolynomial_fin_one K
  haveI hQp : (p.comap (algebraMap (MvPolynomial (Fin 1) K) A)).IsPrime :=
    Ideal.comap_isPrime _ _
  set Q : Ideal (MvPolynomial (Fin 1) K) := p.comap (algebraMap (MvPolynomial (Fin 1) K) A)
    with hQdef
  -- the residue-field embedding `κ(Q) ↪ κ(p)`, as a `K`-algebra map
  let f : Q.ResidueField →ₐ[K] p.ResidueField :=
    Ideal.ResidueField.mapₐ Q p (IsScalarTower.toAlgHom K (MvPolynomial (Fin 1) K) A) hQdef
  constructor
  · intro hbot halg
    haveI : Algebra.IsAlgebraic K Q.ResidueField :=
      Algebra.IsAlgebraic.of_injective f f.toRingHom.injective
    have hinj : Function.Injective (algebraMap (MvPolynomial (Fin 1) K) Q.ResidueField) := by
      rw [RingHom.injective_iff_ker_eq_bot, Ideal.ker_algebraMap_residueField]
      exact hbot
    haveI : Algebra.IsAlgebraic K (MvPolynomial (Fin 1) K) :=
      Algebra.IsAlgebraic.of_injective
        (IsScalarTower.toAlgHom K (MvPolynomial (Fin 1) K) Q.ResidueField) hinj
    exact (MvPolynomial.algebraicIndependent_X (Fin 1) K).transcendental 0
      (Algebra.IsAlgebraic.isAlgebraic _)
  · intro h
    by_contra hne
    refine h ?_
    haveI hQmax : Q.IsMaximal := IsPrime.to_maximal_ideal hne
    haveI : Algebra.IsIntegral K (MvPolynomial (Fin 1) K ⧸ Q) :=
      ⟨fun x => MvPolynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing Q x⟩
    haveI : Algebra.IsAlgebraic K Q.ResidueField :=
      (AlgEquiv.ofBijective (IsScalarTower.toAlgHom K (MvPolynomial (Fin 1) K ⧸ Q) Q.ResidueField)
        (Ideal.bijective_algebraMap_quotient_residueField Q)).isAlgebraic
    letI : Algebra Q.ResidueField p.ResidueField := f.toRingHom.toAlgebra
    haveI : IsScalarTower K Q.ResidueField p.ResidueField :=
      IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
    haveI : IsScalarTower (MvPolynomial (Fin 1) K) Q.ResidueField p.ResidueField :=
      IsScalarTower.of_algebraMap_eq fun r => by
        simp [f, RingHom.algebraMap_toAlgebra,
          IsScalarTower.algebraMap_apply (MvPolynomial (Fin 1) K) A p.ResidueField]
    haveI : Algebra.QuasiFinite (MvPolynomial (Fin 1) K) p.ResidueField := inferInstance
    haveI : Algebra.QuasiFinite Q.ResidueField p.ResidueField :=
      Algebra.QuasiFinite.of_restrictScalars (MvPolynomial (Fin 1) K) _ _
    haveI : Module.Finite Q.ResidueField p.ResidueField := Module.Finite.of_quasiFinite
    exact Algebra.IsAlgebraic.trans K Q.ResidueField p.ResidueField

/-- **THE DIMENSION DICHOTOMY over an étale chart of the affine line.** -/
theorem height_eq_zero_iff_not_isAlgebraic_residueField :
    p.height = 0 ↔ ¬ Algebra.IsAlgebraic K p.ResidueField :=
  (height_eq_zero_iff_comap_eq_bot p).trans (comap_eq_bot_iff_not_isAlgebraic p)

end Etale

/-! ### The dimension formula, ring level -/

section Ring

variable {K : Type u} [Field K] {A : Type u} [CommRing A] [Algebra K A]

/-- **THE DIMENSION FORMULA, RING LEVEL.**  A localization at a prime `p` of a standard
smooth `K`-algebra of relative dimension one is zero-dimensional exactly when its residue
field is transcendental over `K`.

Stated for an ARBITRARY localization `S` rather than for `Localization.AtPrime p`, for
the same reason `ringKrullDim_localization_le_of_isStandardSmoothOfRelativeDimension`
gives in `CurveExtension.lean`: the scheme-level consumer holds a stalk, a colimit in
`CommRingCat`, and unifying that against the concrete `Localization.AtPrime p` sends
`whnf` into the colimit. -/
theorem ringKrullDim_eq_zero_iff_not_isAlgebraic
    [Algebra.IsStandardSmoothOfRelativeDimension 1 K A] (p : Ideal A) [p.IsPrime]
    (S : Type u) [CommRing S] [IsLocalRing S] [Algebra A S] [IsLocalization.AtPrime S p]
    [Algebra K S] [IsScalarTower K A S] :
    ringKrullDim S = 0 ↔ ¬ Algebra.IsAlgebraic K (IsLocalRing.ResidueField S) := by
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial 1 K A
  letI : Algebra (MvPolynomial (Fin 1) K) A := g.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin 1) K) A := by
    rw [← RingHom.etale_algebraMap]; rwa [RingHom.algebraMap_toAlgebra]
  haveI : IsScalarTower K (MvPolynomial (Fin 1) K) A :=
    IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p S, WithBot.coe_eq_zero,
    height_eq_zero_iff_not_isAlgebraic_residueField (K := K) p]
  haveI : IsScalarTower K A (IsLocalRing.ResidueField S) := inferInstance
  haveI : IsScalarTower K A p.ResidueField := inferInstance
  exact not_congr ((IsLocalRing.ResidueField.mapAlgEquiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) S)).restrictScalars
      K).isAlgebraic_iff

end Ring

end Fermat

/-! ### The dimension formula, scheme level -/

namespace AlgebraicGeometry

open CategoryTheory Opposite

/-- **The canonical `K`-algebra structure on the residue field of a point of a
`K`-scheme**, namely `K ≅ Γ(Spec K, ⊤) → Γ(X, ⊤) → κ(x)`.

Not an instance: it depends on the structure morphism, which is data.  It is
`@[reducible]` so that `letI` uses of it unify. -/
@[reducible] noncomputable def residueFieldAlgebra {K : Type u} [Field K] {X : Scheme.{u}}
    (strX : X ⟶ Spec (CommRingCat.of K)) (x : X) : Algebra K (X.residueField x) :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ strX.appTop ≫ X.Γevaluation x).hom.toAlgebra

/-- **THE DIMENSION FORMULA, SCHEME LEVEL**: on a scheme smooth of relative dimension `1`
over a field `K`, a point is a maximal point exactly when its residue field is
transcendental over `K`. -/
theorem ringKrullDim_stalk_eq_zero_iff {K : Type u} [Field K] {X : Scheme.{u}}
    (strX : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 1 strX] (x : X) :
    letI := residueFieldAlgebra strX x
    ringKrullDim (X.presheaf.stalk x) = 0 ↔ ¬ Algebra.IsAlgebraic K (X.residueField x) := by
  obtain ⟨U, hU, V, hV, hxV, e, hss⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := strX) x
  haveI : Subsingleton (Spec (CommRingCat.of K)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have hUtop : U = ⊤ := by
    have hmem : strX.base x ∈ U := e hxV
    exact le_antisymm le_top fun y _ => (Subsingleton.elim y (strX.base x)) ▸ hmem
  subst hUtop
  letI : Algebra K Γ(X, V) :=
    ((strX.appLE ⊤ V e).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.toRingHom).toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 1 K Γ(X, V) := by
    rw [← RingHom.isStandardSmoothOfRelativeDimension_algebraMap, RingHom.algebraMap_toAlgebra]
    exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _ _ hss
  letI : Algebra Γ(X, V) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (U := V) ⟨x, hxV⟩
  haveI : IsLocalization.AtPrime (X.presheaf.stalk x) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨x, hxV⟩
  letI : Algebra K (X.presheaf.stalk x) :=
    ((X.presheaf.germ V x hxV).hom.comp (algebraMap K Γ(X, V))).toAlgebra
  haveI : IsScalarTower K Γ(X, V) (X.presheaf.stalk x) := IsScalarTower.of_algebraMap_eq' rfl
  have key := Fermat.ringKrullDim_eq_zero_iff_not_isAlgebraic (K := K)
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal (X.presheaf.stalk x)
  refine key.trans (not_congr ?_)
  -- the chart's `K`-algebra structure on `κ(x)` IS the canonical one
  have halg : (IsLocalRing.ResidueField.algebra (R₀ := K)
      (R := X.presheaf.stalk x)) = residueFieldAlgebra strX x := by
    refine Algebra.algebra_ext _ _ fun r => ?_
    show IsLocalRing.residue _ ((X.presheaf.germ V x hxV).hom
        ((strX.appLE ⊤ V e).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom r))) = _
    show _ = ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ strX.appTop ≫ X.Γevaluation x).hom r
    have hcomp : (strX.appLE ⊤ V e ≫ X.presheaf.germ V x hxV ≫ X.residue x)
        = strX.appTop ≫ X.Γevaluation x := by
      rw [Scheme.Hom.appLE, Category.assoc, ← Category.assoc (X.presheaf.map (homOfLE e).op),
        X.presheaf.germ_res]
      rfl
    exact congrArg (fun (f : Γ(Spec (CommRingCat.of K), ⊤) ⟶ X.residueField x) => f.hom
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom r)) hcomp
  exact iff_of_eq (congrArg (fun i : Algebra K ↥(X.residueField x) =>
    @Algebra.IsAlgebraic K ↥(X.residueField x) _ _ i) halg)

/-- **A QUASI-FINITE MAP OF SMOOTH CURVES OVER A FIELD CARRIES GENERIC POINTS TO GENERIC
POINTS** — the general form of `MazurTorsion.lean`'s
`ringKrullDim_stalk_eq_zero_of_mono_of_curve_over_field`, which is this theorem.

`Mono u` is used only through `FormallyUnramified u`; together with `LocallyOfFiniteType u`
(free from `locallyOfFiniteType_of_comp`) mathlib's instance makes `κ(x)` SEPARABLE, hence
algebraic, over `κ(u x)`.  So `κ(x)` transcendental over `K` forces `κ(u x)` transcendental
over `K`, and `ringKrullDim_stalk_eq_zero_iff` reads that off at both ends.

The scalar tower `K → κ(u x) → κ(x)` is where `hu : u ≫ jstr = strX` enters, through
`Scheme.Γevaluation_naturality` and `Scheme.Hom.comp_appTop`. -/
theorem ringKrullDim_stalk_eq_zero_of_mono_of_curve_over_field
    {K : Type u} [Field K] {X J : Scheme.{u}}
    {strX : X ⟶ Spec (CommRingCat.of K)} {jstr : J ⟶ Spec (CommRingCat.of K)}
    (hXsmooth : SmoothOfRelativeDimension 1 strX)
    (hJsmooth : SmoothOfRelativeDimension 1 jstr)
    (u : X ⟶ J) (hu : u ≫ jstr = strX) (hmono : Mono u) (x : X)
    (hx : ringKrullDim (X.presheaf.stalk x) = 0) :
    ringKrullDim (J.presheaf.stalk (u.base x)) = 0 := by
  haveI := hXsmooth
  haveI := hJsmooth
  haveI := hmono
  haveI hXsm : Smooth strX := SmoothOfRelativeDimension.smooth (n := 1) (f := strX)
  haveI hftX : LocallyOfFiniteType strX := inferInstance
  haveI hftu : LocallyOfFiniteType u := by
    haveI : LocallyOfFiniteType (u ≫ jstr) := hu ▸ hftX
    exact locallyOfFiniteType_of_comp u jstr
  haveI hfu : FormallyUnramified u := inferInstance
  letI : Algebra K ↥(X.residueField x) := residueFieldAlgebra strX x
  letI : Algebra K ↥(J.residueField (u.base x)) := residueFieldAlgebra jstr (u.base x)
  letI : Algebra ↥(J.residueField (u.base x)) ↥(X.residueField x) :=
    (u.residueFieldMap x).hom.toAlgebra
  haveI htower : IsScalarTower K ↥(J.residueField (u.base x)) ↥(X.residueField x) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    show ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ strX.appTop ≫ X.Γevaluation x).hom
      = (u.residueFieldMap x).hom.comp
          ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ jstr.appTop ≫ J.Γevaluation (u.base x)).hom
    have hnat : ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ jstr.appTop ≫
        J.Γevaluation (u.base x)) ≫ u.residueFieldMap x
        = (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ strX.appTop ≫ X.Γevaluation x := by
      simp only [Category.assoc]
      rw [Scheme.Γevaluation_naturality, ← Category.assoc jstr.appTop,
        ← Scheme.Hom.comp_appTop, hu]
    exact congrArg CommRingCat.Hom.hom hnat.symm
  haveI : Algebra.IsSeparable ↥(J.residueField (u.base x)) ↥(X.residueField x) := inferInstance
  have hnX : ¬ Algebra.IsAlgebraic K ↥(X.residueField x) :=
    (ringKrullDim_stalk_eq_zero_iff strX x).mp hx
  refine (ringKrullDim_stalk_eq_zero_iff jstr (u.base x)).mpr fun halgJ => hnX ?_
  haveI := halgJ
  haveI : Algebra.IsAlgebraic ↥(J.residueField (u.base x)) ↥(X.residueField x) :=
    Algebra.IsSeparable.isAlgebraic _ _
  exact Algebra.IsAlgebraic.trans K ↥(J.residueField (u.base x)) ↥(X.residueField x)

end AlgebraicGeometry
