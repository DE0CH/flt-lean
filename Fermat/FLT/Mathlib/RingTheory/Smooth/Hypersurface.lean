/-
Fermat/FLT/Mathlib/RingTheory/Smooth/Hypersurface.lean — own work for the
Fermat project (not vendored from the FLT project).

# The Jacobian criterion for a HYPERSURFACE, in the form mathlib does not state

A quotient `R[X_v : v ∈ V] ⧸ (G)` by a SINGLE polynomial is standard smooth of
relative dimension `#V - 1` over `R` on the basic open where one of the partial
derivatives `∂G/∂X_j` is invertible.

That is the whole content of `Algebra.IsStandardSmoothOfRelativeDimension` for a
plane curve, a Weierstrass chart, an affine hypersurface of any dimension — and
mathlib has the machinery (`Algebra.PreSubmersivePresentation.naive`) without the
statement.

## Why this module exists

This development had TWO copies of the statement already, and both are
SPECIALISED to a Weierstrass chart, hence unusable anywhere else:

| copy | file |
|---|---|
| `Fermat.isStandardSmoothOfRelativeDimension_projChartAway` | `Fermat/FLT/ModularCurve/EllipticScheme.lean` (over `ℚ`) |
| `…MoretBailly…isStandardSmoothOfRelativeDimension_projChartAway` | `Fermat/FLT/Modularity/MoretBailly.lean` (over a field `F`) |

Both are stated about `projChartPolynomial E i` and `ProjChartVar i`, and the
`EllipticScheme` one is additionally UNREACHABLE from most of the tree: `X0.lean`
imports `EllipticScheme.lean` NON-publicly (deliberately — a `public import`
propagates the reserved token `over` and truncates a structure), so nothing
downstream of `X0` can name it.  A third consumer,
`Fermat/FLT/FreyCurve/MazurTorsion.lean`, needed it for the level-`37` sextic and
could reach neither copy.

Neither of those proofs uses anything about a Weierstrass equation.  This module
is that proof with the elliptic-curve vocabulary deleted: `ProjChartVar i` becomes
an arbitrary finite `V`, `projChartPolynomial E i` an arbitrary `G`, and the base
`ℚ` an arbitrary commutative ring.  Its statement is pure mathlib vocabulary, so
it imports mathlib and nothing else, and it elaborates in seconds.

## The construction (unchanged from the two copies)

`Algebra.PreSubmersivePresentation.naive` builds a pre-submersive presentation of
`R[X_σ] ⧸ (v_ι)` from an INJECTIVE assignment `a : ι → σ`, with
`jacobiMatrix_naive` computing the Jacobian matrix as `(v_i).pderiv (a i)`.  So:

* variables `σ := Option V`, i.e. the `X_v` together with one new `t`;
* relations `ι := Fin 2`, namely `G` and `t · ∂G/∂X_j - 1`;
* the assignment sends the first relation to `X_j` and the second to `t`, which is
  injective;
* the Jacobian matrix is LOWER TRIANGULAR,
  `[[∂G/∂X_j, 0], [t · ∂²G/∂X_j², ∂G/∂X_j]]`, with determinant `(∂G/∂X_j)²`, a unit
  in the quotient because the second relation says `t` inverts it;
* `dimension = #σ - #ι = (#V + 1) - 2 = #V - 1`.

The one piece of plumbing is the identification of the presented ring with `T`,

  `R[X_V, t] ⧸ (G, t·∂G/∂X_j - 1)`  ≃  `(R[X_V] ⧸ (G))_{∂G/∂X_j}` ,

built here by hand as a pair of mutually inverse maps (`Ideal.Quotient.liftₐ` one
way, `IsLocalization.lift` the other, compared on generators with
`MvPolynomial.ringHom_ext` and `IsLocalization.ringHom_ext`) rather than by chaining
`MvPolynomial.optionEquivLeft`, `Ideal.polynomialQuotientEquivQuotientPolynomial` and
`Localization.awayEquivAdjoin`.  That is markedly shorter, and it avoids the
`Algebra R (MvPolynomial V R ⧸ I)` SMul diamond — `Submodule.Quotient.instSMul'`
versus `Algebra.toSMul` — which defeats `IsScalarTower.of_algebraMap_eq` on the nose
and is why the maps below are compared as RING homs wherever the quotient is involved.

Then `SubmersivePresentation.ofAlgEquiv` transports the presentation onto `T`.
-/
module

public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv

@[expose] public section

universe u

namespace Fermat

open scoped Classical in
/-- **A HYPERSURFACE IS STANDARD SMOOTH OF RELATIVE DIMENSION `#V - 1` WHERE A PARTIAL
DERIVATIVE IS INVERTIBLE** (PROVEN).

For `G : R[X_v : v ∈ V]` with `V` finite and `j : V`, and `T` a localization of
`C := R[X_V] ⧸ (G)` away from the image of `∂G/∂X_j`, the composite `R → C → T` is
standard smooth of relative dimension `#V - 1`.

This is the generic form of `Fermat.isStandardSmoothOfRelativeDimension_projChartAway`
(`Fermat/FLT/ModularCurve/EllipticScheme.lean`); see the module docstring for the
construction and for why a third copy was needed. -/
theorem isStandardSmoothOfRelativeDimension_hypersurface_away
    {R : Type u} [CommRing R] {V : Type u} [Fintype V] [DecidableEq V]
    (G : MvPolynomial V R) (j : V) (T : Type u) [CommRing T]
    [Algebra (MvPolynomial V R ⧸ Ideal.span {G}) T]
    [IsLocalization.Away
      (Ideal.Quotient.mk (Ideal.span {G}) (MvPolynomial.pderiv j G) :
        MvPolynomial V R ⧸ Ideal.span {G}) T] :
    RingHom.IsStandardSmoothOfRelativeDimension (Nat.card V - 1)
      ((algebraMap (MvPolynomial V R ⧸ Ideal.span {G}) T).comp
        (algebraMap R (MvPolynomial V R ⧸ Ideal.span {G}))) := by
  classical
  algebraize [(algebraMap (MvPolynomial V R ⧸ Ideal.span {G}) T).comp
    (algebraMap R (MvPolynomial V R ⧸ Ideal.span {G}))]
  -- the two relations of the presentation, in the variables `(X_V, t)`
  set v : Fin 2 → MvPolynomial (Option V) R :=
    ![MvPolynomial.rename Option.some G,
      MvPolynomial.X none * MvPolynomial.rename Option.some (MvPolynomial.pderiv j G) - 1]
    with hv
  set P := MvPolynomial (Option V) R ⧸ (Ideal.span <| Set.range v) with hP
  -- `t` inverts `∂G/∂X_j` in `P`
  have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span <| Set.range v)
      (MvPolynomial.rename Option.some (MvPolynomial.pderiv j G))) := by
    have key : Ideal.Quotient.mk (Ideal.span <| Set.range v)
        (MvPolynomial.rename Option.some (MvPolynomial.pderiv j G))
        * Ideal.Quotient.mk _ (MvPolynomial.X none) = 1 := by
      rw [← map_mul, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk (Ideal.span <| Set.range v)),
        ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span ⟨1, by simp [hv, mul_comm]⟩
    exact ⟨⟨_, _, key, by rw [mul_comm]; exact key⟩, rfl⟩
  set dbar : MvPolynomial V R ⧸ Ideal.span {G} :=
    Ideal.Quotient.mk (Ideal.span {G}) (MvPolynomial.pderiv j G) with hdbar
  -- the ring map `C → P`
  have hkillw : ∀ a ∈ Ideal.span {G},
      (Ideal.Quotient.mk (Ideal.span <| Set.range v)) (MvPolynomial.rename Option.some a) = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    have hz : (Ideal.Quotient.mk (Ideal.span <| Set.range v))
        (MvPolynomial.rename Option.some G) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span ⟨0, by simp [hv]⟩
    rw [map_mul, map_mul, hz, mul_zero]
  set CtoP : (MvPolynomial V R ⧸ Ideal.span {G}) →ₐ[R] P :=
    Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ R (Ideal.span <| Set.range v)).comp
      (MvPolynomial.rename Option.some)) hkillw with hCtoP
  have hCtoP_mk : ∀ p, CtoP (Ideal.Quotient.mk _ p)
      = Ideal.Quotient.mk (Ideal.span <| Set.range v) (MvPolynomial.rename Option.some p) :=
    fun p => rfl
  -- the ring map `P → T`
  set g : Option V → T := fun o => match o with
    | none => IsLocalization.mk' T (1 : MvPolynomial V R ⧸ Ideal.span {G})
        ⟨dbar, Submonoid.mem_powers _⟩
    | some x => algebraMap (MvPolynomial V R ⧸ Ideal.span {G}) T
        (Ideal.Quotient.mk (Ideal.span {G}) (MvPolynomial.X x)) with hg
  have hrename : ∀ p : MvPolynomial V R,
      MvPolynomial.aeval g (MvPolynomial.rename Option.some p)
        = algebraMap (MvPolynomial V R ⧸ Ideal.span {G}) T
          (Ideal.Quotient.mk (Ideal.span {G}) p) := by
    have : ((MvPolynomial.aeval g : MvPolynomial (Option V) R →ₐ[R] T) :
          MvPolynomial (Option V) R →+* T).comp
          ((MvPolynomial.rename Option.some :
            MvPolynomial V R →ₐ[R] MvPolynomial (Option V) R) : MvPolynomial V R →+* _)
        = (algebraMap (MvPolynomial V R ⧸ Ideal.span {G}) T).comp
          (Ideal.Quotient.mk (Ideal.span {G})) := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun n => ?_)
      · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom,
          MvPolynomial.rename_C, MvPolynomial.aeval_C]
        exact IsScalarTower.algebraMap_apply R (MvPolynomial V R ⧸ Ideal.span {G}) T r
      · simp [hg]
    exact fun p => congrArg (fun f : MvPolynomial V R →+* T => f p) this
  have hginv : g none * algebraMap (MvPolynomial V R ⧸ Ideal.span {G}) T dbar = 1 := by
    show IsLocalization.mk' T (1 : MvPolynomial V R ⧸ Ideal.span {G})
      ⟨dbar, Submonoid.mem_powers _⟩
      * algebraMap (MvPolynomial V R ⧸ Ideal.span {G}) T dbar = 1
    rw [IsLocalization.mk'_spec, map_one]
  have hkillv : ∀ a ∈ Ideal.span (Set.range v), MvPolynomial.aeval g a = 0 := by
    intro a ha
    refine Submodule.span_induction ?_ (by simp) (by intro x y _ _ hx hy; simp [hx, hy])
      (by intro c x _ hx; simp [hx]) ha
    rintro _ ⟨k, rfl⟩
    fin_cases k
    · show MvPolynomial.aeval g (MvPolynomial.rename Option.some G) = 0
      rw [hrename, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), map_zero]
    · show MvPolynomial.aeval g (MvPolynomial.X none *
        MvPolynomial.rename Option.some (MvPolynomial.pderiv j G) - 1) = 0
      rw [map_sub, map_mul, MvPolynomial.aeval_X, hrename, map_one, ← hdbar, hginv, sub_self]
  set PtoT : P →ₐ[R] T := Ideal.Quotient.liftₐ _ (MvPolynomial.aeval g) hkillv with hPtoT
  have hPtoT_mk : ∀ q, PtoT (Ideal.Quotient.mk (Ideal.span <| Set.range v) q)
      = MvPolynomial.aeval g q := fun q => rfl
  -- the ring map `T → P`
  have hCtoP_dbar : CtoP dbar = Ideal.Quotient.mk (Ideal.span <| Set.range v)
      (MvPolynomial.rename Option.some (MvPolynomial.pderiv j G)) := rfl
  have hunits : ∀ y : Submonoid.powers dbar,
      IsUnit ((CtoP : (MvPolynomial V R ⧸ Ideal.span {G}) →+* P) y) := by
    rintro ⟨_, n, rfl⟩
    rw [show ((CtoP : (MvPolynomial V R ⧸ Ideal.span {G}) →+* P) (dbar ^ n))
      = (CtoP dbar) ^ n from map_pow _ _ _, hCtoP_dbar]
    exact hunit.pow n
  set TtoP : T →+* P := IsLocalization.lift hunits with hTtoP
  have hTtoP_alg : ∀ c, TtoP (algebraMap (MvPolynomial V R ⧸ Ideal.span {G}) T c) = CtoP c :=
    fun c => IsLocalization.lift_eq hunits c
  have hcomp : ∀ c : MvPolynomial V R ⧸ Ideal.span {G},
      PtoT (CtoP c) = algebraMap (MvPolynomial V R ⧸ Ideal.span {G}) T c := by
    intro c
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [hCtoP_mk, hPtoT_mk, hrename]
  -- the two composites are the identity
  have hTP : ∀ x : T, PtoT (TtoP x) = x := by
    have := IsLocalization.ringHom_ext (M := Submonoid.powers dbar) (S := T)
      (j := (PtoT : P →+* T).comp TtoP) (k := RingHom.id T)
      (RingHom.ext fun c => by
        simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply, AlgHom.coe_toRingHom]
        rw [hTtoP_alg, hcomp])
    exact fun x => congrArg (fun f : T →+* T => f x) this
  have hPT : ∀ x : P, TtoP (PtoT x) = x := by
    have : (TtoP.comp (PtoT : P →+* T)).comp (Ideal.Quotient.mk (Ideal.span <| Set.range v))
        = (RingHom.id P).comp (Ideal.Quotient.mk (Ideal.span <| Set.range v)) := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun n => ?_)
      · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply, AlgHom.coe_toRingHom]
        rw [hPtoT_mk]
        simp only [MvPolynomial.aeval_C]
        rw [IsScalarTower.algebraMap_apply R (MvPolynomial V R ⧸ Ideal.span {G}) T r, hTtoP_alg]
        exact (CtoP.commutes r).trans (by rfl)
      · cases n with
        | none =>
          simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply, AlgHom.coe_toRingHom]
          rw [hPtoT_mk]
          simp only [MvPolynomial.aeval_X]
          show TtoP (IsLocalization.mk' T (1 : MvPolynomial V R ⧸ Ideal.span {G})
            ⟨dbar, Submonoid.mem_powers _⟩) = _
          rw [IsLocalization.lift_mk'_spec]
          rw [map_one]
          change (1 : P) = CtoP dbar *
            Ideal.Quotient.mk (Ideal.span <| Set.range v) (MvPolynomial.X none)
          rw [hCtoP_dbar, ← map_mul, eq_comm, ← sub_eq_zero,
            ← map_one (Ideal.Quotient.mk (Ideal.span <| Set.range v)), ← map_sub,
            Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.subset_span ⟨1, by simp [hv, mul_comm]⟩
        | some x =>
          simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply, AlgHom.coe_toRingHom]
          rw [hPtoT_mk]
          simp only [MvPolynomial.aeval_X]
          show TtoP (algebraMap (MvPolynomial V R ⧸ Ideal.span {G}) T
            (Ideal.Quotient.mk (Ideal.span {G}) (MvPolynomial.X x))) = _
          rw [hTtoP_alg, hCtoP_mk, MvPolynomial.rename_X]
    intro x
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact congrArg (fun f : MvPolynomial (Option V) R →+* P => f q) this
  -- the isomorphism `P ≃ₐ[R] T`
  set eA : P ≃ₐ[R] T := AlgEquiv.ofRingEquiv
    (f := { (PtoT : P →+* T) with invFun := TtoP, left_inv := hPT, right_inv := hTP })
    (fun x => PtoT.commutes x) with heA
  -- `∂/∂t` kills everything pulled back from the `X_V`
  have hpd0 : ∀ p : MvPolynomial V R,
      MvPolynomial.pderiv (none : Option V) (MvPolynomial.rename Option.some p) = 0 := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p n hp => simp [hp]
  have ha : Function.Injective (![some j, none] : Fin 2 → Option V) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  have hdet : (Algebra.PreSubmersivePresentation.naive (R := R) (v := v)
      ![some j, none] ha).jacobiMatrix.det
      = (MvPolynomial.rename Option.some (MvPolynomial.pderiv j G)) ^ 2 := by
    rw [Matrix.det_fin_two, Algebra.PreSubmersivePresentation.jacobiMatrix_naive,
      Algebra.PreSubmersivePresentation.jacobiMatrix_naive,
      Algebra.PreSubmersivePresentation.jacobiMatrix_naive,
      Algebra.PreSubmersivePresentation.jacobiMatrix_naive]
    simp only [hv, Matrix.cons_val_zero, Matrix.cons_val_one,
      map_sub, MvPolynomial.pderiv_X, Derivation.leibniz,
      MvPolynomial.pderiv_rename (Option.some_injective V), hpd0]
    simp [sq]
  refine (Algebra.SubmersivePresentation.ofAlgEquiv
    ⟨Algebra.PreSubmersivePresentation.naive (R := R) (v := v) ![some j, none] ha, ?_⟩
    eA).isStandardSmoothOfRelativeDimension ?_
  · rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, hdet, map_pow]
    refine IsUnit.pow 2 ?_
    show IsUnit (Ideal.Quotient.mk (Ideal.span <| Set.range v)
      (MvPolynomial.rename Option.some (MvPolynomial.pderiv j G)))
    exact hunit
  · show Nat.card (Option V) - Nat.card (Fin 2) = Nat.card V - 1
    simp [Nat.card_eq_fintype_card]

end Fermat
