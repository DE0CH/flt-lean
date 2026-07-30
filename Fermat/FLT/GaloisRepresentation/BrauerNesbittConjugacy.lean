/-
BrauerNesbittConjugacy.lean — own work for the Fermat project (not
vendored from the FLT project).

# Brauer–Nesbitt conjugacy in dimension 2 over a finite coefficient field

The abstract (topology-free) core shared by the Chebotarev–Brauer–Nesbitt
conjugacy leaves `exists_conj_of_charFrob_eq`
(`HardlyRamified/Deformation.lean`) and `exists_conj_of_charFrob_eq_away`
(`Modularity/Patching.lean`): two representations of an abstract group
`G` on 2-dimensional spaces over a finite field `k` whose characteristic
polynomials agree at EVERY group element, the second irreducible, are
intertwined by a linear isomorphism (Brauer–Nesbitt; Curtis–Reiner,
*Methods of Representation Theory* §30.16, hand-rolled at dimension 2;
Diamond–Darmon–Taylor, *Fermat's Last Theorem* (1995), Lemma 3.27).

Proof route (dimension-2 elementary, valid in EVERY characteristic —
including 2, where the characteristic-zero trace argument of
`Modularity/Interface.lean`'s `nonempty_linearEquiv_of_trace_eq` breaks
because `tr 1 = 2 = 0`):

1. **Irreducibility transfer** (`rep_isIrreducible_of_charpoly_eq`): if
   `τ` had a stable line, the two diagonal characters `α, β : G →* kˣ` of
   that line and its quotient would split every characteristic polynomial
   `charpoly (ρ g) = (X − α g)(X − β g)`; twisting `ρ` by `α⁻¹` produces
   the `1 ⊕ χ` charpoly shape with `χ = β·α⁻¹`, and the
   Kolchin/common-eigenvector machinery of `BrauerNesbitt.lean`
   (transferred to abstract groups in
   `rep_exists_stable_submodule_of_charpoly_eq_units`) yields a stable
   line for the twist, hence for `ρ` — refuting irreducibility.

2. **Simple versus simple** (`exists_linearEquiv_of_charpoly_eq`): both
   spaces are then simple modules over `A = MonoidAlgebra k G`. Either a
   nonzero `A`-hom `W' → W` exists — bijective by simplicity of the
   target plus rank–nullity — or the Jacobson density theorem produces a
   projector `r ∈ A` acting as the identity on `W` and as zero on `W'`,
   making EVERY `b ∈ A` traceless on `W`
   (`tr_W b = tr_W (r·b) = tr_{W'} (r·b) = 0`). That is impossible over a
   finite coefficient field (`false_of_trace_toModuleEnd_eq_zero`): the
   commutant `D = End_A W` is a finite division ring — a FIELD by little
   Wedderburn — with `dim_k D · dim_D W = dim_k W = 2`; if `dim_k D = 1`,
   every `A`-endomorphism is a `k`-scalar and a rank-one projection is
   realized by an algebra element via Jacobson density, of trace
   `1 ≠ 0`; if `dim_k D = 2`, then `W ≃ D` by evaluation and
   multiplication by an element of nonzero field trace — which exists by
   separability of the finite extension `D/k` — is realized, again of
   nonzero trace.
-/
module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.LinearAlgebra.Dimension.Free
-- the shared Galois-level conjugacy node states `GaloisRep`, `charFrob`
-- and the prime-to-place dictionary, so those two homes are public
public import Fermat.FLT.Deformations.RepresentationTheory.GaloisRep
public import Fermat.FLT.Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Fermat.FLT.GaloisRepresentation.Chebotarev
import Fermat.FLT.GaloisRepresentation.BrauerNesbitt
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.LittleWedderburn
import Mathlib.RingTheory.Trace.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.Finiteness.Cardinality

@[expose] public section

namespace GaloisRepresentation

open Polynomial

universe uk uG uW uW' uA

variable {k : Type uk} [Field k] {G : Type uG} [Group G]

/-!
## Step 0: invariant submodules against irreducibility, and stable lines
-/

/-- **A nonzero proper stable submodule refutes irreducibility** (the
`Representation`-level form of `Chebotarev.lean`'s
`not_isIrreducible_of_invariant_submodule`, over an abstract group and an
abstract coefficient field). -/
lemma rep_not_isIrreducible_of_stable_submodule
    {W : Type uW} [AddCommGroup W] [Module k W]
    (ρ : Representation k G W) (U : Submodule k W)
    (hne : U ≠ ⊥) (htop : U ≠ ⊤)
    (hinv : ∀ g w, w ∈ U → ρ g w ∈ U) :
    ¬ ρ.IsIrreducible := by
  intro hirr
  haveI : IsSimpleOrder (Subrepresentation ρ) := hirr
  rcases eq_bot_or_eq_top
    (⟨U, fun g w hw => hinv g w hw⟩ : Subrepresentation ρ) with hP | hP
  · exact hne (congrArg Subrepresentation.toSubmodule hP)
  · exact htop (congrArg Subrepresentation.toSubmodule hP)

/-- **Stable-line extraction in dimension 2** (the `Representation`-level
form of `Chebotarev.lean`'s `exists_stable_line_of_not_isIrreducible`): a
non-irreducible representation on a 2-dimensional space has a nonzero
vector whose line is stable under every group element. -/
lemma rep_exists_stable_line_of_not_isIrreducible
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    (hfr : Module.finrank k W = 2)
    (τ : Representation k G W) (hirr : ¬ τ.IsIrreducible) :
    ∃ v : W, v ≠ 0 ∧ ∀ g, τ g v ∈ Submodule.span k {v} := by
  classical
  haveI : Nontrivial W := by
    rw [← Module.finrank_pos_iff (R := k)]
    omega
  haveI : Nontrivial (Subrepresentation τ) := ⟨⊥, ⊤, fun hbt => by
    have h := congrArg Subrepresentation.toSubmodule hbt
    exact bot_ne_top (α := Submodule k W) h⟩
  obtain ⟨P, hPbot, hPtop⟩ : ∃ P : Subrepresentation τ, P ≠ ⊥ ∧ P ≠ ⊤ := by
    by_contra hall
    push Not at hall
    exact hirr ⟨fun P => or_iff_not_imp_left.mpr (hall P)⟩
  have hbot' : P.toSubmodule ≠ ⊥ := fun h =>
    hPbot (Subrepresentation.toSubmodule_injective
      (h.trans (rfl : (⊥ : Subrepresentation _).toSubmodule = ⊥).symm))
  have htop' : P.toSubmodule ≠ ⊤ := fun h =>
    hPtop (Subrepresentation.toSubmodule_injective
      (h.trans (rfl : (⊤ : Subrepresentation _).toSubmodule = ⊤).symm))
  have hlt : Module.finrank k P.toSubmodule < 2 :=
    hfr ▸ Submodule.finrank_lt htop'
  have hpos : 0 < Module.finrank k P.toSubmodule := by
    rw [Module.finrank_pos_iff]
    exact Submodule.nontrivial_iff_ne_bot.mpr hbot'
  have h1 : Module.finrank k P.toSubmodule = 1 :=
    Nat.le_antisymm (Nat.lt_succ_iff.mp hlt) hpos
  obtain ⟨v₀, hv₀ne, hv₀span⟩ := finrank_eq_one_iff'.mp h1
  refine ⟨(v₀ : W), fun h0 => hv₀ne (Subtype.ext h0), fun g => ?_⟩
  obtain ⟨c, hc⟩ := hv₀span ⟨τ g (v₀ : W), P.apply_mem_toSubmodule g v₀.2⟩
  exact Submodule.mem_span_singleton.mpr ⟨c, congrArg Subtype.val hc⟩

/-!
## Step 1: characters of a stable line and the split charpoly shape
-/

/-- **The two diagonal characters of a reducible 2-dimensional
representation**: a stable line spanned by `v ≠ 0` carries a character
`α` (the scalar of the line action, a unit since the group acts
invertibly), and together with the determinant character it splits every
characteristic polynomial: `charpoly (τ g) = (X − α g)(X − β g)`. The
second root is produced as `β = det·α⁻¹`, which is multiplicative for
free; the factorization is Cayley–Hamilton bookkeeping — `α g` is an
eigenvalue, hence a root of the monic quadratic `charpoly (τ g)`, whose
complementary root is `det/α`. -/
lemma rep_exists_characters_of_stable_line
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hfr : Module.finrank k W = 2)
    (τ : Representation k G W) {v : W} (hv : v ≠ 0)
    (hstab : ∀ g, τ g v ∈ Submodule.span k {v}) :
    ∃ α β : G →* kˣ, ∀ g,
      (τ g).charpoly =
        (X - C ((α g : kˣ) : k)) * (X - C ((β g : kˣ) : k)) := by
  classical
  have hex : ∀ g, ∃ c : k, c • v = τ g v := fun g =>
    Submodule.mem_span_singleton.mp (hstab g)
  choose c hc using hex
  have huniq : ∀ a b : k, a • v = b • v → a = b := by
    intro a b hab
    by_contra hne
    have h0 : (a - b) • v = 0 := by rw [sub_smul, hab, sub_self]
    rcases smul_eq_zero.mp h0 with h | h
    · exact hne (sub_eq_zero.mp h)
    · exact hv h
  have hone : c 1 = 1 := by
    refine huniq _ _ ?_
    rw [hc, map_one, one_smul]
    rfl
  have hmul : ∀ g h : G, c (g * h) = c g * c h := by
    intro g h
    refine huniq _ _ ?_
    calc c (g * h) • v = τ (g * h) v := hc _
      _ = τ g (τ h v) := by rw [map_mul]; rfl
      _ = τ g (c h • v) := by rw [← hc]
      _ = c h • τ g v := map_smul _ _ _
      _ = c h • (c g • v) := by rw [← hc]
      _ = (c g * c h) • v := by rw [smul_smul, mul_comm]
  have hunit : ∀ g, IsUnit (c g) := by
    intro g
    refine isUnit_iff_exists.mpr ⟨c g⁻¹, ?_, ?_⟩
    · rw [← hmul, mul_inv_cancel, hone]
    · rw [← hmul, inv_mul_cancel, hone]
  set α : G →* kˣ := MonoidHom.mk' (fun g => (hunit g).unit)
    (fun g h => Units.ext (by
      simp only [IsUnit.unit_spec, Units.val_mul]
      exact hmul g h)) with hα
  set dU : G →* kˣ :=
    ((LinearMap.det : (W →ₗ[k] W) →* k).comp (τ : G →* (W →ₗ[k] W))).toHomUnits
    with hdU
  refine ⟨α, dU * α⁻¹, fun g => ?_⟩
  have hαg : ((α g : kˣ) : k) = c g := by
    rw [hα]
    exact IsUnit.unit_spec (hunit g)
  have hcne : c g ≠ 0 := (hunit g).ne_zero
  have hquad : (τ g).charpoly =
      X ^ 2 - C (LinearMap.trace k W (τ g)) * X + C (LinearMap.det (τ g)) :=
    charpoly_eq_quadratic_of_finrank_two hfr (τ g)
  -- the line scalar is an eigenvalue, hence a root of the charpoly
  have hroot : ((τ g).charpoly).IsRoot (c g) := by
    rw [← Module.End.hasEigenvalue_iff_isRoot_charpoly]
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr (hc g).symm, hv⟩
  have heval : c g ^ 2 - LinearMap.trace k W (τ g) * c g
      + LinearMap.det (τ g) = 0 := by
    have h0 := hroot
    rw [hquad] at h0
    simpa [Polynomial.IsRoot] using h0
  have hβg : (((dU * α⁻¹) g : kˣ) : k) =
      LinearMap.trace k W (τ g) - c g := by
    have h1 : (((dU * α⁻¹) g : kˣ) : k) = LinearMap.det (τ g) * (c g)⁻¹ := by
      simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul,
        Units.val_inv_eq_inv_val, hαg, hdU, MonoidHom.coe_toHomUnits,
        MonoidHom.comp_apply]
    rw [h1]
    field_simp [hcne]
    linear_combination heval
  have hd : LinearMap.det (τ g) = c g * (LinearMap.trace k W (τ g) - c g) := by
    linear_combination heval
  rw [hquad, hαg, hβg, hd]
  have hsum : LinearMap.trace k W (τ g) =
      c g + (LinearMap.trace k W (τ g) - c g) := by ring
  calc X ^ 2 - C (LinearMap.trace k W (τ g)) * X
        + C (c g * (LinearMap.trace k W (τ g) - c g))
      = X ^ 2 - C (c g + (LinearMap.trace k W (τ g) - c g)) * X
        + C (c g * (LinearMap.trace k W (τ g) - c g)) := by rw [← hsum]
    _ = (X - C (c g)) * (X - C (LinearMap.trace k W (τ g) - c g)) := by
        rw [map_add, map_mul]
        ring

/-!
## Step 2: the abstract Kolchin/common-eigenvector stable submodule

The abstract-group form of the Kolchin route of
`Modularity/KhareWintenberger.lean`'s
`not_isIrreducible_of_charpoly_eq_units` (there stated for Galois
representations), returning the stable submodule itself.
-/

set_option backward.isDefEq.respectTransparency false in
/-- **Kolchin/common-eigenvector stable submodule**: a 2-dimensional
representation whose characteristic polynomials are everywhere
`(X − 1)(X − χ g)` for a unit character `χ` admits a nonzero proper
stable submodule. Cayley–Hamilton turns the charpoly hypothesis into
`(ρ g − 1)(ρ g − χ g) = 0`; on `ker χ` every element is unipotent, so
`BrauerNesbitt.exists_fixed_of_unipotent` gives a nonzero fixed subspace,
stable by normality of `ker χ`; if it is everything, the image commutes
and `BrauerNesbitt.exists_common_eigenvector_of_commuting` produces a
stable line. -/
theorem rep_exists_stable_submodule_of_charpoly_eq_units
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hfr : Module.finrank k W = 2) (ρ : Representation k G W)
    (χ : G →* kˣ)
    (h : ∀ g, (ρ g).charpoly =
      X ^ 2 - C (((χ g : kˣ) : k) + 1) * X + C ((χ g : kˣ) : k)) :
    ∃ U : Submodule k W, U ≠ ⊥ ∧ U ≠ ⊤ ∧ ∀ g w, w ∈ U → ρ g w ∈ U := by
  classical
  have hdim : Module.rank k W = 2 := by
    rw [← Module.finrank_eq_rank k W, hfr]
    norm_num
  -- Cayley–Hamilton: `(ρ g − 1)(ρ g − χ g) = 0`
  have hCH : ∀ g, (ρ g - 1) * (ρ g - algebraMap k
      (Module.End k W) ((χ g : kˣ) : k)) = 0 := by
    intro g
    have hch := LinearMap.aeval_self_charpoly (ρ g)
    rw [h g] at hch
    simp only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X,
      Polynomial.aeval_C] at hch
    have hcomm : Commute (ρ g) (algebraMap k
        (Module.End k W) ((χ g : kˣ) : k)) :=
      (Algebra.commute_algebraMap_right _ _)
    have hexp : (ρ g - 1) * (ρ g - algebraMap k
        (Module.End k W) ((χ g : kˣ) : k)) =
        (ρ g) ^ 2 - (algebraMap k (Module.End k W) ((χ g : kˣ) : k)
          + algebraMap k (Module.End k W) 1) * ρ g
        + algebraMap k (Module.End k W) ((χ g : kˣ) : k) := by
      have e1 : (ρ g - 1) * (ρ g - algebraMap k
          (Module.End k W) ((χ g : kˣ) : k)) =
          ρ g * ρ g - ρ g * algebraMap k
            (Module.End k W) ((χ g : kˣ) : k)
          - ρ g + algebraMap k (Module.End k W) ((χ g : kˣ) : k) := by
        noncomm_ring
      rw [e1, hcomm.eq, map_one]
      noncomm_ring
    rw [hexp]
    exact hch
  -- the kernel of the character acts unipotently
  by_cases hWtop : (⨅ hH : χ.ker,
      LinearMap.ker (ρ (hH : G) - 1)) = ⊤
  · -- `ρ` kills the kernel of `χ`: commuting image, split quadratics
    have hker1 : ∀ hH : χ.ker, ρ (hH : G) = 1 := by
      intro hH
      ext v
      have hv : v ∈ (⨅ hH : χ.ker,
          LinearMap.ker (ρ (hH : G) - 1)) :=
        hWtop ▸ Submodule.mem_top
      have hvk := (Submodule.mem_iInf _).mp hv hH
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hvk
      simpa using hvk
    have hcommim : ∀ g₁ g₂, Commute (ρ g₁) (ρ g₂) := by
      intro g₁ g₂
      have hcker : g₁⁻¹ * g₂⁻¹ * g₁ * g₂ ∈ χ.ker := by
        rw [MonoidHom.mem_ker]
        simp only [map_mul, map_inv]
        rw [mul_comm (χ g₁)⁻¹ (χ g₂)⁻¹, mul_assoc, mul_assoc,
          ← mul_assoc (χ g₁)⁻¹, inv_mul_cancel, one_mul, inv_mul_cancel]
      have h1 := hker1 ⟨g₁⁻¹ * g₂⁻¹ * g₁ * g₂, hcker⟩
      have h2 : ρ (g₁ * (g₁⁻¹ * g₂⁻¹ * g₁ * g₂)) = ρ g₁ := by
        rw [map_mul]
        simp only at h1
        rw [h1, mul_one]
      have h3 : g₁ * (g₁⁻¹ * g₂⁻¹ * g₁ * g₂) = g₂⁻¹ * g₁ * g₂ := by
        group
      rw [h3, map_mul, map_mul] at h2
      unfold Commute SemiconjBy
      have hcancel : ρ g₂ * ρ g₂⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel, map_one]
      calc ρ g₁ * ρ g₂
          = ρ g₂ * ρ g₂⁻¹ * (ρ g₁ * ρ g₂) := by
            rw [hcancel, one_mul]
        _ = ρ g₂ * (ρ g₂⁻¹ * ρ g₁ * ρ g₂) := by
            noncomm_ring
        _ = ρ g₂ * ρ g₁ := by rw [h2]
    obtain ⟨v, hv, heig⟩ :=
      BrauerNesbitt.exists_common_eigenvector_of_commuting hdim
        (Set.range fun g => ρ g)
        (by rintro _ ⟨g₁, rfl⟩ _ ⟨g₂, rfl⟩; exact hcommim g₁ g₂)
        (by
          rintro _ ⟨g, rfl⟩
          exact ⟨1, ((χ g : kˣ) : k),
            by rw [map_one]; exact hCH g⟩)
    refine ⟨Submodule.span k {v}, ?_, ?_, ?_⟩
    · simpa [Submodule.span_singleton_eq_bot] using hv
    · intro htop
      have h1 : Module.finrank k (Submodule.span k {v}) = 1 :=
        finrank_span_singleton hv
      rw [htop, finrank_top, hfr] at h1
      omega
    · intro g x hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      obtain ⟨cc, hcc⟩ := heig (ρ g) ⟨g, rfl⟩
      rw [map_smul, hcc]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
        (Submodule.mem_span_singleton_self v))
  · -- the `ker χ`-fixed space is nonzero (Kolchin), proper, stable
    let ρH : χ.ker →* Module.End k W :=
      { toFun := fun hH => ρ (hH : G)
        map_one' := map_one ρ
        map_mul' := fun x y => map_mul ρ _ _ }
    have huni : ∀ hH : χ.ker, (ρH hH - 1) ^ 2 = 0 := by
      intro hH
      have hχ1 : ((χ (hH : G) : kˣ) : k) = 1 := by
        rw [MonoidHom.mem_ker.mp hH.2]
        rfl
      have hthis := hCH (hH : G)
      rw [hχ1, map_one] at hthis
      rw [pow_two]
      exact hthis
    obtain ⟨v₀, hv₀ne, hv₀fix⟩ :=
      BrauerNesbitt.exists_fixed_of_unipotent hdim ρH huni
    refine ⟨⨅ hH : χ.ker, LinearMap.ker (ρ (hH : G) - 1),
      ?_, hWtop, ?_⟩
    · refine Submodule.ne_bot_iff _ |>.mpr ⟨v₀, ?_, hv₀ne⟩
      refine (Submodule.mem_iInf _).mpr fun hH => ?_
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
      exact hv₀fix hH
    · intro g v hv
      refine (Submodule.mem_iInf _).mpr fun hH => ?_
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
      have hconj : (g⁻¹ * (hH : G) * g) ∈ χ.ker := by
        rw [MonoidHom.mem_ker]
        simp only [map_mul, map_inv, MonoidHom.mem_ker.mp hH.2]
        rw [mul_one, inv_mul_cancel]
      have hfix := (Submodule.mem_iInf _).mp hv ⟨_, hconj⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero,
        Module.End.one_apply] at hfix
      have hrw : (hH : G) * g = g * (g⁻¹ * (hH : G) * g) := by group
      calc ρ (hH : G) (ρ g v)
          = ρ ((hH : G) * g) v := by rw [map_mul]; rfl
        _ = ρ g (ρ (g⁻¹ * (hH : G) * g) v) := by rw [hrw, map_mul]; rfl
        _ = ρ g v := by rw [hfix]

/-!
## Step 3: irreducibility transfer along charpoly equality
-/

set_option backward.isDefEq.respectTransparency false in
/-- **Irreducibility transfers along charpoly agreement**: if `ρ` is
irreducible and `τ` has everywhere the same characteristic polynomials,
then `τ` is irreducible. Otherwise a stable line of `τ` splits every
`charpoly (ρ g) = (X − α g)(X − β g)` (`rep_exists_characters_of_stable_line`
via the hypothesis), so the twist `α⁻¹ ⊗ ρ` has the `1 ⊕ (β·α⁻¹)` shape
and the Kolchin machinery produces a stable submodule for the twist —
which is also `ρ`-stable, refuting irreducibility. -/
theorem rep_isIrreducible_of_charpoly_eq
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    {W' : Type uW'} [AddCommGroup W'] [Module k W'] [Module.Finite k W']
    [Module.Free k W']
    (hW : Module.finrank k W = 2) (hW' : Module.finrank k W' = 2)
    (ρ : Representation k G W) (τ : Representation k G W')
    (hirr : ρ.IsIrreducible)
    (hcp : ∀ g, (τ g).charpoly = (ρ g).charpoly) :
    τ.IsIrreducible := by
  classical
  by_contra hτ
  obtain ⟨v, hv, hstab⟩ :=
    rep_exists_stable_line_of_not_isIrreducible hW' τ hτ
  obtain ⟨α, β, hfact⟩ :=
    rep_exists_characters_of_stable_line hW' τ hv hstab
  -- the twist of `ρ` by `α⁻¹`
  set σ : Representation k G W :=
    { toFun := fun g => (((α g)⁻¹ : kˣ) : k) • ρ g
      map_one' := by simp
      map_mul' := fun g h => by
        simp only [map_mul, mul_inv_rev, Units.val_mul]
        rw [smul_mul_smul_comm, mul_comm ((((α h)⁻¹ : kˣ) : k))] } with hσdef
  have hσapp : ∀ g, σ g = (((α g)⁻¹ : kˣ) : k) • ρ g := fun g => rfl
  have hσchar : ∀ g, (σ g).charpoly =
      X ^ 2 - C ((((β * α⁻¹) g : kˣ) : k) + 1) * X
        + C (((β * α⁻¹) g : kˣ) : k) := by
    intro g
    set a := ((α g : kˣ) : k) with ha
    set b := ((β g : kˣ) : k) with hb
    have hane : a ≠ 0 := Units.ne_zero (α g)
    have hρfact : (ρ g).charpoly = (X - C a) * (X - C b) :=
      (hcp g).symm.trans (hfact g)
    have hexp : (X - C a) * (X - C b) =
        X ^ 2 - C (a + b) * X + C (a * b) := by
      rw [map_add, map_mul]
      ring
    have hcoe : X ^ 2 - C (LinearMap.trace k W (ρ g)) * X
        + C (LinearMap.det (ρ g)) = X ^ 2 - C (a + b) * X + C (a * b) :=
      (charpoly_eq_quadratic_of_finrank_two hW (ρ g)).symm.trans
        (hρfact.trans hexp)
    have htr_g : LinearMap.trace k W (ρ g) = a + b := by
      have h1 := congrArg (fun p => p.coeff 1) hcoe
      simp only [coeff_one_quadratic] at h1
      exact neg_inj.mp h1
    have hdet_g : LinearMap.det (ρ g) = a * b := by
      have h1 := congrArg (fun p => p.coeff 0) hcoe
      simpa only [coeff_zero_quadratic] using h1
    have hval : (((β * α⁻¹) g : kˣ) : k) = b * a⁻¹ := by
      simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul,
        Units.val_inv_eq_inv_val, ha, hb]
    have htrσ : LinearMap.trace k W (σ g) = b * a⁻¹ + 1 := by
      rw [hσapp, map_smul, htr_g, smul_eq_mul, Units.val_inv_eq_inv_val,
        ← ha]
      field_simp [hane]
      ring
    have hdetσ : LinearMap.det (σ g) = b * a⁻¹ := by
      rw [hσapp, LinearMap.det_smul, hW, hdet_g, Units.val_inv_eq_inv_val,
        ← ha]
      field_simp [hane]
      try ring
    rw [charpoly_eq_quadratic_of_finrank_two hW (σ g), htrσ, hdetσ, hval]
  obtain ⟨U, hUb, hUt, hUstab⟩ :=
    rep_exists_stable_submodule_of_charpoly_eq_units hW σ (β * α⁻¹) hσchar
  refine (rep_not_isIrreducible_of_stable_submodule ρ U hUb hUt ?_) hirr
  intro g w hw
  have hρσ : ρ g w = ((α g : kˣ) : k) • σ g w := by
    rw [hσapp, LinearMap.smul_apply, smul_smul, Units.val_inv_eq_inv_val,
      mul_inv_cancel₀ (Units.ne_zero (α g)), one_smul]
  rw [hρσ]
  exact Submodule.smul_mem _ _ (hUstab g w hw)

/-!
## Step 4: the Jacobson-density toolkit over the group algebra
-/

/-- **Binary products of semisimple modules are semisimple** (replica of
the `Modularity/Interface.lean` helper, needed upstream of the interface;
mathlib's finite-product instance is stated for `Π`-types only). -/
lemma isSemisimpleModule_prodPair
    {A : Type uA} [Ring A]
    {P Q : Type*}
    [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
    [IsSemisimpleModule A P] [IsSemisimpleModule A Q] :
    IsSemisimpleModule A (P × Q) := by
  refine isSemisimpleModule_of_isSemisimpleModule_submodule' (ι := Bool)
    (p := fun b => bif b then LinearMap.range (LinearMap.inl A P Q)
      else LinearMap.range (LinearMap.inr A P Q)) ?_ ?_
  · rintro (_ | _)
    · exact .congr (LinearEquiv.ofInjective _ LinearMap.inr_injective).symm
    · exact .congr (LinearEquiv.ofInjective _ LinearMap.inl_injective).symm
  · rw [iSup_bool_eq]
    exact LinearMap.sup_range_inl_inr

/-- **Jacobson-density projector extraction** (replica of the
`Modularity/Interface.lean` helper `exists_smul_id_and_smul_zero`, needed
upstream of the interface): given a semisimple `A`-module `P` and a
simple `A`-module `M`, both finite-dimensional over central scalars `k`,
with no nonzero `A`-homs between `P` and `M` in either direction, some
ring element acts as the identity on `M` and as zero on `P`. -/
lemma exists_projector_smul_id_and_smul_zero
    {A : Type uA} [Ring A] [Algebra k A]
    {P M : Type*}
    [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]
    [Module.Finite k P]
    [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    [Module.Finite k M]
    [IsSemisimpleModule A P] [IsSimpleModule A M]
    (hPM : ∀ f : P →ₗ[A] M, f = 0) (hMP : ∀ f : M →ₗ[A] P, f = 0) :
    ∃ r : A, (∀ m : M, r • m = m) ∧ (∀ x : P, r • x = 0) := by
  classical
  haveI hNss : IsSemisimpleModule A (P × M) :=
    isSemisimpleModule_prodPair (A := A)
  set π : (P × M) →ₗ[A] (P × M) :=
    (LinearMap.inr A P M).comp (LinearMap.snd A P M) with hπ
  have hcomm : ∀ φ : Module.End A (P × M), π ∘ₗ φ = φ ∘ₗ π := by
    intro φ
    have hb : (LinearMap.fst A P M) ∘ₗ φ ∘ₗ (LinearMap.inr A P M) = 0 :=
      hMP _
    have hcz : (LinearMap.snd A P M) ∘ₗ φ ∘ₗ (LinearMap.inl A P M) = 0 :=
      hPM _
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply]
    have hxsplit : x = (x.1, (0 : M)) + ((0 : P), x.2) := by
      simp
    have hb' : (φ ((0 : P), x.2)).1 = 0 := by
      simpa using LinearMap.ext_iff.mp hb x.2
    have hc' : (φ (x.1, (0 : M))).2 = 0 := by
      simpa using LinearMap.ext_iff.mp hcz x.1
    have hL : π (φ x) = ((0 : P), (φ x).2) := by simp [hπ]
    have hsnd : (φ x).2 = (φ ((0 : P), x.2)).2 := by
      conv_lhs => rw [hxsplit]
      rw [map_add]
      simp [hc']
    rw [hL, hsnd]
    have hR : φ (π x) = φ ((0 : P), x.2) := by simp [hπ]
    rw [hR]
    exact Prod.ext (by rw [hb']) rfl
  let f : Module.End (Module.End A (P × M)) (P × M) :=
    { toFun := π
      map_add' := map_add π
      map_smul' := fun φ x => by
        simpa [Module.End.smul_def] using LinearMap.ext_iff.mp (hcomm φ) x }
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := k) (M := P × M)
  obtain ⟨r, hr⟩ := jacobson_density (R := A) (M := P × M) f s
  have hall : ∀ n : P × M, π n = r • n := by
    intro n
    have hn : n ∈ Submodule.span k (s : Set (P × M)) := by
      rw [hs]; trivial
    induction hn using Submodule.span_induction with
    | mem m hm => exact hr m hm
    | zero => simp
    | add u v _ _ hu hv => rw [map_add, hu, hv, smul_add]
    | smul cc u _ hu => rw [LinearMap.map_smul_of_tower, hu, smul_comm]
  refine ⟨r, fun m => ?_, fun x => ?_⟩
  · have h0 := hall ((0 : P), m)
    have hpair : ((0 : P), m) = (r • (0 : P), r • m) := by
      simpa [hπ] using h0
    simpa using (Prod.ext_iff.mp hpair).2.symm
  · have h0 := hall (x, (0 : M))
    have hpair : ((0 : P), (0 : M)) = (r • x, r • (0 : M)) := by
      simpa [hπ] using h0
    simpa using (Prod.ext_iff.mp hpair).1.symm

/-- **Realizing a commuting endomorphism by an algebra element**
(Jacobson density plus `k`-linear spanning): an endomorphism of a simple
`A`-module `N`, finite-dimensional over the central scalars `k`, that
commutes with every `A`-endomorphism of `N` is the action of some
`b ∈ A`. -/
lemma exists_toModuleEnd_eq_of_forall_comm
    {A : Type uA} [Ring A] [Algebra k A]
    {N : Type uW} [AddCommGroup N] [Module k N] [Module A N]
    [IsScalarTower k A N] [Module.Finite k N] [IsSimpleModule A N]
    (f : N →ₗ[k] N)
    (hf : ∀ (φ : Module.End A N) (x : N), f (φ x) = φ (f x)) :
    ∃ b : A, Module.toModuleEnd k (S := A) N b = f := by
  classical
  let F : Module.End (Module.End A N) N :=
    { toFun := f
      map_add' := map_add f
      map_smul' := fun φ x => by
        simp only [RingHom.id_apply, Module.End.smul_def]
        exact hf φ x }
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := k) (M := N)
  obtain ⟨b, hb⟩ := jacobson_density (R := A) (M := N) F s
  refine ⟨b, LinearMap.ext fun x => ?_⟩
  have hx : x ∈ Submodule.span k (s : Set N) := by rw [hs]; trivial
  have hgoal : ∀ y ∈ Submodule.span k (s : Set N), b • y = f y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem m hm => exact (hb m hm).symm
    | zero => simp
    | add u u' _ _ hu hu' => rw [smul_add, map_add, hu, hu']
    | smul cc u _ hu => rw [smul_comm, map_smul, hu]
  exact hgoal x hx

/-!
## Step 5: no simple 2-dimensional module is everywhere traceless

The finite-field heart: over a finite coefficient field the image of the
algebra in the endomorphisms of a simple 2-dimensional module always
contains an element of nonzero trace. This replaces the `char k = 0`
trace-of-identity argument of the interface's char-0 Brauer–Nesbitt and
is exactly the point where separability of finite fields (little
Wedderburn + nonvanishing of the field trace) enters.
-/

set_option backward.isDefEq.respectTransparency false in
/-- **No simple 2-dimensional module over a finite field is everywhere
traceless**: if `N` is a simple `A`-module of `k`-dimension 2 over a
finite field `k`, some `b ∈ A` acts with nonzero trace. Route: the
commutant `D = End_A N` is a finite division ring, hence a field (little
Wedderburn), with `dim_k D · dim_D N = 2`. If `dim_k D = 1`, every
`A`-endomorphism is a `k`-scalar, and a rank-one projection commutes
with them all, is realized by some `b ∈ A` via Jacobson density, and has
trace `1`. If `dim_k D = 2`, evaluation at any `x₀ ≠ 0` identifies
`N ≃ D` `k`-linearly, the action of `δ ∈ D` conjugates to multiplication
on `D`, whose trace is the field trace `Tr_{D/k} δ` — nonzero for some
`δ` since the finite extension `D/k` is separable. -/
theorem false_of_trace_toModuleEnd_eq_zero
    [Finite k]
    {A : Type uA} [Ring A] [Algebra k A]
    {N : Type uW} [AddCommGroup N] [Module k N] [Module A N]
    [IsScalarTower k A N] [Module.Finite k N] [IsSimpleModule A N]
    (hN : Module.finrank k N = 2)
    (h0 : ∀ b : A,
      LinearMap.trace k N (Module.toModuleEnd k (S := A) N b) = 0) :
    False := by
  classical
  haveI : Nontrivial N := by
    rw [← Module.finrank_pos_iff (R := k)]
    omega
  letI : DecidableEq (Module.End A N) := Classical.decEq _
  letI : DivisionRing (Module.End A N) := Module.End.instDivisionRing
  haveI : Finite N := Module.finite_of_finite k
  haveI : Finite (Module.End A N) := by
    have hinj : Function.Injective
        (fun (φ : Module.End A N) => (φ : N → N)) := fun φ ψ hfg =>
      LinearMap.ext (congrFun hfg)
    exact Finite.of_injective _ hinj
  letI : Field (Module.End A N) := littleWedderburn _
  -- the scalar embedding `k → D`
  letI : Algebra k (Module.End A N) :=
    (Module.toModuleEnd A (S := k) N).toAlgebra
  have halg : ∀ (cc : k) (x : N),
      (algebraMap k (Module.End A N) cc) x = cc • x := fun cc x => rfl
  -- `N` as a `D`-module by application
  letI : Module (Module.End A N) N := Module.End.applyModule
  have happly : ∀ (φ : Module.End A N) (x : N), φ • x = φ x :=
    fun φ x => rfl
  haveI : IsScalarTower k (Module.End A N) N := ⟨fun cc φ x => by
    rw [happly, Algebra.smul_def, Module.End.mul_apply, halg, happly]⟩
  haveI : Module.Finite (Module.End A N) N := Module.Finite.of_finite
  haveI : Module.Finite k (Module.End A N) := Module.Finite.of_finite
  have htow : Module.finrank k (Module.End A N) *
      Module.finrank (Module.End A N) N = Module.finrank k N :=
    Module.finrank_mul_finrank k (Module.End A N) N
  have hdm : Module.finrank k (Module.End A N) *
      Module.finrank (Module.End A N) N = 2 := htow.trans hN
  have hdvd : Module.finrank k (Module.End A N) ∣ 2 :=
    ⟨Module.finrank (Module.End A N) N, hdm.symm⟩
  -- the two commutant branches
  rcases Nat.prime_two.eq_one_or_self_of_dvd _ hdvd with hd1 | hd2
  · -- `D = k`: rank-one projection of trace 1
    have hscal : ∀ φ : Module.End A N, ∃ cc : k, ∀ x : N, φ x = cc • x := by
      intro φ
      have hspan : Submodule.span k {(1 : Module.End A N)} = ⊤ := by
        apply Submodule.eq_top_of_finrank_eq
        rw [finrank_span_singleton (one_ne_zero), hd1]
      have hφ : φ ∈ Submodule.span k {(1 : Module.End A N)} :=
        hspan ▸ Submodule.mem_top
      obtain ⟨cc, hcc⟩ := Submodule.mem_span_singleton.mp hφ
      refine ⟨cc, fun x => ?_⟩
      rw [← hcc, Algebra.smul_def, Module.End.mul_apply, halg]
      simp
    set bb : Module.Basis (Fin 2) k N := Module.finBasisOfFinrankEq k N hN
      with hbb
    set f₀ : N →ₗ[k] N :=
      bb.constr k (fun i => if i = 0 then bb 0 else 0) with hf₀
    have hf₀0 : f₀ (bb 0) = bb 0 := by
      rw [hf₀, Module.Basis.constr_basis]
      simp
    have hf₀1 : f₀ (bb 1) = 0 := by
      rw [hf₀, Module.Basis.constr_basis]
      simp
    have htr : LinearMap.trace k N f₀ = 1 := by
      rw [LinearMap.trace_eq_matrix_trace k bb, Matrix.trace,
        Fin.sum_univ_two]
      simp [Matrix.diag, LinearMap.toMatrix_apply, hf₀0, hf₀1]
    have hcomm : ∀ (φ : Module.End A N) (x : N), f₀ (φ x) = φ (f₀ x) := by
      intro φ x
      obtain ⟨cc, hcc⟩ := hscal φ
      rw [hcc, map_smul, hcc]
    obtain ⟨b, hb⟩ := exists_toModuleEnd_eq_of_forall_comm f₀ hcomm
    have hcontr := h0 b
    rw [hb, htr] at hcontr
    exact one_ne_zero hcontr
  · -- `dim_k D = 2`, `dim_D N = 1`: multiplication by an element of
    -- nonzero field trace
    haveI : Algebra.IsSeparable k (Module.End A N) :=
      inferInstance
    obtain ⟨δ, hδ⟩ := Algebra.trace_surjective k (Module.End A N) 1
    obtain ⟨x₀, hx₀⟩ := exists_ne (0 : N)
    -- evaluation `D → N` at `x₀` is a `k`-linear bijection
    set ev : Module.End A N →ₗ[k] N :=
      { toFun := fun φ => φ x₀
        map_add' := fun φ ψ => rfl
        map_smul' := fun cc φ => by
          simp only [RingHom.id_apply]
          rw [Algebra.smul_def, Module.End.mul_apply, halg] } with hev
    have hevinj : Function.Injective ev := by
      intro φ ψ hφψ
      by_contra hne
      have hsub : φ - ψ ≠ 0 := sub_ne_zero.mpr hne
      apply hx₀
      have hker : (φ - ψ) x₀ = 0 := by
        simp only [hev, LinearMap.coe_mk, AddHom.coe_mk] at hφψ
        rw [LinearMap.sub_apply, hφψ, sub_self]
      calc x₀ = ((φ - ψ)⁻¹ * (φ - ψ)) x₀ := by
            rw [inv_mul_cancel₀ hsub, Module.End.one_apply]
        _ = (φ - ψ)⁻¹ ((φ - ψ) x₀) := Module.End.mul_apply _ _ _
        _ = 0 := by rw [hker, map_zero]
    have hevsurj : Function.Surjective ev := by
      rw [← LinearMap.range_eq_top]
      apply Submodule.eq_top_of_finrank_eq
      rw [LinearMap.finrank_range_of_inj hevinj, hd2, hN]
    set e : Module.End A N ≃ₗ[k] N :=
      LinearEquiv.ofBijective ev ⟨hevinj, hevsurj⟩ with he
    -- the `k`-linear action of `δ` on `N`
    set fδ : N →ₗ[k] N := LinearMap.restrictScalars k δ with hfδ
    have hfδapp : ∀ x : N, fδ x = δ x := fun x => rfl
    have hcommδ : ∀ (φ : Module.End A N) (x : N), fδ (φ x) = φ (fδ x) := by
      intro φ x
      rw [hfδapp, hfδapp, ← Module.End.mul_apply, ← Module.End.mul_apply,
        mul_comm]
    have hconj : fδ = e.conj ((Algebra.lmul k (Module.End A N)) δ) := by
      refine LinearMap.ext fun x => ?_
      have h1 : e.conj ((Algebra.lmul k (Module.End A N)) δ) x =
          e ((Algebra.lmul k (Module.End A N)) δ (e.symm x)) := by
        rw [LinearEquiv.conj_apply]
        rfl
      rw [h1]
      calc fδ x = δ (e (e.symm x)) := by rw [e.apply_symm_apply]; exact hfδapp x
        _ = (δ * (e.symm x)) x₀ := rfl
        _ = e ((Algebra.lmul k (Module.End A N)) δ (e.symm x)) := rfl
    have htrδ : LinearMap.trace k N fδ = 1 := by
      rw [hconj, LinearMap.trace_conj', ← Algebra.trace_apply, hδ]
    obtain ⟨b, hb⟩ := exists_toModuleEnd_eq_of_forall_comm fδ hcommδ
    have hcontr := h0 b
    rw [hb, htrδ] at hcontr
    exact one_ne_zero hcontr

/-!
## Step 5b: rank-two Cayley–Hamilton, and trace extraction from charpolys

Two bookkeeping facts about `2`-dimensional endomorphisms, both used by
the CHARACTERISTIC-ZERO branch of Step 6 and Step 8 below (added
2026-07-26 with the char-`≠ 2` generalization).

`two_mul_det_eq_of_finrank_two` is the reason the char-`≠ 2` Galois node
of Step 8 needs only the *trace* to be continuous: once `2` is a unit,
the determinant is a polynomial in the traces of `f` and `f²`, so
trace agreement at every group element upgrades by itself to charpoly
agreement at every group element. Over the discrete finite fields of
Step 7 that upgrade is unnecessary (the whole charpoly locus is open and
closed), which is why it appears only now.
-/

/-- **Cayley–Hamilton in rank two**: on a free module of rank `2`,
`2 · det f = (tr f)² − tr (f²)`. Take the trace of
`f² − (tr f)·f + (det f)·1 = 0`, which is `LinearMap.aeval_self_charpoly`
read through `charpoly_eq_quadratic_of_finrank_two`; the identity
endomorphism contributes `tr 1 = finrank = 2`. -/
lemma two_mul_det_eq_of_finrank_two
    {F : Type*} [CommRing F] [Nontrivial F] {V : Type*} [AddCommGroup V]
    [Module F V] [Module.Finite F V] [Module.Free F V]
    (hfr : Module.finrank F V = 2) (f : V →ₗ[F] V) :
    2 * LinearMap.det f =
      LinearMap.trace F V f * LinearMap.trace F V f
        - LinearMap.trace F V (f * f) := by
  have hCH : (Polynomial.aeval f) f.charpoly = 0 :=
    LinearMap.aeval_self_charpoly f
  rw [charpoly_eq_quadratic_of_finrank_two hfr f] at hCH
  have hexp : (f * f) - (LinearMap.trace F V f) • f
      + (LinearMap.det f) • (1 : Module.End F V) = 0 := by
    rw [← hCH]
    simp only [map_add, map_sub, map_mul, Polynomial.aeval_X,
      Polynomial.aeval_C, map_pow, Algebra.smul_def]
    simp only [pow_two, mul_one]
  have htr := congrArg (LinearMap.trace F V) hexp
  simp only [map_add, map_sub, map_smul, smul_eq_mul, LinearMap.trace_one,
    map_zero, hfr, Nat.cast_ofNat] at htr
  linear_combination htr

/-- **Traces agree when charpolys do**, in rank two: read off the linear
coefficient of `X² − (tr)·X + det`. -/
lemma trace_eq_of_charpoly_eq_finrank_two
    {F : Type*} [CommRing F] [Nontrivial F]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    [Module.Free F V]
    {V' : Type*} [AddCommGroup V'] [Module F V'] [Module.Finite F V']
    [Module.Free F V']
    (hV : Module.finrank F V = 2) (hV' : Module.finrank F V' = 2)
    {f : V →ₗ[F] V} {f' : V' →ₗ[F] V'} (h : f.charpoly = f'.charpoly) :
    LinearMap.trace F V f = LinearMap.trace F V' f' := by
  have hq : X ^ 2 - C (LinearMap.trace F V f) * X + C (LinearMap.det f) =
      X ^ 2 - C (LinearMap.trace F V' f') * X + C (LinearMap.det f') := by
    rw [← charpoly_eq_quadratic_of_finrank_two hV f,
      ← charpoly_eq_quadratic_of_finrank_two hV' f']
    exact h
  have h3 := congrArg (fun p => p.coeff 1) hq
  simp only [coeff_one_quadratic] at h3
  exact neg_inj.mp h3

/-!
## Step 6: the main abstract theorem

Refactored 2026-07-26 into a CORE plus two witnesses. The core
`exists_linearEquiv_of_charpoly_eq_of_traceWitness` carries the whole
Brauer–Nesbitt argument and takes, as its last hypothesis, exactly the
one thing the finite-field proof of Step 5 supplied: that not every
element of the group algebra acts on `W` with trace zero. The two
witnesses are then:

* `[Finite k]`, any characteristic — Step 5's little-Wedderburn theorem
  `false_of_trace_toModuleEnd_eq_zero`; and
* `(2 : k) ≠ 0`, any field finite or not — the identity `1` of the group
  algebra already has trace `finrank k W = 2 ≠ 0`.

Neither subsumes the other: `𝔽₂ⁿ`-coefficients need the first, and
characteristic-zero coefficients (`ℚ_p`, a finite extension of it, `ℂ`)
need the second, since they are not finite.
-/

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- **Brauer–Nesbitt conjugacy, dimension 2, over an arbitrary
coefficient field, parameterized by a trace witness** (the abstract core
of the Chebotarev–Brauer–Nesbitt conjugacy leaves): two representations
of a group `G` on 2-dimensional `k`-spaces with equal characteristic
polynomials at every group element, the second irreducible, are
intertwined by a `k`-linear isomorphism — provided the image of the
group algebra `k[G]` in `End k W` is not everywhere traceless.

That last hypothesis is the ONLY place the coefficient field enters. The
Jacobson-density dichotomy of Step 4 shows that if no nonzero
equivariant map `W' → W` exists then every `b ∈ k[G]` is traceless on
`W`; `hwit` is precisely the refutation of that, and its two standard
sources are recorded in the section header above (Curtis–Reiner §30.16 at
dimension 2; Diamond–Darmon–Taylor Lemma 3.27). -/
theorem exists_linearEquiv_of_charpoly_eq_of_traceWitness
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    {W' : Type uW'} [AddCommGroup W'] [Module k W'] [Module.Finite k W']
    [Module.Free k W']
    (hW : Module.finrank k W = 2) (hW' : Module.finrank k W' = 2)
    (ρ : Representation k G W) (τ : Representation k G W')
    (hirr : ρ.IsIrreducible)
    (hcp : ∀ g, (τ g).charpoly = (ρ g).charpoly)
    (hwit : ¬ ∀ x : MonoidAlgebra k G,
      LinearMap.trace k W (Representation.asAlgebraHom ρ x) = 0) :
    ∃ e : W' ≃ₗ[k] W, ∀ g w, e (τ g w) = ρ g (e w) := by
  classical
  have hτirr : τ.IsIrreducible :=
    rep_isIrreducible_of_charpoly_eq hW hW' ρ τ hirr hcp
  haveI : Nontrivial W := by
    rw [← Module.finrank_pos_iff (R := k)]
    omega
  haveI : Nontrivial W' := by
    rw [← Module.finrank_pos_iff (R := k)]
    omega
  -- group-algebra module structures
  letI : Module (MonoidAlgebra k G) W :=
    Module.compHom W (Representation.asAlgebraHom ρ).toRingHom
  letI : Module (MonoidAlgebra k G) W' :=
    Module.compHom W' (Representation.asAlgebraHom τ).toRingHom
  have hsmulW : ∀ (x : MonoidAlgebra k G) (w : W),
      x • w = Representation.asAlgebraHom ρ x w := fun _ _ => rfl
  have hsmulW' : ∀ (x : MonoidAlgebra k G) (w : W'),
      x • w = Representation.asAlgebraHom τ x w := fun _ _ => rfl
  haveI : IsScalarTower k (MonoidAlgebra k G) W := ⟨fun cc x w => by
    rw [hsmulW, hsmulW, map_smul]
    rfl⟩
  haveI : IsScalarTower k (MonoidAlgebra k G) W' := ⟨fun cc x w => by
    rw [hsmulW', hsmulW', map_smul]
    rfl⟩
  haveI hsimpW : IsSimpleModule (MonoidAlgebra k G) W := by
    haveI h1 : IsSimpleModule (MonoidAlgebra k G) ρ.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp hirr
    exact IsSimpleModule.congr
      ({ toFun := id, invFun := id, map_add' := fun _ _ => rfl,
         map_smul' := fun _ _ => rfl, left_inv := fun _ => rfl,
         right_inv := fun _ => rfl } :
        W ≃ₗ[MonoidAlgebra k G] ρ.asModule)
  haveI hsimpW' : IsSimpleModule (MonoidAlgebra k G) W' := by
    haveI h1 : IsSimpleModule (MonoidAlgebra k G) τ.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule τ).mp hτirr
    exact IsSimpleModule.congr
      ({ toFun := id, invFun := id, map_add' := fun _ _ => rfl,
         map_smul' := fun _ _ => rfl, left_inv := fun _ => rfl,
         right_inv := fun _ => rfl } :
        W' ≃ₗ[MonoidAlgebra k G] τ.asModule)
  -- trace agreement at group elements, extended over the group algebra
  have htrg : ∀ g, LinearMap.trace k W' (τ g) = LinearMap.trace k W (ρ g) := by
    intro g
    have h2 : X ^ 2 - C (LinearMap.trace k W' (τ g)) * X
        + C (LinearMap.det (τ g)) =
        X ^ 2 - C (LinearMap.trace k W (ρ g)) * X
        + C (LinearMap.det (ρ g)) := by
      rw [← charpoly_eq_quadratic_of_finrank_two hW' (τ g),
        ← charpoly_eq_quadratic_of_finrank_two hW (ρ g)]
      exact hcp g
    have h3 := congrArg (fun p => p.coeff 1) h2
    simp only [coeff_one_quadratic] at h3
    exact neg_inj.mp h3
  have htrA : ∀ x : MonoidAlgebra k G,
      LinearMap.trace k W' (Representation.asAlgebraHom τ x) =
        LinearMap.trace k W (Representation.asAlgebraHom ρ x) := by
    intro x
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, map_add, map_add, ha, hb]
    | single g a =>
      rw [Representation.asAlgebraHom_single,
        Representation.asAlgebraHom_single, map_smul, map_smul, htrg g]
  -- dichotomy on nonzero equivariant homs
  by_cases hex : ∃ f : W' →ₗ[MonoidAlgebra k G] W, f ≠ 0
  · obtain ⟨f, hf⟩ := hex
    have hsurj : Function.Surjective f := by
      have hrange : LinearMap.range f = ⊤ := by
        rcases eq_bot_or_eq_top (LinearMap.range f) with hr | hr
        · exact absurd (LinearMap.range_eq_bot.mp hr) hf
        · exact hr
      exact LinearMap.range_eq_top.mp hrange
    have hinj : Function.Injective f := by
      have hres : Function.Surjective (f.restrictScalars k) := hsurj
      have h1 : Module.finrank k
          (LinearMap.range (f.restrictScalars k)) = 2 := by
        rw [LinearMap.range_eq_top.mpr hres, finrank_top, hW]
      have h2 := LinearMap.finrank_range_add_finrank_ker
        (f.restrictScalars k)
      rw [hW', h1] at h2
      have hker : LinearMap.ker (f.restrictScalars k) = ⊥ := by
        rw [← Submodule.finrank_eq_zero (R := k)]
        omega
      have hinj' : Function.Injective (f.restrictScalars k) :=
        LinearMap.ker_eq_bot.mp hker
      exact hinj'
    refine ⟨(LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).restrictScalars k,
      fun g w => ?_⟩
    have h1 : τ g w = (MonoidAlgebra.of k G g) • w := by
      rw [hsmulW', Representation.asAlgebraHom_of]
    have h2 : ρ g (f w) = (MonoidAlgebra.of k G g) • (f w) := by
      rw [hsmulW, Representation.asAlgebraHom_of]
    show f (τ g w) = ρ g (f w)
    rw [h1, h2, map_smul]
  · push Not at hex
    exfalso
    have hMP : ∀ f : W →ₗ[MonoidAlgebra k G] W', f = 0 := by
      intro f
      rcases LinearMap.bijective_or_eq_zero f with hbij | hzz
      · exfalso
        set eqv := LinearEquiv.ofBijective f hbij with heqv
        have hzero := hex (eqv.symm : W' ≃ₗ[MonoidAlgebra k G] W).toLinearMap
        obtain ⟨x, hx⟩ := exists_ne (0 : W)
        apply hx
        calc x = eqv.symm (eqv x) := (eqv.symm_apply_apply x).symm
          _ = 0 := LinearMap.ext_iff.mp hzero (eqv x)
      · exact hzz
    obtain ⟨r, hrW, hrW'⟩ :=
      exists_projector_smul_id_and_smul_zero (k := k) (P := W') (M := W)
        hex hMP
    -- the toModuleEnd/asAlgebraHom bridge for traces
    have hE1 : ∀ x : MonoidAlgebra k G,
        Module.toModuleEnd k (S := MonoidAlgebra k G) W' x =
          Representation.asAlgebraHom τ x :=
      fun x => LinearMap.ext fun w => hsmulW' x w
    have hE2 : ∀ x : MonoidAlgebra k G,
        Module.toModuleEnd k (S := MonoidAlgebra k G) W x =
          Representation.asAlgebraHom ρ x :=
      fun x => LinearMap.ext fun w => hsmulW x w
    -- every algebra element is traceless on `W`, refuting `hwit`
    refine hwit fun b => ?_
    have hEb : Module.toModuleEnd k (S := MonoidAlgebra k G) W (r * b) =
        Module.toModuleEnd k (S := MonoidAlgebra k G) W b := by
      refine LinearMap.ext fun x => ?_
      show (r * b) • x = b • x
      rw [mul_smul, hrW]
    have hEb' : Module.toModuleEnd k (S := MonoidAlgebra k G) W' (r * b) =
        0 := by
      refine LinearMap.ext fun x => ?_
      show (r * b) • x = 0
      rw [mul_smul, hrW']
    calc LinearMap.trace k W (Representation.asAlgebraHom ρ b)
        = LinearMap.trace k W
          (Module.toModuleEnd k (S := MonoidAlgebra k G) W b) := by
          rw [hE2]
      _ = LinearMap.trace k W
          (Module.toModuleEnd k (S := MonoidAlgebra k G) W (r * b)) := by
          rw [hEb]
      _ = LinearMap.trace k W'
          (Module.toModuleEnd k (S := MonoidAlgebra k G) W' (r * b)) := by
          rw [hE1, hE2]; exact (htrA (r * b)).symm
      _ = 0 := by rw [hEb', map_zero]

set_option backward.isDefEq.respectTransparency false in
/-- **Brauer–Nesbitt conjugacy, dimension 2, finite coefficient field**
(unchanged statement; since 2026-07-26 a five-line delegation to
`exists_linearEquiv_of_charpoly_eq_of_traceWitness` above): two
representations of a group `G` on 2-dimensional `k`-spaces with equal
characteristic polynomials at every group element, the second
irreducible, are intertwined by a `k`-linear isomorphism. Valid in every
characteristic (Curtis–Reiner §30.16 at dimension 2;
Diamond–Darmon–Taylor Lemma 3.27).

The trace witness is Step 5's `false_of_trace_toModuleEnd_eq_zero`, i.e.
little Wedderburn plus separability of the finite extension `D/k`. -/
theorem exists_linearEquiv_of_charpoly_eq
    [Finite k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    {W' : Type uW'} [AddCommGroup W'] [Module k W'] [Module.Finite k W']
    [Module.Free k W']
    (hW : Module.finrank k W = 2) (hW' : Module.finrank k W' = 2)
    (ρ : Representation k G W) (τ : Representation k G W')
    (hirr : ρ.IsIrreducible)
    (hcp : ∀ g, (τ g).charpoly = (ρ g).charpoly) :
    ∃ e : W' ≃ₗ[k] W, ∀ g w, e (τ g w) = ρ g (e w) := by
  classical
  letI : Module (MonoidAlgebra k G) W :=
    Module.compHom W (Representation.asAlgebraHom ρ).toRingHom
  have hsmulW : ∀ (x : MonoidAlgebra k G) (w : W),
      x • w = Representation.asAlgebraHom ρ x w := fun _ _ => rfl
  haveI : IsScalarTower k (MonoidAlgebra k G) W := ⟨fun cc x w => by
    rw [hsmulW, hsmulW, map_smul]
    rfl⟩
  haveI hsimpW : IsSimpleModule (MonoidAlgebra k G) W := by
    haveI h1 : IsSimpleModule (MonoidAlgebra k G) ρ.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp hirr
    exact IsSimpleModule.congr
      ({ toFun := id, invFun := id, map_add' := fun _ _ => rfl,
         map_smul' := fun _ _ => rfl, left_inv := fun _ => rfl,
         right_inv := fun _ => rfl } :
        W ≃ₗ[MonoidAlgebra k G] ρ.asModule)
  refine exists_linearEquiv_of_charpoly_eq_of_traceWitness hW hW' ρ τ hirr hcp
    fun hall => ?_
  refine false_of_trace_toModuleEnd_eq_zero (A := MonoidAlgebra k G) hW
    fun b => ?_
  have hE2 : Module.toModuleEnd k (S := MonoidAlgebra k G) W b =
      Representation.asAlgebraHom ρ b :=
    LinearMap.ext fun w => hsmulW b w
  rw [hE2]
  exact hall b

/-- **Brauer–Nesbitt conjugacy, dimension 2, coefficient field of
characteristic `≠ 2`** (new 2026-07-26 — the CHARACTERISTIC-ZERO
analogue of `exists_linearEquiv_of_charpoly_eq`, which is restricted to
FINITE coefficient fields): the same conclusion over an arbitrary,
possibly infinite, coefficient field in which `2 ≠ 0`.

The whole content is that the trace witness is now free: the identity of
the group algebra acts as the identity of `End k W`, whose trace is
`finrank k W = 2 ≠ 0`. Concretely this covers every characteristic-zero
coefficient field — `ℚ_p`, a finite extension of `ℚ_p`, the fraction
field of a coefficient ring module-finite over `ℤ_p`, a number field,
`ℂ` — none of which is finite, so none of which is reachable from
`exists_linearEquiv_of_charpoly_eq`. -/
theorem exists_linearEquiv_of_charpoly_eq_of_two_ne_zero
    (h2 : (2 : k) ≠ 0)
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    {W' : Type uW'} [AddCommGroup W'] [Module k W'] [Module.Finite k W']
    [Module.Free k W']
    (hW : Module.finrank k W = 2) (hW' : Module.finrank k W' = 2)
    (ρ : Representation k G W) (τ : Representation k G W')
    (hirr : ρ.IsIrreducible)
    (hcp : ∀ g, (τ g).charpoly = (ρ g).charpoly) :
    ∃ e : W' ≃ₗ[k] W, ∀ g w, e (τ g w) = ρ g (e w) := by
  refine exists_linearEquiv_of_charpoly_eq_of_traceWitness hW hW' ρ τ hirr hcp
    fun hall => h2 ?_
  have h1 := hall 1
  rw [map_one, LinearMap.trace_one, hW] at h1
  simpa using h1

/-!
## Step 7: the Chebotarev upgrade — the shared Galois-level conjugacy node
-/

open IsDedekindDomain in
set_option backward.isDefEq.respectTransparency false in
/-- **Conjugation invariance of the characteristic polynomial** along a
Galois representation: `charpoly (ρ (g·x·g⁻¹)) = charpoly (ρ x)`, since
`ρ (g·x·g⁻¹)` is the conjugate of `ρ x` by the invertible `ρ g`
(bookkeeping shared by the density steps of the twins in `Lift.lean` and
`Modularity/KhareWintenberger.lean`).

(Generalized 2026-07-26 from the base field `ℚ` to an arbitrary field
`K`, for the general-base Galois node of Step 8; the proof is unchanged
and every existing call site infers `K = ℚ` positionally.) -/
lemma charpoly_conj_mul_inv {K : Type*} [Field K]
    {k : Type uk} [CommRing k] [TopologicalSpace k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (ρ : GaloisRep K k W) (g x : Field.absoluteGaloisGroup K) :
    (ρ (g * x * g⁻¹)).charpoly = (ρ x).charpoly := by
  have hgu : (ρ g).comp (ρ g⁻¹) = LinearMap.id := by
    have hmul : ρ g * ρ g⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    exact hmul
  have hgu' : (ρ g⁻¹).comp (ρ g) = LinearMap.id := by
    have hmul : ρ g⁻¹ * ρ g = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    exact hmul
  have heq : ρ (g * x * g⁻¹) =
      (LinearEquiv.ofLinear (ρ g) (ρ g⁻¹) hgu hgu').conj (ρ x) := by
    ext w
    simp [map_mul, LinearEquiv.conj_apply, Module.End.mul_apply]
  rw [heq, LinearEquiv.charpoly_conj]

open IsDedekindDomain in
set_option backward.isDefEq.respectTransparency false in
/-- **Chebotarev–Brauer–Nesbitt conjugacy over an abstract finite
coefficient field, away from an arbitrary finite exceptional set** — THE
shared conjugacy node behind `HardlyRamified/Deformation.lean`'s
`exists_conj_of_charFrob_eq` (fixed exceptional set `{2, ℓ}`) and
`Modularity/Patching.lean`'s `exists_conj_of_charFrob_eq_away`
(verbatim): a continuous representation `τ` of `Gal(ℚ̄/ℚ)` on a
2-dimensional space over a finite discrete field `k` whose Frobenius
characteristic polynomials agree with those of an *irreducible*
2-dimensional `ρbar` at all primes outside a finite set `S` of places is
conjugate to `ρbar`.

Route: by the Chebotarev density node (`dense_conjClasses_globalFrob`)
the conjugates of the global Frobenius elements at places outside `S`
are dense; the charpoly agreement locus is closed (both representations
are continuous into DISCRETE finite endomorphism spaces,
`discreteTopology_moduleTopology`) and conjugation-stable
(`charpoly_conj_mul_inv`), hence everything; the abstract dimension-2
Brauer–Nesbitt core `exists_linearEquiv_of_charpoly_eq` (valid in every
characteristic over the finite field `k`) then produces the intertwining
isomorphism (Carayol, Contemp. Math. 165 (1994), Théorème 1;
Diamond–Darmon–Taylor, Lemma 3.27). -/
theorem exists_conj_of_charFrob_eq_away
    {k : Type uk} [Field k] [Finite k] [TopologicalSpace k]
    [DiscreteTopology k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2)
    {ρbar : GaloisRep ℚ k W} (hirr : ρbar.IsIrreducible)
    {W' : Type uW'} [AddCommGroup W'] [Module k W'] [Module.Finite k W']
    [Module.Free k W']
    (hW' : Module.rank k W' = 2)
    (τ : GaloisRep ℚ k W')
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
    (hcf : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S →
      τ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat) :
    ∃ e : W' ≃ₗ[k] W, τ.conj e = ρbar := by
  classical
  have hfrW : Module.finrank k W = 2 :=
    Module.finrank_eq_of_rank_eq (by exact_mod_cast hW)
  have hfrW' : Module.finrank k W' = 2 :=
    Module.finrank_eq_of_rank_eq (by exact_mod_cast hW')
  -- the endomorphism spaces are discrete in their module topologies
  letI : TopologicalSpace (Module.End k W) :=
    moduleTopology k (Module.End k W)
  letI : TopologicalSpace (Module.End k W') :=
    moduleTopology k (Module.End k W')
  haveI : DiscreteTopology (Module.End k W) :=
    discreteTopology_moduleTopology _ _
  haveI : DiscreteTopology (Module.End k W') :=
    discreteTopology_moduleTopology _ _
  -- the charpoly agreement locus is closed …
  have hcont : Continuous fun g : Field.absoluteGaloisGroup ℚ =>
      ((τ g : Module.End k W'), (ρbar g : Module.End k W)) :=
    (ContinuousMonoidHom.continuous_toFun τ).prodMk
      (ContinuousMonoidHom.continuous_toFun ρbar)
  have hclosed : IsClosed {g : Field.absoluteGaloisGroup ℚ |
      (τ g).charpoly = (ρbar g).charpoly} := by
    have hpre : {g : Field.absoluteGaloisGroup ℚ |
        (τ g).charpoly = (ρbar g).charpoly} =
        (fun g : Field.absoluteGaloisGroup ℚ =>
          ((τ g : Module.End k W'), (ρbar g : Module.End k W))) ⁻¹'
        {p : Module.End k W' × Module.End k W |
          p.1.charpoly = p.2.charpoly} := rfl
    rw [hpre]
    exact (isClosed_discrete _).preimage hcont
  -- … contains the dense set of Frobenius conjugates off `S` …
  have hsub : {x : Field.absoluteGaloisGroup ℚ |
      ∃ v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ), v ∉ S ∧
        ∃ g, x = g * globalFrob v * g⁻¹} ⊆
      {g : Field.absoluteGaloisGroup ℚ |
        (τ g).charpoly = (ρbar g).charpoly} := by
    rintro x ⟨v, hvS, g, rfl⟩
    obtain ⟨q, hq, rfl⟩ := exists_prime_toHeightOneSpectrum v
    have hval := hcf q hq hvS
    rw [GaloisRep.charFrob_eq_charpoly_globalFrob,
      GaloisRep.charFrob_eq_charpoly_globalFrob] at hval
    show (τ _).charpoly = (ρbar _).charpoly
    rw [charpoly_conj_mul_inv τ, charpoly_conj_mul_inv ρbar]
    exact hval
  -- … hence is everything, by Chebotarev density
  have hall : ∀ g : Field.absoluteGaloisGroup ℚ,
      (τ g).charpoly = (ρbar g).charpoly := by
    intro g
    have hdense := dense_conjClasses_globalFrob (K := ℚ) S
    have huniv : (Set.univ : Set (Field.absoluteGaloisGroup ℚ)) ⊆
        {g : Field.absoluteGaloisGroup ℚ |
          (τ g).charpoly = (ρbar g).charpoly} :=
      hdense.closure_eq ▸ hclosed.closure_subset_iff.mpr hsub
    exact huniv (Set.mem_univ g)
  -- the abstract dimension-2 Brauer–Nesbitt core
  obtain ⟨e, he⟩ := exists_linearEquiv_of_charpoly_eq hfrW hfrW'
    ρbar.toRepresentation τ.toRepresentation hirr hall
  refine ⟨e, GaloisRep.ext fun σ => LinearMap.ext fun x => ?_⟩
  have h1 : e (τ σ (e.symm x)) = ρbar σ (e (e.symm x)) := he σ (e.symm x)
  rw [e.apply_symm_apply] at h1
  calc (τ.conj e) σ x = (e.conj (τ σ)) x := by rw [GaloisRep.conj_apply]
    _ = e (τ σ (e.symm x)) := by rw [LinearEquiv.conj_apply]; rfl
    _ = ρbar σ x := h1

/-!
## Step 8: the same node over a GENERAL number field and in characteristic `≠ 2`

(New 2026-07-26.) Step 7 is pinned twice over: to the base field `ℚ`,
and to a FINITE DISCRETE coefficient field. Both pins are removed here.

What the two versions have in common is the Chebotarev density node
(`dense_conjClasses_globalFrob`, already stated over an arbitrary number
field `K`) and the abstract dimension-2 Brauer–Nesbitt core of Step 6.
What differs is how the agreement locus is shown CLOSED:

* over a finite discrete `k` (Step 7) the whole charpoly locus is a
  preimage of a clopen set, and nothing has to be continuous;
* over a Hausdorff topological field (here) only the TRACE is available
  as a continuous function — it is `k`-linear, and `Module.End k W`
  carries the module topology by the very definition of `GaloisRep`, so
  `IsModuleTopology.continuous_of_linearMap` applies. The determinant is
  not linear, and is instead recovered *after* the density argument from
  Step 5b's rank-two Cayley–Hamilton identity
  `2 · det f = (tr f)² − tr (f²)`, using `tr (τ (g·g)) = tr ((τ g)²)`.
  This is the only place `2 ≠ 0` is used a second time.

Neither node subsumes the other: a finite field of characteristic `2`
is out of reach here, and an infinite (e.g. characteristic-zero)
coefficient field is out of reach there.
-/

open IsDedekindDomain NumberField in
set_option backward.isDefEq.respectTransparency false in
/-- **Chebotarev alone propagates charpoly agreement from "off a finite
set of places" to EVERY element of the absolute Galois group** — the
irreducibility-free half of the conjugacy node below (cut out
2026-07-30).

Two continuous representations of `Gal(K̄/K)`, `K` any number field, on
2-dimensional spaces over a Hausdorff topological field `k` with
`2 ≠ 0`, whose Frobenius characteristic polynomials agree at all finite
places outside a finite set `S`, have EQUAL characteristic polynomials
at every group element.

This is exactly the first two thirds of
`exists_conj_of_charFrob_eq_away_of_two_ne_zero` below, which now consumes
it rather than repeating it. It is worth having under its own name
because it needs **no irreducibility hypothesis at all**: the
trace-agreement locus is closed (the trace is `k`-linear out of a
module-topology endomorphism space and `k` is Hausdorff), Chebotarev
(`dense_conjClasses_globalFrob`) makes it everything, and rank-two
Cayley–Hamilton (`two_mul_det_eq_of_finrank_two`, with `2` a unit) turns
traces everywhere back into charpolys everywhere. Irreducibility enters
only in the LAST step of the conjugacy node, where an intertwiner is
produced — so a consumer that wants only the charpoly VALUES need not
pay for it.

PROVENANCE (2026-07-30, `flt-lean-183`). Cut out while costing the
Chebotarev route to strong multiplicity one in `Modularity/Interface.lean`,
which wanted precisely this weaker statement — the two attached
representations there are irreducible, but nothing needs to know it. That
route turned out to be CIRCULAR for an unrelated reason (the
Eichler–Shimura attachment in this tree is downstream of strong
multiplicity one; see the docstring of
`qCoeff_prime_eq_of_isWeightTwoNewform_of_not_dvd_mul`), so the separation
is kept here for its own sake: it makes the irreducibility-free content of
the node explicit and removes a duplicated forty-line argument. -/
theorem charpoly_eq_of_charFrob_eq_away_of_two_ne_zero
    {K : Type*} [Field K] [NumberField K]
    {k : Type uk} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
    [T2Space k] (h2 : (2 : k) ≠ 0)
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2)
    {W' : Type uW'} [AddCommGroup W'] [Module k W'] [Module.Finite k W']
    [Module.Free k W']
    (hW' : Module.rank k W' = 2)
    (ρ : GaloisRep K k W) (τ : GaloisRep K k W')
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hcf : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      τ.charFrob v = ρ.charFrob v) :
    ∀ g : Field.absoluteGaloisGroup K, (τ g).charpoly = (ρ g).charpoly := by
  classical
  have hfrW : Module.finrank k W = 2 :=
    Module.finrank_eq_of_rank_eq (by exact_mod_cast hW)
  have hfrW' : Module.finrank k W' = 2 :=
    Module.finrank_eq_of_rank_eq (by exact_mod_cast hW')
  letI : TopologicalSpace (Module.End k W) :=
    moduleTopology k (Module.End k W)
  letI : TopologicalSpace (Module.End k W') :=
    moduleTopology k (Module.End k W')
  haveI : IsModuleTopology k (Module.End k W) := ⟨rfl⟩
  haveI : IsModuleTopology k (Module.End k W') := ⟨rfl⟩
  -- the trace-agreement locus is closed: the trace is `k`-linear out of a
  -- module-topology endomorphism space, and `k` is Hausdorff
  have hcont1 : Continuous fun g : Field.absoluteGaloisGroup K =>
      LinearMap.trace k W' (τ g) :=
    (IsModuleTopology.continuous_of_linearMap
      (LinearMap.trace k W')).comp (ContinuousMonoidHom.continuous_toFun τ)
  have hcont2 : Continuous fun g : Field.absoluteGaloisGroup K =>
      LinearMap.trace k W (ρ g) :=
    (IsModuleTopology.continuous_of_linearMap
      (LinearMap.trace k W)).comp (ContinuousMonoidHom.continuous_toFun ρ)
  have hclosed : IsClosed {g : Field.absoluteGaloisGroup K |
      LinearMap.trace k W' (τ g) = LinearMap.trace k W (ρ g)} :=
    isClosed_eq hcont1 hcont2
  -- … and it contains the dense set of Frobenius conjugates off `S`
  have hsub : {x : Field.absoluteGaloisGroup K |
      ∃ v : HeightOneSpectrum (𝓞 K), v ∉ S ∧
        ∃ g, x = g * globalFrob v * g⁻¹} ⊆
      {g : Field.absoluteGaloisGroup K |
        LinearMap.trace k W' (τ g) = LinearMap.trace k W (ρ g)} := by
    rintro x ⟨v, hvS, g, rfl⟩
    have hval := hcf v hvS
    rw [GaloisRep.charFrob_eq_charpoly_globalFrob,
      GaloisRep.charFrob_eq_charpoly_globalFrob] at hval
    have hcpx : (τ (g * globalFrob v * g⁻¹)).charpoly =
        (ρ (g * globalFrob v * g⁻¹)).charpoly := by
      rw [charpoly_conj_mul_inv τ, charpoly_conj_mul_inv ρ]
      exact hval
    exact trace_eq_of_charpoly_eq_finrank_two hfrW' hfrW hcpx
  have halltr : ∀ g : Field.absoluteGaloisGroup K,
      LinearMap.trace k W' (τ g) = LinearMap.trace k W (ρ g) := by
    intro g
    have hdense := dense_conjClasses_globalFrob (K := K) S
    have huniv : (Set.univ : Set (Field.absoluteGaloisGroup K)) ⊆
        {g : Field.absoluteGaloisGroup K |
          LinearMap.trace k W' (τ g) = LinearMap.trace k W (ρ g)} :=
      hdense.closure_eq ▸ hclosed.closure_subset_iff.mpr hsub
    exact huniv (Set.mem_univ g)
  -- traces everywhere ⟹ determinants everywhere (Cayley–Hamilton, `2` a unit)
  intro g
  have hsq : LinearMap.trace k W' (τ g * τ g) =
      LinearMap.trace k W (ρ g * ρ g) := by
    rw [← map_mul, ← map_mul]
    exact halltr (g * g)
  have hdet : LinearMap.det (τ g) = LinearMap.det (ρ g) := by
    refine mul_left_cancel₀ h2 ?_
    rw [two_mul_det_eq_of_finrank_two hfrW' (τ g),
      two_mul_det_eq_of_finrank_two hfrW (ρ g), halltr g, hsq]
  rw [charpoly_eq_quadratic_of_finrank_two hfrW' (τ g),
    charpoly_eq_quadratic_of_finrank_two hfrW (ρ g), halltr g, hdet]

open IsDedekindDomain NumberField in
set_option backward.isDefEq.respectTransparency false in
/-- **Chebotarev–Brauer–Nesbitt conjugacy over a general number field
and a coefficient field of characteristic `≠ 2`** — the
characteristic-zero/general-base analogue of
`exists_conj_of_charFrob_eq_away` (Step 7), which is pinned to the base
`ℚ` and to a finite discrete coefficient field.

A continuous representation `τ` of `Gal(K̄/K)`, `K` any number field, on
a 2-dimensional space over a Hausdorff topological field `k` with
`2 ≠ 0`, whose Frobenius characteristic polynomials agree with those of
an *irreducible* 2-dimensional `ρbar` at all finite places outside a
finite set `S`, is conjugate to `ρbar`.

Route: charpoly agreement at the places off `S` gives TRACE agreement
there (`trace_eq_of_charpoly_eq_finrank_two`); the trace-agreement locus
is conjugation-stable (`charpoly_conj_mul_inv`) and CLOSED, because the
trace is `k`-linear out of the module-topology endomorphism space that
`GaloisRep` is continuous into and `k` is Hausdorff; Chebotarev density
(`dense_conjClasses_globalFrob`) makes it everything; rank-two
Cayley–Hamilton (`two_mul_det_eq_of_finrank_two`) with `2` a unit turns
traces everywhere back into charpolys everywhere; and
`exists_linearEquiv_of_charpoly_eq_of_two_ne_zero` produces the
intertwining isomorphism (Carayol, Contemp. Math. 165 (1994),
Théorème 1; Diamond–Darmon–Taylor, Lemma 3.27).

NOT a statement about coefficient RINGS. Over a coefficient ring `O`
module-finite over `ℤ_p` the analogous statement is FALSE without a
further residual hypothesis — two `O`-lattices in the same `Frac O`
representation have identical Frobenius charpolys and need not be
`O`-conjugate — so the ring-level version requires residual
irreducibility and a lattice-uniqueness argument, which is NOT proved
here. What IS immediate from this theorem is the statement after
inverting `p`, i.e. over `Frac O`. -/
theorem exists_conj_of_charFrob_eq_away_of_two_ne_zero
    {K : Type*} [Field K] [NumberField K]
    {k : Type uk} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
    [T2Space k] (h2 : (2 : k) ≠ 0)
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2)
    {ρbar : GaloisRep K k W} (hirr : ρbar.IsIrreducible)
    {W' : Type uW'} [AddCommGroup W'] [Module k W'] [Module.Finite k W']
    [Module.Free k W']
    (hW' : Module.rank k W' = 2)
    (τ : GaloisRep K k W')
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hcf : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      τ.charFrob v = ρbar.charFrob v) :
    ∃ e : W' ≃ₗ[k] W, τ.conj e = ρbar := by
  classical
  have hfrW : Module.finrank k W = 2 :=
    Module.finrank_eq_of_rank_eq (by exact_mod_cast hW)
  have hfrW' : Module.finrank k W' = 2 :=
    Module.finrank_eq_of_rank_eq (by exact_mod_cast hW')
  -- Chebotarev plus rank-two Cayley–Hamilton, with no irreducibility used
  have hall : ∀ g : Field.absoluteGaloisGroup K,
      (τ g).charpoly = (ρbar g).charpoly :=
    charpoly_eq_of_charFrob_eq_away_of_two_ne_zero h2 hW hW' ρbar τ S hcf
  obtain ⟨e, he⟩ := exists_linearEquiv_of_charpoly_eq_of_two_ne_zero h2
    hfrW hfrW' ρbar.toRepresentation τ.toRepresentation hirr hall
  refine ⟨e, GaloisRep.ext fun σ => LinearMap.ext fun x => ?_⟩
  have h1 : e (τ σ (e.symm x)) = ρbar σ (e (e.symm x)) := he σ (e.symm x)
  rw [e.apply_symm_apply] at h1
  calc (τ.conj e) σ x = (e.conj (τ σ)) x := by rw [GaloisRep.conj_apply]
    _ = e (τ σ (e.symm x)) := by rw [LinearEquiv.conj_apply]; rfl
    _ = ρbar σ x := h1

open IsDedekindDomain NumberField in
/-- **Chebotarev–Brauer–Nesbitt conjugacy in characteristic zero** — the
form in which the previous theorem is meant to be applied, the `2 ≠ 0`
hypothesis being automatic. Covers `k = ℚ_p`, any finite extension of
it, and the fraction field of a coefficient ring module-finite over
`ℤ_p` — precisely the coefficient fields of the `p`-adic members of a
compatible system, none of which is finite and so none of which is in
range of `exists_conj_of_charFrob_eq_away`. -/
theorem exists_conj_of_charFrob_eq_away_of_charZero
    {K : Type*} [Field K] [NumberField K]
    {k : Type uk} [Field k] [CharZero k] [TopologicalSpace k]
    [IsTopologicalRing k] [T2Space k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2)
    {ρbar : GaloisRep K k W} (hirr : ρbar.IsIrreducible)
    {W' : Type uW'} [AddCommGroup W'] [Module k W'] [Module.Finite k W']
    [Module.Free k W']
    (hW' : Module.rank k W' = 2)
    (τ : GaloisRep K k W')
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hcf : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      τ.charFrob v = ρbar.charFrob v) :
    ∃ e : W' ≃ₗ[k] W, τ.conj e = ρbar :=
  exists_conj_of_charFrob_eq_away_of_two_ne_zero two_ne_zero hW hirr hW' τ S hcf

end GaloisRepresentation
