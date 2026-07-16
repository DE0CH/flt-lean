/-
BrauerNesbitt.lean — own work for the Fermat project (not vendored from
the FLT project).

Decomposition of the Brauer–Nesbitt node
(`not_isIrreducible_of_charpoly_eq`, `Chebotarev.lean`) along the
elementary route that avoids the semisimplification machinery.

Route: by Cayley–Hamilton (`LinearMap.aeval_self_charpoly`), the charpoly
hypothesis makes every `ρ g` satisfy `(ρ g − 1)(ρ g − χ̄ g) = 0`. On
`H := ker χ̄` every element is unipotent (`(ρ h − 1)² = 0`), so by the
2-dimensional Kolchin node below the `H`-fixed vectors are nonzero; the
fixed subspace is Galois-stable (`H` is normal). If it is proper, it is a
nontrivial invariant submodule; if it is everything, `ρ` factors through
the abelian quotient, the image is a commuting family annihilated by
split quadratics, and the common-eigenvector node produces an invariant
line. Either way `ρ` is not irreducible.

This file states the two group-theoretic inputs as sorry nodes (both
elementary, to be proven here — no arithmetic content):

* `exists_fixed_of_unipotent` (**Kolchin, 2-dimensional case**): a group
  of unipotent endomorphisms of a 2-dimensional space has a common
  nonzero fixed vector.

* `exists_common_eigenvector_of_commuting`: a commuting family of
  endomorphisms of a 2-dimensional space, each annihilated by a split
  quadratic, has a common eigenvector.
-/
module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.NoncommRing

@[expose] public section

namespace BrauerNesbitt

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

section MatrixHelpers

/-- A square-zero `2 × 2` matrix over a field has zero trace and zero
determinant (its characteristic polynomial is `X²`). Entry computation:
from the four entries of `N² = 0`, if `a + d ≠ 0` then `b = c = 0` and
`a² = d² = 0`, forcing `a = d = 0` — a contradiction; then
`det = ad − bc = −d² − bc = 0`. -/
lemma trace_eq_zero_and_det_eq_zero_of_sq_eq_zero
    {N : Matrix (Fin 2) (Fin 2) F} (hN : N * N = 0) :
    N.trace = 0 ∧ N.det = 0 := by
  rw [Matrix.eta_fin_two N] at hN ⊢
  rw [← Matrix.ext_iff] at hN
  simp only [Matrix.mul_fin_two, Fin.forall_fin_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.zero_apply] at hN
  obtain ⟨⟨h00, h01⟩, h10, h11⟩ := hN
  set a := N 0 0
  set b := N 0 1
  set c := N 1 0
  set d := N 1 1
  have htr : a + d = 0 := by
    by_contra had
    have hb : b = 0 := by
      have hb' : b * (a + d) = 0 := by linear_combination h01
      exact (mul_eq_zero.mp hb').resolve_right had
    have hc : c = 0 := by
      have hc' : c * (a + d) = 0 := by linear_combination h10
      exact (mul_eq_zero.mp hc').resolve_right had
    have ha : a = 0 := mul_self_eq_zero.mp (by linear_combination h00 - b * hc)
    have hd : d = 0 := mul_self_eq_zero.mp (by linear_combination h11 - c * hb)
    exact had (by rw [ha, hd, add_zero])
  refine ⟨by simpa [Matrix.trace_fin_two] using htr, ?_⟩
  have hdet : a * d - b * c = 0 := by linear_combination a * htr - h00
  simpa [Matrix.det_fin_two] using hdet

/-- The rank-one sandwich identity for `2 × 2` matrices: if `det N₀ = 0`,
then `N₀ * N * N₀ = tr (N * N₀) • N₀` (entry computation; each entry
difference is a multiple of `det N₀`). -/
lemma sandwich_of_det_eq_zero {N₀ : Matrix (Fin 2) (Fin 2) F}
    (hdet : N₀.det = 0) (N : Matrix (Fin 2) (Fin 2) F) :
    N₀ * N * N₀ = (N * N₀).trace • N₀ := by
  rw [Matrix.det_fin_two] at hdet
  rw [← Matrix.ext_iff]
  simp only [Fin.forall_fin_two, Matrix.mul_apply, Matrix.smul_apply,
    Matrix.trace_fin_two, Fin.sum_univ_two, smul_eq_mul]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · linear_combination -(N 1 1) * hdet
  · linear_combination (N 0 1) * hdet
  · linear_combination (N 1 0) * hdet
  · linear_combination -(N 0 0) * hdet

end MatrixHelpers

set_option backward.isDefEq.respectTransparency false in
/-- **Kolchin's theorem, 2-dimensional case**: a group of unipotent
endomorphisms of a 2-dimensional space has a common nonzero fixed vector.
PROVEN: if all `ρ g = 1`, any nonzero vector works. Otherwise take
`n₀ := ρ g₀ − 1 ≠ 0` with `n₀² = 0`; its range `W` is a line contained in
(hence equal to) its kernel. For any `g`, unipotency of `ρ g`, `ρ g₀` and
`ρ (g g₀)` forces `tr(N N₀) = 0` on the matrix side, so the rank-one
sandwich identity gives `n₀ (ρ g − 1) n₀ = 0`; hence `ρ g − 1` maps `W`
into `ker n₀ = W`, acts on its generator by a scalar `c` with `c² = 0`,
so `c = 0` and the generator is fixed. -/
theorem exists_fixed_of_unipotent (hrank : Module.rank F V = 2)
    {G : Type*} [Group G] (ρ : G →* (V →ₗ[F] V))
    (huni : ∀ g, (ρ g - 1) ^ 2 = 0) :
    ∃ v : V, v ≠ 0 ∧ ∀ g, ρ g v = v := by
  classical
  haveI : Module.Finite F V :=
    Module.finite_of_rank_eq_nat (by exact_mod_cast hrank)
  haveI : Nontrivial V := by
    rw [← rank_pos_iff_nontrivial (R := F), hrank]
    norm_num
  have hfr : Module.finrank F V = 2 :=
    Module.finrank_eq_of_rank_eq (by exact_mod_cast hrank)
  by_cases htriv : ∀ g, ρ g = 1
  · obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact ⟨v, hv, fun g => by rw [htriv g]; rfl⟩
  push Not at htriv
  obtain ⟨g₀, hg₀⟩ := htriv
  have hn₀ : ρ g₀ - 1 ≠ 0 := fun h => hg₀ (by rwa [sub_eq_zero] at h)
  have hn₀sq : (ρ g₀ - 1) * (ρ g₀ - 1) = 0 := by rw [← pow_two]; exact huni g₀
  -- transport unipotency data to matrices
  let b : Module.Basis (Fin 2) F V := Module.finBasisOfFinrankEq F V hfr
  let Φ : (V →ₗ[F] V) ≃ₐ[F] Matrix (Fin 2) (Fin 2) F :=
    LinearMap.toMatrixAlgEquiv b
  -- the key vanishing: `n₀ (ρ g − 1) n₀ = 0` for every `g`
  have hkey : ∀ g, (ρ g₀ - 1) * (ρ g - 1) * (ρ g₀ - 1) = 0 := by
    intro g
    have hnsq : (ρ g - 1) * (ρ g - 1) = 0 := by rw [← pow_two]; exact huni g
    have hprodsq : ((ρ g - 1) + (ρ g₀ - 1) + (ρ g - 1) * (ρ g₀ - 1)) *
        ((ρ g - 1) + (ρ g₀ - 1) + (ρ g - 1) * (ρ g₀ - 1)) = 0 := by
      have h1 : ρ (g * g₀) - 1 =
          (ρ g - 1) + (ρ g₀ - 1) + (ρ g - 1) * (ρ g₀ - 1) := by
        rw [map_mul]
        noncomm_ring
      rw [← h1, ← pow_two]
      exact huni (g * g₀)
    have hM0 : Φ (ρ g₀ - 1) * Φ (ρ g₀ - 1) = 0 := by
      rw [← map_mul, hn₀sq, map_zero]
    have hMn : Φ (ρ g - 1) * Φ (ρ g - 1) = 0 := by
      rw [← map_mul, hnsq, map_zero]
    have hMp : (Φ (ρ g - 1) + Φ (ρ g₀ - 1) + Φ (ρ g - 1) * Φ (ρ g₀ - 1)) *
        (Φ (ρ g - 1) + Φ (ρ g₀ - 1) + Φ (ρ g - 1) * Φ (ρ g₀ - 1)) = 0 := by
      have := congrArg Φ hprodsq
      simpa [map_mul, map_add, map_zero] using this
    obtain ⟨htr0, hdet0⟩ := trace_eq_zero_and_det_eq_zero_of_sq_eq_zero hM0
    obtain ⟨htrn, -⟩ := trace_eq_zero_and_det_eq_zero_of_sq_eq_zero hMn
    obtain ⟨htrp, -⟩ := trace_eq_zero_and_det_eq_zero_of_sq_eq_zero hMp
    have htrmul : (Φ (ρ g - 1) * Φ (ρ g₀ - 1)).trace = 0 := by
      have hsum : (Φ (ρ g - 1) + Φ (ρ g₀ - 1) +
          Φ (ρ g - 1) * Φ (ρ g₀ - 1)).trace =
          (Φ (ρ g - 1)).trace + (Φ (ρ g₀ - 1)).trace +
          (Φ (ρ g - 1) * Φ (ρ g₀ - 1)).trace := by
        simp [Matrix.trace_add]
      rw [htrp, htrn, htr0, zero_add, zero_add] at hsum
      exact hsum.symm
    have hsand := sandwich_of_det_eq_zero hdet0 (Φ (ρ g - 1))
    rw [htrmul, zero_smul] at hsand
    apply Φ.injective
    rw [map_mul, map_mul, map_zero, hsand]
  -- the fixed line `W = range n₀ = ker n₀`
  have hWle : LinearMap.range (ρ g₀ - 1) ≤ LinearMap.ker (ρ g₀ - 1) := by
    rintro _ ⟨u, rfl⟩
    rw [LinearMap.mem_ker]
    have := congrArg (fun φ : V →ₗ[F] V => φ u) hn₀sq
    simpa [Module.End.mul_apply] using this
  have hWne : LinearMap.range (ρ g₀ - 1) ≠ ⊥ :=
    fun h => hn₀ (LinearMap.range_eq_bot.mp h)
  have hkerne : LinearMap.ker (ρ g₀ - 1) ≠ ⊤ :=
    fun h => hn₀ (LinearMap.ker_eq_top.mp h)
  have hkerlt : Module.finrank F (LinearMap.ker (ρ g₀ - 1)) < 2 :=
    hfr ▸ Submodule.finrank_lt hkerne
  have hWfr : Module.finrank F (LinearMap.range (ρ g₀ - 1)) = 1 := by
    have h1 : Module.finrank F (LinearMap.range (ρ g₀ - 1)) ≤
        Module.finrank F (LinearMap.ker (ρ g₀ - 1)) :=
      Submodule.finrank_mono hWle
    have h3 : 0 < Module.finrank F (LinearMap.range (ρ g₀ - 1)) := by
      rw [Module.finrank_pos_iff]
      exact (Submodule.nontrivial_iff_ne_bot).mpr hWne
    omega
  have hker1 : Module.finrank F (LinearMap.ker (ρ g₀ - 1)) = 1 := by
    have h1 : Module.finrank F (LinearMap.range (ρ g₀ - 1)) ≤
        Module.finrank F (LinearMap.ker (ρ g₀ - 1)) :=
      Submodule.finrank_mono hWle
    omega
  have hWker : LinearMap.range (ρ g₀ - 1) = LinearMap.ker (ρ g₀ - 1) :=
    Submodule.eq_of_le_of_finrank_le hWle (by rw [hWfr, hker1])
  -- generator of the line
  haveI : Nontrivial (LinearMap.range (ρ g₀ - 1)) :=
    (Submodule.nontrivial_iff_ne_bot).mpr hWne
  obtain ⟨w₀, hw₀ne⟩ := exists_ne (0 : LinearMap.range (ρ g₀ - 1))
  have hgen := (finrank_eq_one_iff_of_nonzero' w₀ hw₀ne).mp hWfr
  refine ⟨(w₀ : V), by simpa using hw₀ne, fun g => ?_⟩
  -- `ρ g − 1` maps the line into itself …
  have hnW : (ρ g - 1) (w₀ : V) ∈ LinearMap.range (ρ g₀ - 1) := by
    have hker : (ρ g - 1) (w₀ : V) ∈ LinearMap.ker (ρ g₀ - 1) := by
      rw [LinearMap.mem_ker]
      obtain ⟨u, hu⟩ := w₀.2
      have := congrArg (fun φ : V →ₗ[F] V => φ u) (hkey g)
      simp only [Module.End.mul_apply, LinearMap.zero_apply] at this
      rw [hu] at this
      exact this
    exact hWker.ge hker
  obtain ⟨c, hc⟩ := hgen ⟨(ρ g - 1) (w₀ : V), hnW⟩
  have hcoe : c • (w₀ : V) = (ρ g - 1) (w₀ : V) := by
    have := congrArg Subtype.val hc
    simpa using this
  -- … by a square-zero scalar, which must vanish
  have hnsq : (ρ g - 1) * (ρ g - 1) = 0 := by rw [← pow_two]; exact huni g
  have hc2 : (c * c) • (w₀ : V) = 0 := by
    have happ := congrArg (fun φ : V →ₗ[F] V => φ (w₀ : V)) hnsq
    simp only [Module.End.mul_apply, LinearMap.zero_apply] at happ
    calc (c * c) • (w₀ : V) = c • (c • (w₀ : V)) := by rw [mul_smul]
    _ = c • ((ρ g - 1) (w₀ : V)) := by rw [hcoe]
    _ = (ρ g - 1) (c • (w₀ : V)) := (map_smul _ _ _).symm
    _ = (ρ g - 1) ((ρ g - 1) (w₀ : V)) := by rw [hcoe]
    _ = 0 := happ
  have hc0 : c = 0 := by
    have hw : (w₀ : V) ≠ 0 := by simpa using hw₀ne
    rcases smul_eq_zero.mp hc2 with h | h
    · exact mul_self_eq_zero.mp h
    · exact absurd h hw
  have hfix : (ρ g - 1) (w₀ : V) = 0 := by
    rw [← hcoe, hc0, zero_smul]
  have := hfix
  rw [LinearMap.sub_apply] at this
  simpa [sub_eq_zero] using this

set_option backward.isDefEq.respectTransparency false in
/-- **Common eigenvector of a commuting split family**: a commuting
family of endomorphisms of a 2-dimensional space, each annihilated by a
split quadratic, has a common eigenvector. PROVEN: if every member is
scalar, any nonzero vector works; otherwise a non-scalar member `f₀` with
`(f₀ − a)(f₀ − b) = 0` has `ker (f₀ − a)` nonzero (else `f₀ − b = 0` by
injectivity) and proper (else `f₀ = a`), hence 1-dimensional; every
member preserves it by commutativity and therefore acts on its generator
by a scalar. -/
theorem exists_common_eigenvector_of_commuting (hrank : Module.rank F V = 2)
    (S : Set (V →ₗ[F] V)) (hcomm : ∀ f ∈ S, ∀ g ∈ S, Commute f g)
    (hsplit : ∀ f ∈ S, ∃ a b : F,
      (f - algebraMap F (V →ₗ[F] V) a) * (f - algebraMap F (V →ₗ[F] V) b) = 0) :
    ∃ v : V, v ≠ 0 ∧ ∀ f ∈ S, ∃ c : F, f v = c • v := by
  classical
  haveI : Module.Finite F V :=
    Module.finite_of_rank_eq_nat (by exact_mod_cast hrank)
  haveI : Nontrivial V := by
    rw [← rank_pos_iff_nontrivial (R := F), hrank]
    norm_num
  have hfr : Module.finrank F V = 2 :=
    Module.finrank_eq_of_rank_eq (by exact_mod_cast hrank)
  by_cases hscal : ∀ f ∈ S, ∃ c : F, f = algebraMap F (V →ₗ[F] V) c
  · -- every member is scalar: any nonzero vector is a common eigenvector
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    refine ⟨v, hv, fun f hf => ?_⟩
    obtain ⟨c, rfl⟩ := hscal f hf
    exact ⟨c, by simp [Module.algebraMap_end_apply]⟩
  · push Not at hscal
    obtain ⟨f₀, hf₀S, hf₀⟩ := hscal
    obtain ⟨a, b, hab⟩ := hsplit f₀ hf₀S
    -- the eigenspace `W = ker (f₀ − a)` is nonzero …
    have hWne : LinearMap.ker (f₀ - algebraMap F (V →ₗ[F] V) a) ≠ ⊥ := by
      intro h
      have hinj : Function.Injective (f₀ - algebraMap F (V →ₗ[F] V) a) :=
        LinearMap.ker_eq_bot.mp h
      apply hf₀ b
      have hz : ∀ v, (f₀ - algebraMap F (V →ₗ[F] V) b) v = 0 := by
        intro v
        apply hinj
        have := congrArg (fun φ : V →ₗ[F] V => φ v) hab
        simpa [Module.End.mul_apply] using this
      ext v
      have := hz v
      rw [LinearMap.sub_apply, sub_eq_zero] at this
      simpa using this
    -- … and proper
    have hWtop : LinearMap.ker (f₀ - algebraMap F (V →ₗ[F] V) a) ≠ ⊤ := by
      intro h
      apply hf₀ a
      ext v
      have hv : v ∈ LinearMap.ker (f₀ - algebraMap F (V →ₗ[F] V) a) :=
        h ▸ Submodule.mem_top
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hv
      simpa using hv
    -- hence 1-dimensional; pick a generator
    have hWfr : Module.finrank F
        (LinearMap.ker (f₀ - algebraMap F (V →ₗ[F] V) a)) = 1 := by
      have hlt : Module.finrank F
          (LinearMap.ker (f₀ - algebraMap F (V →ₗ[F] V) a)) < 2 :=
        hfr ▸ Submodule.finrank_lt hWtop
      have hpos : 0 < Module.finrank F
          (LinearMap.ker (f₀ - algebraMap F (V →ₗ[F] V) a)) := by
        rw [Module.finrank_pos_iff]
        exact (Submodule.nontrivial_iff_ne_bot).mpr hWne
      omega
    haveI : Nontrivial (LinearMap.ker (f₀ - algebraMap F (V →ₗ[F] V) a)) :=
      (Submodule.nontrivial_iff_ne_bot).mpr hWne
    obtain ⟨w₀, hw₀ne⟩ :=
      exists_ne (0 : LinearMap.ker (f₀ - algebraMap F (V →ₗ[F] V) a))
    have hgen := (finrank_eq_one_iff_of_nonzero' w₀ hw₀ne).mp hWfr
    -- every member of `S` preserves the eigenspace
    have hinv : ∀ g ∈ S, ∀ w ∈ LinearMap.ker (f₀ - algebraMap F (V →ₗ[F] V) a),
        g w ∈ LinearMap.ker (f₀ - algebraMap F (V →ₗ[F] V) a) := by
      intro g hg w hw
      have hc : Commute (f₀ - algebraMap F (V →ₗ[F] V) a) g :=
        ((hcomm f₀ hf₀S g hg)).sub_left (Algebra.commute_algebraMap_left a g)
      rw [LinearMap.mem_ker] at hw ⊢
      have := congrArg (fun φ : V →ₗ[F] V => φ w) hc.eq
      simp only [Module.End.mul_apply] at this
      rw [this, hw, map_zero]
    -- conclude: the generator is a common eigenvector
    refine ⟨(w₀ : V), by simpa using hw₀ne, fun g hg => ?_⟩
    have hgw : g (w₀ : V) ∈ LinearMap.ker (f₀ - algebraMap F (V →ₗ[F] V) a) :=
      hinv g hg _ w₀.2
    obtain ⟨c, hc⟩ := hgen ⟨g (w₀ : V), hgw⟩
    refine ⟨c, ?_⟩
    have := congrArg (Subtype.val) hc
    simpa using this.symm

end BrauerNesbitt
