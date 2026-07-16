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

@[expose] public section

namespace BrauerNesbitt

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

set_option warn.sorry false in
/-- **Kolchin's theorem, 2-dimensional case** (sorry node): a group of
unipotent endomorphisms of a 2-dimensional space has a common nonzero
fixed vector. (Elementary: if some `ρ g₀ ≠ 1`, its fixed space is a line
`L`; for any `g` the product relations force `ρ g` to fix `L` pointwise;
if all `ρ g = 1` any nonzero vector works.) -/
theorem exists_fixed_of_unipotent (hrank : Module.rank F V = 2)
    {G : Type*} [Group G] (ρ : G →* (V →ₗ[F] V))
    (huni : ∀ g, (ρ g - 1) ^ 2 = 0) :
    ∃ v : V, v ≠ 0 ∧ ∀ g, ρ g v = v :=
  sorry

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
