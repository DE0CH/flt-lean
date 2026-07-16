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

set_option warn.sorry false in
/-- **Common eigenvector of a commuting split family** (sorry node): a
commuting family of endomorphisms of a 2-dimensional space, each
annihilated by a split quadratic, has a common eigenvector. (Elementary:
if every member is scalar, any nonzero vector works; otherwise a
non-scalar member has a 1-dimensional eigenspace, which every member
preserves and hence acts on by a scalar.) -/
theorem exists_common_eigenvector_of_commuting (hrank : Module.rank F V = 2)
    (S : Set (V →ₗ[F] V)) (hcomm : ∀ f ∈ S, ∀ g ∈ S, Commute f g)
    (hsplit : ∀ f ∈ S, ∃ a b : F,
      (f - algebraMap F (V →ₗ[F] V) a) * (f - algebraMap F (V →ₗ[F] V) b) = 0) :
    ∃ v : V, v ≠ 0 ∧ ∀ f ∈ S, ∃ c : F, f v = c • v :=
  sorry

end BrauerNesbitt
