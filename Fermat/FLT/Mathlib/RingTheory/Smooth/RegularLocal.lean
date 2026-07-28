/-
Fermat/FLT/Mathlib/RingTheory/Smooth/RegularLocal.lean — own work for the
Fermat project (not vendored from the FLT project).

# Regular ⟹ formally smooth over a perfect field (Stacks `056S`), in its
# regular-LOCAL form

This module states, **once**, the commutative-algebra fact that at least four
open nodes of this development were each about to build separately:

> a **regular local** ring essentially of finite type over a **perfect** field
> is **formally smooth** over that field.

That is `Algebra.FormallySmooth.of_isRegularLocalRing_of_perfectField` below.
The four consumers, all of which now go through it, are

| node | file |
|---|---|
| `formallySmooth_of_isDiscreteValuationRing_of_perfectField` | `Fermat/FLT/Mathlib/AlgebraicGeometry/CurveExtension.lean` |
| `smoothOfRelativeDimension_specMap_algebraMap_of_isRegularRing` | `Fermat/FLT/Mathlib/AlgebraicGeometry/SmoothConnectedCriteria.lean` |
| `smoothOfRelativeDimension_of_gamma0GITPresentation` | `Fermat/FLT/ModularCurve/X0.lean` (already a theorem over the previous row) |
| `smoothOfRelativeDimension_one_fromNormalization` | `Fermat/FLT/Mathlib/AlgebraicGeometry/CurveCompactification.lean` (already a theorem over the first row) |

**This module has no `Fermat` imports**, deliberately: like
`Fermat/FLT/Modularity/RegularStalks.lean` (which carries the CONVERSE,
`isRegularLocalRing_stalk_of_smooth_over_field`, sorry-free) it is importable
from anywhere in the tree, including the mathlib-shim modules.

## The cut

The statement is proven over exactly two named pieces:

* `Algebra.exists_localizationAtPrime_mvPolynomial_surjective` — **PROVEN
  here**.  A local ring essentially of finite type over a field `K` is a
  quotient of a localization of a polynomial ring `K[x₁,…,x_n]` at a prime.
  This is the presentation bookkeeping and contains no mathematics; it is
  modelled on the presentation built inside mathlib's
  `Algebra.FormallySmooth.of_formallySmooth_residueField_tensor`
  (`Mathlib/RingTheory/Smooth/Fiber.lean`), simplified by the fact that our
  base is a field and our target is local, so the localization can be taken at
  a prime and is itself regular local and noetherian.
* `Algebra.injective_cotangentComplexBaseChange_of_isRegularLocalRing` — the
  **one sorry leaf**, and the whole mathematical content: the injectivity that
  the local Jacobian criterion asks for.

## What the sorry leaf says, and the classical proof of it

`Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField`
(`Mathlib/RingTheory/Smooth/Local.lean`) is the **local Jacobian criterion**:
for a presentation `0 → I → P → S → 0` of a LOCAL ring `S` with `P` formally
smooth over `K`, `Ω[P⁄K]` finite free and `I` finitely generated,

    FormallySmooth K S  ↔  κ ⊗_S I/I² → κ ⊗_P Ω[P⁄K]  is injective,

`κ = ResidueField S`.  Taking `P = K[x]_𝔮` (which is what the presentation
lemma supplies), the map factors — by Leibniz, `d f mod 𝔪_P` depends only on
`f mod 𝔪_P²` — as

    κ ⊗_S I/I²  =  I/𝔪_P I  --(a)-->  𝔪_P/𝔪_P²  --(b)-->  κ ⊗_P Ω[P⁄K]

and the two arrows are injective for two different reasons:

* **(a) is regularity.**  `P` is regular local and `S = P/I` is regular local,
  so with `c = dim P - dim S`: pick `f₁,…,f_c ∈ I` whose classes are a basis of
  `(I + 𝔪_P²)/𝔪_P²` (there are exactly `c` of them because
  `𝔪_S/𝔪_S² = 𝔪_P/(𝔪_P² + I)` has dimension `dim S`).  Then `P/(f₁,…,f_c)` is
  regular local of dimension `dim S`, hence a DOMAIN, and it surjects onto
  `P/I = S`, also of dimension `dim S`; a surjection of domains of equal
  dimension over a catenary ring is an isomorphism, so `I = (f₁,…,f_c)`.
  Therefore `I/𝔪_P I` has dimension at most `c` and surjects onto the
  `c`-dimensional `(I + 𝔪_P²)/𝔪_P²`, so (a) is injective.
  **The quotient step is already available in this tree**: the list induction
  `GaloisRepresentation.Modularity.isRegularLocalRing_quotient_span_list_aux`
  and its base case `isRegularLocalRing_quotient_span_singleton`
  (`Fermat/FLT/Modularity/RegularStalks.lean`, both PROVEN, both sorry-free)
  are exactly "quotient by part of a regular system of parameters is regular
  local", and `isDomain_of_isRegularLocalRing` is there too.  Note that
  RegularStalks.lean may not be imported from here without making this module
  Fermat-dependent; a prover closing this leaf should either move those three
  declarations further upstream or import them.
* **(b) is PERFECTNESS.**  For a local `K`-algebra `P` with residue field `κ`
  there is an exact sequence `𝔪_P/𝔪_P² --δ--> κ ⊗_P Ω[P⁄K] → Ω[κ⁄K] → 0`, and
  `δ` is injective **iff** `κ` is formally smooth over `K` (Matsumura, *CRT*
  Thm 25.2 / §28).  `κ` is essentially of finite type over `K`, and `K` is
  perfect, so `Algebra.FormallySmooth.of_perfectField`
  (`Mathlib/RingTheory/Smooth/Field.lean`) applies.  Equivalently
  `H₁(L_{κ⁄K}) = 0`, which is the vanishing that fails over an imperfect base.

## Faithfulness

`PerfectField K` is load-bearing and the statement is FALSE without it.  Over
an imperfect field `k = 𝔽_p(t)` the ring
`R = k[x,y]_{(x,y)}/(y^p - t x^p - t)` is a regular local ring (indeed a DVR)
essentially of finite type over `k` which is NOT formally smooth over `k`: its
residue field contains `t^{1/p}` and is purely inseparable over `k`, so
`H₁(L_{κ⁄k}) ≠ 0` and arrow (b) above fails.  This is the standard
quasi-elliptic counterexample, and it is exactly why the leaf below cannot be
proven without the perfectness hypothesis entering at (b).

`Algebra.EssFiniteType K R` is load-bearing too — it is what supplies the
presentation at all, and what makes `κ` finitely generated over `K` so that
`of_perfectField` applies.  A regular local ring that is merely a `K`-algebra
need not be formally smooth (e.g. a complete DVR of mixed characteristic is
not formally smooth over its residue field in the non-perfect case).

*Refute the main statement with*: a regular local ring, essentially of finite
type over a PERFECT field, that is not formally smooth over it.  There is none
(Stacks `056S`); over an imperfect field there are, and one is displayed above.
-/
module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.Smooth.Field
public import Mathlib.RingTheory.Smooth.Local
public import Mathlib.RingTheory.Smooth.Locus

@[expose] public section

open TensorProduct

universe u

namespace Algebra

/-- **A LOCAL RING ESSENTIALLY OF FINITE TYPE OVER A FIELD IS A QUOTIENT OF A
LOCALIZED POLYNOMIAL RING AT A PRIME** (PROVEN 2026-07-28).

This is the presentation half of `FormallySmooth.of_isRegularLocalRing_of_perfectField`
and contains no mathematics beyond bookkeeping.  `Algebra.EssFiniteType` gives a
finite-type `K`-subalgebra `A ⊆ R` with `R` a localization of `A`; a surjection
`K[x₁,…,x_n] ↠ A` then composes to `g : K[x₁,…,x_n] → R`, and `𝔮 := g⁻¹(𝔪_R)`
is a prime whose complement `g` sends to units, so `g` extends over
`K[x₁,…,x_n]_𝔮`.  Surjectivity is `IsLocalization.lift_surjective_iff`: every
`r ∈ R` is `a/m` with `a, m` coming from `K[x₁,…,x_n]` and `m` a unit in `R`,
hence outside `𝔮`.

The point of localizing **at a prime** rather than at an arbitrary submonoid
(which is what mathlib's `Smooth/Fiber.lean` does) is that the resulting `P` is
itself LOCAL, NOETHERIAN and REGULAR LOCAL, which is what the Jacobian-criterion
step needs. -/
theorem exists_localizationAtPrime_mvPolynomial_surjective
    (K R : Type u) [Field K] [CommRing R] [IsLocalRing R] [Algebra K R]
    [Algebra.EssFiniteType K R] :
    ∃ (n : ℕ) (q : Ideal (MvPolynomial (Fin n) K)) (_ : q.IsPrime)
      (f : Localization.AtPrime q →ₐ[K] R), Function.Surjective f := by
  classical
  obtain ⟨n, f₀, hf₀⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType K (Algebra.EssFiniteType.subalgebra K R))
  set g : MvPolynomial (Fin n) K →ₐ[K] R :=
    (IsScalarTower.toAlgHom K (Algebra.EssFiniteType.subalgebra K R) R).comp f₀ with hgdef
  set q : Ideal (MvPolynomial (Fin n) K) :=
    Ideal.comap g.toRingHom (IsLocalRing.maximalIdeal R) with hqdef
  have hqp : q.IsPrime := Ideal.comap_isPrime _ _
  haveI := hqp
  have hunit : ∀ y : q.primeCompl, IsUnit (g y) := by
    rintro ⟨y, hy⟩
    refine IsLocalRing.notMem_maximalIdeal.mp fun h ↦ hy ?_
    exact Ideal.mem_comap.mpr h
  refine ⟨n, q, hqp, IsLocalization.liftAlgHom (M := q.primeCompl) (f := g) hunit, ?_⟩
  show Function.Surjective (IsLocalization.lift (M := q.primeCompl) (g := g.toRingHom) hunit)
  rw [IsLocalization.lift_surjective_iff]
  intro v
  obtain ⟨⟨a, m⟩, hv⟩ := IsLocalization.mk'_surjective
    (Algebra.EssFiniteType.submonoid K R) v
  obtain ⟨x, rfl⟩ := hf₀ a
  obtain ⟨s, hs⟩ := hf₀ (m : Algebra.EssFiniteType.subalgebra K R)
  have hgs : g s = algebraMap (Algebra.EssFiniteType.subalgebra K R) R m := by
    rw [hgdef]; simp [hs]
  have hsq : s ∈ q.primeCompl := by
    intro hmem
    exact (IsLocalRing.notMem_maximalIdeal.mpr
      (hgs ▸ IsLocalization.map_units R m)) (Ideal.mem_comap.mp hmem)
  refine ⟨⟨x, ⟨s, hsq⟩⟩, ?_⟩
  have hv' : IsLocalization.mk' R (f₀ x) m = v := hv
  have hspec := IsLocalization.mk'_spec (M := Algebra.EssFiniteType.submonoid K R) R
    (f₀ x) m
  rw [hv'] at hspec
  simpa [hgs, hgdef, hs] using hspec

/-- **THE LOCAL JACOBIAN CRITERION'S INJECTIVITY, FOR A REGULAR LOCAL QUOTIENT
OF A REGULAR LOCAL RING OVER A PERFECT FIELD** (sorry leaf, opened 2026-07-28 —
the single mathematical residue of Stacks `056S` in this development).

The map `KaehlerDifferential.cotangentComplexBaseChange K S P κ` is
`κ ⊗_S I/I² → κ ⊗_P Ω[P⁄K]`, `I = ker (P → S)`, `κ = ResidueField S`; see the
module docstring for the two-step factorization
`κ ⊗_S I/I² ↪ 𝔪_P/𝔪_P² ↪ κ ⊗_P Ω[P⁄K]` whose first arrow is regularity of `S`
and whose second arrow is perfectness of `K`.

**Both hypotheses on the ring side are load-bearing.**  `IsRegularLocalRing S`
is arrow (a); drop it and the leaf is false already for `S = K[x]_{(x)}/(x²)`,
where `I = (x²)`, `I/𝔪_P I` is one-dimensional and `x² ∈ 𝔪_P²` maps to `0`.
`PerfectField K` is arrow (b); drop it and the leaf is false for the
quasi-elliptic example in the module docstring, where `S` is a DVR.

`Algebra.EssFiniteType K P` is what makes `ResidueField S` finitely generated
over `K`, which is the hypothesis of `Algebra.FormallySmooth.of_perfectField`;
without it (b) has no input. -/
theorem injective_cotangentComplexBaseChange_of_isRegularLocalRing
    {K P S : Type u} [Field K] [PerfectField K]
    [CommRing P] [IsRegularLocalRing P] [Algebra K P] [Algebra.EssFiniteType K P]
    [Algebra.FormallySmooth K P] [Module.Free P Ω[P⁄K]] [Module.Finite P Ω[P⁄K]]
    [CommRing S] [IsRegularLocalRing S] [Algebra K S] [Algebra P S] [IsScalarTower K P S]
    (_hsurj : Function.Surjective (algebraMap P S)) :
    Function.Injective
      (KaehlerDifferential.cotangentComplexBaseChange K S P (IsLocalRing.ResidueField S)) :=
  sorry

/-- **A REGULAR LOCAL QUOTIENT OF A REGULAR LOCAL FORMALLY SMOOTH ALGEBRA OVER A
PERFECT FIELD IS FORMALLY SMOOTH** (PROVEN 2026-07-28 over
`injective_cotangentComplexBaseChange_of_isRegularLocalRing`).

This is the local Jacobian criterion
(`Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField`)
applied to the presentation `P ↠ S`; the kernel is finitely generated because
`P` is noetherian (`IsRegularLocalRing` extends `IsNoetherianRing`). -/
theorem FormallySmooth.of_surjective_of_isRegularLocalRing
    {K P S : Type u} [Field K] [PerfectField K]
    [CommRing P] [IsRegularLocalRing P] [Algebra K P] [Algebra.EssFiniteType K P]
    [Algebra.FormallySmooth K P] [Module.Free P Ω[P⁄K]] [Module.Finite P Ω[P⁄K]]
    [CommRing S] [IsRegularLocalRing S] [Algebra K S] [Algebra P S] [IsScalarTower K P S]
    (hsurj : Function.Surjective (algebraMap P S)) :
    Algebra.FormallySmooth K S := by
  have hFG : (RingHom.ker (algebraMap P S)).FG :=
    (IsNoetherian.noetherian (R := P) (RingHom.ker (algebraMap P S)))
  rw [Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField P hsurj hFG]
  exact injective_cotangentComplexBaseChange_of_isRegularLocalRing hsurj

/-- **A REGULAR LOCAL RING ESSENTIALLY OF FINITE TYPE OVER A PERFECT FIELD IS
FORMALLY SMOOTH** — Stacks `056S` in its regular-local form (PROVEN 2026-07-28
over `injective_cotangentComplexBaseChange_of_isRegularLocalRing`, the single
sorry leaf of this module).

This is THE statement that four open nodes of this development were each about
to build separately; see the module docstring for the table.  Everything else
here is bookkeeping: the presentation lemma builds `P = K[x₁,…,x_n]_𝔮 ↠ R`, and
`P` is formally smooth over `K` with `Ω[P⁄K]` finite free because it is a
localization of a polynomial ring
(`Algebra.FormallyEtale.of_isLocalization` plus
`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`), and regular local
because `MvPolynomial (Fin n) K` is a regular ring. -/
theorem FormallySmooth.of_isRegularLocalRing_of_perfectField
    {K R : Type u} [Field K] [PerfectField K] [CommRing R] [IsRegularLocalRing R]
    [Algebra K R] [Algebra.EssFiniteType K R] :
    Algebra.FormallySmooth K R := by
  obtain ⟨n, q, hq, f, hf⟩ := exists_localizationAtPrime_mvPolynomial_surjective K R
  haveI := hq
  algebraize [f.toRingHom]
  haveI : IsScalarTower K (Localization.AtPrime q) R :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin n) K) (Localization.AtPrime q) :=
    .of_isLocalization q.primeCompl
  haveI : Algebra.FormallySmooth K (Localization.AtPrime q) :=
    .comp _ (MvPolynomial (Fin n) K) _
  haveI : Module.Free (Localization.AtPrime q) Ω[Localization.AtPrime q⁄K] :=
    .of_equiv (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K
      (MvPolynomial (Fin n) K) (Localization.AtPrime q))
  haveI : Module.Finite (Localization.AtPrime q) Ω[Localization.AtPrime q⁄K] :=
    .of_surjective (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K
      (MvPolynomial (Fin n) K) (Localization.AtPrime q)).toLinearMap
      (LinearEquiv.surjective _)
  exact FormallySmooth.of_surjective_of_isRegularLocalRing
    (K := K) (P := Localization.AtPrime q) (S := R) hf

/-- **A REGULAR RING OF FINITE TYPE OVER A PERFECT FIELD IS SMOOTH** — the
GLOBAL (non-local) form of Stacks `056S` (PROVEN 2026-07-28 over
`FormallySmooth.of_isRegularLocalRing_of_perfectField`, hence over the single
sorry leaf of this module).

The passage from local to global is FREE at this pin and costs no covering
argument: `Algebra.smoothLocus_eq_univ_iff`
(`Mathlib/RingTheory/Smooth/Locus.lean`) says that for a finitely presented
algebra, `FormallySmooth R A` is EQUIVALENT to every localization `A_𝔭` being
formally smooth, and `IsRegularRing B` is by definition the statement that
every `B_𝔭` is regular local.  So the two definitions meet pointwise and the
main theorem above is applied prime by prime.

`Algebra.FiniteType K B` upgrades to `FinitePresentation` for free because `K`
is a field, hence noetherian (`Algebra.FinitePresentation.of_finiteType`). -/
theorem Smooth.of_isRegularRing_of_perfectField
    (K B : Type u) [Field K] [PerfectField K] [CommRing B] [Algebra K B]
    [Algebra.FiniteType K B] [IsRegularRing B] :
    Algebra.Smooth K B := by
  haveI : Algebra.FinitePresentation K B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  refine ⟨?_, inferInstance⟩
  rw [← Algebra.smoothLocus_eq_univ_iff]
  ext p
  simp only [Set.mem_univ, iff_true]
  show Algebra.FormallySmooth K (Localization.AtPrime p.asIdeal)
  haveI : Algebra.EssFiniteType B (Localization.AtPrime p.asIdeal) :=
    .of_isLocalization _ p.asIdeal.primeCompl
  haveI : Algebra.EssFiniteType K (Localization.AtPrime p.asIdeal) := .comp _ B _
  exact FormallySmooth.of_isRegularLocalRing_of_perfectField

end Algebra
