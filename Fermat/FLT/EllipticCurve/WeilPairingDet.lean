/-
WeilPairingDet.lean — own work for the Fermat project (not vendored from the
FLT project).

# The Weil pairing over an ARBITRARY base field, reduced to one determinant

This module holds the general-base form of Silverman *AEC* III.8.1(a)–(e),

  `WeilPairingDet.exists_weilPairing_mu_nondeg_of_natCast_ne_zero`,

and reduces it — completely, by a proven assembly — to the SINGLE equation

  `WeilPairingDet.exists_primitiveRoot_galois_apply_eq_pow_det` :
      `σ ζ = ζ ^ (det (σ | E[n])).val`   for SOME primitive `n`-th root `ζ` of `k̄`,

(the `∀ ζ` forms `galois_apply_pow_eq_one_eq_pow_det` — at every `n`-th root of
unity — and `galois_apply_primitiveRoot_eq_pow_det` — the statement that was the
leaf until 2026-08-02 — are PROVEN over it by `pow_transport`, so no consumer's
signature has moved),

i.e. to `det ρ_{E,n} = χ_n`, the mod-`n` cyclotomic character.  That equation IS
the arithmetic content of the Weil pairing; everything else in III.8.1 is the
rank-two linear algebra of the coordinate determinant form, and that is what is
proven here.

## Why the two statements are equivalent, and why the cut is still worth making

They ARE equivalent: from a pairing one reads off `det = χ_n`
(`coordDet_map_eq_det_mul_of_basis` below run backwards), and from `det = χ_n`
one builds the pairing (`exists_weilPairing_mu_nondeg_of_natCast_ne_zero`
below).  So no mathematics is removed.  What the cut buys:

* the ~120 lines of pairing bookkeeping — bimultiplicativity, alternation,
  `e ^ n = 1`, nondegeneracy, and the transport of the Galois clause through the
  discrete logarithm — leave the frontier PERMANENTLY, at every base and every
  level, and they are not reproved in any successor;
* the residual leaf is one equation between two elements of `k̄`, which can be
  attacked, refuted or specialised without touching a six-clause existential;
* the residual leaf is exactly the shape of the tree's already-proven
  `WeilPairing.det_galoisRep_eq_cyclotomic` (`EllipticCurve/WeilPairing.lean`,
  over `ℚ`, prime level), so the ℚ-case proof is now visibly a TEMPLATE for it
  rather than an unrelated theorem about a different object.

## Where this sits, and why it is HERE rather than in `Modularity/MoretBailly.lean`

`Modularity/MoretBailly.lean` and `FreyCurve/MazurTorsion.lean` each carry a
copy of this statement — the first at an arbitrary base
(`exists_weilPairing_mu_nondeg_of_natCast_ne_zero`, which now delegates here),
the second with the base fixed at `𝔽_q`
(`exists_weilPairing_mu_nondeg_of_coprime`, same six clauses with
`Nat.Coprime N q` in place of `(n : k) ≠ 0` and `σ` specialised to Frobenius).
Neither module imports the other, so the implication could not be written while
the general statement lived in either of them.  `EllipticCurve/Torsion.lean` is
upstream of both, this module sits directly on top of it, and it depends on
nothing else in the project — so BOTH consumers can reach it.

`MazurTorsion.exists_weilPairing_mu_nondeg_of_coprime` is NOT rewired here (that
file has many concurrent editors and the edit is a pure win only once the leaf
below is closed); the rewiring is one `exact` and is queued.

**AND THERE WAS A THIRD COPY, WHICH WAS DEAD** (found 2026-08-02).
`MoretBailly.det_nTorsion_eq_cyclotomicExponent` is this same statement over a
characteristic-zero base, cut on 2026-07-30 out of `exists_weilPairing_mu_charZero`
— which was re-proven the SAME DAY over `exists_weilPairing_mu_nondeg_of_natCast_ne_zero`
instead, so the cut was orphaned at birth.  A comment-stripped scan of `Fermat/`
found exactly ONE occurrence of its name, its own declaration.  It is now PROVEN
over `galois_apply_pow_eq_one_eq_pow_det` below (`MoretBailly` 20 → 19 direct
sorries) and marked for deletion.  The general shape is worth remembering when
reading this module: `det ρ = χ_n` has been cut FOUR times in three files, and
the copies share no identifier, so only a scan for the CONCLUSION finds them.

## What the RESIDUAL leaf will cost, honestly

Not less than the Weil pairing itself.  The two routes visible from here:

* **Reduce to a finitely generated base.**  `E[n]` and `μ_n` are algebraic over
  the subfield `k₀ ⊆ k` generated over the prime field by the coefficients of
  `E`, and the action of `Aut(k̄/k)` on both factors through `Aut(k̄₀/k₀)`.  So
  the leaf for arbitrary `k` follows from the leaf for `k` finitely generated
  over its prime field — where specialisation to number fields / finite fields
  and Chebotarev are available, which is exactly how the tree proves
  `WeilPairing.det_galoisRep_eq_cyclotomic` over `ℚ`.
* **Build the pairing by divisors.**  `WeilPairing.exists_weilPairing_mu`
  (PROVEN, 8 500 lines) does this at `𝔽_q` and prime level.  Its top-level
  predicate `WeilPairing.weilValueProp` is NOT base-generic: its admissibility
  clause quantifies over a pair of subfields `F ≤ F'` of `k̄` REQUIRED TO BE
  FINITE, and in characteristic zero no such `F` contains the given
  coordinates, so the predicate is unsatisfiable for every pair of nonzero
  points.  A port must first replace that genericity device (the natural
  replacement over any `k̄` is a finitely generated subfield, since an
  algebraically closed field is never finitely generated, so points outside
  `E(F)` always exist) and then re-run the 94 assembly steps.  The LEVEL
  generalisation `p ↦ n` is by contrast mechanical: `weilValueProp` already
  takes a bare `(p : ℕ)`.

  **MEASURED 2026-08-02, so the price is a number rather than a line count.**  Of
  the **49** top-level declarations in `EllipticCurve/WeilPairing.lean`, **21**
  have a STATEMENT — not merely a hypothesis — mentioning `ZMod q`, `frobFixed`,
  `frobPeriod`, `frobAlgHom`, `frobeniusTorsionEnd` or `Fact q.Prime`.  That is
  the port's real surface, and it confirms the audit above rather than softening
  it: `weilValueProp`'s own TYPE is `WeierstrassCurve (ZMod q) → …`, so no
  instantiation reaches it and the 21 must be restated.  What the audit gets
  slightly wrong is WHICH clause is the obstruction.  The finite subfields
  `F ≤ F'` are used only for GENERICITY ("pick a point whose abscissa lies
  outside `F`"), and that role does survive over any algebraically closed `k̄`
  with `F` finitely generated.  The clause with no analogue is
  `frobFixed q (…) ≤ F`, i.e. that `F` be FROBENIUS-STABLE: its replacement is
  `σ`-stability, and the auxiliary generic points `S`, `R` are not algebraic
  over `k`, so their `σ`-orbits need not lie in a finitely generated field.  A
  successor should attack that clause first, not the cardinality argument.

## Faithfulness

`(n : k) ≠ 0` is `char k ∤ n` and forces `n ≠ 0`; it is load-bearing twice —
at `n = 0` the `0`-torsion is all of `E(k̄)`, and if `char k ∣ n` then `E[n]` is
not `(ℤ/n)²` and `μ_n(k̄)` is too small for a nondegenerate pairing to exist.
The `k`-automorphism clause is III.8.1(e), which holds for all of `Gal(k̄/k)`.
The `DecidableEq` `letI` is stated with `Classical.typeDecidableEq` and named
identically in the consumers, so the two `AddCommGroup` structures on
`(E⁄k̄).Point` match syntactically.
-/
module

public import Fermat.FLT.EllipticCurve.Torsion
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Algebra.Module.ZMod

@[expose] public section

universe u

open WeierstrassCurve

namespace WeilPairingDet

/-- **THE COORDINATE DETERMINANT FORM TRANSFORMS BY `LinearMap.det`** (PROVEN
2026-07-31), over an arbitrary COMMUTATIVE RING `R` and a free rank-two module:
for a basis `b` of `M` indexed by `Fin 2`,

`e x y := b.repr x 0 · b.repr y 1 − b.repr x 1 · b.repr y 0`

satisfies `e (f x) (f y) = det f · e x y` for every `R`-linear `f`.

`ZMod n` is not a field unless `n` is prime, so
`WeilPairing.pairing_map_eq_det_smul` — which is stated over a field and
manufactures its basis from a rank hypothesis via `Module.finBasisOfFinrankEq` —
cannot be used at composite level.  Written in coordinates the proof is the
`2 × 2` expansion of `Matrix.det_fin_two` and needs no division.

This is a verbatim re-cut of `MoretBailly.coordDet_map_eq_det_mul`, made here
because that module is strictly DOWNSTREAM of this one.  When the leaf below is
closed the two copies should be collapsed onto this one. -/
lemma coordDet_map_eq_det_mul_of_basis {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] (b : Module.Basis (Fin 2) R M) (f : M →ₗ[R] M)
    (x y : M) :
    b.repr (f x) 0 * b.repr (f y) 1 - b.repr (f x) 1 * b.repr (f y) 0
      = LinearMap.det f * (b.repr x 0 * b.repr y 1 - b.repr x 1 * b.repr y 0) := by
  classical
  have key : ∀ (z : M) (i : Fin 2), b.repr (f z) i
      = LinearMap.toMatrix b b f i 0 * b.repr z 0
        + LinearMap.toMatrix b b f i 1 * b.repr z 1 := by
    intro z i
    have hz : f z = (b.repr z 0) • f (b 0) + (b.repr z 1) • f (b 1) := by
      have hsum := b.sum_repr z
      rw [Fin.sum_univ_two] at hsum
      calc f z = f ((b.repr z 0) • b 0 + (b.repr z 1) • b 1) := by rw [hsum]
        _ = (b.repr z 0) • f (b 0) + (b.repr z 1) • f (b 1) := by
            rw [map_add, map_smul, map_smul]
    rw [hz]
    simp only [map_add, map_smul, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, LinearMap.toMatrix_apply]
    ring
  have hdet : LinearMap.det f =
      LinearMap.toMatrix b b f 0 0 * LinearMap.toMatrix b b f 1 1
        - LinearMap.toMatrix b b f 0 1 * LinearMap.toMatrix b b f 1 0 := by
    rw [← LinearMap.det_toMatrix b f, Matrix.det_fin_two]
  rw [key x 0, key x 1, key y 0, key y 1, hdet]
  ring

/-- **EXPONENTS OF A PRIMITIVE `n`-TH ROOT AGREE MODULO `n`** (PROVEN
2026-08-02).  In a domain, `ζ ^ c = ζ ^ d` for a primitive `n`-th root `ζ`
forces `(c : ZMod n) = (d : ZMod n)`.

`pow_eq_pow_iff_modEq` is stated for a `LeftCancelMonoid`, which a field is NOT
(`0` does not cancel), so the argument goes through the UNIT `ζ`; that is the
same device the assembly below already uses for `ζu`. -/
theorem natCast_eq_of_pow_eq_pow {K : Type*} [CommRing K] [IsDomain K] {n : ℕ}
    [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n) {c d : ℕ} (h : ζ ^ c = ζ ^ d) :
    ((c : ℕ) : ZMod n) = ((d : ℕ) : ZMod n) := by
  have hn0 : n ≠ 0 := NeZero.ne n
  have hval : (((hζ.isUnit hn0).unit : Kˣ) : K) = ζ := IsUnit.unit_spec _
  have hζu : IsPrimitiveRoot ((hζ.isUnit hn0).unit : Kˣ) n := hζ.isUnit_unit hn0
  have hord : orderOf ((hζ.isUnit hn0).unit : Kˣ) = n := hζu.eq_orderOf.symm
  have hu : ((hζ.isUnit hn0).unit : Kˣ) ^ c = ((hζ.isUnit hn0).unit : Kˣ) ^ d := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hval]
    exact h
  have hmod := pow_eq_pow_iff_modEq.mp hu
  rw [hord] at hmod
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod

/-- **AN EXPONENT THAT WORKS ON ONE PRIMITIVE `n`-TH ROOT WORKS ON EVERY `n`-TH
ROOT OF UNITY** (PROVEN 2026-08-02).  If `f` is multiplicative and
`f ζ₀ = ζ₀ ^ d` for a single primitive `n`-th root `ζ₀`, then `f ζ = ζ ^ d` for
every `ζ` with `ζ ^ n = 1` — because every such `ζ` is a power of `ζ₀`
(`IsPrimitiveRoot.eq_pow_of_pow_eq_one`) and `f` commutes with powers.

This is what makes the `∃ ζ` form of the leaf below equivalent to the `∀ ζ`
form: a prover may work at whatever primitive root the construction hands them.
Note the CONCLUSION is about all `n`-th roots of unity, not merely the primitive
ones — which is the shape the `hc` hypothesis of
`MoretBailly.det_nTorsion_eq_cyclotomicExponent` asks for. -/
theorem pow_transport {K : Type*} [CommRing K] [IsDomain K] {M : Type*}
    [FunLike M K K] [MonoidHomClass M K K] (f : M) (n : ℕ) [NeZero n] (d : ℕ)
    {ζ₀ : K} (h0 : IsPrimitiveRoot ζ₀ n) (hf : f ζ₀ = ζ₀ ^ d)
    (ζ : K) (hζ : ζ ^ n = 1) : f ζ = ζ ^ d := by
  obtain ⟨i, _, rfl⟩ := h0.eq_pow_of_pow_eq_one hζ
  rw [map_pow, hf, ← pow_mul, ← pow_mul, Nat.mul_comm]

/-- **`det ρ_{E,n} = χ_n`: THE DETERMINANT OF THE GALOIS ACTION ON `E[n]` IS THE
MOD-`n` CYCLOTOMIC CHARACTER** (sorry leaf, cut 2026-07-31 out of
`exists_weilPairing_mu_nondeg_of_natCast_ne_zero` below, which is now a PROVEN
assembly over it; **RECUT 2026-08-02 from `∀ ζ` to `∃ ζ`**, see below).

Stated elementarily and without any cyclotomic-character API: for every
`k`-automorphism `σ` of `k̄` there is SOME primitive `n`-th root of unity
`ζ ∈ k̄` with

    `σ ζ = ζ ^ (det (σ | E[n])).val`.

Since `σ ζ = ζ ^ χ_n(σ)` DEFINES `χ_n(σ) ∈ (ℤ/n)ˣ` (mathlib:
`ModularCyclotomicCharacter`), this says precisely `det ρ_{E,n} = χ_n`.  The
determinant is taken of the `ZMod n`-linear endomorphism of `E[n]` induced by
`σ`; `E[n]` is free of rank two by `WeierstrassCurve.n_torsion_dimension`
(which is where `(n : k) ≠ 0` is spent a second time), so the determinant is not
a junk value.

**THE 2026-08-02 RECUT, and the accounting: the direct-sorry count did NOT move,
`1 → 1`.**  The previous statement quantified over `ζ` UNIVERSALLY, and its own
docstring observed that one primitive root suffices ("a prover may prove it at a
single convenient `ζ` and transport") without paying for the transport.  That
transport is now `pow_transport` above, PROVEN, so the leaf is the `∃ ζ` form —
strictly weaker, and the form every construction of the pairing actually
produces (the pairing's value at a basis IS a specific primitive root; nothing
hands you an arbitrary one).  Both stronger forms are derived below and no
consumer's statement changed.  Since the recut only WEAKENS the leaf, every
counterexample to the new form is a counterexample to the old, so the
faithfulness audit below transfers verbatim rather than being void — that is the
one direction in which CLAUDE.md's "a restatement VOIDS the earlier audit" rule
does not bite, and it is stated here so a reader does not have to re-derive it.

**WHY IT IS TRUE, AND WHAT IT WILL COST — MEASURED 2026-08-02, correcting a
size estimate that was previously given only in lines.**  It is Silverman *AEC*
III.8.1(a)–(e): the Weil pairing `e_n : E[n] × E[n] → μ_n` is alternating,
nondegenerate and Galois-equivariant, so `σ` scales it by `det(σ)` on the source
and by `χ_n(σ)` on the target.  Two routes are visible (both discussed in the
module docstring):

* *Port the divisor-theoretic construction* `WeilPairing.exists_weilPairing_mu`
  off finite fields.  The module docstring's claim that this is a rewrite rather
  than a base substitution was RE-CHECKED on 2026-08-02 and is CORRECT, and can
  now be quoted as a number: of the **49** top-level declarations in
  `EllipticCurve/WeilPairing.lean`, **21** have a STATEMENT (not merely a
  hypothesis) mentioning `ZMod q`, `frobFixed`, `frobPeriod`, `frobAlgHom`,
  `frobeniusTorsionEnd` or `Fact q.Prime` — including `weilValueProp` itself,
  whose very TYPE is `WeierstrassCurve (ZMod q) → …`, so no instantiation
  reaches it.  A useful sharpening of the docstring's pessimism: the finite
  subfields `F ≤ F'` are used only as a GENERICITY device ("pick a point whose
  abscissa lies outside `F`"), and that role survives over any algebraically
  closed `k̄` with `F` a finitely generated subfield, since an algebraically
  closed field is never finitely generated over its prime field.  What does NOT
  survive is the `frobFixed q …≤ F` clause, which asks that `F` be
  FROBENIUS-STABLE; its analogue is `σ`-stability of `F`, and the auxiliary
  generic points `S`, `R` are not algebraic over `k`, so their `σ`-orbits need
  not generate a finitely generated field.  **That clause, not the cardinality
  argument, is the real obstruction, and a successor should attack it first.**
* *Reduce `k` to a finitely generated field* and import the tree's `ℚ`-case
  Chebotarev argument `WeilPairing.det_galoisRep_eq_cyclotomic`.  Note this does
  NOT bottom out as stated: `k₀ = ℚ(a₁,…,a₆)` is a transcendental extension of
  `ℚ` for a general `E`, so the ℚ-case does not apply to it and a specialisation
  (spreading-out) argument is still owed.  It closes the leaf immediately only
  for curves whose coefficients are algebraic and for prime `n`.

FAITHFULNESS (unchanged by the recut, see above).  `(n : k) ≠ 0` forces
`n ≠ 0`; at `n = 0` there is no primitive `0`-th root of unity in a field other
than by the degenerate convention, and `E[0] = E(k̄)` is not free of rank two, so
the hypothesis is doing real work.  At `n = 1` both sides are `1`.  At `n = 2`
the claim is `σ ζ = ζ` for `ζ = -1` and `det ∈ (ℤ/2)ˣ = {1}`, which is true and
vacuous.  No hypothesis on `k` beyond `char k ∤ n` is needed or true: the
statement holds over every field, including `k = k̄` where `Aut(k̄/k)` is trivial
and both sides are `ζ`.  The `∃` is not the junk-witness trap: a junk `ζ` cannot
satisfy `IsPrimitiveRoot ζ n`, and such a `ζ` exists (`(n : k) ≠ 0` gives
`HasEnoughRootsOfUnity (AlgebraicClosure k) n`), so the existential is
contentful. -/
theorem exists_primitiveRoot_galois_apply_eq_pow_det {k : Type u} [Field k]
    (E : WeierstrassCurve k) [E.IsElliptic] (n : ℕ) (hnk : ((n : ℕ) : k) ≠ 0)
    (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) :
    letI : DecidableEq (AlgebraicClosure k) := Classical.typeDecidableEq _
    ∃ ζ : AlgebraicClosure k, IsPrimitiveRoot ζ n ∧
      σ ζ = ζ ^ (LinearMap.det
        (AddMonoidHom.toZModLinearMap n
          (TorsionCounting.endRestrict (WeierstrassCurve.Affine.Point.map (W' := E)
            σ.toAlgHom) (n : ℤ))
          : ((E.map (algebraMap k (AlgebraicClosure k))).nTorsion n) →ₗ[ZMod n]
            ((E.map (algebraMap k (AlgebraicClosure k))).nTorsion n))).val :=
  sorry

/-- **`det ρ_{E,n} = χ_n` AT EVERY `n`-TH ROOT OF UNITY** (**PROVEN 2026-08-02**
over `exists_primitiveRoot_galois_apply_eq_pow_det` above, by `pow_transport`).

This is strictly stronger than the `IsPrimitiveRoot` form below — it asks
nothing of `ζ` except `ζ ^ n = 1` — and it is the shape a consumer that names
the cyclotomic exponent explicitly wants, because "`τ` acts on `μ_n` by the
exponent `c`" is naturally phrased as `∀ ζ, ζ ^ n = 1 → τ ζ = ζ ^ c`.
`MoretBailly.det_nTorsion_eq_cyclotomicExponent` is exactly that consumer. -/
theorem galois_apply_pow_eq_one_eq_pow_det {k : Type u} [Field k]
    (E : WeierstrassCurve k) [E.IsElliptic] (n : ℕ) (hnk : ((n : ℕ) : k) ≠ 0)
    (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
    (ζ : AlgebraicClosure k) (hζ : ζ ^ n = 1) :
    letI : DecidableEq (AlgebraicClosure k) := Classical.typeDecidableEq _
    σ ζ = ζ ^ (LinearMap.det
      (AddMonoidHom.toZModLinearMap n
        (TorsionCounting.endRestrict (WeierstrassCurve.Affine.Point.map (W' := E)
          σ.toAlgHom) (n : ℤ))
        : ((E.map (algebraMap k (AlgebraicClosure k))).nTorsion n) →ₗ[ZMod n]
          ((E.map (algebraMap k (AlgebraicClosure k))).nTorsion n))).val := by
  letI : DecidableEq (AlgebraicClosure k) := Classical.typeDecidableEq _
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hnk (by simp)
  haveI : NeZero n := ⟨hn0⟩
  obtain ⟨ζ₀, h0, hf⟩ := exists_primitiveRoot_galois_apply_eq_pow_det E n hnk σ
  exact pow_transport σ n _ h0 hf ζ hζ

/-- **`det ρ_{E,n} = χ_n` AT A PRIMITIVE ROOT** (**PROVEN 2026-08-02**; this was
itself the leaf until that date, and its signature is UNCHANGED, so the assembly
`exists_weilPairing_mu_nondeg_of_natCast_ne_zero` below and every downstream
consumer are untouched by the recut).  It is
`galois_apply_pow_eq_one_eq_pow_det` at `hζ.pow_eq_one`. -/
theorem galois_apply_primitiveRoot_eq_pow_det {k : Type u} [Field k]
    (E : WeierstrassCurve k) [E.IsElliptic] (n : ℕ) (hnk : ((n : ℕ) : k) ≠ 0)
    (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
    (ζ : AlgebraicClosure k) (hζ : IsPrimitiveRoot ζ n) :
    letI : DecidableEq (AlgebraicClosure k) := Classical.typeDecidableEq _
    σ ζ = ζ ^ (LinearMap.det
      (AddMonoidHom.toZModLinearMap n
        (TorsionCounting.endRestrict (WeierstrassCurve.Affine.Point.map (W' := E)
          σ.toAlgHom) (n : ℤ))
        : ((E.map (algebraMap k (AlgebraicClosure k))).nTorsion n) →ₗ[ZMod n]
          ((E.map (algebraMap k (AlgebraicClosure k))).nTorsion n))).val :=
  galois_apply_pow_eq_one_eq_pow_det E n hnk σ ζ hζ.pow_eq_one

/-- **THE WEIL PAIRING OVER `k̄` IN SILVERMAN'S OWN FORM, OVER AN ARBITRARY BASE
FIELD WITH `(n : k) ≠ 0`** (**PROVEN 2026-07-31** over the single leaf
`galois_apply_primitiveRoot_eq_pow_det` above).  This is Silverman *AEC*
III.8.1(a)–(e) verbatim: on `E[n]` over `k̄` there is a bimultiplicative
alternating pairing into `k̄ˣ`, killed by `n`, NONDEGENERATE, and natural for
every `k`-automorphism of `k̄`.

THE CONSTRUCTION, which is the whole of III.8.1 minus its arithmetic input.
`WeierstrassCurve.n_torsion_dimension` at the algebraically closed `k̄` gives
`E[n] ≃+ (ZMod n)²`; `ZMod.map_smul` upgrades it to a `ZMod n`-linear
equivalence and `Module.Basis.finTwoProd` transports the standard basis back, so
`E[n]` carries a basis `b` indexed by `Fin 2`.  Let

  `cd x y := b.repr x 0 · b.repr y 1 − b.repr x 1 · b.repr y 0`

be the coordinate determinant form, and let `ζ` be a primitive `n`-th root of
unity of `k̄` (`AlgebraicClosure.hasEnoughRootsOfUnity`, whose hypothesis is
again `(n : k) ≠ 0`).  The pairing is `e x y := ζ ^ (cd x y).val`.  Then

* bimultiplicativity is additivity of `cd` in each slot, transported through
  `ζ ^ · ` — which is a homomorphism `ZMod n → k̄ˣ` exactly because `ζ` has order
  `n` (`pow_eq_pow_iff_modEq`);
* alternation is `cd x x = 0`;
* `e ^ n = 1` is `ζ ^ n = 1`;
* nondegeneracy is: `x ≠ 0` makes some coordinate of `x` nonzero, so `cd x (b 1)`
  or `cd x (b 0)` is a nonzero element `a` of `ZMod n`, and `ζ ^ a.val ≠ 1`
  because `a.val < n` and `ζ` is primitive;
* naturality is where the leaf is spent: `cd (σx) (σy) = det(σ) · cd x y`
  (`coordDet_map_eq_det_mul_of_basis`) on the source, and
  `σ ζ = ζ ^ det(σ).val` (the leaf) on the target, and the two exponents agree.

The `IsPrimitiveRoot` strengthening of the nondegeneracy clause is NOT proved
here: it is `MoretBailly.isPrimitiveRoot_of_nondegenerate_fin_two`, which is
already proven at an arbitrary commutative group of values and is where the
downstream consumers pick it up.

FAITHFULNESS: see the module docstring. -/
theorem exists_weilPairing_mu_nondeg_of_natCast_ne_zero {k : Type u} [Field k]
    (E : WeierstrassCurve k) [E.IsElliptic] (n : ℕ)
    (hnk : ((n : ℕ) : k) ≠ 0) :
    letI : DecidableEq (AlgebraicClosure k) := Classical.typeDecidableEq _
    ∃ e : ((E.map (algebraMap k (AlgebraicClosure k))).nTorsion n) →
          ((E.map (algebraMap k (AlgebraicClosure k))).nTorsion n) →
          (AlgebraicClosure k)ˣ,
      (∀ x y z, e (x + y) z = e x z * e y z) ∧
      (∀ x y z, e x (y + z) = e x y * e x z) ∧
      (∀ x, e x x = 1) ∧
      (∀ x y, (e x y) ^ n = 1) ∧
      (∀ x, x ≠ 0 → ∃ y, e x y ≠ 1) ∧
      (∀ (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) x y,
        e (TorsionCounting.endRestrict (WeierstrassCurve.Affine.Point.map (W' := E)
              σ.toAlgHom) (n : ℤ) x)
          (TorsionCounting.endRestrict (WeierstrassCurve.Affine.Point.map (W' := E)
              σ.toAlgHom) (n : ℤ) y)
          = Units.map σ.toAlgHom.toRingHom.toMonoidHom (e x y)) := by
  letI : DecidableEq (AlgebraicClosure k) := Classical.typeDecidableEq _
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hnk (by simp)
  haveI : NeZero n := ⟨hn0⟩
  haveI : NeZero ((n : ℕ) : k) := ⟨hnk⟩
  have hnK : ((n : ℕ) : AlgebraicClosure k) ≠ 0 := by
    have : NeZero ((n : ℕ) : AlgebraicClosure k) :=
      (‹NeZero ((n : ℕ) : k)›).of_injective (algebraMap k (AlgebraicClosure k)).injective
    exact NeZero.ne _
  -- the rank-two basis of `E[n]` at the algebraically closed `k̄`
  obtain ⟨φ⟩ := WeierstrassCurve.n_torsion_dimension
    (E.map (algebraMap k (AlgebraicClosure k))) hnK
  let ψ : ((E.map (algebraMap k (AlgebraicClosure k))).nTorsion n) ≃ₗ[ZMod n]
      (ZMod n × ZMod n) := { φ with map_smul' := ZMod.map_smul φ.toAddMonoidHom }
  let b : Module.Basis (Fin 2) (ZMod n)
      ((E.map (algebraMap k (AlgebraicClosure k))).nTorsion n) :=
    (Module.Basis.finTwoProd (ZMod n)).map ψ.symm
  -- a primitive `n`-th root of unity of `k̄`, as a UNIT
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure k) n
  set ζu : (AlgebraicClosure k)ˣ := (hζ.isUnit hn0).unit with hζudef
  have hζuval : (ζu : AlgebraicClosure k) = ζ := IsUnit.unit_spec _
  have hζu : IsPrimitiveRoot ζu n := hζ.isUnit_unit hn0
  have horder : orderOf ζu = n := hζu.eq_orderOf.symm
  -- `ζu ^ ·` only depends on the exponent mod `n`
  have hcong : ∀ i j : ℕ, ((i : ℕ) : ZMod n) = ((j : ℕ) : ZMod n) → ζu ^ i = ζu ^ j := by
    intro i j h
    rw [pow_eq_pow_iff_modEq, horder]
    exact (ZMod.natCast_eq_natCast_iff i j n).mp h
  have hvalcast : ∀ a : ZMod n, ((a.val : ℕ) : ZMod n) = a := fun a => by
    rw [ZMod.natCast_val, ZMod.cast_id]
  -- the coordinate determinant form
  obtain ⟨cd, hcd⟩ : ∃ cd : ((E.map (algebraMap k (AlgebraicClosure k))).nTorsion n) →
      ((E.map (algebraMap k (AlgebraicClosure k))).nTorsion n) → ZMod n, ∀ x y,
      cd x y = b.repr x 0 * b.repr y 1 - b.repr x 1 * b.repr y 0 :=
    ⟨_, fun _ _ => rfl⟩
  -- `ζu ^ (·).val` turns sums into products
  have hmul : ∀ a c : ZMod n, ζu ^ (a + c).val = ζu ^ a.val * ζu ^ c.val := by
    intro a c
    rw [← pow_add]
    exact hcong _ _ (by rw [hvalcast, Nat.cast_add, hvalcast, hvalcast])
  refine ⟨fun x y => ζu ^ (cd x y).val, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- additivity in the left slot
    intro x y z
    show ζu ^ (cd (x + y) z).val = ζu ^ (cd x z).val * ζu ^ (cd y z).val
    rw [← hmul]
    refine hcong _ _ ?_
    rw [hvalcast, hvalcast, hcd, hcd, hcd]
    simp only [map_add, Finsupp.coe_add, Pi.add_apply]
    ring
  · -- additivity in the right slot
    intro x y z
    show ζu ^ (cd x (y + z)).val = ζu ^ (cd x y).val * ζu ^ (cd x z).val
    rw [← hmul]
    refine hcong _ _ ?_
    rw [hvalcast, hvalcast, hcd, hcd, hcd]
    simp only [map_add, Finsupp.coe_add, Pi.add_apply]
    ring
  · -- alternation
    intro x
    show ζu ^ (cd x x).val = 1
    have : cd x x = 0 := by rw [hcd]; ring
    rw [this]
    simp
  · -- killed by `n`
    intro x y
    show (ζu ^ (cd x y).val) ^ n = 1
    rw [← pow_mul, mul_comm, pow_mul, hζu.pow_eq_one, one_pow]
  · -- nondegeneracy
    intro x hx
    -- a nonzero element of `ZMod n` has `ζu ^ ·.val ≠ 1`
    have hne : ∀ a : ZMod n, a ≠ 0 → ζu ^ a.val ≠ 1 := by
      intro a ha h1
      have hdvd : n ∣ a.val := (hζu.pow_eq_one_iff_dvd _).mp h1
      have hlt : a.val < n := ZMod.val_lt a
      have : a.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
      exact ha (by rw [← hvalcast a, this, Nat.cast_zero])
    have hrepr : b.repr x ≠ 0 := fun h => hx (by
      have := congrArg b.repr.symm h
      simpa using this)
    by_cases h0 : b.repr x 0 = 0
    · have h1 : b.repr x 1 ≠ 0 := by
        intro h1
        exact hrepr (Finsupp.ext fun i => by fin_cases i <;> simpa using ‹_›)
      refine ⟨b 0, ?_⟩
      show ζu ^ (cd x (b 0)).val ≠ 1
      refine hne _ ?_
      rw [hcd]
      simp only [Module.Basis.repr_self, Finsupp.single_apply]
      norm_num [h0]
      simpa using h1
    · refine ⟨b 1, ?_⟩
      show ζu ^ (cd x (b 1)).val ≠ 1
      refine hne _ ?_
      rw [hcd]
      simp only [Module.Basis.repr_self, Finsupp.single_apply]
      norm_num
      exact h0
  · -- Galois naturality: the leaf
    intro σ x y
    -- the induced endomorphism of `E[n]` is abstracted into `f`, so that the
    -- instance path Lean picked when elaborating the STATEMENT is the one used
    -- throughout: re-writing the `endRestrict` term here elaborates
    -- `Point.map` under `Affine.Point.instAddZeroClass` rather than under
    -- `instAddCommGroup.toAddZeroClass`, and the two are not syntactically equal.
    have key : ∀ (f : ((E.map (algebraMap k (AlgebraicClosure k))).nTorsion n) →+
          ((E.map (algebraMap k (AlgebraicClosure k))).nTorsion n)),
        σ ζ = ζ ^ (LinearMap.det (AddMonoidHom.toZModLinearMap n f)).val →
        ∀ u v, ζu ^ (cd (f u) (f v)).val
          = Units.map σ.toAlgHom.toRingHom.toMonoidHom (ζu ^ (cd u v).val) := by
      intro f hf u v
      have hleaf : Units.map σ.toAlgHom.toRingHom.toMonoidHom ζu
          = ζu ^ (LinearMap.det (AddMonoidHom.toZModLinearMap n f)).val := by
        refine Units.ext ?_
        rw [Units.val_pow_eq_pow_val, hζuval]
        exact hf
      have hcdT : cd (f u) (f v)
          = LinearMap.det (AddMonoidHom.toZModLinearMap n f) * cd u v := by
        rw [hcd, hcd]
        exact coordDet_map_eq_det_mul_of_basis b (AddMonoidHom.toZModLinearMap n f) u v
      rw [hcdT, map_pow, hleaf, ← pow_mul]
      refine hcong _ _ ?_
      rw [hvalcast, Nat.cast_mul, hvalcast, hvalcast]
    exact key _ (galois_apply_primitiveRoot_eq_pow_det E n hnk σ ζ hζ) x y

end WeilPairingDet
