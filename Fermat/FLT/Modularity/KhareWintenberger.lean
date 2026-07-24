/-
Modularity/KhareWintenberger.lean — own work for the Fermat project (not
vendored from the FLT project).

# The Khare–Wintenberger cut behind residual modularity at `ℓ ≥ 5`

This module carries the founder decomposition of the residual-modularity
leaf `exists_weightTwoEigenform_residual_of_isIrreducible_of_five_le`
(`Modularity/Interface.lean`, pillar 2 at `ℓ ≥ 5` — the
Khare–Wintenberger content of the modularity subtree).

## Route choice (AUDIT, 2026-07-24)

Two literature routes were audited for that leaf:

* the **Khare–Wintenberger induction** (*Serre's modularity conjecture
  (I), (II)*, Invent. Math. 178 (2009)): minimal lifting of the residual
  representation to a strictly compatible system, then induction on the
  residue characteristic with modularity switching at auxiliary primes;
* the **potential-modularity chain** of the FLT blueprint (ch. 4:
  Moret–Bailly, dihedral residual modularity from converse theorems,
  modularity lifting over totally real fields, base-change descent) —
  the route the reference Lean project (`~/cs/FLT`) chose.

For the HARDLY RAMIFIED type both routes converge onto the same terminal
shape. Any compatible system attached to a hardly ramified
representation has a `3`-adic member which is hardly ramified `3`-adic,
and this project PROVES (Fontaine/Odlyzko discriminant bounds,
`ModThree.lean`; ordinarity lifting, `Threeadic.lean`) that such a
member is a global extension of the trivial character by the cyclotomic
character — its Frobenius traces are `1 + q`. So the anchor-prime step
of either route does not produce a cusp form: it produces the Eisenstein
trace system, and transporting it back through the family forces the
residual representation to be REDUCIBLE (Chebotarev + Brauer–Nesbitt),
contradicting the leaf's irreducibility hypothesis. Both classical
routes, instantiated at this type, are therefore proofs by contradiction
— which is exactly the blueprint's plan (ch. 4, "Compatible families,
and reduction at 3") and exactly why `S₂(Γ₀(2)) = 0` makes Serre's
conjecture at type `(2, 2)` a nonexistence theorem. The sound cut is
hence the blueprint cut: prove the headline

  **no irreducible hardly ramified mod-`ℓ` representation exists for
  `ℓ ≥ 5`** (`not_isIrreducible_of_isHardlyRamified_of_five_le`)

and discharge the interface leaf by `absurd`. The alternative — a
non-vacuous eigenform-producing decomposition — would require
constructing analytic cusp forms (Langlands–Tunnell / converse-theorem
machinery) on a pin with no Hecke theory; that route is strictly deeper
at every node and was rejected.

## Relation to the existing tree (NO CYCLE, NO SILENT DUPLICATION)

The tree already contains this chain ONCE: `Reducible.lean`'s B5 is
proven from `Lift.lean`'s `exists_hardlyRamifiedLift` (B6a),
`residual_charFrob_eq` (B6bc) and `not_isIrreducible_of_charFrob_eq`
(Chebotarev–Brauer–Nesbitt). But B6bc routes through `Family.lean`'s
`mem_isCompatible`, whose proof consumes the modularity interface — the
very assemblies that consume the leaf this module discharges. Importing
`Lift.lean` here would therefore close the dependency cycle that the
interface's CIRCULARITY GUARD forbids. The three sorried pillars below
are consequently FAMILY-FREE restatements, and their docstrings record,
pillar by pillar, which in-tree twin they mirror and which discharge
routes are sound:

* pillar α (`exists_hardlyRamified_lift_residual_of_five_le`) mirrors
  `Lift.lean`'s B6a and may eventually SHARE its proof by a bookkeeping
  refactor (moving the deformation development out of `Lift.lean`'s
  `Family.lean` import);
* pillar β (`exists_threeadic_compatible_member_of_five_le`) mirrors
  B6b + the 3-adic specialization, but its in-tree twin's proof
  (through `Family.lean`) is UNSOUND here — its only sound discharge is
  the potential-modularity construction. This pillar is where the
  genuine depth of the residual-modularity leaf now lives;
* pillar γ (`not_isIrreducible_of_charFrob_eisenstein`) is the
  finite-coefficient-field transfer of the PROVEN
  `not_isIrreducible_of_charFrob_eq`, whose proof consumes only
  Family-free material from `Chebotarev.lean` — a mechanical
  generalization, no new mathematics. PROVEN 2026-07-24: `char k = ℓ`
  (`charP_of_algebra_padicInt`), the twin's density argument with the
  comparison functions pushed into `k` through `ZMod.castHom`, and the
  field-generic Kolchin/Brauer–Nesbitt helper
  `not_isIrreducible_of_charpoly_eq_units`.

The assembly `not_isIrreducible_of_isHardlyRamified_of_five_le` is
PROVEN below from the three pillars plus the PROVEN 3-adic machinery
(`IsHardlyRamified.exists_frobenius_triangular`, `Threeadic.lean` — the
trace form of the same classification is B6c,
`IsHardlyRamified.three_adic`).

(Import note, 2026-07-24: `Chebotarev.lean` — the home of pillar γ's
proof ingredients — is deliberately NOT imported: the assembly does not
need it, thanks to the triangular-Frobenius route through
`Threeadic.lean`; the agent proving pillar γ adds the import then —
done 2026-07-24, as proof-only (non-public) imports.)
-/
module

public import Fermat.FLT.GaloisRepresentation.HardlyRamified.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
-- proof-only imports: the PROVEN 3-adic classification (Family-free —
-- see the module docstring for why `Lift.lean`/`Family.lean` must NOT
-- be imported) and the matrix-charpoly bridges
import Fermat.FLT.GaloisRepresentation.HardlyRamified.Threeadic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
-- pillar-γ proof-only imports (see the module docstring's import note):
-- the Family-free Chebotarev/Brauer–Nesbitt machinery and its Kolchin
-- ingredients
import Fermat.FLT.GaloisRepresentation.Chebotarev
import Fermat.FLT.GaloisRepresentation.BrauerNesbitt
import Mathlib.Tactic.NoncommRing

@[expose] public section

namespace GaloisRepresentation.Modularity

open IsDedekindDomain Polynomial

universe u v

/-- **Pillar α — Khare–Wintenberger minimal lifting** (sorry node): an
IRREDUCIBLE hardly ramified mod-`ℓ` representation, `ℓ ≥ 5`, lifts to a
hardly ramified `ℓ`-adic representation: a characteristic-zero
coefficient package `O` — a local domain, module-finite over `ℤ_ℓ` with
its module topology and `ℤ_ℓ ↪ O` (classically: the image of the
universal hardly ramified deformation ring in a `ℚ̄_ℓ`-point, a subring
of the integers of a finite extension of `ℚ_ℓ`; taking the image rather
than the full valuation ring is what makes the residue field exactly
`k`, so that the reduction `π` below exists onto `k` itself) — carrying
a hardly ramified representation on `Fin 2 → O` whose Frobenius
characteristic polynomials reduce through a surjection `π : O →+* k` to
those of `ρbar` at every prime `q ∉ {2, ℓ}`.

Literature: Khare–Wintenberger, *Serre's modularity conjecture (I)*,
Invent. Math. 178 (2009), Theorem 4.1 and §4 (existence of minimal
`p`-adic lifts of prescribed type — here Serre type `(2, 2)`, i.e. the
hardly ramified conditions: cyclotomic determinant, unramified outside
`2ℓ`, flat at `ℓ`, tame square-trivial rank-1 quotient at `2`). The
proof machinery is Kisin's flat deformation theory (*Moduli of finite
flat group schemes, and modularity*, Ann. of Math. 170 (2009)), Böckle's
presentation bounds for global deformation rings, and Taylor's potential
modularity (*Remarks on a conjecture of Fontaine and Mazur*, J. Inst.
Math. Jussieu 1 (2002); *On the meromorphic continuation of degree two
L-functions*, Doc. Math. Extra Vol. (2006)) supplying the finiteness
input that forces the deformation ring to have a characteristic-zero
point. FLT blueprint ch. 4: "use Khare–Wintenberger to lift `ρ` to a
potentially modular `ℓ`-adic Galois representation of conductor 2".

SOUNDNESS AUDIT (both ways, 2026-07-24): (i) direct — this is KW
Theorem 4.1 specialized to type `(2, 2)`, a true nonvacuous theorem of
deformation theory (its proof nowhere presupposes that the target
spaces of Serre's conjecture are nonzero); (ii) collapse — the
hypothesis set (an irreducible hardly ramified mod-`ℓ` representation,
`ℓ ≥ 5`) is classically unsatisfiable (the headline theorem below), so
the statement is also vacuously sound; no honest weakening of the
conclusion can make the hypotheses satisfiable.

IN-TREE TWIN: `exists_hardlyRamifiedLift` (`Lift.lean`, stated over
`ZMod ℓ`), already decomposed there into deformation-theoretic leaves
(Mazur representability, Carayol subring descent, mod-`ℓ` finiteness,
minimal presentations). That module imports `Family.lean` and is
therefore un-importable here (cycle); its lifting development does not
mathematically depend on the family machinery, so a future bookkeeping
refactor splitting it into a Family-free module can discharge this
pillar by delegation (generalizing `ZMod ℓ` to the finite coefficient
field `k`, which its deformation theory already handles classically).
Until then the two statements are deliberately kept in sync.
CIRCULARITY GUARD: must not be proven through `Family.lean`,
`Lift.lean`, or `Modularity/Interface.lean`. -/
theorem exists_hardlyRamified_lift_residual_of_five_le
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible) :
    ∃ (O : Type u) (_ : CommRing O) (_ : IsDomain O) (_ : TopologicalSpace O)
      (_ : IsTopologicalRing O) (_ : Algebra ℤ_[ℓ] O) (_ : IsLocalRing O)
      (_ : Module.Finite ℤ_[ℓ] O) (_ : IsModuleTopology ℤ_[ℓ] O)
      (_ : Function.Injective (algebraMap ℤ_[ℓ] O))
      (ρ : GaloisRep ℚ O (Fin 2 → O))
      (hrank : Module.rank O (Fin 2 → O) = 2)
      (_ : IsHardlyRamified hℓodd hrank ρ)
      (π : O →+* k) (_ : Function.Surjective π),
      ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
        (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
          ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat :=
  sorry

/-- **Pillar β — the compatible system and its `3`-adic member** (sorry
node — the potential-modularity content, and the genuine depth of the
residual-modularity leaf): a hardly ramified `ℓ`-adic lift (as produced
by pillar α) of an irreducible hardly ramified mod-`ℓ` representation,
`ℓ ≥ 5`, lies in a compatible system: there are a number field `E`, a
family `Pv` of `E`-coefficient polynomials indexed by the places of `ℚ`,
and embeddings identifying `Pv` at almost all places both with the
Frobenius characteristic polynomials of `ρ` (through `ψℓ`, `ιO` into
`ℚ̄_ℓ`) and with those of a hardly ramified `3`-ADIC representation `τ`
(through `ψ₃`, `ιA` into `ℚ̄_3`) over a coefficient package `A` of the
same characteristic-zero shape — in particular `ℤ_3`-FREE, as the
integers of a finite extension of `ℚ_3` are, which is what the proven
`3`-adic classification consumes.

Classically the `3`-adic member is hardly ramified because strict
compatibility transports the type: the conductor divides `2` and the
determinant is cyclotomic across the family; flatness at `3` holds by
Fontaine–Laffaille theory (weight 2, `3` prime to the conductor); the
tame unramified square-trivial rank-1 quotient at `2` is the fixed
Weil–Deligne type at `2`.

Literature: Khare–Wintenberger, *Serre's modularity conjecture (I)*,
Invent. Math. 178 (2009), §5 (the lift is part of a strictly compatible
system — via potential modularity and Brauer's theorem, following
Dieulefait and Taylor); Barnet-Lamb–Gee–Geraghty–Taylor, *Potential
automorphy and change of weight*, Ann. of Math. 179 (2014), §5 (the
Brauer-trick construction of compatible systems attached to potentially
automorphic representations); Taylor, *Remarks on a conjecture of
Fontaine and Mazur*, J. Inst. Math. Jussieu 1 (2002) (potential
modularity via Moret–Bailly). FLT blueprint ch. 4: "put it into an
`ℓ`-adic family using the Brauer's theorem trick … and look at the
`3`-adic specialisation".

SOUNDNESS AUDIT (both ways, 2026-07-24): (i) direct — for the intended
instantiation (pillar α's package, the KW minimal lift) this is KW (I)
§5 verbatim; for an abstract package `(O, ρ, π)` not arising from that
construction the literature statement does not directly apply
(abstract-quantification caveat, same as the interface's pillar 3b),
but (ii) collapse — the hypothesis set includes an irreducible hardly
ramified mod-`ℓ` representation with `ℓ ≥ 5`, classically unsatisfiable
(headline below), so the statement is classically true for every
package.

CIRCULARITY GUARD (load-bearing, stronger than the usual note): the
in-tree twin of this pillar is `Family.lean`'s `mem_isCompatible`
composed with `Lift.lean`'s `residual_charFrob_eq_of_family` — but
`mem_isCompatible` is proven THROUGH the modularity interface (the
compatible family is extracted from the eigenform attached by the
interface's assemblies), i.e. through the consumer of the leaf this
module discharges. Porting that proof here would close the cycle. The
ONLY sound discharges of this pillar are the genuinely independent
constructions: KW (I) §5, or the blueprint's potential-modularity chain
(Moret–Bailly + dihedral residual modularity + modularity lifting over
totally real fields + base-change descent). Future dispatches on this
node must build that machinery, not reuse `Family.lean`. -/
theorem exists_threeadic_compatible_member_of_five_le
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat) :
    ∃ (E : Type u) (_ : Field E) (_ : NumberField E)
      (S₀ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
      (Pv : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) → Polynomial E)
      (ψℓ : E →+* AlgebraicClosure ℚ_[ℓ])
      (ιO : O →+* AlgebraicClosure ℚ_[ℓ]) (_ : Function.Injective ιO)
      (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : IsTopologicalRing A) (_ : Algebra ℤ_[3] A) (_ : IsLocalRing A)
      (_ : Module.Finite ℤ_[3] A) (_ : Module.Free ℤ_[3] A)
      (_ : IsModuleTopology ℤ_[3] A)
      (τ : GaloisRep ℚ A (Fin 2 → A))
      (hrankA : Module.rank A (Fin 2 → A) = 2)
      (_ : IsHardlyRamified (show Odd 3 by decide) hrankA τ)
      (ψ₃ : E →+* AlgebraicClosure ℚ_[3])
      (ιA : A →+* AlgebraicClosure ℚ_[3]) (_ : Function.Injective ιA),
      ∀ (q : ℕ) (hq : q.Prime),
        hq.toHeightOneSpectrumRingOfIntegersRat ∉ S₀ →
        q ≠ 2 → q ≠ 3 → q ≠ ℓ →
        (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map ιO =
          (Pv hq.toHeightOneSpectrumRingOfIntegersRat).map ψℓ ∧
        (τ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map ιA =
          (Pv hq.toHeightOneSpectrumRingOfIntegersRat).map ψ₃ :=
  sorry

/-!
### Pillar-γ helpers: field-generic Chebotarev–Brauer–Nesbitt transfer

Three PROVEN helper lemmas for `not_isIrreducible_of_charFrob_eisenstein`
— the field-generic forms of the `ZMod ℓ`-specific steps of `Lift.lean`'s
`not_isIrreducible_of_charFrob_eq` (whose proof this pillar's proof
mirrors, per the docstring's generalization path).
-/

/-- A finite field `k` receiving a `ℤ_[ℓ]`-algebra structure has
characteristic `ℓ`: the characteristic of `k` is a prime `p` (finiteness
rules out characteristic zero), and were `p ≠ ℓ` then `p` — a unit of
`ℤ_[ℓ]`, having norm one by coprimality — would map to the unit `(p : k)
= 0`, absurd. This is what lets the `ZMod ℓ`-valued mod-`ℓ` cyclotomic
character be compared with `k`-valued Frobenius data through
`ZMod.castHom` in pillar γ. -/
theorem charP_of_algebra_padicInt (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Finite k] [Algebra ℤ_[ℓ] k] :
    CharP k ℓ := by
  obtain ⟨p, hp⟩ := CharP.exists k
  haveI := hp
  rcases CharP.char_is_prime_or_zero k p with hpp | rfl
  · suffices hpe : p = ℓ by rwa [hpe] at hp
    by_contra hne
    have hcop : ℓ.Coprime p :=
      (Nat.coprime_primes Fact.out hpp).mpr fun hle => hne hle.symm
    have hunit : IsUnit ((p : ℤ_[ℓ])) :=
      PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr hcop)
    have hmap : IsUnit ((p : k)) := by
      have hu := hunit.map (algebraMap ℤ_[ℓ] k)
      rwa [map_natCast] at hu
    rw [CharP.cast_eq_zero k p] at hmap
    exact not_isUnit_zero hmap
  · haveI : CharZero k := CharP.charP_to_charZero k
    haveI : Finite ℕ :=
      Finite.of_injective (Nat.cast : ℕ → k) Nat.cast_injective
    exact (not_finite ℕ).elim

set_option backward.isDefEq.respectTransparency false in
/-- **Field-generic invariant-submodule refutation** (helper for pillar
γ): a nonzero proper Galois-stable submodule refutes irreducibility.
Transfer of `Chebotarev.lean`'s
`not_isIrreducible_of_invariant_submodule` (stated there over `ZMod ℓ`)
to an arbitrary coefficient field; the proof is identical. -/
theorem not_isIrreducible_of_invariant_submodule_field
    {k : Type u} [Field k] [TopologicalSpace k]
    {W : Type v} [AddCommGroup W] [Module k W]
    (ρbar : GaloisRep ℚ k W) (U : Submodule k W)
    (hne : U ≠ ⊥) (htop : U ≠ ⊤)
    (hinv : ∀ g w, w ∈ U → ρbar g w ∈ U) :
    ¬ ρbar.IsIrreducible := by
  intro hirr
  haveI : IsSimpleOrder (Subrepresentation ρbar.toRepresentation) := hirr
  rcases eq_bot_or_eq_top
    (⟨U, fun g w hw => hinv g w hw⟩ :
      Subrepresentation ρbar.toRepresentation) with hP | hP
  · exact hne (congrArg Subrepresentation.toSubmodule hP)
  · exact htop (congrArg Subrepresentation.toSubmodule hP)

set_option backward.isDefEq.respectTransparency false in
/-- **Brauer–Nesbitt over a general coefficient field** (helper for
pillar γ): a 2-dimensional representation over a field `k` whose
characteristic polynomials agree *everywhere* with those of `1 ⊕ χ`,
for a unit-valued character `χ`, is not irreducible. Field-generic
transfer of `Chebotarev.lean`'s `not_isIrreducible_of_charpoly_eq`
(stated there over `ZMod ℓ` with `χ = χ̄_cyc`), by the identical
Kolchin/common-eigenvector route: Cayley–Hamilton turns the charpoly
hypothesis into `(ρ g − 1)(ρ g − χ g) = 0`; on `ker χ` every element is
unipotent, so `BrauerNesbitt.exists_fixed_of_unipotent` gives a nonzero
fixed subspace, Galois-stable by normality; if it is everything, the
image commutes and `BrauerNesbitt.exists_common_eigenvector_of_commuting`
produces an invariant line — both `BrauerNesbitt` inputs are already
field-generic. -/
theorem not_isIrreducible_of_charpoly_eq_units
    {k : Type u} [Field k] [TopologicalSpace k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hdim : Module.rank k W = 2) (ρbar : GaloisRep ℚ k W)
    (χ : Field.absoluteGaloisGroup ℚ →* kˣ)
    (h : ∀ g, (ρbar g).charpoly =
      X ^ 2 - C (((χ g : kˣ) : k) + 1) * X + C ((χ g : kˣ) : k)) :
    ¬ ρbar.IsIrreducible := by
  classical
  have hfr : Module.finrank k W = 2 :=
    Module.finrank_eq_of_rank_eq (by exact_mod_cast hdim)
  -- Cayley–Hamilton: `(ρ g − 1)(ρ g − χ g) = 0`
  have hCH : ∀ g, (ρbar g - 1) * (ρbar g - algebraMap k
      (Module.End k W) ((χ g : kˣ) : k)) = 0 := by
    intro g
    have hch := LinearMap.aeval_self_charpoly (ρbar g)
    rw [h g] at hch
    simp only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X,
      Polynomial.aeval_C] at hch
    have hcomm : Commute (ρbar g) (algebraMap k
        (Module.End k W) ((χ g : kˣ) : k)) :=
      (Algebra.commute_algebraMap_right _ _)
    have hexp : (ρbar g - 1) * (ρbar g - algebraMap k
        (Module.End k W) ((χ g : kˣ) : k)) =
        (ρbar g) ^ 2 - (algebraMap k (Module.End k W) ((χ g : kˣ) : k)
          + algebraMap k (Module.End k W) 1) * ρbar g
        + algebraMap k (Module.End k W) ((χ g : kˣ) : k) := by
      have e1 : (ρbar g - 1) * (ρbar g - algebraMap k
          (Module.End k W) ((χ g : kˣ) : k)) =
          ρbar g * ρbar g - ρbar g * algebraMap k
            (Module.End k W) ((χ g : kˣ) : k)
          - ρbar g + algebraMap k (Module.End k W) ((χ g : kˣ) : k) := by
        noncomm_ring
      rw [e1, hcomm.eq, map_one]
      noncomm_ring
    rw [hexp]
    exact hch
  -- the kernel of the character acts unipotently
  by_cases hWtop : (⨅ hH : χ.ker,
      LinearMap.ker (ρbar (hH : Field.absoluteGaloisGroup ℚ) - 1)) = ⊤
  · -- `ρ` kills the kernel of `χ`: commuting image, split quadratics
    have hker1 : ∀ hH : χ.ker,
        ρbar (hH : Field.absoluteGaloisGroup ℚ) = 1 := by
      intro hH
      ext v
      have hv : v ∈ (⨅ hH : χ.ker,
          LinearMap.ker (ρbar (hH : Field.absoluteGaloisGroup ℚ) - 1)) :=
        hWtop ▸ Submodule.mem_top
      have hvk := (Submodule.mem_iInf _).mp hv hH
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hvk
      simpa using hvk
    have hcommim : ∀ g₁ g₂, Commute (ρbar g₁) (ρbar g₂) := by
      intro g₁ g₂
      have hc : g₁⁻¹ * g₂⁻¹ * g₁ * g₂ ∈ χ.ker := by
        rw [MonoidHom.mem_ker]
        simp only [map_mul, map_inv]
        rw [mul_comm (χ g₁)⁻¹ (χ g₂)⁻¹, mul_assoc, mul_assoc,
          ← mul_assoc (χ g₁)⁻¹, inv_mul_cancel, one_mul, inv_mul_cancel]
      have h1 := hker1 ⟨g₁⁻¹ * g₂⁻¹ * g₁ * g₂, hc⟩
      have h2 : ρbar (g₁ * (g₁⁻¹ * g₂⁻¹ * g₁ * g₂)) = ρbar g₁ := by
        rw [map_mul]
        simp only at h1
        rw [h1, mul_one]
      have h3 : g₁ * (g₁⁻¹ * g₂⁻¹ * g₁ * g₂) = g₂⁻¹ * g₁ * g₂ := by
        group
      rw [h3, map_mul, map_mul] at h2
      unfold Commute SemiconjBy
      have hcancel : ρbar g₂ * ρbar g₂⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel, map_one]
      calc ρbar g₁ * ρbar g₂
          = ρbar g₂ * ρbar g₂⁻¹ * (ρbar g₁ * ρbar g₂) := by
            rw [hcancel, one_mul]
      _ = ρbar g₂ * (ρbar g₂⁻¹ * ρbar g₁ * ρbar g₂) := by
            noncomm_ring
      _ = ρbar g₂ * ρbar g₁ := by rw [h2]
    obtain ⟨v, hv, heig⟩ :=
      BrauerNesbitt.exists_common_eigenvector_of_commuting hdim
        (Set.range fun g => ρbar g)
        (by rintro _ ⟨g₁, rfl⟩ _ ⟨g₂, rfl⟩; exact hcommim g₁ g₂)
        (by
          rintro _ ⟨g, rfl⟩
          exact ⟨1, ((χ g : kˣ) : k),
            by rw [map_one]; exact hCH g⟩)
    refine not_isIrreducible_of_invariant_submodule_field ρbar
      (Submodule.span k {v}) ?_ ?_ ?_
    · simpa [Submodule.span_singleton_eq_bot] using hv
    · intro htop
      have h1 : Module.finrank k (Submodule.span k {v}) = 1 :=
        finrank_span_singleton hv
      rw [htop] at h1
      rw [finrank_top] at h1
      rw [hfr] at h1
      omega
    · intro g x hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      obtain ⟨c, hc⟩ := heig (ρbar g) ⟨g, rfl⟩
      rw [map_smul, hc]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
        (Submodule.mem_span_singleton_self v))
  · -- the `ker χ`-fixed space is nonzero (Kolchin), proper, Galois-stable
    let ρH : χ.ker →* Module.End k W :=
      { toFun := fun hH => ρbar (hH : Field.absoluteGaloisGroup ℚ)
        map_one' := map_one ρbar
        map_mul' := fun x y => map_mul ρbar _ _ }
    have huni : ∀ hH : χ.ker, (ρH hH - 1) ^ 2 = 0 := by
      intro hH
      have hχ1 : ((χ (hH : Field.absoluteGaloisGroup ℚ) : kˣ) : k) = 1 := by
        rw [MonoidHom.mem_ker.mp hH.2]
        rfl
      have hthis := hCH (hH : Field.absoluteGaloisGroup ℚ)
      rw [hχ1, map_one] at hthis
      rw [pow_two]
      exact hthis
    obtain ⟨v₀, hv₀ne, hv₀fix⟩ :=
      BrauerNesbitt.exists_fixed_of_unipotent hdim ρH huni
    refine not_isIrreducible_of_invariant_submodule_field ρbar
      (⨅ hH : χ.ker,
        LinearMap.ker (ρbar (hH : Field.absoluteGaloisGroup ℚ) - 1))
      ?_ hWtop ?_
    · refine Submodule.ne_bot_iff _ |>.mpr ⟨v₀, ?_, hv₀ne⟩
      refine (Submodule.mem_iInf _).mpr fun hH => ?_
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
      exact hv₀fix hH
    · intro g v hv
      refine (Submodule.mem_iInf _).mpr fun hH => ?_
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
      have hconj : (g⁻¹ * (hH : Field.absoluteGaloisGroup ℚ) * g) ∈
          χ.ker := by
        rw [MonoidHom.mem_ker]
        simp only [map_mul, map_inv, MonoidHom.mem_ker.mp hH.2]
        rw [mul_one, inv_mul_cancel]
      have hfix := (Submodule.mem_iInf _).mp hv ⟨_, hconj⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero,
        Module.End.one_apply] at hfix
      have hrw : (hH : Field.absoluteGaloisGroup ℚ) * g =
          g * (g⁻¹ * (hH : Field.absoluteGaloisGroup ℚ) * g) := by group
      calc ρbar (hH : Field.absoluteGaloisGroup ℚ) (ρbar g v)
          = ρbar ((hH : Field.absoluteGaloisGroup ℚ) * g) v := by
            rw [map_mul]; rfl
      _ = ρbar g (ρbar (g⁻¹ * (hH : Field.absoluteGaloisGroup ℚ) * g) v) := by
            rw [hrw, map_mul]; rfl
      _ = ρbar g v := by rw [hfix]

/-- **Pillar γ — Chebotarev + Brauer–Nesbitt over a finite coefficient
field** (PROVEN 2026-07-24, along the docstring's generalization path,
over the three field-generic helpers above): a
continuous mod-`ℓ` representation over a finite coefficient field `k`
whose Frobenius characteristic polynomials away from a finite set of
places are those of `1 ⊕ χ̄_cyc` — the Eisenstein quadratic
`X² − (q+1)X + q` at `Frob_q` — is not irreducible.

This is the finite-coefficient-field form of the PROVEN
`GaloisRepresentation.not_isIrreducible_of_charFrob_eq` (`Lift.lean`,
stated over `ZMod ℓ`), whose proof consumes ONLY Family-free material,
all of it in `Chebotarev.lean` (already imported here):
`dense_conjClasses_globalFrob` (Frobenii are dense in conjugates, the
Chebotarev node), `continuous_cyclotomicCharacterModL`,
`cyclotomicCharacterModL_globalFrob`, `discreteTopology_moduleTopology`,
the quadratic coefficient lemmas, and the pointwise Brauer–Nesbitt node
`not_isIrreducible_of_charpoly_eq` (Kolchin/common-eigenvector route,
`BrauerNesbitt.lean`). The `Lift.lean` home of the twin — not its
ingredients — is what blocks a direct import (the `Family.lean` cycle);
the prover of this pillar should `import
Fermat.FLT.GaloisRepresentation.Chebotarev` (Family-free) and follow
the twin's proof.

Generalization path for the eventual proof: `char k = ℓ` (the kernel of
`ℤ_ℓ → k` is a nonzero prime, hence the maximal ideal, since `k` is
finite), so `ZMod ℓ` maps canonically into `k` (`ZMod.castHom`); replace
the `ZMod ℓ`-valued comparison functions of the twin's density argument
by their `k`-valued composites (continuity is free — `k` is discrete),
and rerun the Kolchin argument, whose two `BrauerNesbitt` inputs are
field-generic. Literature: Serre, *Abelian ℓ-adic representations and
elliptic curves*, I-2.3 (density determines the semisimplification);
Curtis–Reiner, *Methods of Representation Theory*, §30 (Brauer–Nesbitt).

SOUNDNESS AUDIT (both ways, 2026-07-24): (i) direct — a true,
NON-vacuous statement (the split representation `1 ⊕ χ̄_cyc` itself
satisfies the hypotheses); its `ZMod ℓ` instance is already proven
in-tree; (ii) no collapse clause is needed — the hypotheses are
satisfiable and the statement is unconditionally true. -/
theorem not_isIrreducible_of_charFrob_eisenstein
    {ℓ : ℕ} [Fact ℓ.Prime]
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    {ρbar : GaloisRep ℚ k W}
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
    (h : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S → q ≠ ℓ →
      ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
        X ^ 2 - C ((q : k) + 1) * X + C (q : k)) :
    ¬ ρbar.IsIrreducible := by
  classical
  -- `char k = ℓ`, so `ZMod ℓ` maps canonically into `k`
  haveI hchar : CharP k ℓ := charP_of_algebra_padicInt ℓ k
  set f : ZMod ℓ →+* k := ZMod.castHom (dvd_refl ℓ) k with hfdef
  -- an auxiliary prime avoiding the exceptional places pins the rank at 2:
  -- distinct primes give distinct places, so a finite set of places
  -- excludes only finitely many primes
  obtain ⟨q₀, hq₀p, hq₀S, hq₀ℓ⟩ :
      ∃ q₀ : ℕ, ∃ hq₀ : q₀.Prime,
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq₀ ∉ S) ∧ q₀ ≠ ℓ := by
    set T : Finset ℕ := (insert
        ((Fact.out : ℓ.Prime).toHeightOneSpectrumRingOfIntegersRat)
        S).attach.image
      (fun v => (exists_prime_toHeightOneSpectrum v.1).choose) with hT
    obtain ⟨q₀, hq₀ge, hq₀p⟩ := Nat.exists_infinite_primes (T.sup id + 1)
    have hq₀T : q₀ ∉ T := by
      intro hmem
      have hle := Finset.le_sup (f := id) hmem
      simp only [id] at hle
      omega
    have hq₀S' : Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq₀p ∉
        insert ((Fact.out : ℓ.Prime).toHeightOneSpectrumRingOfIntegersRat)
          S := by
      intro hmem
      apply hq₀T
      obtain ⟨hcp, hceq⟩ := (exists_prime_toHeightOneSpectrum
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq₀p)).choose_spec
      have hch : (exists_prime_toHeightOneSpectrum
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq₀p)).choose = q₀ :=
        toHeightOneSpectrumRingOfIntegersRat_injective hcp hq₀p hceq.symm
      rw [hT]
      exact Finset.mem_image.mpr ⟨⟨_, hmem⟩, Finset.mem_attach _ _, hch⟩
    refine ⟨q₀, hq₀p, fun hmem => hq₀S' (Finset.mem_insert_of_mem hmem), ?_⟩
    rintro rfl
    exact hq₀S' (Finset.mem_insert.mpr (Or.inl rfl))
  have hfr : Module.finrank k W = 2 := by
    have h0 := congrArg Polynomial.natDegree (h q₀ hq₀p hq₀S hq₀ℓ)
    rwa [GaloisRep.charFrob_eq_charpoly_globalFrob,
      LinearMap.charpoly_natDegree, natDegree_comparisonQuadratic] at h0
  have hrank : Module.rank k W = 2 := by
    rw [← Module.finrank_eq_rank k W, hfr]
    norm_num
  -- the endomorphism space is discrete in its module topology
  letI : TopologicalSpace (Module.End k W) := moduleTopology k (Module.End k W)
  haveI : DiscreteTopology (Module.End k W) :=
    discreteTopology_moduleTopology _ _
  have hρcont : Continuous fun g : Field.absoluteGaloisGroup ℚ => ρbar g :=
    ContinuousMonoidHom.continuous_toFun ρbar
  -- the agreement set is closed …
  have hχcont := continuous_cyclotomicCharacterModL ℓ
  have hc1 : Continuous fun g : Field.absoluteGaloisGroup ℚ =>
      (ρbar g).charpoly.coeff 1 := by
    exact Continuous.comp (continuous_of_discreteTopology
      (f := fun φ : Module.End k W => φ.charpoly.coeff 1)) hρcont
  have hc0 : Continuous fun g : Field.absoluteGaloisGroup ℚ =>
      (ρbar g).charpoly.coeff 0 := by
    exact Continuous.comp (continuous_of_discreteTopology
      (f := fun φ : Module.End k W => φ.charpoly.coeff 0)) hρcont
  have hb1 : Continuous fun g : Field.absoluteGaloisGroup ℚ =>
      -(f ((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ) + 1) := by
    exact Continuous.comp (g := fun x : ZMod ℓ => -(f x + 1))
      continuous_of_discreteTopology hχcont
  have hb0 : Continuous fun g : Field.absoluteGaloisGroup ℚ =>
      f ((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ) := by
    exact Continuous.comp (g := fun x : ZMod ℓ => f x)
      continuous_of_discreteTopology hχcont
  have hDclosed : IsClosed {g : Field.absoluteGaloisGroup ℚ |
      (ρbar g).charpoly.coeff 1 =
        -(f ((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ) + 1) ∧
      (ρbar g).charpoly.coeff 0 =
        f ((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ)} := by
    rw [Set.setOf_and]
    exact (isClosed_eq hc1 hb1).inter (isClosed_eq hc0 hb0)
  -- … and contains the dense set of Frobenius conjugates
  have hsub : {x : Field.absoluteGaloisGroup ℚ |
      ∃ v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
        v ∉ insert
          ((Fact.out : ℓ.Prime).toHeightOneSpectrumRingOfIntegersRat) S ∧
        ∃ g, x = g * globalFrob v * g⁻¹} ⊆
      {g : Field.absoluteGaloisGroup ℚ |
        (ρbar g).charpoly.coeff 1 =
          -(f ((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ) + 1) ∧
        (ρbar g).charpoly.coeff 0 =
          f ((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ)} := by
    rintro x ⟨v, hvS, g, rfl⟩
    obtain ⟨q, hq, rfl⟩ := exists_prime_toHeightOneSpectrum v
    have hqS : Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq ∉ S :=
      fun hmem => hvS (Finset.mem_insert_of_mem hmem)
    have hqℓ : q ≠ ℓ := by
      rintro rfl
      exact hvS (Finset.mem_insert.mpr (Or.inl rfl))
    -- conjugation invariance of the characteristic polynomial
    have hgu : (ρbar g).comp (ρbar g⁻¹) = LinearMap.id := by
      have hmul : ρbar g * ρbar g⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel, map_one]
      exact hmul
    have hgu' : (ρbar g⁻¹).comp (ρbar g) = LinearMap.id := by
      have hmul : ρbar g⁻¹ * ρbar g = 1 := by
        rw [← map_mul, inv_mul_cancel, map_one]
      exact hmul
    have hconj : (ρbar (g * globalFrob
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq) * g⁻¹)).charpoly =
        (ρbar (globalFrob
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))).charpoly := by
      have heq : ρbar (g * globalFrob
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq) * g⁻¹) =
          (LinearEquiv.ofLinear (ρbar g) (ρbar g⁻¹) hgu hgu').conj
            (ρbar (globalFrob
              (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))) := by
        ext x
        simp [map_mul, LinearEquiv.conj_apply, Module.End.mul_apply]
      rw [heq, LinearEquiv.charpoly_conj]
    -- conjugation invariance of the cyclotomic character
    have hχconj : cyclotomicCharacterModL ℓ (g * globalFrob
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq) * g⁻¹) =
        cyclotomicCharacterModL ℓ (globalFrob
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq)) := by
      rw [map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]
    have hval := h q hq hqS hqℓ
    rw [GaloisRep.charFrob_eq_charpoly_globalFrob] at hval
    have hfrob := cyclotomicCharacterModL_globalFrob (ℓ := ℓ) hq hqℓ
    constructor
    · show (ρbar _).charpoly.coeff 1 = _
      rw [hconj, hval, coeff_one_comparisonQuadratic, hχconj, hfrob,
        map_natCast]
    · show (ρbar _).charpoly.coeff 0 = _
      rw [hconj, hval, coeff_zero_comparisonQuadratic, hχconj, hfrob,
        map_natCast]
  -- density: the agreement set is everything
  have hDall : ∀ g : Field.absoluteGaloisGroup ℚ,
      (ρbar g).charpoly.coeff 1 =
        -(f ((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ) + 1) ∧
      (ρbar g).charpoly.coeff 0 =
        f ((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ) := by
    intro g
    have hdense := dense_conjClasses_globalFrob (K := ℚ)
      (insert ((Fact.out : ℓ.Prime).toHeightOneSpectrumRingOfIntegersRat) S)
    have hall : (Set.univ : Set (Field.absoluteGaloisGroup ℚ)) ⊆ _ :=
      hdense.closure_eq ▸ hDclosed.closure_subset_iff.mpr hsub
    exact hall (Set.mem_univ g)
  -- reconstruct the polynomial identity and conclude by the field-generic
  -- Brauer–Nesbitt helper, with `χ = χ̄_cyc` pushed into `k` through `f`
  apply not_isIrreducible_of_charpoly_eq_units hrank ρbar
    ((Units.map (f : ZMod ℓ →* k)).comp (cyclotomicCharacterModL ℓ))
  intro g
  obtain ⟨h1, h0⟩ := hDall g
  refine monic_quadratic_ext (LinearMap.charpoly_monic _)
    (monic_comparisonQuadratic _) ?_ (natDegree_comparisonQuadratic _) ?_ ?_
  · rw [LinearMap.charpoly_natDegree, hfr]
  · rw [h1, coeff_one_comparisonQuadratic]
    simp [Units.coe_map]
  · rw [h0, coeff_zero_comparisonQuadratic]
    simp [Units.coe_map]

/-- **The headline: no irreducible hardly ramified mod-`ℓ`
representation for `ℓ ≥ 5`** (PROVEN 2026-07-24 as an assembly over the
three pillars above and the PROVEN `3`-adic machinery) — the FLT
blueprint's ch. 4 reduction target ("there is no prime `ℓ ≥ 5` and
hardly-ramified irreducible 2-dimensional Galois representation"),
stated over a general finite coefficient field.

Assembly: lift `ρbar` (pillar α), spread the lift into a compatible
system with a hardly ramified `3`-adic member `τ` (pillar β); by the
PROVEN classification (`IsHardlyRamified.exists_frobenius_triangular`,
`Threeadic.lean`: in some basis the local Frobenius at `q ≥ 5` acts by
`[[q, *], [0, 1]]`), the member's Frobenius characteristic polynomials
are the Eisenstein quadratics `X² − (q+1)X + q`
(`LinearMap.charpoly_toMatrix` + `Matrix.charpoly_fin_two`); the
`E`-linkage transports them back — `ψ₃` is injective (a ring
homomorphism out of the field `E`), so the family polynomials `Pv` are
Eisenstein over `E`; `ιO` is injective, so the lift's characteristic
polynomials are Eisenstein over `O`; the reduction `π` carries them to
`ρbar` — whence `ρbar` is reducible by Chebotarev–Brauer–Nesbitt
(pillar γ), refuting irreducibility.

Relation to `Reducible.lean`'s B5 (`not_isIrreducible_of_isHardlyRamified`,
same statement over `ZMod ℓ`): B5 is the TREE's consumer node and its
route runs through `Family.lean`'s compatible-family machinery, which
consumes the modularity interface; this assembly is the Family-free
copy of the same argument, existing precisely so that the interface's
residual-modularity leaf can be discharged without a cycle. The two
routes share their proven 3-adic and Chebotarev ingredients and are
intended to share the lifting proof after the `Lift.lean` refactor
described on pillar α. -/
theorem not_isIrreducible_of_isHardlyRamified_of_five_le
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar) :
    ¬ ρbar.IsIrreducible := by
  classical
  intro hirr
  -- pillar α: the hardly ramified `ℓ`-adic lift
  obtain ⟨O, iO1, iO2, iO3, iO4, iO5, iO6, iO7, iO8, hZinj, ρ, hrank, hρ,
    π, hπsurj, hπ⟩ :=
    exists_hardlyRamified_lift_residual_of_five_le hℓodd hℓ5 hW hρbar hirr
  letI := iO1; letI := iO2; letI := iO3; letI := iO4; letI := iO5
  letI := iO6; letI := iO7; letI := iO8
  -- pillar β: the compatible system and its `3`-adic member
  obtain ⟨E, iE1, iE2, S₀, Pv, ψℓ, ιO, hιO, A, iA1, iA2, iA3, iA4, iA5,
    iA6, iA7, iA8, τ, hrankA, hτ, ψ₃, ιA, hιA, hcompat⟩ :=
    exists_threeadic_compatible_member_of_five_le hℓodd hℓ5 hZinj hrank hρ
      hW hρbar hirr π hπsurj hπ
  letI := iE1; letI := iE2
  letI := iA1; letI := iA2; letI := iA3; letI := iA4; letI := iA5
  letI := iA6; letI := iA7; letI := iA8
  -- pillar γ on the transported Eisenstein polynomials
  refine (not_isIrreducible_of_charFrob_eisenstein (ℓ := ℓ)
    (insert (Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)
      (insert (Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) S₀))
    ?_) hirr
  intro q hq hqS hqℓ
  -- unpack the exceptional-set membership
  have hq2 : q ≠ 2 := by
    rintro rfl
    exact hqS (Finset.mem_insert.mpr (Or.inl rfl))
  have hq3 : q ≠ 3 := by
    rintro rfl
    exact hqS (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
      (Or.inl rfl))))
  have hqS₀ : hq.toHeightOneSpectrumRingOfIntegersRat ∉ S₀ := fun hmem =>
    hqS (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem))
  have hq5 : 5 ≤ q := by
    rcases Nat.lt_or_ge q 5 with h5 | h5
    · interval_cases q
      · exact absurd hq (by decide)
      · exact absurd hq (by decide)
      · omega
      · omega
      · exact absurd hq (by decide)
    · exact h5
  obtain ⟨hcompℓ, hcomp₃⟩ := hcompat q hq hqS₀ hq2 hq3 hqℓ
  -- the `3`-adic member's Frobenius characteristic polynomial is the
  -- Eisenstein quadratic: the PROVEN classification gives a basis in
  -- which the local Frobenius acts by the triangular matrix
  -- `[[q, *], [0, 1]]`, whose characteristic polynomial is
  -- `X² − (q+1)X + q`
  obtain ⟨b, cUp, hb⟩ :=
    IsHardlyRamified.exists_frobenius_triangular (Fin 2 → A) hrankA hτ
      q hq hq5
  have hcpA : τ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
      X ^ 2 - C ((q : A) + 1) * X + C (q : A) := by
    have h1 : τ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
        (LinearMap.toMatrix b b
          (τ.toLocal hq.toHeightOneSpectrumRingOfIntegersRat
            (Field.AbsoluteGaloisGroup.adicArithFrob
              hq.toHeightOneSpectrumRingOfIntegersRat))).charpoly := by
      rw [LinearMap.charpoly_toMatrix]
      rfl
    rw [h1, hb, Matrix.charpoly_fin_two]
    norm_num [Matrix.trace_fin_two, Matrix.det_fin_two, add_comm]
  -- descend the Eisenstein shape to the number field `E` …
  have hPvq : Pv hq.toHeightOneSpectrumRingOfIntegersRat =
      X ^ 2 - C ((q : E) + 1) * X + C (q : E) := by
    apply Polynomial.map_injective ψ₃ ψ₃.injective
    rw [← hcomp₃, hcpA]
    simp [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_X, map_natCast, map_add, map_one]
  -- … transport it to the `ℓ`-adic lift's coefficients …
  have hcpO : ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
      X ^ 2 - C ((q : O) + 1) * X + C (q : O) := by
    apply Polynomial.map_injective ιO hιO
    rw [hcompℓ, hPvq]
    simp [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_X, map_natCast, map_add, map_one]
  -- … and reduce through `π` to `ρbar`
  have hred := hπ q hq hq2 hqℓ
  rw [hcpO] at hred
  rw [← hred]
  simp [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, map_natCast, map_add, map_one]

end GaloisRepresentation.Modularity
