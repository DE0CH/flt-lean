/-
NumberField/UnramifiedClassFieldBound.lean — own work for the Fermat
project (not vendored from the FLT project).
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.ExistsRamified
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.Frobenius

/-!
# The unramified upper bound of class field theory, at finite level

This file carries the **arithmetic** half of
`GaloisRepresentation.Modularity.finrank_le_card_classGroup_of_unramified_abelian`
(`Fermat/FLT/Modularity/Interface.lean`): a finite ABELIAN extension `L/K`
of number fields, unramified at every finite prime and at every infinite
place, has `[L : K] ≤ h_K`. Equivalently, `L` sits inside the Hilbert class
field of `K`.

It lives in its own module ON PURPOSE. `Modularity/Interface.lean`
elaborates for over an hour on one core, and everything here is pure
algebraic number theory that needs none of it — a prover attacking the open
leaf below iterates against THIS file in seconds. Do not move the material
back.

## Main results

* `NumberField.finrank_eq_one_of_unramified_of_finrank_rat_eq_one` — PROVEN.
  Minkowski at a degree-one base.
* `NumberField.relNormClassSubgroup` — the image of the ideal norm in the
  class group; `index` of this subgroup IS the classical `[I_K : P_K·N I_L]`.
* `NumberField.IsArithFrobOver` — `σ` is an arithmetic Frobenius at some prime
  of `𝓞 L` above a given prime of `𝓞 K`, over mathlib's `IsArithFrobAt`.
* `NumberField.exists_isArithFrobOver` — PROVEN. A Frobenius exists above every
  nonzero prime of `𝓞 K` (mathlib's `IsArithFrobAt.exists_of_isInvariant`).
* `NumberField.exists_surjective_classGroupHom_aut_of_unramified_abelian` —
  **PROVEN 2026-07-29**, by pure group theory, over the four leaves below.
  The Artin map at modulus `1`, packaged as "there is a surjection
  `Cl(𝓞 K) ↠ Gal(L/K)` killing the norm classes".
* `NumberField.exists_isPrime_classGroupMk0_eq` — OPEN. Every ideal class of a
  number field contains a prime ideal.
* `NumberField.prod_eq_one_of_forall_isArithFrobOver` — OPEN. **ARTIN
  RECIPROCITY at modulus `1`, in product form** — this is where the missing
  mathematics now is.
* `NumberField.exists_isArithFrobOver_of_aut` — OPEN. Chebotarev: every element
  of `Gal(L/K)` is a Frobenius at some prime.
* `NumberField.apply_classGroupMk0_relNorm_eq_one` — OPEN, and NOT class field
  theory: the classes of relative norms are killed by any Frobenius-compatible
  homomorphism. Pure ideal arithmetic (`Frob^f = 1`, `N 𝔔 = 𝔭^f`).
* `NumberField.finrank_le_index_relNormClassSubgroup` — PROVEN from the leaf
  above by pure group theory (index is antitone; `Subgroup.index_ker`).
  The second inequality at modulus `1`.
* `NumberField.finrank_le_card_classGroup_of_unramified_abelian_of_isUnramifiedAtInfinitePlaces`
  — PROVEN from the previous one by Lagrange.
-/

@[expose] public section

open scoped nonZeroDivisors

namespace NumberField

/-- **MINKOWSKI AT A DEGREE-ONE BASE: a finite extension of a number field
`K` with `[K : ℚ] = 1`, unramified at every finite prime, is trivial**
(PROVEN 2026-07-28).

`Module.finrank ℚ K = 1` says `K` is a model of `ℚ`, so `𝓞 K` is a model of
`ℤ` and the statement is exactly Minkowski's theorem: `ℚ` has no nontrivial
extension unramified at every finite place. Note there is **no abelian and
no Galois hypothesis** — Minkowski needs neither, which is why the `p = 2`
case of the consumer in `Modularity/Interface.lean` does not go through the
class-field-theoretic leaf below.

**Chain.** `Module.finrank ℚ K = 1` makes `(⊥ : Subalgebra ℚ K) = ⊤`
(`Submodule.eq_top_of_finrank_eq`), so `algebraMap ℚ K` is surjective; an
element of `𝓞 K` is therefore `algebraMap ℚ K q` for a `q` integral over
`ℤ`, and `ℤ` is integrally closed in `ℚ`, so `algebraMap ℤ (𝓞 K)` is
surjective too. A surjective algebra map is formally unramified
(`Algebra.FormallyUnramified.of_surjective`), so
`Algebra.FormallyUnramified.comp` upgrades the hypothesis
`Algebra.IsUnramifiedAt (𝓞 K) Q` to `Algebra.IsUnramifiedAt ℤ Q` at every
nonzero prime `Q` of `𝓞 L` — the `Q ≠ ⊥` guard is discharged from
`Ideal.bot_lt_of_maximal` because `𝓞 L` is not a field. Then mathlib's
`NumberField.exists_not_isUnramifiedAt_int`, which IS the Minkowski
discriminant bound, forces `Module.finrank ℚ L = 1`, and
`Module.finrank_mul_finrank` turns that into `Module.finrank K L = 1`.

**Why the archimedean side costs nothing here.** `L/ℚ` is allowed to ramify
at the real place — ramification at infinity does not enter the
discriminant, so Minkowski's bound is insensitive to it. That is precisely
why the `p = 2` case of the consumer CANNOT be routed through
`finrank_le_card_classGroup_of_unramified_abelian_of_isUnramifiedAtInfinitePlaces`
below: supplying that theorem's archimedean hypothesis over `ℚ` would
already require knowing `L = ℚ`. -/
theorem finrank_eq_one_of_unramified_of_finrank_rat_eq_one
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (hK : Module.finrank ℚ K = 1)
    (hunr : ∀ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 K) Q) :
    Module.finrank K L = 1 := by
  classical
  -- Step 1: `ℚ → K` is surjective.
  have hbot : (⊥ : Subalgebra ℚ K) = ⊤ :=
    Algebra.toSubmodule_eq_top.1 (Submodule.eq_top_of_finrank_eq
      ((Subalgebra.finrank_toSubmodule (⊥ : Subalgebra ℚ K)).trans
        (by rw [Subalgebra.finrank_bot, hK])))
  have hsurjQ : Function.Surjective (algebraMap ℚ K) := by
    intro x
    have hx : x ∈ (⊤ : Subalgebra ℚ K) := trivial
    rw [← hbot, Algebra.mem_bot] at hx
    obtain ⟨q, hq⟩ := hx
    exact ⟨q, hq⟩
  -- Step 2: hence `ℤ → 𝓞 K` is surjective.
  have hinjK : Function.Injective (algebraMap (𝓞 K) K) :=
    FaithfulSMul.algebraMap_injective (𝓞 K) K
  have hsurj : Function.Surjective (algebraMap ℤ (𝓞 K)) := by
    intro x
    obtain ⟨q, hq⟩ := hsurjQ (algebraMap (𝓞 K) K x)
    have hxint : IsIntegral ℤ (algebraMap (𝓞 K) K x) :=
      (IsIntegralClosure.isIntegral ℤ K x).map (IsScalarTower.toAlgHom ℤ (𝓞 K) K)
    rw [← hq] at hxint
    have hqint : IsIntegral ℤ q :=
      (isIntegral_algebraMap_iff (R := ℤ) (algebraMap ℚ K).injective).mp hxint
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hqint
    refine ⟨n, hinjK ?_⟩
    rw [← IsScalarTower.algebraMap_apply ℤ (𝓞 K) K, ← hq, ← hn,
      ← IsScalarTower.algebraMap_apply ℤ ℚ K]
  -- Step 3: `𝓞 K` is formally unramified over `ℤ`, so `hunr` transports to `ℤ`.
  haveI : Algebra.FormallyUnramified ℤ (𝓞 K) :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId ℤ (𝓞 K)) hsurj
  have key : ∀ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt ℤ Q := by
    intro Q hQ hQ0
    haveI := hQ
    haveI := hunr Q hQ hQ0
    exact Algebra.FormallyUnramified.comp ℤ (𝓞 K) (Localization.AtPrime Q)
  -- Step 4: Minkowski.
  have hrat : Module.finrank ℚ L = 1 := by
    by_contra hne
    obtain ⟨P, hPmax, hPram⟩ :=
      NumberField.exists_not_isUnramifiedAt_int (K := L) (𝒪 := 𝓞 L) hne
    haveI := hPmax
    exact hPram (key P hPmax.isPrime
      (Ideal.bot_lt_of_maximal P (NumberField.RingOfIntegers.not_isField _)).ne')
  -- Step 5: multiplicativity of degrees.
  have hmul : Module.finrank ℚ K * Module.finrank K L = Module.finrank ℚ L :=
    Module.finrank_mul_finrank ℚ K L
  rw [hK, one_mul, hrat] at hmul
  exact hmul

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L]

/-- **The image of the ideal norm in the class group**: the subgroup of
`Cl(𝓞 K)` generated by the classes of the relative norms `N_{L/K} I` of the
nonzero ideals `I` of `𝓞 L`.

Its `Subgroup.index` is the classical norm index `[I_K : P_K · N_{L/K} I_L]`
of class field theory: `Cl(𝓞 K) = I_K/P_K`, this subgroup is
`(P_K · N_{L/K} I_L)/P_K`, and the index of the quotient is the index in
`I_K`. Restricting the generating set to INTEGRAL ideals loses nothing —
every fractional ideal is a quotient of two integral ones, so its norm class
already lies in the subgroup they generate.

`Ideal.relNorm` is available here in full generality: it is built from
`Algebra.intNorm`, which needs only `IsIntegrallyClosed` and
`Module.Finite`, **not** `Module.Free`. That matters, because `𝓞 L` is in
general NOT free over `𝓞 K` (it is free exactly when its Steinitz class is
trivial), so a norm built from `Algebra.norm` would not have been usable
here. -/
noncomputable def relNormClassSubgroup : Subgroup (ClassGroup (𝓞 K)) :=
  Subgroup.closure {c : ClassGroup (𝓞 K) | ∃ (I : Ideal (𝓞 L)) (hI : I ≠ ⊥),
    c = ClassGroup.mk0 ⟨Ideal.relNorm (𝓞 K) I,
      mem_nonZeroDivisors_of_ne_zero (by
        simpa using (Ideal.relNorm_eq_bot_iff (R := 𝓞 K) (I := I)).not.mpr hI)⟩}

/-- **The Galois group of `L/K` commutes with the `𝓞 K`-action on `𝓞 L`.**

This is the one instance mathlib does not already supply, and without it
`IsArithFrobAt (𝓞 K) σ Q` does not even elaborate for `σ : L ≃ₐ[K] L` and
`Q : Ideal (𝓞 L)`. Mathlib HAS `SMulCommClass G R (integralClosure R K)`
(`Mathlib/RingTheory/IntegralClosure/Algebra/Basic.lean`), but `𝓞 L` is
`integralClosure ℤ L`, not `integralClosure (𝓞 K) L`, so that instance does not
fire. The content is just that a `K`-algebra equivalence fixes the image of
`𝓞 K`. -/
instance : SMulCommClass (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) where
  smul_comm g a b := by
    apply NumberField.RingOfIntegers.ext
    show g ((a • b : 𝓞 L) : L) = ((a • (g • b) : 𝓞 L) : L)
    simp only [Algebra.smul_def, map_mul]
    congr 1
    rw [← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
      IsScalarTower.algebraMap_apply (𝓞 K) K L, AlgEquiv.commutes]

/-- **`σ` is an arithmetic Frobenius above the prime `P` of `𝓞 K`**: there is a
prime `Q` of `𝓞 L` lying over `P` at which `σ` is a Frobenius in mathlib's
sense (`IsArithFrobAt`, i.e. `σ x ≡ x ^ #(𝓞 K / P) (mod Q)` for all `x`).

`P` ranges over `(Ideal (𝓞 K))⁰` rather than over `Ideal (𝓞 K)` so that
`ClassGroup.mk0 P` is available without a side condition; membership in the
nonzero divisors of the ideal monoid of a Dedekind domain is exactly `P ≠ ⊥`.

Note that the prime `Q` is EXISTENTIAL, not a parameter. That is deliberate and
costs nothing in the intended application: `Gal(L/K)` acts transitively on the
primes above `P`, and the Frobenius elements at the various `Q | P` form one
conjugacy class — a single element when the extension is abelian. -/
def IsArithFrobOver (P : (Ideal (𝓞 K))⁰) (σ : L ≃ₐ[K] L) : Prop :=
  ∃ Q : Ideal (𝓞 L), Q.IsPrime ∧ Q.under (𝓞 K) = (P : Ideal (𝓞 K)) ∧
    IsArithFrobAt (𝓞 K) σ Q

/-- **EVERY IDEAL CLASS OF A NUMBER FIELD CONTAINS A PRIME IDEAL** (SORRY LEAF,
cut 2026-07-29 out of `exists_surjective_classGroupHom_aut_of_unramified_abelian`
below).

This is the classical statement that each class of `Cl(𝓞 K)` contains
infinitely many prime ideals; only one is asked for here. Note it mentions `L`
nowhere: it is a statement about the single number field `K`, and closing it is
useful far beyond this file.

**Route.** Chebotarev / Dirichlet density applied to the Hilbert class field
`H/K`: a prime `𝔭` of `K` whose Frobenius in `Gal(H/K) ≅ Cl(𝓞 K)` is the
prescribed class lies in that class. Equivalently, and without class field
theory on the nose, the Hecke `L`-function of the ideal-class group has a
nonvanishing statement at `s = 1` giving positive density in each class
(Hecke; Neukirch VII (13.2); Lang *ANT* ch. VIII). No purely algebraic proof is
known, and none is expected — the statement fails for general Dedekind domains,
whose class groups can be arbitrary (Claborn) with prime ideals confined to a
subgroup. That last sentence is a POINTER, not a verified counterexample; the
`NumberField K` hypothesis has not been refuted here by an explicit witness.

**Not vacuous, and true in the degenerate case.** At `c = 1` the statement says
`𝓞 K` has a principal nonzero prime, which is true (and, for `K = ℚ`, witnessed
by `(2)`). At `K = ℚ` the class group is trivial and the statement is exactly
that. For `K = ℚ(√-5)`, `Cl = ℤ/2`, the nontrivial class is realised by the
prime `(2, 1 + √-5)`.

**The check that would refute it**: a number field `K` and a class of
`Cl(𝓞 K)` containing no prime ideal. -/
theorem exists_isPrime_classGroupMk0_eq (c : ClassGroup (𝓞 K)) :
    ∃ P : (Ideal (𝓞 K))⁰, (P : Ideal (𝓞 K)).IsPrime ∧ ClassGroup.mk0 P = c :=
  sorry

/-- **A FROBENIUS EXISTS ABOVE EVERY NONZERO PRIME OF `𝓞 K`** (PROVEN
2026-07-29, entirely from mathlib).

There is nothing arithmetic to do here: `Ideal.nonempty_primesOver` supplies a
prime `Q` of `𝓞 L` over `P` (going up, `𝓞 L` being integral over `𝓞 K`),
`Ring.HasFiniteQuotients.finiteQuotient` makes its residue ring finite, and
`IsArithFrobAt.exists_of_isInvariant` produces the Frobenius. The invariance
hypothesis `Algebra.IsInvariant (𝓞 K) (𝓞 L) Gal(L/K)` is mathlib's
`IsGaloisGroup.isInvariant`.

Recorded as a separate declaration because the leaves above and below all need
it and because it is the boundary between "mathlib has this" and "this
development must build it": Frobenius EXISTENCE is free, Frobenius RECIPROCITY
is not. -/
theorem exists_isArithFrobOver [IsGalois K L] (P : (Ideal (𝓞 K))⁰)
    (hP : (P : Ideal (𝓞 K)).IsPrime) : ∃ σ : L ≃ₐ[K] L, IsArithFrobOver K L P σ := by
  haveI := hP
  haveI : Algebra.IsInvariant (𝓞 K) (𝓞 L) (L ≃ₐ[K] L) := IsGaloisGroup.isInvariant
  haveI : Algebra.IsIntegral (𝓞 K) (𝓞 L) := Algebra.IsInvariant.isIntegral (G := L ≃ₐ[K] L) ..
  obtain ⟨⟨Q, hQ, hQlies⟩⟩ :
      Nonempty (Ideal.primesOver (P : Ideal (𝓞 K)) (𝓞 L)) := inferInstance
  haveI := hQ
  have hQunder : Q.under (𝓞 K) = (P : Ideal (𝓞 K)) := hQlies.over.symm
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    refine nonZeroDivisors.coe_ne_zero P ?_
    rw [← hQunder]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))
  haveI : Finite (𝓞 L ⧸ Q) := Ring.HasFiniteQuotients.finiteQuotient hQ0
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 K) (L ≃ₐ[K] L) Q
  exact ⟨σ, Q, hQ, hQunder, hσ⟩

/-- **ARTIN RECIPROCITY AT MODULUS `1`, IN PRODUCT FORM: if a finite list of
nonzero primes of `𝓞 K` has trivial product in `Cl(𝓞 K)` — i.e. their product
is a principal ideal — then the product of their Frobenius elements in
`Gal(L/K)` is trivial** (SORRY LEAF, cut 2026-07-29 out of
`exists_surjective_classGroupHom_aut_of_unramified_abelian` below; **THIS IS
WHERE THE MISSING MATHEMATICS IS**).

**Why product form rather than a map on ideals.** Reciprocity is classically
stated as "the Artin map `I_K → Gal(L/K)` kills `P_K`", which requires first
CONSTRUCTING that map — extending `𝔭 ↦ Frob_𝔭` multiplicatively over the free
monoid of ideals. The product form says the same thing without any
construction: it is exactly what a prover of reciprocity ends up with, and the
consumer below turns it into a homomorphism out of `Cl(𝓞 K)` by pure group
theory. The same cut is used, and is PROVEN over, in the sibling
`exists_artinIdealMap_of_unramifiedAbelianSubgroup` in
`Fermat/FLT/Modularity/Interface.lean`, whose leaf
`prod_frobConj_mem_of_mk0_prod_frobIdeal_eq_one` is this statement transported
into the `Γℚ`/character setting.

**Route.** Neukirch VI (6.7)–(6.9); Childress ch. 4–5; Lang *ANT* ch. X;
Cassels–Fröhlich ch. VII. Modulus `1` is admissible exactly because of
`IsUnramifiedAtInfinitePlaces`.

**⚠ ALL THREE HYPOTHESES ARE LOAD-BEARING.**

* `hunr` — **witness, checked 2026-07-29**: `K = ℚ`, `L = ℚ(√5)`, which is
  abelian of degree `2` and unramified at the infinite place (disc `5 > 0`, so
  both archimedean places of `L` are real) but RAMIFIED at `5`. Take the
  one-element list `[((2), Frob₂)]`. Since `5 ≡ 5 (mod 8)`, `x² - x - 1` is
  irreducible mod `2`, so `2` is INERT and `Frob₂` is the nontrivial
  automorphism. `Cl(ℤ)` is trivial, so the class hypothesis holds vacuously,
  while the conclusion reads `Frob₂ = 1`. False.
* `IsUnramifiedAtInfinitePlaces` — **witness**: `K = ℚ(√3)`, `L` its NARROW
  Hilbert class field. `h_K = 1` but `h⁺_K = 2` (PARI/GP, recorded below), so
  `L/K` is abelian of degree `2`, unramified at every finite place, and
  ramified at both real places. Again every class of `Cl(𝓞 K)` is trivial, so
  every list satisfies the hypothesis. Since `L ≠ K`, not every prime of `K`
  splits completely in `L` (Chebotarev), so some prime `𝔭` is inert and the
  one-element list `[(𝔭, Frob_𝔭)]` refutes the conclusion.
* `habel` is load-bearing **FORMALLY**, and the argument is worth recording
  because it is not the usual "the class group is abelian" one. Swapping the
  first two entries of a three-element list leaves the class hypothesis
  unchanged (`Cl(𝓞 K)` is commutative) but reverses the order of the first two
  Frobenii, so the statement forces `σ₁σ₂ = σ₂σ₁` for ANY two Frobenius
  elements; by `exists_isArithFrobOver_of_aut` below (Chebotarev) those
  generate `Gal(L/K)`. So this leaf IMPLIES `habel`, and dropping `habel` makes
  it false for every everywhere-unramified extension with non-abelian Galois
  group — such exist, being what a Golod–Shafarevich class field tower of
  length `≥ 2` produces.

**Not vacuous.** The one-element list at a PRINCIPAL prime says `Frob_𝔭 = 1`
for every principal `𝔭`, which is the whole substance of reciprocity; the empty
list is the trivial `1 = 1`.

**The check that would refute it**: an everywhere-unramified abelian `L/K` and
nonzero primes `𝔭₁, …, 𝔭ₙ` of `𝓞 K` with `𝔭₁ ⋯ 𝔭ₙ` principal but
`Frob_{𝔭₁} ⋯ Frob_{𝔭ₙ} ≠ 1`. -/
theorem prod_eq_one_of_forall_isArithFrobOver [IsGalois K L]
    [IsUnramifiedAtInfinitePlaces K L]
    (habel : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (hunr : ∀ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 K) Q)
    (l : List ((Ideal (𝓞 K))⁰ × (L ≃ₐ[K] L)))
    (hl : ∀ x ∈ l, (x.1 : Ideal (𝓞 K)).IsPrime ∧ IsArithFrobOver K L x.1 x.2)
    (hcl : (l.map fun x => ClassGroup.mk0 x.1).prod = 1) :
    (l.map Prod.snd).prod = 1 :=
  sorry

/-- **CHEBOTAREV, IN THE FORM USED HERE: every element of `Gal(L/K)` is an
arithmetic Frobenius above some nonzero prime of `𝓞 K`** (SORRY LEAF, cut
2026-07-29 out of `exists_surjective_classGroupHom_aut_of_unramified_abelian`
below).

**This is TRUE for an arbitrary finite Galois extension of number fields** —
no abelian and no unramifiedness hypothesis is taken, and none is needed: the
Chebotarev density theorem produces, for each `σ`, infinitely many primes
UNRAMIFIED in `L/K` whose Frobenius class contains `σ`, and for an unramified
prime the Frobenius at a prime above it is genuinely an `IsArithFrobAt`
witness. Stating it in this generality is deliberate: the leaf is then a clean,
quotable theorem rather than a fragment of this file's argument.

**Route.** Chebotarev density (Neukirch VII (13.4); Lang *ANT* ch. VIII);
for the weaker "the Frobenius elements generate `Gal(L/K)`" that this leaf is
used for, the analytic input is unavoidable — the algebraic statement "no
proper subfield in which every prime splits completely" IS the first
inequality.

**Not vacuous, and the degenerate case is true.** At `σ = 1` the statement asks
for a prime of `K` splitting completely in `L`, which exists. At `L = K` every
prime works and `Gal(L/K)` is trivial.

**The check that would refute it**: a finite Galois extension of number fields
and a `σ ∈ Gal(L/K)` which is not a Frobenius at any prime — equivalently, by
Chebotarev, nothing. -/
theorem exists_isArithFrobOver_of_aut [IsGalois K L] (σ : L ≃ₐ[K] L) :
    ∃ P : (Ideal (𝓞 K))⁰, (P : Ideal (𝓞 K)).IsPrime ∧ IsArithFrobOver K L P σ :=
  sorry

/-- **THE NORM CLASSES ARE KILLED BY ANY FROBENIUS-COMPATIBLE HOMOMORPHISM**
(SORRY LEAF, cut 2026-07-29 out of
`exists_surjective_classGroupHom_aut_of_unramified_abelian` below).

**THIS LEAF IS NOT CLASS FIELD THEORY.** It is the "two-line computation" that
the parent's docstring promised: given ANY homomorphism `φ : Cl(𝓞 K) → Gal(L/K)`
which sends the class of each nonzero prime `𝔭` to a Frobenius above `𝔭`, the
class of `N_{L/K} I` is in its kernel. Whoever closes it needs no reciprocity,
no Chebotarev and no ideles — only ideal arithmetic:

1. `Ideal.relNorm` is multiplicative and `I` factors into primes in the
   Dedekind domain `𝓞 L`, so it suffices to treat `I = 𝔔` prime.
2. `N_{L/K} 𝔔 = 𝔭 ^ f`, where `𝔭 = 𝔔 ∩ 𝓞 K` and `f = Ideal.inertiaDeg 𝔭 𝔔`.
3. `φ (mk0 𝔭)` is a Frobenius at some prime above `𝔭`, and at an UNRAMIFIED
   prime the decomposition group is cyclic of order `f` generated by the
   Frobenius, so `φ (mk0 𝔭) ^ f = 1`.
4. Hence `φ (mk0 (N 𝔔)) = φ (mk0 𝔭) ^ f = 1`.

**`hunr` is used at step 3 and the ARGUMENT provably fails without it**: at a
ramified prime a Frobenius at `Q` is only determined modulo the inertia group,
`IsArithFrobAt` is satisfied by `Frob · i` for every `i` in inertia, and
`(Frob · i) ^ f` lands in inertia rather than at `1`. That is a failure of the
PROOF; no counterexample to the STATEMENT with `hunr` deleted has been
constructed here, and any witness would need `Cl(𝓞 K)` nontrivial (otherwise
`φ` is the trivial map and the conclusion is free) — the obvious candidate
`K = ℚ`, `L = ℚ(√5)` does NOT refute it for exactly that reason. Treat the
necessity of `hunr` as unaudited.

**`hφ` is what makes the leaf non-vacuous, and it is not free**: the trivial
homomorphism satisfies the conclusion but not `hφ` unless every Frobenius is
trivial. Conversely `hφ` alone does not force `φ` to be the Artin map — it
constrains `φ` only on classes of primes — but by
`exists_isPrime_classGroupMk0_eq` every class IS the class of a prime, so `hφ`
in fact pins `φ` completely. Nothing weaker is needed here.

**The check that would refute it**: an everywhere-unramified `L/K`, a
homomorphism `φ` satisfying `hφ`, and a nonzero `I ⊆ 𝓞 L` with
`φ [N_{L/K} I] ≠ 1`. -/
theorem apply_classGroupMk0_relNorm_eq_one [IsGalois K L]
    (hunr : ∀ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 K) Q)
    (φ : ClassGroup (𝓞 K) →* (L ≃ₐ[K] L))
    (hφ : ∀ P : (Ideal (𝓞 K))⁰, (P : Ideal (𝓞 K)).IsPrime →
      IsArithFrobOver K L P (φ (ClassGroup.mk0 P)))
    (I : Ideal (𝓞 L)) (hI : I ≠ ⊥) (J : (Ideal (𝓞 K))⁰)
    (hJ : (J : Ideal (𝓞 K)) = Ideal.relNorm (𝓞 K) I) :
    φ (ClassGroup.mk0 J) = 1 :=
  sorry

/-- **THE ARTIN MAP AT MODULUS `1`, AS AN EXISTENTIAL: for `L/K` finite
abelian, unramified at every finite prime and at every infinite place, there
is a SURJECTIVE homomorphism `Cl(𝓞 K) →* Gal(L/K)` that kills the class of
every relative norm `N_{L/K} I`** (cut 2026-07-28 out of
`finrank_le_index_relNormClassSubgroup` below; **DECOMPOSED AND PROVEN
2026-07-29** — the proof below is `choose`, three applications of
`prod_eq_one_of_forall_isArithFrobOver` to lists of length `2` and `3`, and
`MonoidHom.mk'`, and contains no arithmetic whatsoever).

**THE CUT, 2026-07-29.** What was one monolithic leaf is now four, and only
one of them is class field theory:

* `exists_isPrime_classGroupMk0_eq` — every ideal class contains a prime
  ideal. A statement about `K` alone; Chebotarev/Hecke.
* `prod_eq_one_of_forall_isArithFrobOver` — **RECIPROCITY**, in product form:
  a list of primes with principal product has trivial product of Frobenii.
  **This is where the missing mathematics is.**
* `exists_isArithFrobOver_of_aut` — **CHEBOTAREV**: every element of
  `Gal(L/K)` is a Frobenius somewhere. Needs neither `habel` nor `hunr`.
* `apply_classGroupMk0_relNorm_eq_one` — the norm clause. NOT class field
  theory: ideal factorisation, `N 𝔔 = 𝔭^f`, and `Frob^f = 1`.

Frobenius EXISTENCE is free from mathlib and is proven above as
`exists_isArithFrobOver`; the cut is drawn exactly at the boundary where
mathlib stops.

**Why the cut is safe — the assembly, in one paragraph.**
`exists_isPrime_classGroupMk0_eq` and `exists_isArithFrobOver` give, for each
class `c`, a prime `P c` in that class and a Frobenius `A c` above it. Applying
reciprocity to `[(P c, A c), (P d, A d), (P (cd)⁻¹, A (cd)⁻¹)]` and to
`[(P (cd), A (cd)), (P (cd)⁻¹, A (cd)⁻¹)]` — both lists have trivial class
product — and cancelling gives `A (cd) = A c · A d`, so `A` is a homomorphism.
The same trick on `[(P', τ), (P (mk0 P')⁻¹, A (mk0 P')⁻¹)]` shows that ANY
Frobenius `τ` above ANY prime `P'` equals `A (mk0 P')`: that single lemma
yields surjectivity (from Chebotarev) and the Frobenius-compatibility
hypothesis `hφ` of the norm leaf. No padding is needed — unlike the sibling
cut in `Modularity/Interface.lean`, where the target group is a quotient
`ker χ / N` and Lagrange has to be run by hand.

Classically this is the Artin map of the everywhere-unramified abelian
extension `L/K`: `𝔭 ↦ Frob_𝔭` on `I_K`, which descends to `Cl(𝓞 K)` because
principal ideals lie in its kernel (Artin RECIPROCITY), is surjective by
Chebotarev, and kills `N_{L/K} I_L` because `Frob_{N𝔓} = Frob_𝔭^{f(𝔓/𝔭)} = 1`.
Only the first of those three is deep; the third is a two-line computation
once the map exists, and is the reason the norm clause is cheap to add here.

**Why the conclusion is an `∃` and why that is safely PINNED.** The consumer
below uses EXACTLY the two stated clauses and nothing else, and the
inequality it deduces holds for ANY witness: `Nat.card (Gal(L/K))` is the
index of `ker φ` for any surjection `φ`, and `ker φ` contains
`relNormClassSubgroup K L` as soon as the second clause holds. So an
adversary who post-composes an automorphism of `Gal(L/K)`, or replaces `φ`
by a different surjection with a larger kernel, still yields a true
consumer — there is nothing to pin. Note that the true Artin map has kernel
EXACTLY `relNormClassSubgroup K L`; only `≤` is asked for, because only `≤`
is used, and asking for equality would make the leaf strictly harder for no
gain.

**Route.** Neukirch VI (6.9) and the sections preceding it; Childress
ch. 4–5; Lang *ANT* ch. X; Cassels–Fröhlich ch. VII.

**Relation to the sibling leaf — read this before starting.** This IS the
reciprocity route, and the docstring that this leaf was cut out of said, in
so many words, that the reciprocity route is "NOT independent of the sibling
leaf `exists_artinIdealMap_of_unramifiedAbelianSubgroup` in
`Modularity/Interface.lean`". That remains true and the choice was made
anyway, deliberately, on 2026-07-28: the allegedly independent route is the
cohomological one, and it needs the idele class group and the Tate
cohomology of a class formation, of which the pin has NEITHER (see the
survey below). Between "no decomposition" and "a decomposition that shares
mathematical content with a sibling", the second is worth more — and this
statement is strictly smaller than the sibling's (no `χ`, no `CF`, no
`frobIdeal`, no cyclotomic vocabulary) and lives in a module that elaborates
in ten seconds rather than the sibling's tens of minutes. Whoever proves one
should look hard at the other.

**An idele-free route that reaches the ULTIMATE consumer, recorded here
because it is not obvious and was found while cutting this leaf.** The
consumer of this whole file,
`finrank_le_card_classGroup_of_unramified_abelian` in
`Modularity/Interface.lean`, needs only `[L : K] ≤ h_K` — it never uses the
norm index. For `L/K` CYCLIC that inequality drops straight out of
Chevalley's ambiguous class number formula
`|Cl_L^{Gal(L/K)}| = h_K · ∏_v e_v / ([L:K] · [E_K : E_K ∩ N L^×])`:
everywhere-unramified makes every `e_v = 1`, so
`h_K = [L:K] · |Cl_L^{Gal}| · [E_K : E_K ∩ N L^×] ≥ [L:K]`. That derivation
uses only ideals, units and Hilbert 90 — all of which the pin HAS
(`Mathlib/RepresentationTheory/Homological/GroupCohomology/Hilbert90.lean`) —
and no ideles at all. **The gap is cyclic → abelian**: the naive tower
induction FAILS, because `[Cl_K : N_{M/K} Cl_M] · [Cl_M : N_{L/M} Cl_L]` only
bounds `[Cl_K : N_{L/K} Cl_L]` from ABOVE (the image index
`[N_{M/K} Cl_M : N_{M/K} N_{L/M} Cl_L]` can be smaller than
`[Cl_M : N_{L/M} Cl_L]`), and multiplicativity of the norm index in towers is
itself a theorem of class field theory. Anyone who closes that gap gets the
whole file without reciprocity.

*Assessed 2026-07-29, and the gap is worse than "not obvious".* Two natural
repairs were tried and both fail, for the same structural reason.
(i) *Tower induction on the degree.* With `K ⊆ M ⊆ L`, `M/K` cyclic of prime
degree `p` and `L/M` abelian everywhere unramified, induction gives
`[L : M] ≤ h_M` and `[M : K] = p ≤ h_K`, but `h_M` is unrelated to `h_K` — the
naive product `p · h_M ≤ h_K` is simply false, and relating `h_M` to `h_K`
along an unramified extension is again reciprocity.
(ii) *Characters.* Every cyclic quotient of `G = Gal(L/K)` cuts out a cyclic
everywhere-unramified subextension, so the cyclic case gives `m ∣ h_K` for the
order `m` of every character of `G`. That bounds the EXPONENT of `G`, never its
ORDER: `G = (ℤ/2)^10` over a `K` with `h_K = 2` is consistent with every
character statement, and excluding it is precisely genus theory, i.e. class
field theory again. What the cyclic case does deliver in Chevalley's form is
`|Cl_M^{Gal}| = |(Cl_M)_{Gal}|` (true for any finite module over a cyclic
group) — but identifying the `p`-quotients of `(Cl_M)_{Gal}` with unramified
extensions is the correspondence itself. So route (2) closes the CYCLIC case
and nothing more; the honest cheap deliverable it offers is a cyclic-only
sibling of this leaf, not a replacement for it.

**⚠ ALL THREE HYPOTHESES ARE LOAD-BEARING, and for this statement `habel` is
load-bearing FORMALLY.** `Cl(𝓞 K)` is abelian, so it cannot surject onto a
non-abelian group at all; without `habel` the leaf is false for every
everywhere-unramified extension with non-abelian Galois group (such exist —
they are what a Golod–Shafarevich class field tower of length `≥ 2`
produces). For the two ramification hypotheses see the consumer below;
both counterexamples recorded there refute THIS statement as well, since in
each of them `Cl(𝓞 K)` is trivial and `Gal(L/K)` has order `2`.

**The check that would refute it**: a finite abelian extension of a number
field `K`, unramified at every finite prime and at every infinite place, for
which no surjection `Cl(𝓞 K) ↠ Gal(L/K)` kills the norm classes — for
instance any such `L/K` with `[L : K] > h_K`. -/
theorem exists_surjective_classGroupHom_aut_of_unramified_abelian [IsGalois K L]
    [IsUnramifiedAtInfinitePlaces K L]
    (habel : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (hunr : ∀ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 K) Q) :
    ∃ φ : ClassGroup (𝓞 K) →* (L ≃ₐ[K] L), Function.Surjective φ ∧
      ∀ (I : Ideal (𝓞 L)) (J : (Ideal (𝓞 K))⁰), I ≠ ⊥ →
        (J : Ideal (𝓞 K)) = Ideal.relNorm (𝓞 K) I → φ (ClassGroup.mk0 J) = 1 := by
  classical
  -- a prime in every ideal class, and a Frobenius above it
  choose P hPprime hPclass using exists_isPrime_classGroupMk0_eq K
  choose A hA using fun c : ClassGroup (𝓞 K) => exists_isArithFrobOver K L (P c) (hPprime c)
  have hpack : ∀ c : ClassGroup (𝓞 K),
      ((P c : Ideal (𝓞 K)).IsPrime ∧ IsArithFrobOver K L (P c) (A c)) :=
    fun c => ⟨hPprime c, hA c⟩
  -- `A` is multiplicative, from reciprocity applied to two short lists
  have hmul : ∀ c d : ClassGroup (𝓞 K), A (c * d) = A c * A d := by
    intro c d
    have hl3 : ∀ x ∈ [(P c, A c), (P d, A d), (P (c * d)⁻¹, A (c * d)⁻¹)],
        (x.1 : Ideal (𝓞 K)).IsPrime ∧ IsArithFrobOver K L x.1 x.2 := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> exact hpack _
    have hc3 : (([(P c, A c), (P d, A d), (P (c * d)⁻¹, A (c * d)⁻¹)]).map
        fun x => ClassGroup.mk0 x.1).prod = 1 := by
      simp [hPclass]
    have h3 := prod_eq_one_of_forall_isArithFrobOver K L habel hunr _ hl3 hc3
    have hl2 : ∀ x ∈ [(P (c * d), A (c * d)), (P (c * d)⁻¹, A (c * d)⁻¹)],
        (x.1 : Ideal (𝓞 K)).IsPrime ∧ IsArithFrobOver K L x.1 x.2 := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> exact hpack _
    have hc2 : (([(P (c * d), A (c * d)), (P (c * d)⁻¹, A (c * d)⁻¹)]).map
        fun x => ClassGroup.mk0 x.1).prod = 1 := by
      simp [hPclass]
    have h2 := prod_eq_one_of_forall_isArithFrobOver K L habel hunr _ hl2 hc2
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      ← mul_assoc] at h3 h2
    exact mul_right_cancel (h2.trans h3.symm)
  -- every Frobenius above every prime is the value of `A` on that prime's class
  have hfrobeq : ∀ (P' : (Ideal (𝓞 K))⁰) (τ : L ≃ₐ[K] L), (P' : Ideal (𝓞 K)).IsPrime →
      IsArithFrobOver K L P' τ → τ = A (ClassGroup.mk0 P') := by
    intro P' τ hP' hτ
    have hl2 : ∀ x ∈ [(P', τ), (P (ClassGroup.mk0 P')⁻¹, A (ClassGroup.mk0 P')⁻¹)],
        (x.1 : Ideal (𝓞 K)).IsPrime ∧ IsArithFrobOver K L x.1 x.2 := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ⟨hP', hτ⟩
      · exact hpack _
    have hc2 : (([(P', τ), (P (ClassGroup.mk0 P')⁻¹, A (ClassGroup.mk0 P')⁻¹)]).map
        fun x => ClassGroup.mk0 x.1).prod = 1 := by
      simp [hPclass]
    have h2 := prod_eq_one_of_forall_isArithFrobOver K L habel hunr _ hl2 hc2
    have hl2' : ∀ x ∈ [(P (ClassGroup.mk0 P'), A (ClassGroup.mk0 P')),
          (P (ClassGroup.mk0 P')⁻¹, A (ClassGroup.mk0 P')⁻¹)],
        (x.1 : Ideal (𝓞 K)).IsPrime ∧ IsArithFrobOver K L x.1 x.2 := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> exact hpack _
    have hc2' : (([(P (ClassGroup.mk0 P'), A (ClassGroup.mk0 P')),
        (P (ClassGroup.mk0 P')⁻¹, A (ClassGroup.mk0 P')⁻¹)]).map
        fun x => ClassGroup.mk0 x.1).prod = 1 := by
      simp [hPclass]
    have h2' := prod_eq_one_of_forall_isArithFrobOver K L habel hunr _ hl2' hc2'
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h2 h2'
    exact mul_right_cancel (h2.trans h2'.symm)
  refine ⟨MonoidHom.mk' A hmul, fun g => ?_, fun I J hI hJ => ?_⟩
  · -- surjectivity, from Chebotarev
    obtain ⟨P', hP', hfrob⟩ := exists_isArithFrobOver_of_aut K L g
    exact ⟨ClassGroup.mk0 P', (hfrobeq P' g hP' hfrob).symm⟩
  · -- the norm clause
    refine apply_classGroupMk0_relNorm_eq_one K L hunr (MonoidHom.mk' A hmul) ?_ I hI J hJ
    intro P' hP'
    obtain ⟨τ, hτ⟩ := exists_isArithFrobOver K L P' hP'
    have hval : (MonoidHom.mk' A hmul) (ClassGroup.mk0 P') = τ := (hfrobeq P' τ hP' hτ).symm
    rw [hval]
    exact hτ

/-- **THE SECOND INEQUALITY AT MODULUS `1`: for `L/K` finite abelian,
unramified at every finite prime and at every infinite place,
`[L : K] ≤ [I_K : P_K · N_{L/K} I_L]`** (cut 2026-07-28, PROVEN the same day
from `exists_surjective_classGroupHom_aut_of_unramified_abelian` above and
pure group theory).

This is the classical second inequality of class field theory, at the
modulus `1`, written with `Subgroup.index` of `relNormClassSubgroup` in
place of the norm index `[I_K : P_K · N_{L/K} I_L]` (see that definition's
docstring for why the two agree). Nothing else in this development is
needed to state it: no `Γℚ`, no `ker χ`, no Artin map, no Frobenius, no
cyclotomic theory.

**The step performed here.** Given the surjection `φ : Cl(𝓞 K) ↠ Gal(L/K)`
of the leaf above, `Subgroup.index_ker` gives
`(ker φ).index = Nat.card (Gal(L/K)) = [L : K]`
(`IsGalois.card_aut_eq_finrank`, which in this pin is already stated with
`Nat.card` — not `Fintype.card`). The norm clause of that leaf is exactly
the generating set of `relNormClassSubgroup`, so `Subgroup.closure_le` puts
that subgroup inside `ker φ`, and `Subgroup.index_dvd_of_le` (index is
antitone, and every index in the finite group `Cl(𝓞 K)` is nonzero) finishes.
All the mathematics is in the leaf above.

**⚠ BOTH RAMIFICATION HYPOTHESES ARE LOAD-BEARING.**

* `habel` is needed because the norm index only ever sees the
  abelianization: for non-abelian `L/K` the inequality is false as soon as
  `Gal(L/K)` has a proper commutator subgroup.
* `hunr` (unramifiedness at the FINITE primes) is load-bearing, and deleting
  it makes the statement FALSE. Witness: `K = ℚ`, `L = ℚ(√5)`. The extension
  is abelian of degree `2`, and it is unramified at the infinite place (the
  discriminant `5` is positive, so both archimedean places of `L` are real),
  so it satisfies every OTHER hypothesis; it is ramified at `5`. Since
  `Cl(ℤ)` is trivial, `(relNormClassSubgroup ℚ (ℚ(√5))).index = 1` while
  `[L : K] = 2`, so the conclusion reads `2 ≤ 1`.
* `IsUnramifiedAtInfinitePlaces` is what makes modulus `1` ADMISSIBLE, and
  deleting it makes the statement FALSE. Counterexample computed with
  PARI/GP on 2026-07-28 and re-checked on 2026-07-28: `K = ℚ(√3)` has
  `bnfinit(x^2-3,1).no = 1` but `bnrinit(K,[1,[1,1]]).no = 2`, so its narrow
  Hilbert class field is a quadratic extension, abelian and unramified at
  every FINITE place, with `[L : K] = 2` while `Cl(𝓞 K)` is trivial — so the
  right-hand side is `1`. That extension is ramified at both real places of
  `ℚ(√3)`, which is exactly what this hypothesis excludes.

**Mathlib survey (checked 2026-07-28, re-checked 2026-07-28).** Ray class
groups, the Hilbert class field, the norm index, the Artin map, Artin
reciprocity and Chebotarev density are ALL absent from the pin and from
`~/cs/FLT`. Present and usable: `ClassGroup`, `ClassGroup.mk0`,
`Ideal.relNorm` (in the general, `Module.Free`-free form — see
`relNormClassSubgroup`), `Ideal.ramificationIdx`, `Ideal.inertiaDeg`,
`Algebra.IsUnramifiedAt`, `NumberField.InfinitePlace.IsUnramified`,
`IsUnramifiedAtInfinitePlaces`, `IsGalois.card_aut_eq_finrank`,
`Subgroup.index_ker`, `Subgroup.index_dvd_of_le`, and — newly noted —
Hilbert 90 in
`Mathlib/RepresentationTheory/Homological/GroupCohomology/Hilbert90.lean`.
The Herbrand-quotient machinery is NOT: `Mathlib/RepresentationTheory/`
`Homological/TateCohomology/` still carries `Basic.lean` only — definitions,
no class formations and no Tate theorem — and there is no `Herbrand`, no
idele class group and no `ClassFormation` anywhere in the pin, so the
cohomological route must be built, not cited.

**The check that would refute it**: a finite abelian extension of a number
field `K`, unramified at every finite prime and at every infinite place,
with `[L : K] > (relNormClassSubgroup K L).index`. -/
theorem finrank_le_index_relNormClassSubgroup [IsGalois K L]
    [IsUnramifiedAtInfinitePlaces K L]
    (habel : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (hunr : ∀ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 K) Q) :
    Module.finrank K L ≤ (relNormClassSubgroup K L).index := by
  obtain ⟨φ, hsurj, hnorm⟩ :=
    exists_surjective_classGroupHom_aut_of_unramified_abelian K L habel hunr
  -- The norm classes generate `relNormClassSubgroup`, so they cut it into `ker φ`.
  have hker : relNormClassSubgroup K L ≤ φ.ker := by
    refine (Subgroup.closure_le _).2 ?_
    rintro c ⟨I, hI, rfl⟩
    exact hnorm I _ hI rfl
  -- `ker φ` has index `#Gal(L/K) = [L : K]`.
  have hidx : φ.ker.index = Module.finrank K L := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top]
    exact IsGalois.card_aut_eq_finrank K L
  calc Module.finrank K L = φ.ker.index := hidx.symm
    _ ≤ (relNormClassSubgroup K L).index :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
          (Subgroup.index_dvd_of_le hker)

/-- **UNRAMIFIED CFT, THE UPPER BOUND: a finite ABELIAN extension of a
number field `K`, unramified at every finite prime AND at every infinite
place, has degree at most `h_K`** (PROVEN 2026-07-28 from
`finrank_le_index_relNormClassSubgroup` above and Lagrange, and from
nothing else).

Equivalently: such an `L` sits inside the Hilbert class field of `K`, whose
Galois group is `Cl(𝓞 K)`.

The step performed here is the EASY half of `h_K ≥ [I_K : P_K N I_L] ≥
[L : K]`: `relNormClassSubgroup K L` is a subgroup of the finite group
`Cl(𝓞 K)`, so its index divides `h_K` (`Subgroup.index_dvd_card`) and in
particular does not exceed it. All the content is in the leaf above.

Read that leaf's docstring before weakening any hypothesis here: it records
an explicit PARI/GP counterexample (`ℚ(√3)`, `h = 1`, narrow `h⁺ = 2`)
showing that the same inequality with unramifiedness only at the FINITE
places is FALSE. -/
theorem finrank_le_card_classGroup_of_unramified_abelian_of_isUnramifiedAtInfinitePlaces
    [IsGalois K L] [IsUnramifiedAtInfinitePlaces K L]
    (habel : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (hunr : ∀ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 K) Q) :
    Module.finrank K L ≤ Nat.card (ClassGroup (𝓞 K)) :=
  le_trans (finrank_le_index_relNormClassSubgroup K L habel hunr)
    (Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _))

end NumberField
