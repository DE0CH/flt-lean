/-
NumberField/ArtinSymbol.lean — own work for the Fermat project (not vendored
from the FLT project).
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.RingTheory.Frobenius
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.RingTheory.Invariant.Galois
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.ClassGroup.Basic
-- `public` because the Chebotarev reduction below elaborates inside an `@[expose] public`
-- declaration and needs `IntermediateField.fixedField` / `fixingSubgroup_fixedField`
-- and `differentIdeal` / `not_dvd_differentIdeal_iff` to be visible there.
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Fermat.FLT.NumberField.Density
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# The Artin symbol of a number field, and the two deep inputs of unramified CFT

This file carries the **Frobenius layer** of unramified class field theory: the
Frobenius automorphism `frobAt K L Q` attached to a maximal ideal `Q` of `𝓞 L` in
a Galois extension `L/K` of number fields, everything about it that is provable
from what the pin already has, and — clearly labelled as such — the two
statements that are NOT (reciprocity and Chebotarev).

It sits UPSTREAM of `Fermat/FLT/NumberField/UnramifiedClassFieldBound.lean`, whose
`exists_surjective_classGroupHom_aut_of_unramified_abelian` is now PROVEN from the
two leaves below, and upstream of
`Fermat/FLT/NumberField/UnramifiedClassFieldExistence.lean`. It deliberately uses
NO vocabulary from either — only mathlib's `ClassGroup`, `Ideal.relNorm` and
`arithFrobAt` — so that the ramification-theoretic content is separable from the
class-field-theoretic bookkeeping, and so that the two open leaves here can be
attacked without loading either consumer.

## What mathlib already had, and why that changed the cut

`Mathlib/RingTheory/Frobenius.lean` (present at this pin) constructs
`arithFrobAt R G Q` — a Frobenius element of a finite group `G` acting on `S` with
fixed subring `R`, at a prime `Q` of `S` with finite residue field — and proves it
unique when `S/R` is unramified at `Q` (`AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt`)
and conjugate along the `G`-orbit (`isConj_arithFrobAt`). For number fields every
instance it wants is already available: the action of `Gal(L/K)` on `𝓞 L` comes
from `MulSemiringAction G (integralClosure ℤ K)`, and
`Algebra.IsInvariant (𝓞 K) (𝓞 L) Gal(L/K)` is an instance via
`Algebra.isInvariant_of_isGalois`. So the Artin SYMBOL is constructible here, and
the previous single-leaf cut of the reciprocity statement (which packaged the
symbol, its multiplicativity, reciprocity and Chebotarev into one `sorry`) was
coarser than it needed to be.

## Main results

* `NumberField.frobAt` — the Frobenius automorphism at a maximal ideal of `𝓞 L`.
* `NumberField.frobAt_eq_frobAt_of_comm` — PROVEN. For `Gal(L/K)` abelian,
  `frobAt` depends only on the prime of `𝓞 K` below. This is what makes it the
  *Artin symbol* and what makes `exists_classGroupHom_eq_frobAt` below satisfiable.
* `NumberField.frobAt_pow_inertiaDeg` — PROVEN. `frobAt K L Q ^ f(Q|K) = 1` at an
  unramified `Q`. This is the computation that kills the norm classes.
* `NumberField.mem_of_relNorm_of_forall_isMaximal` — PROVEN. To check that a
  subgroup of `Cl(𝓞 K)` contains the class of `N_{L/K} I` for EVERY nonzero ideal
  `I` of `𝓞 L`, it is enough to check the maximal ones.
* `NumberField.frobAt_eq_one_iff_inertiaDeg_eq_one` — PROVEN. At an unramified
  `Q`, the Frobenius is trivial exactly when `Q` has inertia degree `1`, i.e.
  exactly when the prime below splits completely. The dictionary Chebotarev runs
  on.
* `NumberField.artinMap` — PROVEN CONSTRUCTION. The Artin map on the group of
  INVERTIBLE FRACTIONAL IDEALS of `𝓞 K`, `I ↦ ∏_v Frob_v ^ v(I)`, together with its
  multiplicativity and its value `Frob_v` at a prime.
* `NumberField.artinMap_toPrincipalIdeal` — **OPEN LEAF: ARTIN RECIPROCITY.** The
  Artin map kills the principal ideals.
* `NumberField.exists_classGroupHom_eq_frobAt` — PROVEN 2026-07-30 over the leaf
  above: the descent of the Artin map to `Cl(𝓞 K)`.
* `NumberField.inertiaDeg_eq_one_of_forall_pow_natCard` — PROVEN. If every element of
  the residue field `𝓞 F ⧸ q` is a root of `X ^ (N 𝔭) - X` then `f(q | 𝔭) = 1`.
* `NumberField.finite_ramifiedBelow` — PROVEN. Only finitely many primes of `𝓞 K`
  ramify in `L` (via the different ideal).
* `NumberField.finrank_eq_one_of_forall_inertiaDeg_eq_one` — **OPEN LEAF: THE DENSITY
  INPUT OF CHEBOTAREV.** A finite extension of number fields in which all but finitely
  many primes of the base have residue degree `1` is trivial.
* `NumberField.closure_frobAt_eq_top` — PROVEN 2026-07-31 over the leaf above, by the
  fixed-field reduction.

## The reciprocity cut (2026-07-30)

The single leaf `exists_classGroupHom_eq_frobAt` has been split. Its docstring
already diagnosed the split correctly — *"its existence as a map on IDEALS is
bookkeeping … what is deep is that it kills the PRINCIPAL ideals"* — and that is
now what the file does: the bookkeeping is DONE (`artinMap` and the descent
through `ClassGroup.equiv`), and exactly one deep statement is left over,
`artinMap_toPrincipalIdeal`. Nothing else in the reciprocity half of this file is
open.

The construction is the honest one: `FractionalIdeal.count K v I` is the
`v`-valuation of a fractional ideal (mathlib, `DedekindDomain/Factorization`),
finitely supported by `FractionalIdeal.finite_factors`, and
`FractionalIdeal.finprod_heightOneSpectrum_factorization'` says the fractional
ideal group really is free on the height-one primes. The target `Gal(L/K)` is
only a `Group`, so the `∏ᶠ` is taken after transporting `habel` into a
`CommGroup` structure (`galCommGroup`), which is the reason `habel` appears in
the DEFINITION of `artinMap` and not only in its lemmas.
-/

@[expose] public section

open scoped nonZeroDivisors NumberField

namespace NumberField

section Faithful

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The action of `Gal(L/K)` on `𝓞 L` is the restriction of its action on `L`.
`rfl`, recorded because the instance is assembled through
`MulSemiringAction G (integralClosure ℤ L)` and the unfolding is not otherwise
visible. -/
theorem coe_smul_ringOfIntegers (τ : L ≃ₐ[K] L) (x : 𝓞 L) :
    ((τ • x : 𝓞 L) : L) = τ (x : L) := rfl

variable [NumberField L]

/-- **The action of `Gal(L/K)` on `𝓞 L` is FAITHFUL.** An automorphism fixing
every algebraic integer of `L` is the identity, because every element of `L` is a
ratio of two of them (`IsFractionRing.div_surjective`).

This is what converts the uniqueness statement
`AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt` — an equality of `𝓞 K`-algebra maps
`𝓞 L →ₐ 𝓞 L` — back into an equality in `Gal(L/K)`. -/
theorem eq_one_of_smul_eq_self (τ : L ≃ₐ[K] L) (h : ∀ x : 𝓞 L, τ • x = x) : τ = 1 := by
  have h' : ∀ x : 𝓞 L, τ (algebraMap (𝓞 L) L x) = algebraMap (𝓞 L) L x := by
    intro x
    have hx := congrArg (fun z : 𝓞 L ↦ (z : L)) (h x)
    simpa [coe_smul_ringOfIntegers] using hx
  refine AlgEquiv.ext fun y ↦ ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) y
  rw [AlgEquiv.one_apply, map_div₀, h' a, h' b]

end Faithful

section NormClasses

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L]

/-- **THE NORM CLASSES ARE GENERATED BY THE PRIMES: a subgroup of `Cl(𝓞 K)`
containing the class of `N_{L/K} Q` for every MAXIMAL ideal `Q` of `𝓞 L` contains
the class of `N_{L/K} I` for every nonzero ideal `I`** (PROVEN 2026-07-30).

Pure bookkeeping over the unique factorisation of ideals in the Dedekind domain
`𝓞 L`, but bookkeeping that the consumer cannot avoid:
`relNormClassSubgroup K L` is generated by the norm classes of ALL nonzero
ideals, while everything one can actually compute about the Artin map happens at
the primes.

Stated with an explicit `J : (Ideal (𝓞 K))⁰` and an equation rather than with a
`ClassGroup.mk0` of a bundled subtype element, to match the idiom of
`relNormClassSubgroup`'s own generating set (the nonzero-divisor witness there is
an inline proof term, so a caller never has the same subtype element in hand).

The `I = ⊥` case is discharged not by a hypothesis but by the shape of the
statement: `N_{L/K} ⊥ = ⊥` is a zero divisor, so no `J : (Ideal (𝓞 K))⁰` can
satisfy the equation. -/
theorem mem_of_relNorm_of_forall_isMaximal {H : Subgroup (ClassGroup (𝓞 K))}
    (h : ∀ (Q : Ideal (𝓞 L)) (J : (Ideal (𝓞 K))⁰), Q.IsMaximal →
      (J : Ideal (𝓞 K)) = Ideal.relNorm (𝓞 K) Q → ClassGroup.mk0 J ∈ H) :
    ∀ (I : Ideal (𝓞 L)) (J : (Ideal (𝓞 K))⁰),
      (J : Ideal (𝓞 K)) = Ideal.relNorm (𝓞 K) I → ClassGroup.mk0 J ∈ H := by
  intro I
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
      intro J hJ
      exact absurd (hJ.trans (by simp)) (nonZeroDivisors.coe_ne_zero J)
  | h₂ I hI =>
      intro J hJ
      rw [Ideal.isUnit_iff.mp hI, Ideal.relNorm_top] at hJ
      have hJ1 : J = 1 := by
        refine Subtype.ext ?_
        rw [hJ, OneMemClass.coe_one, Ideal.one_eq_top]
      rw [hJ1, map_one]
      exact H.one_mem
  | h₃ a p ha hp ih =>
      intro J hJ
      have hpb : p ≠ ⊥ := hp.ne_zero
      have hnp : Ideal.relNorm (𝓞 K) p ≠ ⊥ := by
        simpa using (Ideal.relNorm_eq_bot_iff (R := 𝓞 K) (I := p)).not.mpr hpb
      have hna : Ideal.relNorm (𝓞 K) a ≠ ⊥ := by
        simpa using (Ideal.relNorm_eq_bot_iff (R := 𝓞 K) (I := a)).not.mpr ha
      set Jp : (Ideal (𝓞 K))⁰ :=
        ⟨Ideal.relNorm (𝓞 K) p, mem_nonZeroDivisors_of_ne_zero hnp⟩ with hJp
      set Ja : (Ideal (𝓞 K))⁰ :=
        ⟨Ideal.relNorm (𝓞 K) a, mem_nonZeroDivisors_of_ne_zero hna⟩ with hJa
      have hmul : J = Jp * Ja := by
        refine Subtype.ext ?_
        rw [hJ, map_mul]
        rfl
      rw [hmul, map_mul]
      exact H.mul_mem (h p Jp ((Ideal.isPrime_of_prime hp).isMaximal hpb) rfl) (ih Ja rfl)

end NormClasses

section FinprodAux

open IsDedekindDomain

variable (K : Type*) [Field K] [NumberField K] {M : Type*} [CommGroup M]

/-! ### The fractional ideal group is free on the height-one primes

Four lemmas saying that `I ↦ ∏ᶠ v, F v ^ v(I)` is a homomorphism out of
`(FractionalIdeal (𝓞 K)⁰ K)ˣ` sending the prime `v` to `F v`, for an arbitrary
family `F` valued in a commutative group. They are stated for a general `M` on
purpose: `Gal(L/K)` carries only a `Group` instance, and the `CommGroup` used
below is built from the `habel` hypothesis, so keeping the group-theoretic content
here — where the instance is a genuine `[CommGroup M]` — is what stops the
commutativity bookkeeping from leaking into the arithmetic. -/

/-- The exponents `count K v I` vanish for all but finitely many `v`
(`FractionalIdeal.finite_factors`), so the products below have finite support. -/
theorem finite_mulSupport_zpow_count (F : HeightOneSpectrum (𝓞 K) → M)
    (I : FractionalIdeal (𝓞 K)⁰ K) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) =>
      F v ^ FractionalIdeal.count K v I).Finite := by
  refine Set.Finite.subset (Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors I)) ?_
  intro v hv
  simp only [Function.mem_mulSupport] at hv
  simp only [Set.mem_setOf_eq]
  intro h
  exact hv (by rw [h, zpow_zero])

theorem finprod_zpow_count_one (F : HeightOneSpectrum (𝓞 K) → M) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 K),
      F v ^ FractionalIdeal.count K v ((1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K)) = 1 := by
  refine (finprod_congr fun v => ?_).trans finprod_one
  rw [Units.val_one, FractionalIdeal.count_one, zpow_zero]

theorem finprod_zpow_count_mul (F : HeightOneSpectrum (𝓞 K) → M)
    (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 K),
      F v ^ FractionalIdeal.count K v ((I * J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K)) =
      (∏ᶠ v : HeightOneSpectrum (𝓞 K),
        F v ^ FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K)) *
      (∏ᶠ v : HeightOneSpectrum (𝓞 K),
        F v ^ FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K)) := by
  have hI : (I : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := I.ne_zero
  have hJ : (J : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := J.ne_zero
  refine (finprod_congr fun v => ?_).trans
    (finprod_mul_distrib (finite_mulSupport_zpow_count K F _)
      (finite_mulSupport_zpow_count K F _))
  rw [Units.val_mul, FractionalIdeal.count_mul K v hI hJ, zpow_add]

theorem finprod_zpow_count_coe (F : HeightOneSpectrum (𝓞 K) → M)
    (v : HeightOneSpectrum (𝓞 K)) :
    (∏ᶠ w : HeightOneSpectrum (𝓞 K),
      F w ^ FractionalIdeal.count K w ((v.asIdeal : Ideal (𝓞 K)) :
        FractionalIdeal (𝓞 K)⁰ K)) = F v := by
  rw [finprod_eq_single _ v fun w hw => by
    rw [FractionalIdeal.count_maximal_coprime K w (Ne.symm hw), zpow_zero]]
  rw [FractionalIdeal.count_self K v, zpow_one]

end FinprodAux

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- **The Frobenius automorphism at a maximal ideal `Q` of `𝓞 L`**: the unique
`σ ∈ Gal(L/K)` with `σ x ≡ x ^ q (mod Q)` for every `x ∈ 𝓞 L`, where `q` is the
cardinality of the residue field of the prime of `𝓞 K` below `Q`.

This is mathlib's `arithFrobAt` for the action of `Gal(L/K)` on `𝓞 L`, whose fixed
subring is `𝓞 K`. Uniqueness holds exactly when `L/K` is unramified at `Q`
(at a ramified `Q` the choice is only canonical up to the inertia group, and
`arithFrobAt` makes an arbitrary one, coherently along each `Gal(L/K)`-orbit).

For `Gal(L/K)` abelian this depends only on the prime of `𝓞 K` below `Q`
(`frobAt_eq_frobAt_of_comm`), which is the classical **Artin symbol** `(Q, L/K)`. -/
noncomputable def frobAt (Q : Ideal (𝓞 L)) [Q.IsMaximal] : L ≃ₐ[K] L :=
  arithFrobAt (𝓞 K) (L ≃ₐ[K] L) Q

theorem isArithFrobAt_frobAt (Q : Ideal (𝓞 L)) [Q.IsMaximal] :
    IsArithFrobAt (𝓞 K) (frobAt K L Q) Q :=
  IsArithFrobAt.arithFrobAt (𝓞 K) (L ≃ₐ[K] L) Q

/-- **THE ARTIN SYMBOL IS WELL DEFINED ON PRIMES OF `𝓞 K` WHEN `Gal(L/K)` IS
ABELIAN** (PROVEN 2026-07-30).

`arithFrobAt` is conjugate along a `Gal(L/K)`-orbit of primes
(`isConj_arithFrobAt`), and the primes over a fixed prime of `𝓞 K` form one orbit;
in an abelian group conjugate elements are equal.

**Why this lemma is load-bearing rather than decorative.**
`exists_classGroupHom_eq_frobAt` below asks for a single `φ` with
`φ [Q ∩ 𝓞 K] = frobAt K L Q` for EVERY maximal `Q`; without this lemma that
demand would be contradictory as soon as two primes over one `𝔭` had different
Frobenius elements, i.e. the leaf would be FALSE rather than open. With `habel`
it is consistent. Note the hypothesis is genuinely needed: for `Gal(L/K)`
non-abelian the Frobenius elements over one `𝔭` form a full conjugacy class, not
a point, and no such `φ` can exist (`Cl(𝓞 K)` is abelian, so it cannot surject
onto a non-abelian group either — see the consumer's own audit). -/
theorem frobAt_eq_frobAt_of_comm (habel : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (Q Q' : Ideal (𝓞 L)) [Q.IsMaximal] [Q'.IsMaximal]
    (h : Q.under (𝓞 K) = Q'.under (𝓞 K)) :
    frobAt K L Q = frobAt K L Q' := by
  obtain ⟨u, hu⟩ := isConj_arithFrobAt (𝓞 K) (L ≃ₐ[K] L) Q Q' h
  have hu' : (u : L ≃ₐ[K] L) * frobAt K L Q = (u : L ≃ₐ[K] L) * frobAt K L Q' := by
    simp only [frobAt]
    rw [hu.eq]
    exact habel _ _
  exact mul_left_cancel hu'

/-- **THE ORDER OF THE FROBENIUS DIVIDES THE INERTIA DEGREE: at a prime `Q` of
`𝓞 L` unramified over `𝓞 K`, `frobAt K L Q ^ f(Q|𝓞 K) = 1`** (PROVEN 2026-07-30).

This is the computation the docstring of
`exists_surjective_classGroupHom_aut_of_unramified_abelian` calls "a two-line
computation once the map exists" — `Frob_{N𝔓} = Frob_𝔭 ^ f(𝔓/𝔭) = 1` — and it is
what makes the norm clause of that leaf a THEOREM rather than an assumption.

**Chain.** `σ x ≡ x ^ q (mod Q)` iterates to `σ ^ k x ≡ x ^ (q ^ k) (mod Q)`; the
residue field of `Q` has `q ^ f` elements (`Ideal.cardQuot_pow_inertiaDeg`), so
`x ^ (q ^ f) = x` there (`FiniteField.pow_card`) and `σ ^ f` acts trivially on
`𝓞 L ⧸ Q`. Hence `σ ^ f * σ` is again an arithmetic Frobenius at `Q`; at an
UNRAMIFIED `Q` the Frobenius is unique
(`AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt`), so `σ ^ f * σ = σ` as maps of
`𝓞 L`, and the action of `Gal(L/K)` on `𝓞 L` is faithful
(`eq_one_of_smul_eq_self`), so `σ ^ f = 1`.

**Unramifiedness is load-bearing.** At a ramified `Q` the conclusion is false in
general: `σ ^ f` lands in the inertia group, which then has order
`e(Q|𝓞 K) > 1`, and `arithFrobAt`'s arbitrary choice need not have order
dividing `f`. Witness in the smallest possible shape: `K = ℚ`, `L = ℚ(i)`,
`Q = (1 + i)`, where `e = 2`, `f = 1`, and the unique nontrivial element of
`Gal(L/K)` satisfies `σ x ≡ x ^ 2 (mod Q)` — it IS an arithmetic Frobenius at `Q`
— while `σ ^ 1 = σ ≠ 1`. -/
theorem frobAt_pow_inertiaDeg (Q : Ideal (𝓞 L)) [Q.IsMaximal]
    [Algebra.IsUnramifiedAt (𝓞 K) Q] :
    frobAt K L Q ^ Q.inertiaDeg (𝓞 K) = 1 := by
  classical
  letI := Ideal.Quotient.field Q
  letI : Fintype (𝓞 L ⧸ Q) := Fintype.ofFinite _
  set σ : L ≃ₐ[K] L := frobAt K L Q with hσ
  set q : ℕ := Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) with hq
  set f : ℕ := Q.inertiaDeg (𝓞 K) with hf
  have H : IsArithFrobAt (𝓞 K) σ Q := isArithFrobAt_frobAt K L Q
  have hmk : ∀ y : 𝓞 L,
      Ideal.Quotient.mk Q (σ • y) = (Ideal.Quotient.mk Q y) ^ q := fun y ↦ H.mk_apply y
  -- iterating the Frobenius congruence
  have key : ∀ (k : ℕ) (x : 𝓞 L),
      Ideal.Quotient.mk Q ((σ ^ k) • x) = (Ideal.Quotient.mk Q x) ^ (q ^ k) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
        intro x
        rw [pow_succ', mul_smul, hmk, ih, ← pow_mul, ← pow_succ]
  -- the residue field of `Q` has `q ^ f` elements
  have hcard : Nat.card (𝓞 L ⧸ Q) = q ^ f := by
    rw [hq, hf, ← Submodule.cardQuot_apply, ← Submodule.cardQuot_apply]
    exact (Ideal.cardQuot_pow_inertiaDeg (Q.under (𝓞 K)) Q).symm
  -- so `σ ^ f` is the identity on the residue field
  have hfix : ∀ x : 𝓞 L, Ideal.Quotient.mk Q ((σ ^ f) • x) = Ideal.Quotient.mk Q x := by
    intro x
    rw [key f x, ← hcard, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card _
  -- hence `σ ^ f * σ` is again an arithmetic Frobenius at `Q`
  have H2 : IsArithFrobAt (𝓞 K) (σ ^ f * σ) Q := by
    intro x
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
    have hx : ((σ ^ f * σ) • x : 𝓞 L) = (σ ^ f) • (σ • x) := by rw [mul_smul]
    show Ideal.Quotient.mk Q ((σ ^ f * σ) • x) = _
    rw [hx, hfix (σ • x)]
    exact hmk x
  -- uniqueness of the Frobenius at an unramified prime, then faithfulness
  have heq := H2.eq_of_isUnramifiedAt H Q.primeCompl_le_nonZeroDivisors
  have hsmul : ∀ x : 𝓞 L, (σ ^ f * σ) • x = σ • x := fun x ↦ DFunLike.congr_fun heq x
  refine eq_one_of_smul_eq_self _ fun y ↦ ?_
  have hy := hsmul (σ⁻¹ • y)
  rwa [mul_smul, smul_inv_smul] at hy

/-- **A PRIME SPLITS COMPLETELY IFF ITS FROBENIUS IS TRIVIAL: at an unramified
maximal `Q` of `𝓞 L`, `frobAt K L Q = 1 ↔ f(Q | 𝓞 K) = 1`** (PROVEN 2026-07-30).

This is the dictionary that the classical proof of `closure_frobAt_eq_top` below
runs on — "the primes unramified in `L` split completely in `L^H`" is exactly
"their Frobenius elements lie in `H`" — and it is the whole of that proof which
does not require a density input. Recorded here so that whoever attacks
Chebotarev does not have to re-derive it.

**Chain.** `←` is `frobAt_pow_inertiaDeg` with `pow_one`. For `→`: `σ = 1` turns
the defining congruence `σ x ≡ x ^ q (mod Q)` into `z ^ q = z` for EVERY `z` in
the residue field `𝓞 L ⧸ Q` (`Ideal.Quotient.mk` is surjective). That field is
cyclic of order `q ^ f` (`Ideal.cardQuot_pow_inertiaDeg`), so its unit group has
exponent dividing `q - 1` (`IsCyclic.exponent_eq_card`), giving
`q ^ f - 1 ∣ q - 1`; with `q ≥ 2` that forces `f = 1`.

**Unramifiedness is used only in `←`** (through `frobAt_pow_inertiaDeg`); the `→`
direction holds at a ramified `Q` too, since `arithFrobAt`'s arbitrary choice is
still an arithmetic Frobenius. It is kept as a hypothesis on both sides because
the statement is only *meaningful* about `L/K` at an unramified prime. -/
theorem frobAt_eq_one_iff_inertiaDeg_eq_one (Q : Ideal (𝓞 L)) [Q.IsMaximal]
    [Algebra.IsUnramifiedAt (𝓞 K) Q] :
    frobAt K L Q = 1 ↔ Q.inertiaDeg (𝓞 K) = 1 := by
  classical
  letI := Ideal.Quotient.field Q
  letI : Fintype (𝓞 L ⧸ Q) := Fintype.ofFinite _
  set σ : L ≃ₐ[K] L := frobAt K L Q with hσ
  set q : ℕ := Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) with hq
  set f : ℕ := Q.inertiaDeg (𝓞 K) with hf
  have H : IsArithFrobAt (𝓞 K) σ Q := isArithFrobAt_frobAt K L Q
  have hmk : ∀ y : 𝓞 L,
      Ideal.Quotient.mk Q (σ • y) = (Ideal.Quotient.mk Q y) ^ q := fun y ↦ H.mk_apply y
  have hcard : Nat.card (𝓞 L ⧸ Q) = q ^ f := by
    rw [hq, hf, ← Submodule.cardQuot_apply, ← Submodule.cardQuot_apply]
    exact (Ideal.cardQuot_pow_inertiaDeg (Q.under (𝓞 K)) Q).symm
  have hcard2 : 2 ≤ q ^ f := by
    rw [← hcard, Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hq2 : 2 ≤ q := by
    rcases Nat.lt_or_ge q 2 with hcon | hcon
    · have : q ^ f ≤ 1 ^ f := Nat.pow_le_pow_left (by omega) f
      simp only [one_pow] at this
      omega
    · exact hcon
  constructor
  · intro h1
    -- every element of the residue field is a root of `X ^ q - X`
    have hz : ∀ z : 𝓞 L ⧸ Q, z ^ q = z := by
      intro z
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
      rw [← hmk y, h1, one_smul]
    -- so the (cyclic) unit group has exponent dividing `q - 1`
    have hu : ∀ u : (𝓞 L ⧸ Q)ˣ, u ^ (q - 1) = 1 := by
      intro u
      refine Units.ext ?_
      have hne : (u : 𝓞 L ⧸ Q) ≠ 0 := u.ne_zero
      have hmul : (u : 𝓞 L ⧸ Q) ^ (q - 1) * (u : 𝓞 L ⧸ Q) = 1 * (u : 𝓞 L ⧸ Q) := by
        rw [one_mul, ← pow_succ, Nat.sub_add_cancel (by omega), hz]
      simpa using mul_right_cancel₀ hne hmul
    have hdvd : Nat.card (𝓞 L ⧸ Q)ˣ ∣ q - 1 := by
      rw [← IsCyclic.exponent_eq_card]
      exact Monoid.exponent_dvd_of_forall_pow_eq_one hu
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hcard] at hdvd
    -- `q ^ f - 1 ∣ q - 1` with `q ≥ 2` forces `f = 1`
    by_contra hne
    have hf0 : f ≠ 0 := by
      rintro h0
      rw [h0, pow_zero] at hcard2
      omega
    have hf2 : 2 ≤ f := by omega
    have hpow : q ^ 2 ≤ q ^ f := Nat.pow_le_pow_right (by omega) hf2
    have hsq : q < q ^ 2 := by nlinarith [sq_nonneg q]
    have hle : q ^ f - 1 ≤ q - 1 := Nat.le_of_dvd (by omega) hdvd
    omega
  · intro h1
    have hpow := frobAt_pow_inertiaDeg K L Q
    rwa [← hσ, ← hf, h1, pow_one] at hpow

section ArtinMap

open IsDedekindDomain

omit [NumberField L] [IsGalois K L] in
/-- Every height-one prime of `𝓞 K` has a maximal ideal of `𝓞 L` above it: `𝓞 L` is
integral over `𝓞 K` and the structure map is injective, so going-up applies. -/
theorem exists_isMaximal_under_eq (v : HeightOneSpectrum (𝓞 K)) :
    ∃ Q : Ideal (𝓞 L), Q.IsMaximal ∧ Q.under (𝓞 K) = v.asIdeal := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  obtain ⟨Q, hQ, hQ'⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 L) v.asIdeal
    (le_trans (le_of_eq
      ((RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))))
      bot_le)
  exact ⟨Q, hQ, hQ'⟩

/-- A choice of maximal ideal of `𝓞 L` lying over the height-one prime `v` of `𝓞 K`.

The choice is arbitrary and NOT canonical; it is `frobAt_eq_frobAt_of_comm`, i.e.
`Gal(L/K)` being abelian, that makes everything below independent of it — see
`frobAtBelow_eq_frobAt`. Deliberately no hypothesis: the choice exists for any
finite extension, only its irrelevance needs `habel`. -/
noncomputable def primeAbove (v : HeightOneSpectrum (𝓞 K)) : Ideal (𝓞 L) :=
  (exists_isMaximal_under_eq K L v).choose

instance isMaximal_primeAbove (v : HeightOneSpectrum (𝓞 K)) : (primeAbove K L v).IsMaximal :=
  (exists_isMaximal_under_eq K L v).choose_spec.1

omit [NumberField L] [IsGalois K L] in
theorem under_primeAbove (v : HeightOneSpectrum (𝓞 K)) :
    (primeAbove K L v).under (𝓞 K) = v.asIdeal :=
  (exists_isMaximal_under_eq K L v).choose_spec.2

/-- **The Artin symbol `(v, L/K)` of a height-one prime `v` of `𝓞 K`.** -/
noncomputable def frobAtBelow (v : HeightOneSpectrum (𝓞 K)) : L ≃ₐ[K] L :=
  frobAt K L (primeAbove K L v)

/-- For `Gal(L/K)` abelian, `frobAtBelow` is the Frobenius at ANY prime of `𝓞 L`
above `v`, not merely at the chosen one (PROVEN 2026-07-30). -/
theorem frobAtBelow_eq_frobAt (habel : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (v : HeightOneSpectrum (𝓞 K)) (Q : Ideal (𝓞 L)) [Q.IsMaximal]
    (hQ : Q.under (𝓞 K) = v.asIdeal) : frobAtBelow K L v = frobAt K L Q :=
  frobAt_eq_frobAt_of_comm K L habel _ _ ((under_primeAbove K L v).trans hQ.symm)

/-- The commutative group structure on `Gal(L/K)` witnessed by `habel`.

`Gal(L/K)` carries only a `Group` instance, and `∏ᶠ` needs a `CommMonoid`; the
mixin `IsMulCommutative` does NOT supply one (checked at this pin: no instance
path `Group + IsMulCommutative → CommMonoid`, and `Subgroup.center` has the mixin
but no `CommMonoid` either). Building the structure with `{ ‹Group _› with … }`
keeps `mul`, `one` and `zpow` definitionally the ambient ones, which is what lets
`artinMap` be a `MonoidHom` for the AMBIENT instances. -/
abbrev galCommGroup (habel : ∀ a b : L ≃ₐ[K] L, a * b = b * a) : CommGroup (L ≃ₐ[K] L) :=
  { (inferInstance : Group (L ≃ₐ[K] L)) with mul_comm := habel }

/-- **THE ARTIN MAP ON INVERTIBLE FRACTIONAL IDEALS** (PROVEN CONSTRUCTION,
2026-07-30): `I ↦ ∏_v (v, L/K) ^ v(I)`, a homomorphism
`(FractionalIdeal (𝓞 K)⁰ K)ˣ →* Gal(L/K)`.

This is the "bookkeeping" half that the previous single-leaf cut of
`exists_classGroupHom_eq_frobAt` had swallowed: no arithmetic input at all, only
that the fractional ideal group is free abelian on the height-one primes
(`FractionalIdeal.count`, `FractionalIdeal.finite_factors`) and that the Artin
symbol is well defined on primes (`frobAt_eq_frobAt_of_comm`, via `habel`).

Defined for ALL invertible fractional ideals, not just integral ones, because the
class group is a quotient of that group — going through integral ideals would
force the descent to re-prove that every class has an integral representative. -/
noncomputable def artinMap (habel : ∀ a b : L ≃ₐ[K] L, a * b = b * a) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ →* (L ≃ₐ[K] L) where
  toFun I :=
    letI := galCommGroup K L habel
    ∏ᶠ v : HeightOneSpectrum (𝓞 K),
      frobAtBelow K L v ^ FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K)
  map_one' :=
    letI := galCommGroup K L habel
    finprod_zpow_count_one K (frobAtBelow K L)
  map_mul' I J :=
    letI := galCommGroup K L habel
    finprod_zpow_count_mul K (frobAtBelow K L) I J

/-- **The Artin map sends a prime to its Artin symbol** (PROVEN 2026-07-30). -/
theorem artinMap_apply_coe (habel : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (v : HeightOneSpectrum (𝓞 K)) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hI : (I : FractionalIdeal (𝓞 K)⁰ K) = (v.asIdeal : Ideal (𝓞 K))) :
    artinMap K L habel I = frobAtBelow K L v := by
  letI := galCommGroup K L habel
  show (∏ᶠ w : HeightOneSpectrum (𝓞 K),
      frobAtBelow K L w ^ FractionalIdeal.count K w (I : FractionalIdeal (𝓞 K)⁰ K)) = _
  rw [hI]
  exact finprod_zpow_count_coe K (frobAtBelow K L) v

/-! ### The cyclic reduction

`artinMap_toPrincipalIdeal` is PROVEN below over the single sorried input
`artinMap_toPrincipalIdeal_of_isCyclic`, which is the same statement for `L/K`
CYCLIC. Everything between the two is proven here: tower functoriality of the
Artin symbol and of the Artin map, the descent of both unramifiedness hypotheses
to an intermediate field, and the separation of a finite abelian group by its
cyclic quotients.

**This reverses the "deliberately NOT decomposed" verdict recorded on 2026-07-30
and re-recorded on 2026-07-31.** That verdict named three costs — tower
functoriality of the Artin symbol, compatibility of `artinMap` with
`restrictNormalHom` through the `∏ᶠ`, and the structure theorem for finite abelian
groups — and priced them at "several hundred lines". Measured, the whole reduction
is about 150, because each cost is either already in the pin or falls out of the
`IsArithFrobAt` API:

* the unramifiedness descent `𝓞 L ⊇ 𝓞 M ⊇ 𝓞 K`, which the earlier audit of
  `closure_frobAt_eq_top` called out as the expensive part ("no mathlib lemma at
  this pin does this"), IS in the pin: `Algebra.IsUnramifiedAt.of_liesOver` in
  `Mathlib/NumberTheory/RamificationInertia/Unramified.lean`;
* tower functoriality is 15 lines: the restriction of a Frobenius satisfies the
  defining congruence on `𝓞 M` because `Ideal.under_under` makes the exponent the
  same and `AlgEquiv.restrictNormal_commutes` moves the action across
  `𝓞 M → 𝓞 L`; then `eq_of_isUnramifiedAt` plus `eq_one_of_smul_eq_self`;
* the structure theorem is not needed. `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity`
  (finite-abelian duality, in the pin) gives a character `φ` with `φ g ≠ 1`, and a
  finite subgroup of the units of a domain is cyclic (`isCyclic_subgroup_units`),
  so `G ⧸ ker φ` is cyclic;
* `IsGalois.of_fixedField_normal_subgroup`, `IsGalois.normalAutEquivQuotient` and
  `IsUnramifiedAtInfinitePlaces.bot` supply the Galois correspondence and the
  archimedean hypothesis for the subfield, all three already in the pin.

The verdict was also right that this reduction removes no MATHEMATICS: the cyclic
case is where every classical treatment spends its effort. It is made anyway
because (a) the alternative the verdict held out for is not available — see the
insufficiency argument in the docstring of the leaf below — and (b) every
classical route to reciprocity (Artin's cyclotomic argument, the cohomological
one, Chevalley's) passes through the cyclic case, so this is work that has to be
done on any route. -/

/-- **A FINITE ABELIAN GROUP IS SEPARATED BY ITS CYCLIC QUOTIENTS: for `g ≠ 1`
there is a subgroup `H` with `g ∉ H` and `G ⧸ H` cyclic** (PROVEN 2026-07-31).

Stated with a commutativity HYPOTHESIS rather than `[CommGroup G]` because the
only consumer is `Gal(L/K)`, which carries a bare `Group` instance and gets its
commutativity from `habel`; taking the hypothesis keeps `Subgroup G` in the
statement attached to the ambient instance and avoids the instance juggling that
`galCommGroup` would otherwise force on the caller.

No structure theorem: `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity`
produces a character `φ : G →* (AlgebraicClosure ℚ)ˣ` with `φ g ≠ 1`, and
`G ⧸ ker φ ≃* φ.range` is a finite subgroup of the units of a domain, hence cyclic
(`isCyclic_subgroup_units`). `AlgebraicClosure ℚ` rather than `ℂ` only to keep the
analysis library out of the import cone. -/
theorem exists_subgroup_notMem_isCyclic_quotient {G : Type*} [Group G] [Finite G]
    (hcomm : ∀ a b : G, a * b = b * a) {g : G} (hg : g ≠ 1) :
    ∃ H : Subgroup G, ∃ _ : H.Normal, g ∉ H ∧ IsCyclic (G ⧸ H) := by
  letI : CommGroup G := { ‹Group G› with mul_comm := hcomm }
  haveI : NeZero (Monoid.exponent G) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨φ, hφ⟩ :=
    CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G (AlgebraicClosure ℚ) hg
  refine ⟨φ.ker, inferInstance, by simpa [MonoidHom.mem_ker] using hφ, ?_⟩
  haveI : Finite ↥φ.range := Finite.of_surjective _ φ.rangeRestrict_surjective
  exact isCyclic_of_surjective (QuotientGroup.quotientKerEquivRange φ).symm
    (QuotientGroup.quotientKerEquivRange φ).symm.surjective

section Tower

variable (M : IntermediateField K L)

omit [NumberField K] [NumberField L] [IsGalois K L] in
/-- `𝓞 M → 𝓞 L → L` is `𝓞 M → M → L`. `rfl`, recorded because the two routes go
through different `Algebra` instances and the unfolding is not otherwise visible. -/
theorem coe_algebraMap_ringOfIntegers (y : 𝓞 M) :
    ((algebraMap (𝓞 M) (𝓞 L) y : 𝓞 L) : L) = algebraMap M L (y : M) := rfl

omit [NumberField K] [NumberField L] [IsGalois K L] in
/-- The action of `Gal(L/K)` on `𝓞 L` restricts to the action of `Gal(M/K)` on
`𝓞 M`. This is `AlgEquiv.restrictNormal_commutes` transported through the rings of
integers, and it is what makes the restriction of a Frobenius a Frobenius. -/
theorem algebraMap_restrictNormalHom_smul [Normal K M] (σ : L ≃ₐ[K] L) (y : 𝓞 M) :
    algebraMap (𝓞 M) (𝓞 L) (AlgEquiv.restrictNormalHom M σ • y) =
      σ • algebraMap (𝓞 M) (𝓞 L) y := by
  apply RingOfIntegers.ext
  simp only [coe_algebraMap_ringOfIntegers, coe_smul_ringOfIntegers]
  exact σ.restrictNormal_commutes M (y : M)

/-- **TOWER FUNCTORIALITY OF THE ARTIN SYMBOL: for `M` an intermediate field Galois
over `K` and `Q` unramified, the restriction of `Frob_Q` to `M` is `Frob_{Q ∩ 𝓞 M}`**
(PROVEN 2026-07-31).

Named as missing by the 2026-07-30 audit of `closure_frobAt_eq_top` ("it needs
`𝓞 M` for an `IntermediateField`, and multiplicativity of `e` in towers"); both
are in the pin. The proof is the direct one: `τ = restrictNormalHom M σ` satisfies
`τ y ≡ y ^ (N𝔭) (mod Q ∩ 𝓞 M)` for `y ∈ 𝓞 M`, because the congruence for `σ` holds
in `Q` and both sides are images from `𝓞 M`, and the exponent is unchanged since
`Ideal.under_under` gives `(Q ∩ 𝓞 M) ∩ 𝓞 K = Q ∩ 𝓞 K`. Uniqueness of the Frobenius
at an unramified prime (`AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt`) then identifies
it, and faithfulness (`eq_one_of_smul_eq_self`) converts the equality of
`𝓞 M`-maps back into an equality in `Gal(M/K)`.

**Unramifiedness of `Q ∩ 𝓞 M` over `𝓞 K` is not an extra hypothesis**: it descends
from that of `Q` by `Algebra.IsUnramifiedAt.of_liesOver`, which is the pin's
tower-bottom lemma for `Algebra.IsUnramifiedAt`. -/
theorem restrictNormalHom_frobAt [IsGalois K M]
    (Q : Ideal (𝓞 L)) [Q.IsMaximal] [Algebra.IsUnramifiedAt (𝓞 K) Q] :
    AlgEquiv.restrictNormalHom M (frobAt K L Q) = frobAt K M (Q.under (𝓞 M)) := by
  set q : Ideal (𝓞 M) := Q.under (𝓞 M) with hq
  haveI : q.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q
  haveI : Algebra.IsUnramifiedAt (𝓞 K) q := Algebra.IsUnramifiedAt.of_liesOver (𝓞 K) q Q
  set σ : L ≃ₐ[K] L := frobAt K L Q with hσ
  set τ : M ≃ₐ[K] M := AlgEquiv.restrictNormalHom M σ with hτ
  have hQ : IsArithFrobAt (𝓞 K) σ Q := isArithFrobAt_frobAt K L Q
  have hunder : q.under (𝓞 K) = Q.under (𝓞 K) := Ideal.under_under Q
  have hτfrob : IsArithFrobAt (𝓞 K) τ q := by
    intro y
    show algebraMap (𝓞 M) (𝓞 L) (τ • y - y ^ Nat.card (𝓞 K ⧸ q.under (𝓞 K))) ∈ Q
    rw [map_sub, map_pow, algebraMap_restrictNormalHom_smul K L M σ y, hunder]
    exact hQ (algebraMap (𝓞 M) (𝓞 L) y)
  have heq := hτfrob.eq_of_isUnramifiedAt (isArithFrobAt_frobAt K M q)
    q.primeCompl_le_nonZeroDivisors
  have hsmul : ∀ y : 𝓞 M, τ • y = frobAt K M q • y := fun y ↦ DFunLike.congr_fun heq y
  have hone : τ * (frobAt K M q)⁻¹ = 1 := by
    refine eq_one_of_smul_eq_self _ fun y ↦ ?_
    rw [mul_smul, hsmul, smul_inv_smul]
  exact mul_inv_eq_one.mp hone

omit [NumberField L] [IsGalois K L] in
/-- The chosen prime of `𝓞 L` above a height-one prime `v` of `𝓞 K` is nonzero,
because it contracts to `v.asIdeal ≠ ⊥`. -/
theorem primeAbove_ne_bot (v : HeightOneSpectrum (𝓞 K)) : primeAbove K L v ≠ ⊥ := by
  intro h
  have hu := under_primeAbove K L v
  rw [h] at hu
  exact v.ne_bot (by simpa using hu.symm)

/-- **TOWER FUNCTORIALITY OF THE ARTIN MAP** (PROVEN 2026-07-31): restriction to an
intermediate field `M` carries `artinMap K L` to `artinMap K M`.

`restrictNormalHom M` is a `MonoidHom` for the AMBIENT group instances, and
`galCommGroup` keeps `mul`/`one`/`zpow` definitionally ambient, so it passes
through the `∏ᶠ` by `MonoidHom.map_finprod` with the support finiteness already
proven (`finite_mulSupport_zpow_count`). Termwise it is `restrictNormalHom_frobAt`
at the chosen prime above `v`, followed by `frobAtBelow_eq_frobAt` over `M` to
recognise the result as `M`'s own Artin symbol at `v` — the two files' choices of
prime above `v` are unrelated, and `habelM` is exactly what makes that irrelevant. -/
theorem restrictNormalHom_artinMap [IsGalois K M]
    (habel : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (habelM : ∀ a b : M ≃ₐ[K] M, a * b = b * a)
    (hunr : ∀ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime), Q ≠ ⊥ → Algebra.IsUnramifiedAt (𝓞 K) Q)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    AlgEquiv.restrictNormalHom M (artinMap K L habel I) = artinMap K M habelM I := by
  letI := galCommGroup K L habel
  letI := galCommGroup K M habelM
  have hbelow : ∀ v : HeightOneSpectrum (𝓞 K),
      AlgEquiv.restrictNormalHom M (frobAtBelow K L v) = frobAtBelow K M v := by
    intro v
    haveI : Algebra.IsUnramifiedAt (𝓞 K) (primeAbove K L v) :=
      hunr _ (isMaximal_primeAbove K L v).isPrime (primeAbove_ne_bot K L v)
    rw [frobAtBelow, restrictNormalHom_frobAt K L M (primeAbove K L v)]
    haveI : ((primeAbove K L v).under (𝓞 M)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
    exact (frobAtBelow_eq_frobAt K M habelM v ((primeAbove K L v).under (𝓞 M))
      ((Ideal.under_under (primeAbove K L v)).trans (under_primeAbove K L v))).symm
  show AlgEquiv.restrictNormalHom M (∏ᶠ v : HeightOneSpectrum (𝓞 K),
      frobAtBelow K L v ^ FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K)) = _
  rw [MonoidHom.map_finprod _ (finite_mulSupport_zpow_count K (frobAtBelow K L) _)]
  refine finprod_congr fun v => ?_
  rw [map_zpow, hbelow v]

omit [IsGalois K L] in
/-- **UNRAMIFIEDNESS AT THE FINITE PRIMES DESCENDS TO AN INTERMEDIATE FIELD**
(PROVEN 2026-07-31). Going-up supplies a maximal `Q` of `𝓞 L` over the given
nonzero prime `q` of `𝓞 M` (a nonzero prime of the Dedekind domain `𝓞 M` is
maximal), and `Algebra.IsUnramifiedAt.of_liesOver` transports unramifiedness over
`𝓞 K` from `Q` down to `q`. -/
theorem isUnramifiedAt_of_intermediateField
    (hunr : ∀ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime), Q ≠ ⊥ → Algebra.IsUnramifiedAt (𝓞 K) Q)
    (q : Ideal (𝓞 M)) (hqp : q.IsPrime) (hq0 : q ≠ ⊥) :
    Algebra.IsUnramifiedAt (𝓞 K) q := by
  haveI := hqp
  haveI : q.IsMaximal := hqp.isMaximal hq0
  obtain ⟨Q, hQ, hQ'⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 L) q
    (le_trans (le_of_eq
      ((RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective (𝓞 M) (𝓞 L))))
      bot_le)
  haveI := hQ
  haveI : Q.IsPrime := hQ.isPrime
  haveI : Q.LiesOver q := ⟨hQ'.symm⟩
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    exact hq0 (by simpa using hQ'.symm)
  haveI := hunr Q inferInstance hQ0
  exact Algebra.IsUnramifiedAt.of_liesOver (𝓞 K) q Q

end Tower

/-- **ARTIN RECIPROCITY AT MODULUS `1` FOR CYCLIC EXTENSIONS: for `L/K` finite
CYCLIC, unramified at every finite prime and at every infinite place, the Artin map
kills the PRINCIPAL ideals** (SORRY LEAF, cut 2026-07-31 out of
`artinMap_toPrincipalIdeal` below, which is now PROVEN over it).

**THIS IS ONE OF THE TWO PLACES WHERE THE MISSING MATHEMATICS IS**, the other being
the density input of Chebotarev. Everything else in this cluster — the construction
of the Artin map, its tower functoriality, the reduction of the abelian case to this
one, the descent to `Cl(𝓞 K)`, the norm clause of the consumer, its surjectivity,
and the Hilbert-class-field material two files down — is proven over it.

Unwound: if `(x) = ∏ 𝔭ᵢ^{aᵢ}` is the factorisation of a principal fractional ideal
of `𝓞 K`, then `∏ Frob_{𝔭ᵢ}^{aᵢ} = 1` in the cyclic group `Gal(L/K)`.

**FAITHFULNESS.** Inherited from `artinMap_toPrincipalIdeal`, whose audit applies
verbatim with one extra hypothesis: `hcyc` only restricts the extension, so it can
only make the statement weaker, and the `K = ℚ(√3)` counterexample showing
`[IsUnramifiedAtInfinitePlaces K L]` to be load-bearing is itself CYCLIC (the narrow
Hilbert class field there is quadratic), so it refutes this leaf too if that
hypothesis is dropped. `habel` is implied by `hcyc` and is kept because `artinMap`
cannot be stated without it. The degenerate case `L = K` is fine.

**ROUTE, AND ONE ROUTE THAT IS RULED OUT.** Neukirch VI; Childress ch. 4–5; Lang
*ANT* ch. X; Cassels–Fröhlich ch. VII. Artin's own proof adjoins `ζ_m`, where the
Artin symbol is computable (`Frob_𝔭 : ζ ↦ ζ ^ N𝔭`, so reciprocity for `ℚ(ζ_m)/ℚ`
is the elementary congruence `∏ pᵢ^{aᵢ} ≡ a (mod m)`), and descends by the
translation theorem. See the docstring of `exists_classField_of_subgroup` in
`Fermat/FLT/NumberField/UnramifiedClassFieldExistence.lean` for the PARI/GP
refutation of the naive "descend an unramified abelian extension from `K(ζ_ℓ)`"
cut, which must not be re-attempted.

**WHY "THE SECOND INEQUALITY PLUS THE FIRST" IS NOT A CUT OF THIS LEAF**
(checked 2026-07-31; recorded because the docstring this replaces proposed exactly
that as the shape a real cut would take, and formalising the second inequality in
the expectation that it closes this node would be a wasted development).

Write `A` for `artinMap`, `T = ker A`, `S = A(P_K)`, `n = [L : K]`. Grant every
input that route offers:

* `N_{L/K} I_L ⊆ T` — in substance already PROVEN here (`frobAt_pow_inertiaDeg`
  gives `Frob_𝔭 ^ f = 1`, and `N_{L/K} Q = 𝔭 ^ f`);
* `A` surjective — Chebotarev, so `[I_K : T] = n`;
* `[I_K : P_K · N_{L/K} I_L] = n` — the second inequality `≤ n` together with the
  first `≥ n`.

The conclusion wanted is `S = 1`, i.e. `P_K ⊆ T`. But `T` and `P_K · N_{L/K} I_L`
are now two subgroups of `I_K` of the SAME index `n`, and equal index does not make
two subgroups nested. All the counting yields is
`[I_K : P_K · N_{L/K} I_L] ≥ n / |S|`, which every `S` satisfies; so `S ≠ 1` is not
contradicted, and no refinement of the two inequalities can contradict it, since
they constrain only that one index. The deep content of reciprocity is the
statement `S = 1` itself, and it is not an index computation.

**A SECOND DEAD END, for the same reason it looks attractive.** The only consumer of
this whole cluster is `[L : K] ≤ h_K` for `L/K` abelian everywhere-unramified
(`finrank_le_card_classGroup_of_unramified_abelian` in
`Fermat/FLT/Modularity/Interface.lean`), and that is the FIRST inequality, which
classically needs no reciprocity and no Chebotarev — only a Herbrand-quotient
computation, and only for CYCLIC extensions. It does not follow for abelian `L/K` by
dévissage along a chain of cyclic steps `K ⊂ F₁ ⊂ ⋯ ⊂ L`: each step gives
`[Fᵢ₊₁ : Fᵢ] ≤ h_{Fᵢ}`, and multiplying them bounds `[L : K]` by `∏ h_{Fᵢ}`, not by
`h_K`. Closing that gap would need `h_{F₁} ≤ h_K / [F₁ : K]` for an everywhere
unramified `F₁/K`, which is not a theorem (class field towers do not have decreasing
class numbers). The abelian statement really does go through the Artin map.

**The check that would refute this leaf**: a finite cyclic `L/K` unramified at every
finite prime and every infinite place, an `x : Kˣ`, and a factorisation of `(x)`
into primes whose Frobenius elements do not multiply to `1`. -/
theorem artinMap_toPrincipalIdeal_of_isCyclic [IsUnramifiedAtInfinitePlaces K L]
    (habel : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (hunr : ∀ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 K) Q)
    (hcyc : IsCyclic (L ≃ₐ[K] L)) (x : Kˣ) :
    artinMap K L habel (toPrincipalIdeal (𝓞 K) K x) = 1 :=
  sorry

/-- **ARTIN RECIPROCITY AT MODULUS `1`: for `L/K` finite abelian, unramified at
every finite prime and at every infinite place, the Artin map kills the PRINCIPAL
ideals** (SORRY LEAF, cut 2026-07-30 out of `exists_classGroupHom_eq_frobAt`
below, which is now proven over it).

**THIS IS ONE OF THE TWO PLACES WHERE THE MISSING MATHEMATICS IS**, the other
being `closure_frobAt_eq_top` below. Everything else in this cluster — the
construction of the Artin map itself, its descent to `Cl(𝓞 K)`, the norm clause
of the consumer, its surjectivity, the whole second inequality, and the
Hilbert-class-field material two files down — is proven over these two.

**What is being asked, and what is NOT.** Classically the Artin map on ideals is
`𝔭 ↦ Frob_𝔭`, extended multiplicatively. Its existence as a map on IDEALS is
bookkeeping and is now DONE (`artinMap`, together with `artinMap_apply_coe`);
what is deep — and all that is left — is that it kills the principal ideals, so
that it descends to `Cl(𝓞 K)`. Surjectivity is deliberately NOT part of this: it
is a genuinely separate input (`closure_frobAt_eq_top`), and bundling the two is
what made the original single-leaf cut opaque.

Unwound, the statement is: if `(x) = ∏ 𝔭ᵢ^{aᵢ}` is the factorisation of a
principal fractional ideal of `𝓞 K`, then `∏ Frob_{𝔭ᵢ}^{aᵢ} = 1` in `Gal(L/K)`.

**`IsUnramifiedAtInfinitePlaces` is load-bearing.** It is what makes `1` an
admissible modulus, i.e. what makes ALL principal ideals — not merely those with
a totally positive generator — lie in the kernel. Deleting it makes the leaf
false: `K = ℚ(√3)` has `h_K = 1`, so `Cl(𝓞 K)` is trivial, while its narrow
Hilbert class field `L` is abelian of degree `2` over `K`, unramified at every
FINITE prime, and has primes with nontrivial Frobenius. Concretely there, a
totally negative unit generates a principal ideal whose Artin symbol is the
nontrivial element. The same counterexample is recorded, for the consumer's
conclusion rather than for this one, in
`finrank_le_index_relNormClassSubgroup`.

**`habel` is load-bearing FORMALLY, not just mathematically** — see
`frobAt_eq_frobAt_of_comm`: without it "the" Frobenius at `𝔭` is a whole
conjugacy class, and `artinMap` cannot even be DEFINED (a homomorphism out of an
abelian group has abelian image).

**Route.** Neukirch VI (6.9) and (7.3) and the sections preceding them; Childress
ch. 4–5; Lang *ANT* ch. X; Cassels–Fröhlich ch. VII. The classical proof reduces
to a congruence subgroup of prime exponent, adjoins `ζ_ℓ`, runs Kummer theory
over `K(ζ_ℓ)` and descends by the translation theorem. See the docstring of
`exists_classField_of_subgroup` in
`Fermat/FLT/NumberField/UnramifiedClassFieldExistence.lean` for the PARI/GP
refutation of the naive "descend an unramified abelian extension from `K(ζ_ℓ)`"
cut, which must not be re-attempted.

**The check that would refute it**: a finite abelian `L/K` unramified at every
finite prime and every infinite place, an `x : Kˣ`, and a factorisation of `(x)`
into primes whose Frobenius elements do not multiply to `1`.

**STATUS 2026-07-31 — re-audited, faithful, and NOT usefully decomposable by the
one cut that suggests itself.** Recorded so the next owner does not spend the
cycle finding this out, and stated with the reasoning rather than as a verdict,
because the corresponding verdict on `closure_frobAt_eq_top` was overturned the
same day (see the `Chebotarev` section) and this one should be re-examined too if
anyone sees past it.

*Faithfulness.* All four hypotheses were re-checked. `[IsGalois K L]` comes from
the ambient variable block; `habel` makes `Gal(L/K)` abelian, without which
`artinMap` is not even definable; `hunr` is unramifiedness at every nonzero prime
of `𝓞 L`, and `[IsUnramifiedAtInfinitePlaces K L]` at every infinite place. Under
all four, `L` sits inside the Hilbert class field of `K`, so the statement is the
classical reciprocity law at modulus `1`, and it is TRUE. The degenerate case
`L = K` is fine (`Gal(L/K)` trivial).

*The cut that does NOT work.* The obvious analogue of what worked for Chebotarev
is the cyclic reduction: `Gal(L/K)` abelian decomposes as a product of cyclic
groups, so `g = 1` can be tested in the cyclic quotients `Gal(M/K)`, `M = L^H`,
and one is left with reciprocity for CYCLIC `L/K`. That is a correct reduction,
but it is not progress. It costs the tower functoriality of the Artin symbol
(`frobAtBelow K M v = restrictNormalHom M (frobAtBelow K L v)`), the compatibility
of `artinMap` with `restrictNormalHom` through the `∏ᶠ`, and the structure theorem
for finite abelian groups — several hundred lines — and hands back a leaf which is
where every classical treatment spends essentially all of its effort. The
Chebotarev cut was worth making because it removed ALL the Galois-theoretic
bookkeeping between the leaf and a standard analytic statement; this one removes
none of the mathematics and adds bookkeeping.

*What a real cut would have to look like.* Something that turns this into a
statement not mentioning `frobAt` or `Gal(L/K)` — i.e. the second inequality
(`[I_K : P_K N I_L] ≤ [L : K]`) plus the first, or a Kummer-theoretic statement
over `K(ζ_ℓ)`. Note the warning in `exists_classField_of_subgroup`
(`Fermat/FLT/NumberField/UnramifiedClassFieldExistence.lean`) about the naive
"descend from `K(ζ_ℓ)`" cut, which has a PARI/GP refutation and must not be
re-attempted. Beware also the weakening trap: "`Frob_𝔭 = 1` for every PRINCIPAL
prime `𝔭`" is a strictly weaker statement (it constrains only the primes, not the
products), so it does not suffice as a cut here. -/
theorem artinMap_toPrincipalIdeal [IsUnramifiedAtInfinitePlaces K L]
    (habel : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (hunr : ∀ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 K) Q) (x : Kˣ) :
    artinMap K L habel (toPrincipalIdeal (𝓞 K) K x) = 1 := by
  by_contra hne
  obtain ⟨H, hnorm, hmem, hcyc⟩ := exists_subgroup_notMem_isCyclic_quotient habel hne
  haveI := hnorm
  haveI : IsUnramifiedAtInfinitePlaces K (IntermediateField.fixedField H) :=
    IsUnramifiedAtInfinitePlaces.bot (k := K)
      (K := ↥(IntermediateField.fixedField H)) (F := L)
  have habelM : ∀ a b : (IntermediateField.fixedField H) ≃ₐ[K]
      (IntermediateField.fixedField H), a * b = b * a := by
    intro a b
    obtain ⟨a', rfl⟩ := AlgEquiv.restrictNormalHom_surjective
      (K₁ := ↥(IntermediateField.fixedField H)) (E := L) a
    obtain ⟨b', rfl⟩ := AlgEquiv.restrictNormalHom_surjective
      (K₁ := ↥(IntermediateField.fixedField H)) (E := L) b
    rw [← map_mul, ← map_mul, habel]
  have hcycM : IsCyclic ((IntermediateField.fixedField H) ≃ₐ[K]
      (IntermediateField.fixedField H)) :=
    isCyclic_of_surjective (IsGalois.normalAutEquivQuotient H)
      (IsGalois.normalAutEquivQuotient H).surjective
  have hunrM : ∀ (q : Ideal (𝓞 (IntermediateField.fixedField H))) (_ : q.IsPrime), q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 K) q :=
    fun q hq hq0 => isUnramifiedAt_of_intermediateField K L _ hunr q hq hq0
  have key := restrictNormalHom_artinMap K L (IntermediateField.fixedField H) habel habelM hunr
    (toPrincipalIdeal (𝓞 K) K x)
  rw [artinMap_toPrincipalIdeal_of_isCyclic K (IntermediateField.fixedField H) habelM hunrM
    hcycM x] at key
  refine hmem ?_
  rw [← IntermediateField.fixingSubgroup_fixedField H,
    ← IntermediateField.restrictNormalHom_ker (IntermediateField.fixedField H)]
  exact MonoidHom.mem_ker.mpr key

/-- **THE ARTIN SYMBOL DESCENDS TO THE IDEAL CLASS GROUP** (PROVEN 2026-07-30 over
`artinMap_toPrincipalIdeal`).

Pure quotient bookkeeping now: `ClassGroup.equiv K` identifies `Cl(𝓞 K)` with
`(FractionalIdeal (𝓞 K)⁰ K)ˣ` modulo the principal ideals for the fraction field
`K` at hand (mathlib's `ClassGroup` is defined over `FractionRing (𝓞 K)`, and
this is the transport), and `artinMap_toPrincipalIdeal` says `artinMap` kills
that subgroup, so `QuotientGroup.lift` applies. The value at the class of a prime
is read off with `ClassGroup.equiv_mk0` and `artinMap_apply_coe`.

Surjectivity is deliberately NOT asserted here — that is `closure_frobAt_eq_top`,
and the consumer assembles the two. -/
theorem exists_classGroupHom_eq_frobAt [IsUnramifiedAtInfinitePlaces K L]
    (habel : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (hunr : ∀ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 K) Q) :
    ∃ φ : ClassGroup (𝓞 K) →* (L ≃ₐ[K] L),
      ∀ (Q : Ideal (𝓞 L)) (_ : Q.IsMaximal) (J : (Ideal (𝓞 K))⁰),
        (J : Ideal (𝓞 K)) = Q.under (𝓞 K) → φ (ClassGroup.mk0 J) = frobAt K L Q := by
  have hker : ∀ I ∈ (toPrincipalIdeal (𝓞 K) K).range, artinMap K L habel I = 1 := by
    rintro I ⟨x, rfl⟩
    exact artinMap_toPrincipalIdeal K L habel hunr x
  refine ⟨(QuotientGroup.lift _ (artinMap K L habel) hker).comp
    (ClassGroup.equiv (R := 𝓞 K) K).toMonoidHom, ?_⟩
  intro Q hQ J hJ
  haveI := hQ
  haveI : Q.IsPrime := hQ.isPrime
  have hJ0 : (J : Ideal (𝓞 K)) ≠ ⊥ := by
    simpa using mem_nonZeroDivisors_iff_ne_zero.mp J.2
  set v : HeightOneSpectrum (𝓞 K) :=
    ⟨Q.under (𝓞 K), inferInstance, by rw [← hJ]; exact hJ0⟩ with hv
  have hcoe : ((FractionalIdeal.mk0 K J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) = (v.asIdeal : Ideal (𝓞 K)) := by
    rw [FractionalIdeal.coe_mk0, hJ]
  have h1 : ((QuotientGroup.lift _ (artinMap K L habel) hker).comp
      (ClassGroup.equiv (R := 𝓞 K) K).toMonoidHom) (ClassGroup.mk0 J)
      = artinMap K L habel (FractionalIdeal.mk0 K J) := by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ClassGroup.equiv_mk0,
      QuotientGroup.mk'_apply, QuotientGroup.lift_mk]
  rw [h1, artinMap_apply_coe K L habel v _ hcoe]
  exact frobAtBelow_eq_frobAt K L habel v Q rfl

end ArtinMap

section Chebotarev

/-! ### The fixed-field reduction of Chebotarev

`closure_frobAt_eq_top` is PROVEN below over a single sorried input,
`finrank_eq_one_of_forall_inertiaDeg_eq_one`, which is the classical density
statement "a nontrivial extension of number fields has infinitely many primes that
do not split completely". Everything between the two — the fixed field of the
subgroup generated by the Frobenius elements, the fact that every prime unramified
in `L` splits completely in it, and the finiteness of the exceptional set — is
proven here.

This reverses the "deliberately NOT decomposed" verdict recorded in the docstring
of `closure_frobAt_eq_top` on 2026-07-30. That verdict was right about the cut it
considered (the contrapositive "for every proper `H` there is an unramified `Q`
with `frobAt K L Q ∉ H`", which is indeed noise) and right about which
ingredients the fixed-field reduction needs; it was wrong that they are missing.
Two of its three named obstacles do not have to be paid at all:

* it is NOT necessary to know that the subgroup generated is NORMAL, hence not
  necessary to transport `Algebra.IsUnramifiedAt` along a `𝓞 K`-automorphism of
  `𝓞 L`. Normality would be needed to talk about `frobAt K M` for the fixed field
  `M`; but the only thing wanted about `M` is that its primes have residue degree
  `1`, and that is read off directly from the congruence `σ x ≡ x ^ (N𝔭) (mod Q)`
  restricted to `𝓞 M`. No Galois hypothesis on `M/K` is used anywhere below.
* consequently no functoriality of `arithFrobAt` down a tower is needed either.
  `Ideal.under_under` and `Ideal.mem_under` do all the tower bookkeeping.

What the reduction does need and mathlib does have: `NumberField.of_intermediateField`
(an intermediate field of a number field is a number field),
`RingOfIntegers.inst_isScalarTower` (so `𝓞 K ⊆ 𝓞 M ⊆ 𝓞 L` is a tower),
`IntermediateField.fixingSubgroup_fixedField` (Galois correspondence) and
`not_dvd_differentIdeal_iff` (a prime is unramified iff it does not divide the
different), which is what makes the exceptional set finite. -/

/-- **A RESIDUE-FIELD CRITERION FOR `f = 1`: if every element of `𝓞 F ⧸ q` is a
root of `X ^ (N 𝔭) - X`, where `𝔭 = q ∩ 𝓞 k`, then `f(q | 𝔭) = 1`** (PROVEN
2026-07-31).

This is the `→` half of `frobAt_eq_one_iff_inertiaDeg_eq_one` with the Frobenius
stripped out of it. It is stated for an arbitrary finite extension `F/k` of number
fields — no Galois hypothesis, no automorphism — because the reduction of
Chebotarev below applies it to the fixed field of a subgroup, where no Galois
structure over `k` is available (and none is needed).

**Chain.** The residue field `𝓞 F ⧸ q` has `(N𝔭) ^ f` elements
(`Ideal.cardQuot_pow_inertiaDeg`), it is cyclic, so its unit group has exponent
dividing `N𝔭 - 1` (`IsCyclic.exponent_eq_card`), giving `(N𝔭) ^ f - 1 ∣ N𝔭 - 1`;
with `N𝔭 ≥ 2` that forces `f = 1`. -/
theorem inertiaDeg_eq_one_of_forall_pow_natCard
    (k F : Type*) [Field k] [NumberField k] [Field F] [NumberField F] [Algebra k F]
    (q : Ideal (𝓞 F)) [q.IsMaximal]
    (h : ∀ z : 𝓞 F ⧸ q, z ^ (Nat.card (𝓞 k ⧸ q.under (𝓞 k))) = z) :
    q.inertiaDeg (𝓞 k) = 1 := by
  classical
  letI := Ideal.Quotient.field q
  letI : Fintype (𝓞 F ⧸ q) := Fintype.ofFinite _
  set p : ℕ := Nat.card (𝓞 k ⧸ q.under (𝓞 k)) with hp
  set f : ℕ := q.inertiaDeg (𝓞 k) with hf
  have hcard : Nat.card (𝓞 F ⧸ q) = p ^ f := by
    rw [hp, hf, ← Submodule.cardQuot_apply, ← Submodule.cardQuot_apply]
    exact (Ideal.cardQuot_pow_inertiaDeg (q.under (𝓞 k)) q).symm
  have hcard2 : 2 ≤ p ^ f := by
    rw [← hcard, Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hp2 : 2 ≤ p := by
    rcases Nat.lt_or_ge p 2 with hcon | hcon
    · have : p ^ f ≤ 1 ^ f := Nat.pow_le_pow_left (by omega) f
      simp only [one_pow] at this
      omega
    · exact hcon
  have hu : ∀ u : (𝓞 F ⧸ q)ˣ, u ^ (p - 1) = 1 := by
    intro u
    refine Units.ext ?_
    have hne : (u : 𝓞 F ⧸ q) ≠ 0 := u.ne_zero
    have hmul : (u : 𝓞 F ⧸ q) ^ (p - 1) * (u : 𝓞 F ⧸ q) = 1 * (u : 𝓞 F ⧸ q) := by
      rw [one_mul, ← pow_succ, Nat.sub_add_cancel (by omega), h]
    simpa using mul_right_cancel₀ hne hmul
  have hdvd : Nat.card (𝓞 F ⧸ q)ˣ ∣ p - 1 := by
    rw [← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one hu
  rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hcard] at hdvd
  by_contra hne
  have hf0 : f ≠ 0 := by
    rintro h0
    rw [h0, pow_zero] at hcard2
    omega
  have hf2 : 2 ≤ f := by omega
  have hpow : p ^ 2 ≤ p ^ f := Nat.pow_le_pow_right (by omega) hf2
  have hsq : p < p ^ 2 := by nlinarith [sq_nonneg p]
  have hle : p ^ f - 1 ≤ p - 1 := Nat.le_of_dvd (by omega) hdvd
  omega

omit [IsGalois K L] in
/-- **The primes of `𝓞 K` that ramify in `L`**: those carrying a prime of `𝓞 L`
at which `𝓞 L / 𝓞 K` is not unramified.

Stated with `Q.IsPrime` rather than `Q.IsMaximal` so that it matches the shape of
`Algebra.IsUnramifiedAt`; the zero ideal is harmless, being unramified in
characteristic zero (`Algebra.isUnramifiedAt_bot`). -/
def ramifiedBelow : Set (Ideal (𝓞 K)) :=
  {𝔭 | ∃ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime),
    Q.under (𝓞 K) = 𝔭 ∧ ¬ Algebra.IsUnramifiedAt (𝓞 K) Q}

omit [IsGalois K L] in
/-- **ONLY FINITELY MANY PRIMES OF `𝓞 K` RAMIFY IN `L`** (PROVEN 2026-07-31).

A prime `Q` of `𝓞 L` is ramified exactly when it divides the different ideal
`𝔡_{L/K}` (`dvd_differentIdeal_iff`), the different is nonzero
(`differentIdeal_ne_bot`), and a nonzero ideal of a Dedekind domain has only
finitely many prime divisors (`Ideal.finite_factors`). The set below is the image
of that finite set under `Ideal.under`.

The only friction is that both mathlib lemmas are stated with the hypothesis
`Algebra.IsSeparable (FractionRing (𝓞 K)) (FractionRing (𝓞 L))`, and there is no
`Algebra (FractionRing (𝓞 K)) (FractionRing (𝓞 L))` instance to state it against.
It is built here with `FractionRing.liftAlgebra`, whose scalar tower plus
`isAlgebraic_of_isFractionRing` gives algebraicity, hence separability in
characteristic zero. -/
theorem finite_ramifiedBelow : (ramifiedBelow K L).Finite := by
  classical
  letI : Algebra (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) :=
    FractionRing.liftAlgebra (𝓞 K) (FractionRing (𝓞 L))
  haveI : IsScalarTower (𝓞 K) (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) :=
    FractionRing.isScalarTower_liftAlgebra _ _
  haveI : Algebra.IsAlgebraic (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) :=
    isAlgebraic_of_isFractionRing (𝓞 K) (𝓞 L) (FractionRing (𝓞 K)) (FractionRing (𝓞 L))
  haveI : Algebra.IsIntegral (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) :=
    Algebra.IsAlgebraic.isIntegral
  haveI : Algebra.IsSeparable (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) := inferInstance
  have hne : differentIdeal (𝓞 K) (𝓞 L) ≠ 0 := differentIdeal_ne_bot
  have hfin : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 L) |
      v.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 L)}.Finite := Ideal.finite_factors hne
  refine Set.Finite.subset (hfin.image (fun v => v.asIdeal.under (𝓞 K))) ?_
  rintro 𝔭 ⟨Q, hQp, rfl, hQr⟩
  haveI := hQp
  have hQne : Q ≠ ⊥ := by
    rintro rfl
    exact hQr Algebra.isUnramifiedAt_bot
  exact ⟨⟨Q, hQp, hQne⟩, dvd_differentIdeal_iff.mpr hQr, rfl⟩

/-- **THE DENSITY INPUT OF CHEBOTAREV, AND THE ONLY THING LEFT OF IT HERE: a
finite extension of number fields in which all but finitely many primes of the
base split completely is trivial** (SORRY LEAF, cut 2026-07-31 out of
`closure_frobAt_eq_top` below, which is now PROVEN over it).

Only the residue degrees are constrained, not the ramification indices: the
hypothesis is `f(q | 𝔭) = 1` for every maximal `q` of `𝓞 F` whose contraction
avoids the finite set `S`. That is weaker than "splits completely" and makes the
leaf STRONGER, which is what the consumer below needs (it controls `f` and never
touches `e`).

**Why it is true.** Let `N` be the Galois closure of `F/k`, `G = Gal(N/k)`,
`H = Gal(N/F)`. For `𝔭` unramified in `N` the primes of `F` above `𝔭` are the
orbits of `⟨Frob_𝔓⟩` on `G/H`, with `f(q | 𝔭)` the orbit length; so all residue
degrees are `1` exactly when `Frob_𝔓` lies in the normal core `⋂_g g H g⁻¹`. If
`F ≠ k` then `H ≠ G`, so the core is a proper normal subgroup, and Chebotarev
supplies infinitely many `𝔭` whose Frobenius class avoids it — more than the
finitely many that `S` may exclude. Hence `H = G` and `[F : k] = 1`.

**What it needs that the pin does not have.** Dedekind zeta functions, their
simple pole at `s = 1`, and the nonvanishing of `L(1, χ)`: this is the analytic
half of class field theory and it must be built, not cited (mathlib at this pin
has Dirichlet's theorem on primes in arithmetic progressions, i.e. the case
`k = ℚ`, `N` cyclotomic, but nothing over a general number field). The weaker
"infinitely many primes do not split completely", which is all that is used here,
is not known to have an elementary proof either.

**The finiteness hypothesis is load-bearing.** Without it the statement is false
for a trivial reason: take `S` to be everything, and the hypothesis becomes
vacuous while `F` may be any extension. With `S` finite the hypothesis still
speaks about infinitely many primes, since `𝓞 k` has infinitely many maximal
ideals.

**The check that would refute it**: a nontrivial finite extension `F/k` of number
fields and a finite set `S` of primes of `𝓞 k` such that every maximal ideal of
`𝓞 F` contracting outside `S` has residue degree `1` over `𝓞 k`. -/
theorem finrank_eq_one_of_forall_inertiaDeg_eq_one
    (k F : Type*) [Field k] [NumberField k] [Field F] [NumberField F] [Algebra k F]
    (S : Set (Ideal (𝓞 k))) (hS : S.Finite)
    (h : ∀ q : Ideal (𝓞 F), q.IsMaximal → q.under (𝓞 k) ∉ S → q.inertiaDeg (𝓞 k) = 1) :
    Module.finrank k F = 1 :=
  sorry

end Chebotarev

/-- **CHEBOTAREV, IN THE ONLY FORM THIS DEVELOPMENT NEEDS: the Frobenius elements
of the unramified primes GENERATE `Gal(L/K)`** (PROVEN 2026-07-31 over the single
density leaf `finrank_eq_one_of_forall_inertiaDeg_eq_one`; itself cut 2026-07-30
out of `exists_surjective_classGroupHom_aut_of_unramified_abelian` in
`Fermat/FLT/NumberField/UnramifiedClassFieldBound.lean`).

This is the surjectivity half of the Artin map, separated from the reciprocity
half (`exists_classGroupHom_eq_frobAt`) because the two are independent inputs with
independent classical proofs: reciprocity is the Verschiebungssatz/Kummer
argument, this is a density statement.

**Why the generating set is restricted to UNRAMIFIED primes.** At a ramified `Q`
the Frobenius is only canonical modulo inertia and `arithFrobAt` makes an
arbitrary choice, so a statement quantified over all maximal `Q` would be a
statement about that choice rather than about `L/K`. Restricting to the
unramified primes makes this the honest classical content and STRENGTHENS the
leaf; the consumers all hold unramifiedness at every finite prime anyway, so
nothing is lost.

**What the classical proof needs, and what the pin has.** The usual argument is:
let `H` be the subgroup generated, `M = L^H`; every prime of `K` unramified in
`L` splits completely in `M`, and a nontrivial extension in which almost every
prime splits completely is impossible. The last step is Frobenius/Chebotarev
density, i.e. Dedekind zeta functions and the nonvanishing of `L(1, χ)` — absent
from the pin, along with ray class groups, the Artin map, and any Dirichlet
density material. So this must be built, not cited. Note this leaf needs NO
abelian hypothesis and NO archimedean hypothesis, which is the sense in which it
is the smaller of the two.

**STATUS 2026-07-30 — audited and faithful.** The statement was re-checked
against the mathlib notion of `Algebra.IsUnramifiedAt` (at a maximal `Q` of `𝓞 L`
over a number field it is `e(Q | 𝔭) = 1`, the residue extension being
automatically separable), including the degenerate case `L = K`, where `Gal(L/K)`
is trivial and the conclusion holds vacuously. It is TRUE, and it is deep.

**STATUS 2026-07-31 — the fixed-field reduction was carried out after all.** The
2026-07-30 note recorded three obstacles to it; two of them turned out not to
exist, and the third IS the residual leaf. See the `Chebotarev` section above for
the correction in detail. The short version: the reduction never needs the
subgroup to be NORMAL, so it needs neither the transport of
`Algebra.IsUnramifiedAt` along an automorphism (obstacle 1) nor functoriality of
`arithFrobAt` down a tower (obstacle 2) — the fixed field `M` is used only as a
ring, `𝓞 K ⊆ 𝓞 M ⊆ 𝓞 L`, and the residue degree of `Q ∩ 𝓞 M` is read off from the
Frobenius congruence restricted to `𝓞 M`. Obstacle 3, the density input, is
`finrank_eq_one_of_forall_inertiaDeg_eq_one`.

The 2026-07-30 note was right about the OTHER candidate cut, and that judgement
stands: "for every proper subgroup `H` there is an unramified `Q` with
`frobAt K L Q ∉ H`" is the contrapositive, and trades one leaf for an equivalent
one. What makes the fixed-field cut progress and that one noise is that the
residual statement here mentions no Frobenius, no Galois group and no `arithFrobAt`
— it is a statement about residue degrees in an arbitrary finite extension of
number fields, which is the form a Dedekind-zeta development actually produces.

**Proof.** Let `H` be the subgroup generated and `M = L^H` its fixed field. Let
`q` be a maximal ideal of `𝓞 M` whose contraction `𝔭` to `𝓞 K` is unramified in
`L`, and pick `Q` of `𝓞 L` above `q`. Then `σ = frobAt K L Q` lies in `H`, so it
fixes `M` pointwise; and for `y ∈ 𝓞 M` the defining congruence
`σ y ≡ y ^ (N𝔭) (mod Q)` therefore reads `y ^ (N𝔭) ≡ y (mod Q)`, hence
`(mod q)` since `q = Q ∩ 𝓞 M`. Every element of the residue field `𝓞 M ⧸ q` is
thus a root of `X ^ (N𝔭) - X`, so `f(q | 𝔭) = 1`
(`inertiaDeg_eq_one_of_forall_pow_natCard`). Only finitely many `𝔭` ramify in `L`
(`finite_ramifiedBelow`), so the density leaf gives `[M : K] = 1`, i.e. `M = ⊥`,
and the Galois correspondence (`IntermediateField.fixingSubgroup_fixedField`)
turns that into `H = ⊤`.

**Non-vacuity.** For `L/K` nontrivial the conclusion is a genuine assertion: the
right-hand side `⊤` is not the closure of the empty set, and it fails for the
subgroup generated by any proper subset of the conjugacy classes.

**The check that would refute it**: a finite Galois extension `L/K` of number
fields, nontrivial, in which every prime of `𝓞 K` unramified in `L` splits
completely. -/
theorem closure_frobAt_eq_top :
    Subgroup.closure {σ : L ≃ₐ[K] L | ∃ (Q : Ideal (𝓞 L)) (_ : Q.IsMaximal),
      Algebra.IsUnramifiedAt (𝓞 K) Q ∧ σ = frobAt K L Q} = ⊤ := by
  classical
  set H : Subgroup (L ≃ₐ[K] L) :=
    Subgroup.closure {σ : L ≃ₐ[K] L | ∃ (Q : Ideal (𝓞 L)) (_ : Q.IsMaximal),
      Algebra.IsUnramifiedAt (𝓞 K) Q ∧ σ = frobAt K L Q} with hH
  set M : IntermediateField K L := IntermediateField.fixedField H with hM
  -- every prime of `𝓞 M` whose contraction is unramified in `L` has residue degree one
  have hsplit : ∀ q : Ideal (𝓞 M), q.IsMaximal → q.under (𝓞 K) ∉ ramifiedBelow K L →
      q.inertiaDeg (𝓞 K) = 1 := by
    intro q hq hqS
    haveI := hq
    obtain ⟨Q, hQmax, hQu⟩ : ∃ Q : Ideal (𝓞 L), Q.IsMaximal ∧ Q.under (𝓞 M) = q :=
      Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 L) q
        (le_trans (le_of_eq ((RingHom.injective_iff_ker_eq_bot _).mp
          (FaithfulSMul.algebraMap_injective (𝓞 M) (𝓞 L)))) bot_le)
    haveI := hQmax
    have hunder : Q.under (𝓞 K) = q.under (𝓞 K) := by
      rw [← hQu, Ideal.under_under]
    have hQunr : Algebra.IsUnramifiedAt (𝓞 K) Q := by
      by_contra hcon
      haveI := hQmax.isPrime
      exact hqS ⟨Q, hQmax.isPrime, hunder, hcon⟩
    haveI := hQunr
    have hσH : frobAt K L Q ∈ H := by
      rw [hH]
      exact Subgroup.subset_closure ⟨Q, hQmax, hQunr, rfl⟩
    refine inertiaDeg_eq_one_of_forall_pow_natCard K M q ?_
    intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    -- the Frobenius lies in `H`, hence fixes the image of `y` in `𝓞 L`
    have hyM : ((algebraMap (𝓞 M) (𝓞 L) y : 𝓞 L) : L) ∈ M := (y : M).2
    have hfix : frobAt K L Q • (algebraMap (𝓞 M) (𝓞 L) y) = algebraMap (𝓞 M) (𝓞 L) y := by
      refine RingOfIntegers.ext ?_
      rw [coe_smul_ringOfIntegers]
      exact (IntermediateField.mem_fixedField_iff H _).mp hyM _ hσH
    have H1 : IsArithFrobAt (𝓞 K) (frobAt K L Q) Q := isArithFrobAt_frobAt K L Q
    have hmk : Ideal.Quotient.mk Q (frobAt K L Q • (algebraMap (𝓞 M) (𝓞 L) y))
        = (Ideal.Quotient.mk Q (algebraMap (𝓞 M) (𝓞 L) y)) ^
            (Nat.card (𝓞 K ⧸ Q.under (𝓞 K))) := H1.mk_apply _
    rw [hfix] at hmk
    rw [← hunder, ← map_pow, Ideal.Quotient.eq, ← hQu, Ideal.mem_under, map_sub, map_pow,
      ← Ideal.Quotient.eq, map_pow]
    exact hmk.symm
  have hrank :=
    finrank_eq_one_of_forall_inertiaDeg_eq_one K M _ (finite_ramifiedBelow K L) hsplit
  have hMbot : M = ⊥ := IntermediateField.finrank_eq_one_iff.mp hrank
  have hfix := IntermediateField.fixingSubgroup_fixedField (F := K) (E := L) H
  rw [← hM, hMbot, IntermediateField.fixingSubgroup_bot] at hfix
  exact hfix.symm

end NumberField
