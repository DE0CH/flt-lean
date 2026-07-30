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
* `NumberField.exists_surjective_classGroupHom_aut_of_unramified_abelian` — OPEN.
  The Artin map at modulus `1`, packaged as "there is a surjection
  `Cl(𝓞 K) ↠ Gal(L/K)` killing the norm classes". **This is where the missing
  mathematics is** (decomposed out of the leaf below on 2026-07-28).
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

/-- **THE ARTIN MAP AT MODULUS `1`, AS AN EXISTENTIAL: for `L/K` finite
abelian, unramified at every finite prime and at every infinite place, there
is a SURJECTIVE homomorphism `Cl(𝓞 K) →* Gal(L/K)` that kills the class of
every relative norm `N_{L/K} I`** (SORRY LEAF, cut 2026-07-28 out of
`finrank_le_index_relNormClassSubgroup` below — **this is where the missing
mathematics is**).

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
        (J : Ideal (𝓞 K)) = Ideal.relNorm (𝓞 K) I → φ (ClassGroup.mk0 J) = 1 :=
  sorry

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
