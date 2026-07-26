/-
GaloisRepresentation/HardlyRamified/ProfiniteLocalNoetherian.lean — own
work for the Fermat project (not vendored from the FLT project).

# A profinite local ring with finitely many points in each finite test ring
# is Noetherian, and its topology is the maximal-adic one

This module isolates, as pure commutative algebra, the FINITENESS half of
the deformation-theoretic core
`exists_isStrictlyUniversalOnFrames_of_deformationCondition`
(`Deformation.lean`): the step that upgrades the pro-object of the hardly
ramified deformation problem — which the Schlessinger construction
delivers as a mere PROFINITE local ring, an inverse limit of finite
levels — into an object of Mazur's category, i.e. a NOETHERIAN local ring
carrying the `𝔪`-adic topology and adically complete.

> Let `R` be a compact Hausdorff topological local `ℤ_ℓ`-algebra whose
> open ideals form a neighbourhood basis of `0`, with residue field the
> finite field `k` (a continuous surjection `π : R ↠ k`). Suppose that
> for EVERY finite local `ℤ_ℓ`-algebra `A` and every `πA : A →+* k` the
> set of continuous `ℤ_ℓ`-algebra maps `R → A` lifting `π` is FINITE.
> Then `R` is Noetherian, its topology is the `𝔪`-adic one, and it is
> `𝔪`-adically complete.

This is Mazur's `Φ_ℓ`-finiteness criterion (*Deforming Galois
representations*, MSRI Publ. 16 (1989), §1.2) in abstract form, or
equivalently the Noetherian clause of Schlessinger's Theorem 2.11
(*Functors of Artin rings*, Trans. AMS 130 (1968)): a pro-object of the
category of Artinian local rings is a genuine Noetherian complete local
ring exactly when its tangent space is finite dimensional. It is stated
here with the tangent space replaced by the (equivalent, and
arithmetically usable) hypothesis that `R` has only finitely many
continuous points in every finite test ring, because that is the form the
deformation-theoretic consumer can supply directly: there the points of
`R` in `A` inject into the hardly ramified framed representations over
`A`, of which there are finitely many by the restricted-ramification
finiteness leaf.

**Why the statement is not vacuous, and why the hypothesis is needed.**
A profinite local ring need NOT be Noetherian: take
`R = 𝔽_ℓ ⊕ ∏_{i ∈ ℕ} 𝔽_ℓ · x_i` with `x_i x_j = 0`, a compact local ring
with square-zero maximal ideal. Its continuous points in the dual numbers
`k[ε]` are the continuous `k`-functionals on `∏_{i} 𝔽_ℓ`, i.e. the
finitely supported ones — infinitely many, so the hypothesis fails, as it
must.

## The intended route (no power series, no Witt vectors)

1. **`𝔪` is open and `R ⧸ I` is finite for every open ideal `I`.**
   `𝔪 = ker π` because `π` is a surjection onto a field and `R` is local;
   `π` is continuous and `k` is discrete, so `𝔪` is open. An open ideal
   has discrete quotient (`QuotientRing.isOpenQuotientMap_mk`), and the
   quotient of a compact space is compact, so `R ⧸ I` is finite
   (`finite_of_compact_of_discrete`).
2. **Every open ideal contains a power of `𝔪`.** `R ⧸ I` is a finite
   local ring, so its maximal ideal is nilpotent (Artinian
   Jacobson-radical nilpotence — `Deformation.lean`'s
   `exists_maximalIdeal_pow_eq_bot`, restated here rather than imported,
   this module being upstream of that file), and `𝔪` maps into it.
3. **The cotangent space is finite dimensional.** Write `N` for the
   closure of `𝔪 ^ 2 + ℓ • R` (note `ℓ ∈ 𝔪`, `k` having characteristic
   `ℓ`) and `t = 𝔪 ⧸ N`, a profinite `k`-vector space. Because `k` is
   FINITE, hence perfect and monogenic, the complete local ring `R ⧸ N`
   contains a coefficient field: lift a generator of `kˣ` to a
   `(|k| − 1)`-st root of unity by Hensel's lemma (the same elementary
   route `Deformation.lean`'s `exists_coefficientRing_ringHom` takes, and
   the reason no Witt vectors are needed). Hence continuous
   `ℤ_ℓ`-algebra maps `R → k[ε]` lifting `π` correspond bijectively to
   continuous `k`-linear functionals on `t`. A profinite `k`-vector space
   with only finitely many continuous functionals is finite dimensional —
   an infinite dimensional one, being the inverse limit of its finite
   dimensional discrete quotients, has infinitely many. So `hhom` applied
   at `A = k[ε]` bounds `dim_k t`.
4. **`𝔪` is finitely generated.** Lift a `k`-basis of `t` to
   `x₁, …, x_g ∈ 𝔪`; topological Nakayama in the compact ring `R`
   (successive approximation, converging by compactness plus
   Hausdorffness) gives `𝔪 = (x₁, …, x_g)`.
5. **`IsAdic` and `IsAdicComplete`.** With `𝔪` finitely generated and
   open, every `𝔪 ^ n` is open, and by step 2 every open ideal contains
   some `𝔪 ^ n`: the two families are cofinal, so the given topology IS
   the `𝔪`-adic one. A compact Hausdorff topological group is complete,
   and separatedness is Hausdorffness, so `R` is `𝔪`-adically complete.
6. **Noetherian.**
   `CompleteLocalNoetherian.isNoetherianRing_of_isAdicComplete_of_fg`
   (Stacks 05GH / Matsumura Thm 8.4, proven in this project) turns steps
   4 and 5 into Noetherianity.

Only step 3 has genuine content beyond bookkeeping; it is where the
hypothesis is consumed, and it is the reason the module needs a finite
residue field rather than an arbitrary one.

## The two leaves

The route above is cut in two, along the seam between the FINITENESS
argument (steps 3–4, which is where the hypothesis `hhom` is spent, and
the only place the residue field has to be finite) and the TOPOLOGY
(steps 1, 2, 5, which hold for any profinite local ring with finitely
generated maximal ideal):

* `fg_maximalIdeal_of_finite_ringHom` — the maximal ideal is finitely
  generated (PROVEN 2026-07-26; see its docstring, which records the two
  places where the executed argument is SIMPLER than the sketch in step 3
  above — the count is run over the finite levels `R ⧸ J` rather than over
  a profinite cotangent space, and the coefficient field of a level is the
  `q`-th power map rather than a Hensel lift, so no completeness and no
  Hensel's lemma are needed anywhere);
* `isAdic_isAdicComplete_of_isOpen_of_fg` — a profinite local ring whose
  maximal ideal is open and finitely generated carries the `𝔪`-adic
  topology and is `𝔪`-adically complete (PROVEN 2026-07-26, steps 1, 2
  and 5 above).

The main theorem is proven over them: it identifies `𝔪` with `ker π`,
which is open because `π` is continuous and `k` is discrete, and then
applies `CompleteLocalNoetherian.isNoetherianRing_of_isAdicComplete_of_fg`.
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Basic
-- proof-only: `ker π` is a maximal ideal when `π` is onto a field.
import Mathlib.RingTheory.Ideal.Quotient.Operations
-- the quotient topology on `R ⧸ I` and the openness of the quotient map, from which
-- an open ideal is shown to have finite quotient; also `Ideal.closure`, which occurs in
-- the SIGNATURE of the topological Nakayama lemma below.
public import Mathlib.Topology.Algebra.Ring.Ideal
-- proof-only: `Ideal.finite_quotient_pow` — finiteness of `R ⧸ 𝔪 ^ n` from
-- finiteness of `R ⧸ 𝔪` for a finitely generated `𝔪`.
import Mathlib.RingTheory.Ideal.Quotient.Index
-- proof-only: `Ideal.FG.pow` — a power of a finitely generated ideal is
-- finitely generated.
import Mathlib.RingTheory.Finiteness.Ideal
-- proof-only: `Ideal.isCompact_of_fg` — a finitely generated ideal of a
-- compact topological ring is compact, hence closed.
import Mathlib.Topology.Algebra.Module.Compact
-- proof-only: `AddSubgroup.isOpen_of_isClosed_of_finiteIndex`.
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
-- proof-only: nilpotence of the Jacobson radical of an Artinian ring, which
-- is what makes the maximal ideal of a FINITE local quotient nilpotent.
import Mathlib.RingTheory.Artinian.Ring
-- proof-only: `isLocalHom_of_le_jacobson_bot`.
import Mathlib.RingTheory.LocalRing.RingHom.Basic
-- proof-only: `isLocalHom_of_le_jacobson_bot`, used to see the maximal ideal
-- of `R` inside that of a finite local quotient.
import Mathlib.RingTheory.Henselian
-- proof-only: the Noetherianity criterion this module's last step applies.
import Fermat.FLT.GaloisRepresentation.HardlyRamified.CompleteLocalNoetherian
-- the fixed test object `k[ε]` of the cotangent-space count, and `Nat.card`, both of
-- which occur in the SIGNATURES of the auxiliary counting lemmas below.
public import Mathlib.Algebra.DualNumber
public import Mathlib.SetTheory.Cardinal.Finite
-- `CharP`, in the signature of the Frobenius-section lemma, and `add_pow_char_pow`,
-- which is what makes that section a ring homomorphism.
public import Mathlib.Algebra.CharP.Lemmas
-- proof-only: `FiniteField.card` / `FiniteField.pow_card` — the residue field has
-- `ℓ ^ n` elements and every element is fixed by the `q`-th power map.
import Mathlib.FieldTheory.Finite.Basic
-- proof-only: `Basis.toDualEquiv` and `Module.finBasis` — a finite-dimensional vector
-- space over a finite field has exactly as many functionals as elements.
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dimension.Free
-- proof-only: `PadicInt.sub_zmodRepr_mem` — every `ℤ_ℓ`-element is a natural number
-- modulo `ℓ`, which is how the `ℤ_ℓ`-algebra clause of `hhom` is discharged.
import Mathlib.NumberTheory.Padics.RingHoms
-- proof-only: `Ideal.isOpen_of_isOpen_subideal`, `AddSubgroup.isClosed_of_isOpen`.
import Mathlib.Topology.Algebra.OpenSubgroup

@[expose] public section

namespace ProfiniteLocalNoetherian

universe u

/-! ### Auxiliary lemmas for the finiteness half

The four topological lemmas (`discreteTopology_quotient_of_isOpen`,
`finite_quotient_of_isOpen`, `isClosed_sup`, `exists_pow_le_of_isOpen`,
`exists_isOpen_ideal_of_notMem`) and the two counting lemmas
(`exists_ringHom_section`, `card_le_card_ringHom_dualNumber`) below are
consumed by `fg_maximalIdeal_of_finite_ringHom`; see its docstring for the
route. They are stated for their own sake because each is a general
statement about compact topological rings or about finite square-zero
extensions of a finite field, with no reference to the deformation problem.
-/

/-- **The Frobenius (Teichmüller) coefficient field of a square-zero extension of a
finite field.** If `πA : A ↠ k` is a surjection of commutative rings of characteristic
`ℓ` onto a FINITE field, and its kernel squares to zero, then `πA` splits as a ring
homomorphism.

The section is `a ↦ x ^ q` for `q = |k|` and `x` ANY lift of `a`: two lifts differ by an
element `m` of the kernel, and `(x + m) ^ q = x ^ q + m ^ q = x ^ q` because `q` is a
power of the characteristic (`add_pow_char_pow`) and `m ^ q = m ^ 2 * m ^ (q - 2) = 0`.
The same Frobenius identity gives additivity, and `FiniteField.pow_card` gives
`πA (s a) = a ^ q = a`.

This replaces the Hensel lift of a `(|k| − 1)`-st root of unity that the module header
proposes: it needs neither completeness nor Hensel's lemma, only that the kernel squares
to zero. -/
theorem exists_ringHom_section
    {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Finite k] [CharP k ℓ]
    {A : Type u} [CommRing A] [CharP A ℓ]
    (πA : A →+* k) (hsurj : Function.Surjective πA)
    (hsq : ∀ x ∈ RingHom.ker πA, ∀ y ∈ RingHom.ker πA, x * y = 0) :
    ∃ s : k →+* A, ∀ a : k, πA (s a) = a := by
  classical
  haveI := Fintype.ofFinite k
  obtain ⟨n, hprime, hq⟩ := FiniteField.card k ℓ
  have hq2 : 2 ≤ Fintype.card k := by
    rw [hq]
    calc (2 : ℕ) ≤ ℓ := hprime.two_le
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ (n : ℕ) := Nat.pow_le_pow_right hprime.pos n.2
  have hker0 : ∀ m ∈ RingHom.ker πA, m ^ Fintype.card k = 0 := by
    intro m hm
    have hsplit : m ^ Fintype.card k = m ^ 2 * m ^ (Fintype.card k - 2) := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit, pow_two, hsq m hm m hm, zero_mul]
  have hpow : ∀ x y : A, x - y ∈ RingHom.ker πA →
      x ^ Fintype.card k = y ^ Fintype.card k := by
    intro x y h
    have hx : x = y + (x - y) := by ring
    calc x ^ Fintype.card k = (y + (x - y)) ^ Fintype.card k := by rw [← hx]
      _ = (y + (x - y)) ^ ℓ ^ (n : ℕ) := by rw [hq]
      _ = y ^ ℓ ^ (n : ℕ) + (x - y) ^ ℓ ^ (n : ℕ) := add_pow_char_pow _ _ _ _
      _ = y ^ Fintype.card k + (x - y) ^ Fintype.card k := by rw [hq]
      _ = y ^ Fintype.card k := by rw [hker0 _ h, add_zero]
  have hmem : ∀ x y : A, πA x = πA y → x - y ∈ RingHom.ker πA := by
    intro x y h
    simp [RingHom.mem_ker, h]
  have hsi : ∀ a : k, πA (Function.surjInv hsurj a) = a := fun a =>
    Function.surjInv_eq hsurj a
  refine ⟨{ toFun := fun a => (Function.surjInv hsurj a) ^ Fintype.card k
            map_one' := ?_
            map_mul' := ?_
            map_zero' := ?_
            map_add' := ?_ }, ?_⟩
  · rw [hpow _ 1 (hmem _ _ (by rw [hsi, map_one])), one_pow]
  · intro a b
    rw [hpow _ (Function.surjInv hsurj a * Function.surjInv hsurj b)
      (hmem _ _ (by rw [hsi, map_mul, hsi, hsi])), mul_pow]
  · rw [hpow _ 0 (hmem _ _ (by rw [hsi, map_zero])), zero_pow (by omega)]
  · intro a b
    rw [hpow _ (Function.surjInv hsurj a + Function.surjInv hsurj b)
      (hmem _ _ (by rw [hsi, map_add, hsi, hsi]))]
    calc (Function.surjInv hsurj a + Function.surjInv hsurj b) ^ Fintype.card k
        = (Function.surjInv hsurj a + Function.surjInv hsurj b) ^ ℓ ^ (n : ℕ) := by rw [hq]
      _ = Function.surjInv hsurj a ^ ℓ ^ (n : ℕ)
            + Function.surjInv hsurj b ^ ℓ ^ (n : ℕ) := add_pow_char_pow _ _ _ _
      _ = _ := by rw [hq]
  · intro a
    show πA ((Function.surjInv hsurj a) ^ Fintype.card k) = a
    rw [map_pow, hsi, FiniteField.pow_card]

/-- **A finite square-zero extension of a finite field has at most `|k|` times as many
elements as it has ring maps to the dual numbers over `πA`.**

With the coefficient field `s : k →+* A` of `exists_ringHom_section` in hand, `A` injects
into `k × 𝔫` by `x ↦ (πA x, x - s (πA x))`, where `𝔫 = ker πA`; and `𝔫`, being a
finite-dimensional vector space over the finite field `k` (the `k`-action being the one
induced by `s`), has exactly as many `k`-functionals as elements (`Basis.toDualEquiv`).
Each functional `λ` gives a ring map `x ↦ πA x + λ (x - s (πA x)) ε` to `k[ε]` — the
multiplicativity is exactly `𝔫 ^ 2 = 0` — and distinct functionals give distinct maps,
because on `𝔫` the map reads off `λ` itself.

This is the finite-level form of "the cotangent space is finite dimensional"; running it
at a fixed `k[ε]` rather than at the profinite cotangent space is what lets the bound be
uniform over all the levels. -/
theorem card_le_card_ringHom_dualNumber
    {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Finite k] [CharP k ℓ]
    {A : Type u} [CommRing A] [Finite A] [CharP A ℓ]
    (πA : A →+* k) (hsurj : Function.Surjective πA)
    (hsq : ∀ x ∈ RingHom.ker πA, ∀ y ∈ RingHom.ker πA, x * y = 0) :
    Nat.card A ≤ Nat.card k *
      Nat.card {ψ : A →+* DualNumber k // ∀ x : A, (ψ x).fst = πA x} := by
  classical
  haveI : Finite (DualNumber k) := inferInstanceAs (Finite (k × k))
  haveI : Finite (A →+* DualNumber k) :=
    Finite.of_injective (fun f : A →+* DualNumber k => (f : A → DualNumber k))
      DFunLike.coe_injective
  obtain ⟨s, hs⟩ := exists_ringHom_section πA hsurj hsq
  letI : Algebra k A := s.toAlgebra
  have halg : ∀ a : k, algebraMap k A a = s a := fun _ => rfl
  have hδ : ∀ x : A, x - s (πA x) ∈ RingHom.ker πA := by
    intro x
    simp [RingHom.mem_ker, hs]
  -- **Step 1**: `A` injects into `k × 𝔫`.
  have h1 : Nat.card A ≤ Nat.card k * Nat.card ↥(RingHom.ker πA) := by
    have hinj : Function.Injective
        (fun x : A => (πA x, (⟨x - s (πA x), hδ x⟩ : ↥(RingHom.ker πA)))) := by
      intro x y hxy
      have hf : πA x = πA y := congrArg Prod.fst hxy
      have hsn : x - s (πA x) = y - s (πA y) := congrArg (fun p => (p.2 : A)) hxy
      rw [hf] at hsn
      exact sub_left_inj.mp hsn
    calc Nat.card A ≤ Nat.card (k × ↥(RingHom.ker πA)) :=
          Nat.card_le_card_of_injective _ hinj
      _ = Nat.card k * Nat.card ↥(RingHom.ker πA) := Nat.card_prod _ _
  -- **Step 2**: a finite-dimensional vector space has as many functionals as elements.
  have h2 : Nat.card ↥(RingHom.ker πA) = Nat.card (Module.Dual k ↥(RingHom.ker πA)) :=
    Nat.card_congr (Module.finBasis k ↥(RingHom.ker πA)).toDualEquiv.toEquiv
  -- **Step 3**: each functional gives a ring map to the dual numbers over `πA`.
  have hkey : ∀ lam : Module.Dual k ↥(RingHom.ker πA),
      ∃ ψ : A →+* DualNumber k, (∀ x : A, (ψ x).fst = πA x) ∧
        ∀ m : ↥(RingHom.ker πA), (ψ (m : A)).snd = lam m := by
    intro lam
    refine ⟨{ toFun := fun x => TrivSqZeroExt.inl (πA x) +
                TrivSqZeroExt.inr (lam ⟨x - s (πA x), hδ x⟩)
              map_one' := ?_
              map_mul' := ?_
              map_zero' := ?_
              map_add' := ?_ }, ?_, ?_⟩
    · have h0 : (⟨(1 : A) - s (πA 1), hδ 1⟩ : ↥(RingHom.ker πA)) = 0 := by
        apply Subtype.ext; simp
      rw [h0]
      simp
    · intro x y
      have h0 : (x - s (πA x)) * (y - s (πA y)) = 0 := hsq _ (hδ x) _ (hδ y)
      have hstep : (⟨x * y - s (πA (x * y)), hδ (x * y)⟩ : ↥(RingHom.ker πA)) =
          πA x • (⟨y - s (πA y), hδ y⟩ : ↥(RingHom.ker πA)) +
            πA y • (⟨x - s (πA x), hδ x⟩ : ↥(RingHom.ker πA)) := by
        apply Subtype.ext
        show x * y - s (πA (x * y)) =
          πA x • (y - s (πA y)) + πA y • (x - s (πA x))
        rw [Algebra.smul_def, Algebra.smul_def, halg, halg, map_mul, map_mul]
        linear_combination h0
      rw [hstep, map_add, map_smul, map_smul]
      apply TrivSqZeroExt.ext
      · simp [map_mul]
      · simp
        ring
    · have h0 : (⟨(0 : A) - s (πA 0), hδ 0⟩ : ↥(RingHom.ker πA)) = 0 := by
        apply Subtype.ext; simp
      rw [h0]
      simp
    · intro x y
      have hstep : (⟨x + y - s (πA (x + y)), hδ (x + y)⟩ : ↥(RingHom.ker πA)) =
          (⟨x - s (πA x), hδ x⟩ : ↥(RingHom.ker πA)) +
            (⟨y - s (πA y), hδ y⟩ : ↥(RingHom.ker πA)) := by
        apply Subtype.ext
        show x + y - s (πA (x + y)) = (x - s (πA x)) + (y - s (πA y))
        rw [map_add, map_add]; ring
      rw [hstep, map_add lam]
      apply TrivSqZeroExt.ext
      · simp
      · simp
    · intro x
      simp
    · intro m
      have hm : πA (m : A) = 0 := m.2
      have h0 : (⟨(m : A) - s (πA (m : A)), hδ _⟩ : ↥(RingHom.ker πA)) = m := by
        apply Subtype.ext
        show (m : A) - s (πA (m : A)) = (m : A)
        rw [hm, map_zero, sub_zero]
      show (TrivSqZeroExt.inl (πA (m : A)) +
        TrivSqZeroExt.inr (lam ⟨(m : A) - s (πA (m : A)), hδ _⟩)).snd = lam m
      rw [h0]
      simp
  choose ψ hψ1 hψ2 using hkey
  have h3 : Nat.card (Module.Dual k ↥(RingHom.ker πA)) ≤
      Nat.card {ψ : A →+* DualNumber k // ∀ x : A, (ψ x).fst = πA x} := by
    refine Nat.card_le_card_of_injective
      (fun lam => (⟨ψ lam, hψ1 lam⟩ :
        {ψ : A →+* DualNumber k // ∀ x : A, (ψ x).fst = πA x})) ?_
    intro l1 l2 hl
    have hval : ψ l1 = ψ l2 := congrArg Subtype.val hl
    ext m
    rw [← hψ2 l1 m, ← hψ2 l2 m, hval]
  calc Nat.card A ≤ Nat.card k * Nat.card ↥(RingHom.ker πA) := h1
    _ = Nat.card k * Nat.card (Module.Dual k ↥(RingHom.ker πA)) := by rw [h2]
    _ ≤ _ := Nat.mul_le_mul_left _ h3

section Topology

variable {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- The quotient by an open ideal is discrete. -/
theorem discreteTopology_quotient_of_isOpen (I : Ideal R)
    (hI : IsOpen (I : Set R)) : DiscreteTopology (R ⧸ I) := by
  rw [discreteTopology_iff_isOpen_singleton_zero]
  have hz : ({0} : Set (R ⧸ I)) = Ideal.Quotient.mk I '' (I : Set R) := by
    ext x
    constructor
    · rintro rfl
      exact ⟨0, I.zero_mem, map_zero _⟩
    · rintro ⟨y, hy, rfl⟩
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr hy
  rw [hz]
  exact (QuotientRing.isOpenQuotientMap_mk I).isOpenMap _ hI

/-- An open ideal of a compact ring has finite quotient. -/
theorem finite_quotient_of_isOpen [CompactSpace R] (I : Ideal R)
    (hI : IsOpen (I : Set R)) : Finite (R ⧸ I) := by
  haveI := discreteTopology_quotient_of_isOpen I hI
  exact finite_of_compact_of_discrete

/-- In a compact Hausdorff topological ring the sum of two closed ideals is closed. -/
theorem isClosed_sup [CompactSpace R] [T2Space R] {M N : Ideal R}
    (hM : IsClosed ((M : Ideal R) : Set R)) (hN : IsClosed ((N : Ideal R) : Set R)) :
    IsClosed (((M ⊔ N : Ideal R) : Ideal R) : Set R) := by
  have hset : ((M ⊔ N : Ideal R) : Set R) =
      (fun p : R × R => p.1 + p.2) '' ((M : Set R) ×ˢ (N : Set R)) := by
    ext z
    simp only [SetLike.mem_coe, Submodule.mem_sup, Set.mem_image, Set.mem_prod, Prod.exists]
    constructor
    · rintro ⟨y, hy, w, hw, rfl⟩; exact ⟨y, w, ⟨hy, hw⟩, rfl⟩
    · rintro ⟨y, w, ⟨hy, hw⟩, rfl⟩; exact ⟨y, hy, w, hw, rfl⟩
  rw [hset]
  exact ((hM.isCompact.prod hN.isCompact).image (by fun_prop)).isClosed

/-- Every open ideal of a compact local ring contains a power of the maximal ideal. -/
theorem exists_pow_le_of_isOpen [IsLocalRing R] [CompactSpace R] (I : Ideal R)
    (hI : IsOpen (I : Set R)) : ∃ n : ℕ, IsLocalRing.maximalIdeal R ^ n ≤ I := by
  classical
  rcases eq_or_ne I ⊤ with rfl | hItop
  · exact ⟨0, le_top⟩
  haveI := finite_quotient_of_isOpen I hI
  haveI : Nontrivial (R ⧸ I) := by
    rw [← not_subsingleton_iff_nontrivial, Ideal.Quotient.subsingleton_iff]
    exact hItop
  haveI : IsLocalHom (Ideal.Quotient.mk I) :=
    isLocalHom_of_le_jacobson_bot I (by
      rw [IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top]
      exact IsLocalRing.le_maximalIdeal hItop)
  haveI : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  haveI : IsArtinianRing (R ⧸ I) := isArtinian_of_finite
  obtain ⟨N, hN⟩ : ∃ N : ℕ, IsLocalRing.maximalIdeal (R ⧸ I) ^ N = ⊥ := by
    obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R ⧸ I)
    exact ⟨N, by
      rwa [IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal (R ⧸ I)) bot_ne_top,
        Ideal.zero_eq_bot] at hN⟩
  refine ⟨N, ?_⟩
  have hmapmono : (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk I) ≤
      IsLocalRing.maximalIdeal (R ⧸ I) := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    show Ideal.Quotient.mk I y ∈ IsLocalRing.maximalIdeal (R ⧸ I)
    rw [IsLocalRing.mem_maximalIdeal] at hy ⊢
    exact fun hu => hy (isUnit_of_map_unit (Ideal.Quotient.mk I) y hu)
  have hmono : ∀ n : ℕ, ((IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk I)) ^ n ≤
      IsLocalRing.maximalIdeal (R ⧸ I) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ m ih => rw [pow_succ, pow_succ]; exact Ideal.mul_mono ih hmapmono
  have hpow : ((IsLocalRing.maximalIdeal R) ^ N).map (Ideal.Quotient.mk I) = ⊥ := by
    rw [Ideal.map_pow, ← le_bot_iff, ← hN]
    exact hmono N
  rwa [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at hpow

/-- **Separating a point from a closed ideal by an open ideal**, inside a prescribed
open ideal `V`. -/
theorem exists_isOpen_ideal_of_notMem
    (hbasis : ∀ U ∈ nhds (0 : R), ∃ I : Ideal R, IsOpen (I : Set R) ∧ (I : Set R) ⊆ U)
    (C V : Ideal R) (hC : IsClosed (C : Set R)) (hV : IsOpen (V : Set R)) (hCV : C ≤ V)
    {x : R} (hx : x ∉ C) :
    ∃ J : Ideal R, IsOpen (J : Set R) ∧ C ≤ J ∧ J ≤ V ∧ x ∉ J := by
  have hU : (V : Set R) ∩ (fun y => x + y) ⁻¹' (C : Set R)ᶜ ∈ nhds (0 : R) := by
    refine Filter.inter_mem (hV.mem_nhds V.zero_mem) ?_
    refine (hC.isOpen_compl.preimage (by fun_prop)).mem_nhds ?_
    simpa using hx
  obtain ⟨I, hIopen, hIU⟩ := hbasis _ hU
  refine ⟨I ⊔ C, Ideal.isOpen_of_isOpen_subideal le_sup_left hIopen, le_sup_right,
    sup_le (fun y hy => (hIU hy).1) hCV, ?_⟩
  intro hmem
  rw [Submodule.mem_sup] at hmem
  obtain ⟨i, hi, c, hc, hic⟩ := hmem
  have hxc : x + (-i) = c := by rw [← hic]; ring
  have h2 := (hIU (I.neg_mem hi)).2
  simp only [Set.mem_preimage, Set.mem_compl_iff, SetLike.mem_coe] at h2
  exact h2 (hxc ▸ hc)

/-- **Topological Nakayama** in a compact Hausdorff local ring. -/
theorem le_of_le_sup_closure_sq [IsLocalRing R] [CompactSpace R] [T2Space R]
    (hbasis : ∀ U ∈ nhds (0 : R), ∃ I : Ideal R, IsOpen (I : Set R) ∧ (I : Set R) ⊆ U)
    (M : Ideal R) (hMfg : M.FG)
    (hle : IsLocalRing.maximalIdeal R ≤ M ⊔ (IsLocalRing.maximalIdeal R ^ 2).closure) :
    IsLocalRing.maximalIdeal R ≤ M := by
  classical
  have hMcl : IsClosed ((M : Ideal R) : Set R) := (Ideal.isCompact_of_fg hMfg).isClosed
  have hsupcl : ∀ N : Ideal R, IsClosed ((N : Ideal R) : Set R) →
      IsClosed (((M ⊔ N : Ideal R) : Ideal R) : Set R) := fun N hN => isClosed_sup hMcl hN
  have hstep : ∀ n : ℕ,
      (IsLocalRing.maximalIdeal R * ((IsLocalRing.maximalIdeal R ^ n).closure) : Ideal R) ≤
        (IsLocalRing.maximalIdeal R ^ (n + 1)).closure := by
    intro n
    rw [Ideal.mul_le]
    intro r hr y hy
    have hsub : closure (((IsLocalRing.maximalIdeal R ^ n : Ideal R)) : Set R) ⊆
        (fun z : R => r * z) ⁻¹'
          (((IsLocalRing.maximalIdeal R ^ (n + 1)).closure : Ideal R) : Set R) := by
      refine closure_minimal ?_ (IsClosed.preimage (by fun_prop) isClosed_closure)
      intro z hz
      refine subset_closure ?_
      rw [pow_succ']
      exact Ideal.mul_mem_mul hr hz
    exact hsub hy
  have hind : ∀ n : ℕ, IsLocalRing.maximalIdeal R ≤
      M ⊔ (IsLocalRing.maximalIdeal R ^ (n + 2)).closure := by
    intro n
    induction n with
    | zero => exact hle
    | succ m ih =>
      refine le_trans hle (sup_le le_sup_left ?_)
      have hcl : IsClosed
          (((M ⊔ (IsLocalRing.maximalIdeal R ^ (m + 3)).closure : Ideal R)) : Set R) :=
        hsupcl _ isClosed_closure
      have hsq : ((IsLocalRing.maximalIdeal R) ^ 2 : Ideal R) ≤
          M ⊔ (IsLocalRing.maximalIdeal R ^ (m + 3)).closure := by
        rw [sq, Ideal.mul_le]
        intro r hr y hy
        have hy' : y ∈ M ⊔ (IsLocalRing.maximalIdeal R ^ (m + 2)).closure := ih hy
        rw [Submodule.mem_sup] at hy'
        obtain ⟨a, ha, b, hb, rfl⟩ := hy'
        rw [mul_add]
        exact Submodule.add_mem_sup (M.mul_mem_left r ha)
          (hstep (m + 2) (Ideal.mul_mem_mul hr hb))
      exact closure_minimal hsq hcl
  have hopenle : ∀ I : Ideal R, IsOpen ((I : Ideal R) : Set R) →
      IsLocalRing.maximalIdeal R ≤ M ⊔ I := by
    intro I hI
    obtain ⟨n, hn⟩ := exists_pow_le_of_isOpen I hI
    have h2 : ((IsLocalRing.maximalIdeal R) ^ (n + 2) : Ideal R) ≤ I :=
      le_trans (Ideal.pow_le_pow_right (by omega)) hn
    refine le_trans (hind n) (sup_le le_sup_left (le_trans ?_ le_sup_right))
    intro z hz
    exact closure_minimal (fun w hw => h2 hw) (I.toAddSubgroup.isClosed_of_isOpen hI) hz
  intro x hx
  by_contra hxM
  obtain ⟨J, hJopen, hMJ, -, hxJ⟩ :=
    exists_isOpen_ideal_of_notMem hbasis M ⊤ hMcl (by simp) le_top hxM
  exact hxJ (by simpa [sup_eq_right.mpr hMJ] using hopenle J hJopen hx)

end Topology

/-- **The maximal ideal of a profinite local ring with finitely many points
in every finite test ring is finitely generated** (PROVEN 2026-07-26 — the
FINITENESS half of this module's cut, steps 3–4 of the header route, and
the only place where the residue field must be finite).

This is the exact point at which Mazur's `Φ_ℓ` condition is consumed; the
counterexample in the module header (a compact local ring with square-zero
maximal ideal `∏_{i ∈ ℕ} 𝔽_ℓ`) shows the hypothesis cannot be dropped.

`hhom` QUANTIFIES ONLY OVER DISCRETE TEST RINGS (`[DiscreteTopology A]`,
added 2026-07-26 in alignment with `Deformation.lean`'s
`exists_isStrictlyUniversalOnFrames_of_deformationCondition`, whose `hfin`
carries the same binder). This costs the prover nothing: `hhom` is spent at
`A = k[ε]` with `k` FINITE, and a finite topological ring in the Mazur
category is discrete, so the instance is available at the only point of use.
The narrowing is mathematically necessary rather than cosmetic — over a
finite ring carrying the INDISCRETE topology, continuity of `φ` is no
constraint at all and the finiteness hypothesis would be asserting something
false about the abstract (non-topological) point set.

THE ROUTE ACTUALLY TAKEN differs from the sketch in the module header in
two ways, both simplifications, and neither of them changes the
mathematics.

*No profinite cotangent space, and no Hensel.* Rather than forming the
profinite `k`-vector space `t = 𝔪 ⧸ closure (𝔪 ^ 2 + ℓ • R)` and bounding
`dim_k t` by the number of CONTINUOUS functionals on it, the count is run
one FINITE level at a time. Write `𝒥` for the family of OPEN ideals `J`
with `𝔪 ^ 2 + (ℓ) ≤ J ≤ 𝔪`. For `J ∈ 𝒥` the quotient `A = R ⧸ J` is a
finite local ring of characteristic `ℓ` whose maximal ideal `𝔫` squares to
zero, so `hhom` at the FIXED test object `k[ε]` bounds `Nat.card A`
uniformly over `𝒥`, by `Nat.card k * |Hom^{cont}_{ℤ_ℓ}(R, k[ε])|`
(`card_le_card_ringHom_dualNumber`). A level `J₀ ∈ 𝒥` of MAXIMAL size then
lies inside every other level, since `R ⧸ (J ⊓ J₀) ↠ R ⧸ J₀` is a
surjection of finite sets of equal cardinality, hence injective. Separating
points from the closed ideal `(ℓ) + closure (𝔪 ^ 2)` by open ideals
(`exists_isOpen_ideal_of_notMem`) identifies `J₀` as contained in it, so
`𝔪` is generated by finitely many elements together with
`(ℓ) + closure (𝔪 ^ 2)`, and topological Nakayama
(`le_of_le_sup_closure_sq`) removes the closure term.

*The coefficient field is the `q`-th power map, not a Hensel lift.* Over a
finite level `A` the square-zero condition `𝔫 ^ 2 = 0` and `ℓ = 0` make
`a ↦ (any lift of a) ^ q`, `q = |k|`, well defined — two lifts differ by
`m ∈ 𝔫` and `(x + m) ^ q = x ^ q + m ^ q = x ^ q` because `q` is a power of
the characteristic and `m ^ q = 0` — and a ring homomorphism, additivity
being exactly the Frobenius identity `add_pow_char_pow`. That is
`exists_ringHom_section`: it needs no completeness, no Hensel's lemma and
no Witt vectors, only `char = ℓ` and `𝔫 ^ 2 = 0`.

Every hypothesis is used: `hbasis` for the separation and Nakayama steps,
`hπsurj` to see `𝔪 = ker π`, `hπcont` together with `[DiscreteTopology k]`
for the openness of `𝔪`, and `hhom` — at `A = k[ε]` only — for the
uniform bound. -/
theorem fg_maximalIdeal_of_finite_ringHom
    {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Finite k]
    [Algebra ℤ_[ℓ] k] [TopologicalSpace k] [DiscreteTopology k]
    {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [Algebra ℤ_[ℓ] R] [CompactSpace R] [T2Space R]
    (hbasis : ∀ U ∈ nhds (0 : R), ∃ I : Ideal R, IsOpen (I : Set R) ∧
      (I : Set R) ⊆ U)
    (π : R →+* k) (hπsurj : Function.Surjective π) (hπcont : Continuous π)
    (hhom : ∀ (A : Type u) [CommRing A] [TopologicalSpace A]
      [IsTopologicalRing A] [IsLocalRing A] [Algebra ℤ_[ℓ] A] [Finite A]
      [DiscreteTopology A]
      (πA : A →+* k),
      {φ : R →+* A | Continuous φ ∧ πA.comp φ = π ∧
        φ.comp (algebraMap ℤ_[ℓ] R) = algebraMap ℤ_[ℓ] A}.Finite) :
    (IsLocalRing.maximalIdeal R).FG := by
  classical
  -- **(0)** `k` has characteristic `ℓ`.
  have hlk : ((ℓ : ℕ) : k) = 0 := by
    haveI : CharP k (ringChar k) := ringChar.charP k
    have hpprime : Nat.Prime (ringChar k) := CharP.prime_ringChar k
    have hpk : ((ringChar k : ℕ) : k) = 0 := CharP.cast_eq_zero k _
    have hpl : ringChar k = ℓ := by
      by_contra hne
      have hnd : ¬ ((ℓ : ℤ) ∣ ((ringChar k : ℕ) : ℤ)) := by
        rw [Int.natCast_dvd_natCast]
        exact fun h => hne ((Nat.prime_dvd_prime_iff_eq Fact.out hpprime).mp h).symm
      have hnorm : (1 : ℝ) ≤ ‖(((ringChar k : ℕ) : ℤ) : ℤ_[ℓ])‖ :=
        not_lt.mp fun h => hnd ((PadicInt.norm_int_lt_one_iff_dvd _).mp h)
      have hu : IsUnit (((ringChar k : ℕ)) : ℤ_[ℓ]) := by
        rw [PadicInt.isUnit_iff]
        refine le_antisymm (PadicInt.norm_le_one _) ?_
        simpa using hnorm
      have hu' := IsUnit.map (algebraMap ℤ_[ℓ] k) hu
      rw [map_natCast, hpk] at hu'
      exact not_isUnit_zero hu'
    rw [← hpl]; exact hpk
  haveI hchark : CharP k ℓ := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hlk
  -- **(1)** `𝔪 = ker π`, and it is open.
  have hker : RingHom.ker π = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective π hπsurj)
  have hopen : IsOpen ((IsLocalRing.maximalIdeal R : Ideal R) : Set R) := by
    rw [← hker, show ((RingHom.ker π : Ideal R) : Set R) = π ⁻¹' {0} from
      Set.ext fun x => by simp [RingHom.mem_ker]]
    exact (isOpen_discrete _).preimage hπcont
  have hℓm : ((ℓ : ℕ) : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [← hker, RingHom.mem_ker, map_natCast]
    exact hlk
  -- **(2)** the dual numbers as the fixed test object.
  letI : TopologicalSpace (DualNumber k) := ⊥
  haveI : DiscreteTopology (DualNumber k) := ⟨rfl⟩
  haveI : IsTopologicalRing (DualNumber k) :=
    { continuous_add := continuous_of_discreteTopology
      continuous_mul := continuous_of_discreteTopology
      continuous_neg := continuous_of_discreteTopology }
  haveI : Finite (DualNumber k) := inferInstanceAs (Finite (k × k))
  haveI : IsLocalRing (DualNumber k) := by
    refine IsLocalRing.of_nonunits_add ?_
    intro a b ha hb
    rw [mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero,
      not_not] at ha hb ⊢
    rw [TrivSqZeroExt.fst_add, ha, hb, add_zero]
  letI : Algebra ℤ_[ℓ] (DualNumber k) :=
    ((algebraMap k (DualNumber k)).comp (algebraMap ℤ_[ℓ] k)).toAlgebra
  have halgε : ∀ z : ℤ_[ℓ], algebraMap ℤ_[ℓ] (DualNumber k) z =
      algebraMap k (DualNumber k) (algebraMap ℤ_[ℓ] k z) := fun _ => rfl
  have hfin := hhom (DualNumber k) (TrivSqZeroExt.fstHom k k k).toRingHom
  haveI := hfin.to_subtype
  -- **(3)** natural-number representatives modulo `ℓ` in `ℤ_ℓ`.
  have hrep : ∀ z : ℤ_[ℓ], ∃ n : ℕ, ∃ w : ℤ_[ℓ],
      z = ((n : ℕ) : ℤ_[ℓ]) + ((ℓ : ℕ) : ℤ_[ℓ]) * w := by
    intro z
    have hmem := PadicInt.sub_zmodRepr_mem z
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hmem
    obtain ⟨w, hw⟩ := hmem
    exact ⟨PadicInt.zmodRepr z, w, by linear_combination hw⟩
  -- **(4)** the uniform bound on the finite levels between `𝔪 ^ 2 + (ℓ)` and `𝔪`.
  have hbound : ∀ J : Ideal R, IsOpen ((J : Ideal R) : Set R) →
      (IsLocalRing.maximalIdeal R) ^ 2 ≤ J → ((ℓ : ℕ) : R) ∈ J →
      J ≤ IsLocalRing.maximalIdeal R →
      Nat.card (R ⧸ J) ≤ Nat.card k *
        Nat.card ↥{φ : R →+* DualNumber k | Continuous φ ∧
          (TrivSqZeroExt.fstHom k k k).toRingHom.comp φ = π ∧
          φ.comp (algebraMap ℤ_[ℓ] R) = algebraMap ℤ_[ℓ] (DualNumber k)} := by
    intro J hJopen hJsq hJl hJm
    haveI : Finite (R ⧸ J) := finite_quotient_of_isOpen J hJopen
    have hJne : J ≠ ⊤ := by
      intro h
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (h ▸ hJm))
    haveI : Nontrivial (R ⧸ J) := by
      rw [← not_subsingleton_iff_nontrivial, Ideal.Quotient.subsingleton_iff]
      exact hJne
    have hml : (Ideal.Quotient.mk J) ((ℓ : ℕ) : R) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hJl
    haveI : CharP (R ⧸ J) ℓ := by
      refine (CharP.charP_iff_prime_eq_zero Fact.out).mpr ?_
      rw [← map_natCast (Ideal.Quotient.mk J) ℓ]
      exact hml
    have hπAaux : ∀ a ∈ J, π a = 0 := fun a ha => RingHom.mem_ker.mp (hker ▸ hJm ha)
    set πA : (R ⧸ J) →+* k := Ideal.Quotient.lift J π hπAaux
    have hπAmk : ∀ x : R, πA (Ideal.Quotient.mk J x) = π x := fun x =>
      Ideal.Quotient.lift_mk _ _ _
    have hπAsurj : Function.Surjective πA := by
      intro c
      obtain ⟨x, hx⟩ := hπsurj c
      exact ⟨Ideal.Quotient.mk J x, by rw [hπAmk, hx]⟩
    have hsq : ∀ x ∈ RingHom.ker πA, ∀ y ∈ RingHom.ker πA, x * y = 0 := by
      intro x hx y hy
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [RingHom.mem_ker, hπAmk] at hx hy
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      refine hJsq ?_
      rw [sq]
      exact Ideal.mul_mem_mul (hker ▸ (RingHom.mem_ker (f := π)).mpr hx)
        (hker ▸ (RingHom.mem_ker (f := π)).mpr hy)
    have hcard := card_le_card_ringHom_dualNumber πA hπAsurj hsq
    have hmemset : ∀ ψ : (R ⧸ J) →+* DualNumber k, (∀ x, (ψ x).fst = πA x) →
        (ψ.comp (Ideal.Quotient.mk J)) ∈ {φ : R →+* DualNumber k | Continuous φ ∧
          (TrivSqZeroExt.fstHom k k k).toRingHom.comp φ = π ∧
          φ.comp (algebraMap ℤ_[ℓ] R) = algebraMap ℤ_[ℓ] (DualNumber k)} := by
      intro ψ hψ
      refine ⟨?_, ?_, ?_⟩
      · haveI := discreteTopology_quotient_of_isOpen J hJopen
        exact (continuous_of_discreteTopology (f := ⇑ψ)).comp
          (QuotientRing.isOpenQuotientMap_mk J).continuous
      · refine RingHom.ext fun x => ?_
        show (ψ (Ideal.Quotient.mk J x)).fst = π x
        rw [hψ, hπAmk]
      · refine RingHom.ext fun z => ?_
        obtain ⟨n, w, hz⟩ := hrep z
        have hR : algebraMap ℤ_[ℓ] R z =
            ((n : ℕ) : R) + ((ℓ : ℕ) : R) * algebraMap ℤ_[ℓ] R w := by
          rw [hz, map_add, map_mul, map_natCast, map_natCast]
        have hmk : Ideal.Quotient.mk J (algebraMap ℤ_[ℓ] R z) = ((n : ℕ) : R ⧸ J) := by
          rw [hR, map_add, map_mul, hml, zero_mul, add_zero, map_natCast]
        have hkz : algebraMap ℤ_[ℓ] k z = ((n : ℕ) : k) := by
          rw [hz, map_add, map_mul, map_natCast, map_natCast, hlk, zero_mul, add_zero]
        show ψ (Ideal.Quotient.mk J (algebraMap ℤ_[ℓ] R z)) =
          algebraMap ℤ_[ℓ] (DualNumber k) z
        rw [hmk, map_natCast, halgε, hkz, map_natCast]
    have hle : Nat.card {ψ : (R ⧸ J) →+* DualNumber k // ∀ x, (ψ x).fst = πA x} ≤
        Nat.card ↥{φ : R →+* DualNumber k | Continuous φ ∧
          (TrivSqZeroExt.fstHom k k k).toRingHom.comp φ = π ∧
          φ.comp (algebraMap ℤ_[ℓ] R) = algebraMap ℤ_[ℓ] (DualNumber k)} := by
      refine Nat.card_le_card_of_injective
        (fun ψ => (⟨ψ.1.comp (Ideal.Quotient.mk J), hmemset ψ.1 ψ.2⟩ : ↥{φ : R →+* DualNumber k |
          Continuous φ ∧ (TrivSqZeroExt.fstHom k k k).toRingHom.comp φ = π ∧
          φ.comp (algebraMap ℤ_[ℓ] R) = algebraMap ℤ_[ℓ] (DualNumber k)})) ?_
      intro ψ₁ ψ₂ hψ
      have hc : ψ₁.1.comp (Ideal.Quotient.mk J) = ψ₂.1.comp (Ideal.Quotient.mk J) :=
        congrArg Subtype.val hψ
      apply Subtype.ext
      refine RingHom.ext fun c => ?_
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective c
      exact congrFun (congrArg (fun f : R →+* DualNumber k => ⇑f) hc) x
    exact le_trans hcard (Nat.mul_le_mul_left _ hle)
  -- **(5)** a level of maximal size.
  have hmmem : IsOpen ((IsLocalRing.maximalIdeal R : Ideal R) : Set R) ∧
      (IsLocalRing.maximalIdeal R) ^ 2 ≤ IsLocalRing.maximalIdeal R ∧
      ((ℓ : ℕ) : R) ∈ IsLocalRing.maximalIdeal R ∧
      IsLocalRing.maximalIdeal R ≤ IsLocalRing.maximalIdeal R :=
    ⟨hopen, Ideal.pow_le_self (by norm_num), hℓm, le_rfl⟩
  have hSfin : {c : ℕ | ∃ J : Ideal R, (IsOpen ((J : Ideal R) : Set R) ∧
      (IsLocalRing.maximalIdeal R) ^ 2 ≤ J ∧ ((ℓ : ℕ) : R) ∈ J ∧
      J ≤ IsLocalRing.maximalIdeal R) ∧ Nat.card (R ⧸ J) = c}.Finite := by
    refine Set.Finite.subset (Set.finite_Icc 0 (Nat.card k *
      Nat.card ↥{φ : R →+* DualNumber k | Continuous φ ∧
        (TrivSqZeroExt.fstHom k k k).toRingHom.comp φ = π ∧
        φ.comp (algebraMap ℤ_[ℓ] R) = algebraMap ℤ_[ℓ] (DualNumber k)})) ?_
    rintro c ⟨J, ⟨h1, h2, h3, h4⟩, rfl⟩
    exact ⟨Nat.zero_le _, hbound J h1 h2 h3 h4⟩
  have hSne : {c : ℕ | ∃ J : Ideal R, (IsOpen ((J : Ideal R) : Set R) ∧
      (IsLocalRing.maximalIdeal R) ^ 2 ≤ J ∧ ((ℓ : ℕ) : R) ∈ J ∧
      J ≤ IsLocalRing.maximalIdeal R) ∧ Nat.card (R ⧸ J) = c}.Nonempty :=
    ⟨_, IsLocalRing.maximalIdeal R, hmmem, rfl⟩
  obtain ⟨J₀, ⟨hJ₀open, hJ₀sq, hJ₀l, -⟩, hJ₀eq⟩ := hSne.csSup_mem hSfin
  have hJ₀max : ∀ J : Ideal R, IsOpen ((J : Ideal R) : Set R) →
      (IsLocalRing.maximalIdeal R) ^ 2 ≤ J → ((ℓ : ℕ) : R) ∈ J →
      J ≤ IsLocalRing.maximalIdeal R → Nat.card (R ⧸ J) ≤ Nat.card (R ⧸ J₀) := by
    intro J h1 h2 h3 h4
    rw [hJ₀eq]
    exact le_csSup hSfin.bddAbove ⟨J, ⟨h1, h2, h3, h4⟩, rfl⟩
  -- **(6)** `J₀` is the smallest such level.
  haveI hfinJ₀ : Finite (R ⧸ J₀) := finite_quotient_of_isOpen _ hJ₀open
  have hJ₀min : ∀ J : Ideal R, IsOpen ((J : Ideal R) : Set R) →
      (IsLocalRing.maximalIdeal R) ^ 2 ≤ J → ((ℓ : ℕ) : R) ∈ J →
      J ≤ IsLocalRing.maximalIdeal R → J₀ ≤ J := by
    intro J h1 h2 h3 h4
    have hio : IsOpen (((J ⊓ J₀ : Ideal R) : Ideal R) : Set R) := by
      have : (((J ⊓ J₀ : Ideal R)) : Set R) = ((J : Ideal R) : Set R) ∩ (J₀ : Set R) := rfl
      rw [this]
      exact h1.inter hJ₀open
    haveI : Finite (R ⧸ (J ⊓ J₀)) := finite_quotient_of_isOpen _ hio
    have hf : ∀ a ∈ (J ⊓ J₀ : Ideal R), (Ideal.Quotient.mk J₀) a = 0 :=
      fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr ha.2
    set f : (R ⧸ (J ⊓ J₀)) →+* (R ⧸ J₀) :=
      Ideal.Quotient.lift (J ⊓ J₀) (Ideal.Quotient.mk J₀) hf
    have hfmk : ∀ x : R, f (Ideal.Quotient.mk (J ⊓ J₀) x) = Ideal.Quotient.mk J₀ x :=
      fun x => Ideal.Quotient.lift_mk _ _ _
    have hfsurj : Function.Surjective f := by
      intro y
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨Ideal.Quotient.mk _ x, hfmk x⟩
    have hbij : Function.Bijective f := by
      rw [Nat.bijective_iff_surjective_and_card]
      refine ⟨hfsurj, le_antisymm ?_ (Nat.card_le_card_of_surjective f hfsurj)⟩
      exact hJ₀max (J ⊓ J₀) hio (le_inf h2 hJ₀sq) ⟨h3, hJ₀l⟩ (le_trans inf_le_left h4)
    intro x hx
    have h0 : f (Ideal.Quotient.mk (J ⊓ J₀) x) = f 0 := by
      rw [hfmk, map_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
    exact (Ideal.Quotient.eq_zero_iff_mem.mp (hbij.1 h0)).1
  -- **(7)** `𝔪` is generated by finitely many elements together with `J₀`.
  obtain ⟨M₀, hM₀fg, hM₀m, hM₀le⟩ : ∃ M₀ : Ideal R, M₀.FG ∧
      M₀ ≤ IsLocalRing.maximalIdeal R ∧ IsLocalRing.maximalIdeal R ≤ M₀ ⊔ J₀ := by
    set g : (R ⧸ J₀) → R := fun c =>
      if h : ∃ r, r ∈ IsLocalRing.maximalIdeal R ∧ Ideal.Quotient.mk J₀ r = c
      then h.choose else 0 with hg
    have hgm : ∀ c, g c ∈ IsLocalRing.maximalIdeal R := by
      intro c
      rw [hg]
      dsimp only
      split
      · rename_i h; exact h.choose_spec.1
      · exact Submodule.zero_mem _
    have hgeq : ∀ x ∈ IsLocalRing.maximalIdeal R,
        Ideal.Quotient.mk J₀ (g (Ideal.Quotient.mk J₀ x)) = Ideal.Quotient.mk J₀ x := by
      intro x hx
      have hex : ∃ r, r ∈ IsLocalRing.maximalIdeal R ∧
          Ideal.Quotient.mk J₀ r = Ideal.Quotient.mk J₀ x := ⟨x, hx, rfl⟩
      rw [hg]
      dsimp only
      rw [dif_pos hex]
      exact hex.choose_spec.2
    refine ⟨Ideal.span (Set.range g), Submodule.fg_span (Set.finite_range g), ?_, ?_⟩
    · rw [Ideal.span_le]
      rintro _ ⟨c, rfl⟩
      exact hgm c
    · intro x hx
      have h1 : x - g (Ideal.Quotient.mk J₀ x) ∈ J₀ := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hgeq x hx, sub_self]
      have h2 : g (Ideal.Quotient.mk J₀ x) ∈ Ideal.span (Set.range g) :=
        Ideal.subset_span ⟨_, rfl⟩
      have h3 := Submodule.add_mem_sup h2 h1
      have heq : g (Ideal.Quotient.mk J₀ x) + (x - g (Ideal.Quotient.mk J₀ x)) = x := by ring
      rwa [heq] at h3
  -- **(8)** `J₀` sits inside `(ℓ) + closure (𝔪 ^ 2)`.
  have hspanℓcl : IsClosed ((Ideal.span {((ℓ : ℕ) : R)} : Ideal R) : Set R) :=
    (Ideal.isCompact_of_fg (Submodule.fg_span (Set.finite_singleton _))).isClosed
  have hCcl : IsClosed (((Ideal.span {((ℓ : ℕ) : R)} ⊔
      (IsLocalRing.maximalIdeal R ^ 2).closure : Ideal R)) : Set R) :=
    isClosed_sup hspanℓcl isClosed_closure
  have hℓspan : ((ℓ : ℕ) : R) ∈ Ideal.span {((ℓ : ℕ) : R)} :=
    Ideal.subset_span rfl
  have hCm : (Ideal.span {((ℓ : ℕ) : R)} ⊔ (IsLocalRing.maximalIdeal R ^ 2).closure : Ideal R) ≤
      IsLocalRing.maximalIdeal R := by
    refine sup_le ?_ ?_
    · rw [Ideal.span_le, Set.singleton_subset_iff]; exact hℓm
    · exact closure_minimal (fun z hz => Ideal.pow_le_self (by norm_num) hz)
        ((IsLocalRing.maximalIdeal R).toAddSubgroup.isClosed_of_isOpen hopen)
  have hJ₀C : J₀ ≤ (Ideal.span {((ℓ : ℕ) : R)} ⊔
      (IsLocalRing.maximalIdeal R ^ 2).closure : Ideal R) := by
    intro x hx
    by_contra hxC
    obtain ⟨J, hJopen, hCJ, hJm, hxJ⟩ :=
      exists_isOpen_ideal_of_notMem hbasis _ (IsLocalRing.maximalIdeal R) hCcl hopen hCm hxC
    refine hxJ (hJ₀min J hJopen ?_ ?_ hJm hx)
    · exact le_trans (le_trans (fun z hz => subset_closure hz) le_sup_right) hCJ
    · exact hCJ (Ideal.mem_sup_left hℓspan)
  -- **(9)** topological Nakayama finishes.
  have hMfg : (M₀ ⊔ Ideal.span {((ℓ : ℕ) : R)} : Ideal R).FG :=
    Submodule.FG.sup hM₀fg (Submodule.fg_span (Set.finite_singleton _))
  have hMm : (M₀ ⊔ Ideal.span {((ℓ : ℕ) : R)} : Ideal R) ≤ IsLocalRing.maximalIdeal R :=
    sup_le hM₀m (by rw [Ideal.span_le, Set.singleton_subset_iff]; exact hℓm)
  have hfinal : IsLocalRing.maximalIdeal R ≤
      (M₀ ⊔ Ideal.span {((ℓ : ℕ) : R)} : Ideal R) ⊔
        (IsLocalRing.maximalIdeal R ^ 2).closure := by
    refine le_trans hM₀le (sup_le (le_trans le_sup_left le_sup_left) ?_)
    refine le_trans hJ₀C (sup_le (le_trans le_sup_right le_sup_left) le_sup_right)
  have hge := le_of_le_sup_closure_sq hbasis _ hMfg hfinal
  exact (le_antisymm hMm hge) ▸ hMfg

/-- **A profinite local ring whose maximal ideal is open and finitely
generated carries the `𝔪`-adic topology and is `𝔪`-adically complete**
(PROVEN 2026-07-26 — the TOPOLOGY half of this module's cut, steps 1, 2
and 5 of the header route; no arithmetic, and no finiteness of the residue
field).

`IsAdic`: the powers `𝔪 ^ n` and the open ideals are cofinal in each
other. Downwards, every open ideal `I ≠ ⊤` contains some `𝔪 ^ n`, because
`R ⧸ I` is compact and discrete, hence a FINITE local ring, hence has
nilpotent maximal ideal (Artinian Jacobson-radical nilpotence), and `𝔪`
maps into it. Upwards, `𝔪 ^ n` is CLOSED, being finitely generated hence
the image of a compact `R ^ g` under a continuous map
(`Ideal.isCompact_of_fg`), and of FINITE INDEX, `R ⧸ 𝔪 ^ n` being finite
by `Ideal.finite_quotient_pow` over the finite `R ⧸ 𝔪`; a closed subgroup
of finite index is open (`AddSubgroup.isOpen_of_isClosed_of_finiteIndex`).
This is the same route mathlib takes for compact Hausdorff NOETHERIAN
rings in `Ideal.isOpen_pow_of_isMaximal`, with finite generation of `𝔪`
in place of the Noetherian hypothesis that is not yet available here.

`IsAdicComplete`: with the topology identified as the `𝔪`-adic one,
Hausdorffness gives `IsHausdorff` (adic separatedness) and compactness
gives `IsPrecomplete` — a compact Hausdorff topological group is a
complete uniform space, and a compatible sequence of cosets of the
`𝔪 ^ n` has the finite intersection property, so it has a limit. -/
theorem isAdic_isAdicComplete_of_isOpen_of_fg
    {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [CompactSpace R] [T2Space R]
    (hbasis : ∀ U ∈ nhds (0 : R), ∃ I : Ideal R, IsOpen (I : Set R) ∧
      (I : Set R) ⊆ U)
    (hopen : IsOpen ((IsLocalRing.maximalIdeal R : Ideal R) : Set R))
    (hfg : (IsLocalRing.maximalIdeal R).FG) :
    IsAdic (IsLocalRing.maximalIdeal R) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal R) R := by
  classical
  set 𝔪 : Ideal R := IsLocalRing.maximalIdeal R with h𝔪
  -- An ideal of `R`, seen as a submodule, is its own multiple by the top module.
  have hst : ∀ J : Ideal R, J • (⊤ : Submodule R R) = J := fun J => by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  -- **An open ideal has finite quotient**: the quotient is discrete (the
  -- quotient map is open) and compact.
  have hfinq : ∀ I : Ideal R, IsOpen (I : Set R) → Finite (R ⧸ I) := by
    intro I hI
    haveI : DiscreteTopology (R ⧸ I) := by
      rw [discreteTopology_iff_isOpen_singleton_zero]
      have hz : ({0} : Set (R ⧸ I)) = Ideal.Quotient.mk I '' (I : Set R) := by
        ext x
        constructor
        · rintro rfl
          exact ⟨0, I.zero_mem, map_zero _⟩
        · rintro ⟨y, hy, rfl⟩
          exact (Ideal.Quotient.eq_zero_iff_mem).mpr hy
      rw [hz]
      exact (QuotientRing.isOpenQuotientMap_mk I).isOpenMap _ hI
    exact finite_of_compact_of_discrete
  haveI : Finite (R ⧸ 𝔪) := hfinq 𝔪 hopen
  -- **Every power of `𝔪` is open**: it is finitely generated, hence compact,
  -- hence closed, and `R ⧸ 𝔪 ^ n` is finite, so it has finite index.
  have hpowopen : ∀ n : ℕ, IsOpen ((𝔪 ^ n : Ideal R) : Set R) := by
    intro n
    haveI : Finite (R ⧸ 𝔪 ^ n) := Ideal.finite_quotient_pow hfg n
    have hcl : IsClosed ((𝔪 ^ n : Ideal R) : Set R) :=
      (Ideal.isCompact_of_fg (Ideal.FG.pow (n := n) hfg)).isClosed
    haveI : (𝔪 ^ n : Ideal R).toAddSubgroup.FiniteIndex :=
      @AddSubgroup.finiteIndex_of_finite_quotient _ _ _
        (inferInstanceAs (Finite (R ⧸ (𝔪 ^ n : Ideal R))))
    exact (𝔪 ^ n : Ideal R).toAddSubgroup.isOpen_of_isClosed_of_finiteIndex hcl
  -- **Every open ideal contains a power of `𝔪`**: its quotient is a FINITE
  -- local ring, whose maximal ideal is therefore nilpotent.
  have hple : ∀ I : Ideal R, IsOpen (I : Set R) →
      ∃ n : ℕ, (𝔪 ^ n : Ideal R) ≤ I := by
    intro I hI
    rcases eq_or_ne I ⊤ with rfl | hItop
    · exact ⟨0, le_top⟩
    haveI := hfinq I hI
    haveI : Nontrivial (R ⧸ I) := by
      rw [← not_subsingleton_iff_nontrivial, Ideal.Quotient.subsingleton_iff]
      exact hItop
    haveI : IsLocalHom (Ideal.Quotient.mk I) :=
      isLocalHom_of_le_jacobson_bot I (by
        rw [IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top]
        exact IsLocalRing.le_maximalIdeal hItop)
    haveI : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    haveI : IsArtinianRing (R ⧸ I) := isArtinian_of_finite
    obtain ⟨N, hN⟩ : ∃ N : ℕ, IsLocalRing.maximalIdeal (R ⧸ I) ^ N = ⊥ := by
      obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R ⧸ I)
      exact ⟨N, by
        rwa [IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal (R ⧸ I)) bot_ne_top,
          Ideal.zero_eq_bot] at hN⟩
    refine ⟨N, ?_⟩
    have hmapmono : (𝔪).map (Ideal.Quotient.mk I) ≤
        IsLocalRing.maximalIdeal (R ⧸ I) := by
      rw [Ideal.map_le_iff_le_comap]
      intro y hy
      show Ideal.Quotient.mk I y ∈ IsLocalRing.maximalIdeal (R ⧸ I)
      rw [IsLocalRing.mem_maximalIdeal] at hy ⊢
      exact fun hu => hy (isUnit_of_map_unit (Ideal.Quotient.mk I) y hu)
    have hmono : ∀ n : ℕ, ((𝔪).map (Ideal.Quotient.mk I)) ^ n ≤
        IsLocalRing.maximalIdeal (R ⧸ I) ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ m ih => rw [pow_succ, pow_succ]; exact Ideal.mul_mono ih hmapmono
    have hpow : ((𝔪) ^ N).map (Ideal.Quotient.mk I) = ⊥ := by
      rw [Ideal.map_pow, ← le_bot_iff, ← hN]
      exact hmono N
    rwa [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at hpow
  -- **The topology IS the `𝔪`-adic one**: the two families are cofinal.
  have hadic : IsAdic 𝔪 := by
    rw [isAdic_iff]
    refine ⟨hpowopen, fun s hs => ?_⟩
    obtain ⟨I, hIopen, hIs⟩ := hbasis s hs
    obtain ⟨n, hn⟩ := hple I hIopen
    exact ⟨n, fun x hx => hIs (hn hx)⟩
  refine ⟨hadic, ?_⟩
  -- **Adic separatedness** is Hausdorffness: an element inside every `𝔪 ^ n`
  -- lies in every neighbourhood of `0`.
  haveI : IsHausdorff 𝔪 R := by
    constructor
    intro x hx
    by_contra hx0
    obtain ⟨n, hn⟩ := (isAdic_iff.mp hadic).2 ({x}ᶜ)
      (compl_singleton_mem_nhds (Ne.symm hx0))
    have hxmem : x ∈ (𝔪 ^ n : Ideal R) := by
      have h := hx n
      rw [SModEq.sub_mem, hst, sub_zero] at h
      exact h
    exact (hn hxmem) rfl
  -- **Adic precompleteness** is compactness: the cosets `f n + 𝔪 ^ n` are
  -- closed, nonempty and nested, so they have a common point.
  haveI : IsPrecomplete 𝔪 R := by
    constructor
    intro f hf
    set C : ℕ → Set R := fun n => (fun y : R => y - f n) ⁻¹' ((𝔪 ^ n : Ideal R))
      with hC
    have hCclosed : ∀ n, IsClosed (C n) :=
      fun n => IsClosed.preimage (by fun_prop)
        (Ideal.isCompact_of_fg (Ideal.FG.pow (n := n) hfg)).isClosed
    have hanti : ∀ {m n : ℕ}, m ≤ n → C n ⊆ C m := by
      intro m n hmn y hy
      have h1 : y - f n ∈ (𝔪 ^ n : Ideal R) := hy
      have h2 : f m - f n ∈ (𝔪 ^ m : Ideal R) := by
        have h := hf hmn
        rw [SModEq.sub_mem, hst] at h
        exact h
      show y - f m ∈ (𝔪 ^ m : Ideal R)
      have h3 : y - f m = (y - f n) - (f m - f n) := by ring
      rw [h3]
      exact Ideal.sub_mem _ (Ideal.pow_le_pow_right hmn h1) h2
    obtain ⟨L, hL⟩ : (⋂ n, C n).Nonempty := by
      refine IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C
        (fun m n => ⟨max m n, hanti (le_max_left m n), hanti (le_max_right m n)⟩)
        (fun n => ⟨f n, by simp [hC]⟩)
        (fun n => (hCclosed n).isCompact) hCclosed
    refine ⟨L, fun n => ?_⟩
    rw [SModEq.sub_mem, hst]
    have hLn : L - f n ∈ (𝔪 ^ n : Ideal R) := Set.mem_iInter.mp hL n
    have h4 : f n - L = -(L - f n) := by ring
    rw [h4]
    exact neg_mem hLn
  constructor

/-- **A profinite local ring with finitely many points in every finite test
ring is Noetherian, `𝔪`-adic and `𝔪`-adically complete** (PROVEN
2026-07-26 over the two leaves above and
`CompleteLocalNoetherian.isNoetherianRing_of_isAdicComplete_of_fg`; the
FINITENESS half of the Schlessinger core, isolated the same day as pure
commutative algebra — see this module's header for the full route and for
the counterexample showing the hypothesis cannot be dropped).

`R` is a compact Hausdorff topological local `ℤ_ℓ`-algebra whose open
ideals form a neighbourhood basis of `0` — i.e. a profinite local ring —
with residue field the finite field `k`, and `hhom` says `R` has only
FINITELY many continuous `ℤ_ℓ`-algebra points lifting `π` in each finite
local `ℤ_ℓ`-algebra `A`. The conclusion is the three Mazur-category ring
clauses.

This is Mazur's `Φ_ℓ` criterion / the Noetherian clause of Schlessinger's
Theorem 2.11: what makes a pro-Artinian ring a genuine complete Noetherian
local ring is finiteness of its tangent space, and `hhom` at `A = k[ε]` is
exactly that finiteness.

CONSUMER. `exists_isStrictlyUniversalOnFrames_of_deformationCondition` in
`Deformation.lean`, which supplies `hhom` from the
restricted-ramification finiteness leaf: the continuous points of the
universal ring in `A` inject into the hardly ramified framed
representations over `A` (the injection being the minimality clause of
the hull, the target being finite by H3).

`hhom` QUANTIFIES ONLY OVER DISCRETE TEST RINGS (`[DiscreteTopology A]`,
added 2026-07-26): see `fg_maximalIdeal_of_finite_ringHom` above, which is
where the hypothesis is spent and which carries the identical binder. The
consumer's own `hfin` in `Deformation.lean` carries it too, so the three
statements are now aligned.

References: Mazur, *Deforming Galois representations*, MSRI Publ. 16
(1989), §1.2; Schlessinger, *Functors of Artin rings*, Trans. AMS 130
(1968), Thm 2.11; Stacks 05GH (the Noetherianity criterion, proven in
`CompleteLocalNoetherian.lean`). -/
theorem isNoetherianRing_isAdic_of_profinite_of_finite_ringHom
    {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Finite k]
    [Algebra ℤ_[ℓ] k] [TopologicalSpace k] [DiscreteTopology k]
    {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [Algebra ℤ_[ℓ] R] [CompactSpace R] [T2Space R]
    (hbasis : ∀ U ∈ nhds (0 : R), ∃ I : Ideal R, IsOpen (I : Set R) ∧
      (I : Set R) ⊆ U)
    (π : R →+* k) (hπsurj : Function.Surjective π) (hπcont : Continuous π)
    (hhom : ∀ (A : Type u) [CommRing A] [TopologicalSpace A]
      [IsTopologicalRing A] [IsLocalRing A] [Algebra ℤ_[ℓ] A] [Finite A]
      [DiscreteTopology A]
      (πA : A →+* k),
      {φ : R →+* A | Continuous φ ∧ πA.comp φ = π ∧
        φ.comp (algebraMap ℤ_[ℓ] R) = algebraMap ℤ_[ℓ] A}.Finite) :
    IsNoetherianRing R ∧ IsAdic (IsLocalRing.maximalIdeal R) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal R) R := by
  -- `𝔪 = ker π`, `π` being a surjection onto a field out of a local ring, and
  -- it is OPEN because `π` is continuous and `k` is discrete.
  have hker : RingHom.ker π = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective π hπsurj)
  have hopen : IsOpen ((IsLocalRing.maximalIdeal R : Ideal R) : Set R) := by
    rw [← hker, show ((RingHom.ker π : Ideal R) : Set R) = π ⁻¹' {0} from
      Set.ext fun x => by simp [RingHom.mem_ker]]
    exact (isOpen_discrete _).preimage hπcont
  have hfg : (IsLocalRing.maximalIdeal R).FG :=
    fg_maximalIdeal_of_finite_ringHom hbasis π hπsurj hπcont hhom
  obtain ⟨hadic, hcomplete⟩ :=
    isAdic_isAdicComplete_of_isOpen_of_fg hbasis hopen hfg
  exact ⟨CompleteLocalNoetherian.isNoetherianRing_of_isAdicComplete_of_fg
    hcomplete hfg, hadic, hcomplete⟩

end ProfiniteLocalNoetherian
