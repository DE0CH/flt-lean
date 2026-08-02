# HANDOFF — `exists_pow_eq_zero_surjective_aeval_of_heightOne` (ModThree.lean)

Written 2026-08-01 by `flt-lean-174`, whose target was
`exists_pow_eq_zero_surjective_aeval_of_local_finite_hopf_of_charP`
(`Fermat/FLT/GaloisRepresentation/HardlyRamified/ModThree.lean`).  That target is now PROVEN as
glue over two leaves; this file is a VERIFIED, SORRY-FREE Lean development of the mathematical
heart of the FIRST of them.

## What is in here, and what it is worth

The height-one leaf is **Milne, _Algebraic Groups_, CUP 2017, Prop. 11.28**, whose only real
content is **Lemma 11.27** — that the monomials of degree `< p` in a basis of `I/I²` are linearly
independent.  The text below is exactly that lemma, and it is the part a successor would otherwise
spend its whole run on.  It is **not committed as Lean** because nothing consumes it yet, and a
module under `Fermat/` that nothing imports is free-floating (CLAUDE.md's fourth invisibility
class).  Paste it into `ModThree.lean` (or a new `Fermat/FLT/Mathlib/...` module) TOGETHER WITH the
consumer that closes the leaf, and it stops being free-floating.

## COMPILE RECEIPT

Elaborated 2026-08-01 in `/home/chend/flt-lean-174` at `main` = `fe5131ca` with

    lake env lean Fermat/Scratch174b.lean      #  0 errors, 0 `sorry`, ~30 s

against the header

    module
    public import Mathlib.Algebra.MvPolynomial.CommRing
    public import Mathlib.RingTheory.MvPolynomial.Basic
    public import Mathlib.RingTheory.Derivation.Basic
    public import Mathlib.RingTheory.Ideal.Operations
    public import Fermat.FLT.GroupScheme.Cartier
    @[expose] public section

`Fermat.FLT.GroupScheme.Cartier` is reached from `ModThree.lean` through `X0.lean`
(`X0.lean:434` carries `public import Fermat.FLT.GroupScheme.Cartier`), so the ONE project
dependency below — `CartierTheorem.derivation_mem_pow` — resolves in `ModThree.lean` with no
import edit.  (Checked the same way `exists_monomial_quotient_algEquiv_of_local_finite_hopf_of_charZero`
already cites `CartierTheorem.isReduced_of_charZero`.)

## WHAT THIS GIVES YOU, AND WHAT IS LEFT

`eq_zero_of_sum_smul_xm_eq_zero` below says: over a field `K` of characteristic `p` (prime), given

* `x : σ → A`, `e : A →ₐ[K] K` with `e (x i) = 0`,
* derivations `D i` of `A` with `e (D i (x j)) = δᵢⱼ`,

any `K`-linear relation among the monomials `∏ x^m` with every exponent `< p` is trivial.  That is
`dim_k A ≥ p^r`, i.e. the hard half of Prop. 11.28.

**FOUR THINGS REMAIN** to close the leaf, all of them bookkeeping rather than mathematics:

1. **Build the `D i`.**  Take `x : Fin r → A` lifting a `k`-basis of `I/I²`; let `dᵢ : A →ₗ[K] K`
   be the functional killing `1` and `I²` and dual to that basis.  Then `dᵢ` is a POINT DERIVATION
   — copy the `hmul` block of `CartierTheorem.isIdempotentElem_ker_counit`
   (`Cartier.lean:353–370`) verbatim; it derives `D (ab) = ε a · D b + D a · ε b` from "kills `I²`"
   and "kills `1`" and nothing else — and
   `D i := CartierTheorem.pointDerivation dᵢ hmul hone` is the derivation, with
   `e (D i (x j)) = dᵢ (x j) = δᵢⱼ` by `CartierTheorem.counit_pointDerivation`.
2. **Spanning.**  `I` is nilpotent (`isArtinian_of_tower k` + `IsArtinianRing.isNilpotent_jacobson_bot`
   + `IsLocalRing.jacobson_eq_maximalIdeal`), and `I ⊆ span_k{monomials} + I^{n+1}` for every `n`
   by induction on `n` using `Submodule.mul_induction_on`, whence `Surjective (aeval x)` and the
   `p^r` box monomials span.
3. **`finrank ≤ p^r`.**  Already done in the file, inside
   `algEquiv_monomialQuotient_of_surjective_aeval` (its `hspan`/`hle` steps): surjectivity of
   `aeval x` plus `x i ^ p = 0` gives `finrank k A ≤ ∏ p = p^r`.  Extract or re-run those ~25 lines.
4. **Assemble**: `finrank = p^r` from `≤` and `≥`, and hand back `⟨r, x, …⟩`.

The bridge from `Multiset σ`-indexed monomials (used below) to the `Finset`-indexed spanning set of
step 3 is `Multiset.toList` / `Finsupp.toMultiset`; `xm x s` is `(s.map x).prod` by definition.

## THE VERIFIED TEXT

```lean
namespace HeightOneCore

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]
variable {σ : Type*} [DecidableEq σ]

/-- The product of a multiset of variables. -/
def xm (x : σ → A) (s : Multiset σ) : A := (s.map x).prod

@[simp] lemma xm_zero (x : σ → A) : xm x 0 = 1 := by simp [xm]

@[simp] lemma xm_cons (x : σ → A) (i : σ) (s : Multiset σ) :
    xm x (i ::ₘ s) = x i * xm x s := by simp [xm]

lemma xm_mem_pow (x : σ → A) (J : Ideal A) (hx : ∀ i, x i ∈ J) (s : Multiset σ) :
    xm x s ∈ J ^ Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons i s ih =>
    rw [xm_cons, Multiset.card_cons, pow_succ']
    exact Ideal.mul_mem_mul (hx i) ih

/-- **The one-step congruence.**  If `D` is a derivation with `D (x j) ≡ δᵢⱼ` modulo `J`, then
`D` applied to a monomial is the formal derivative modulo one more power of `J`. -/
lemma sub_smul_erase_mem_pow (x : σ → A) (J : Ideal A) (hx : ∀ i, x i ∈ J)
    (D : Derivation K A A) (i : σ) (hD : ∀ j, D (x j) - (if i = j then 1 else 0) ∈ J)
    (s : Multiset σ) :
    D (xm x s) - (Multiset.count i s) • xm x (s.erase i) ∈ J ^ Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    have hcard : Multiset.card (a ::ₘ t) = Multiset.card t + 1 := Multiset.card_cons a t
    have hleib : D (xm x (a ::ₘ t)) = x a * D (xm x t) + xm x t * D (x a) := by
      rw [xm_cons, D.leibniz]; simp [smul_eq_mul]
    have herr1 : x a * (D (xm x t) - (Multiset.count i t) • xm x (t.erase i))
        ∈ J ^ (Multiset.card t + 1) := by
      rw [pow_succ']
      exact Ideal.mul_mem_mul (hx a) ih
    by_cases hia : i = a
    · subst hia
      have hcount : Multiset.count i (i ::ₘ t) = Multiset.count i t + 1 := by
        simp [Multiset.count_cons_self]
      have herase : (i ::ₘ t).erase i = t := Multiset.erase_cons_head i t
      have hDxa : D (x i) - 1 ∈ J := by simpa using hD i
      have herr2 : xm x t * (D (x i) - 1) ∈ J ^ (Multiset.card t + 1) := by
        rw [pow_succ]
        exact Ideal.mul_mem_mul (xm_mem_pow x J hx t) hDxa
      have hkey : x i * ((Multiset.count i t) • xm x (t.erase i))
          = (Multiset.count i t) • xm x t := by
        by_cases hmem : i ∈ t
        · rw [mul_smul_comm]
          congr 1
          rw [← xm_cons, Multiset.cons_erase hmem]
        · rw [Multiset.count_eq_zero_of_notMem hmem]
          simp
      rw [hcard, hcount, herase, hleib]
      have hrw : x i * D (xm x t) + xm x t * D (x i) - (Multiset.count i t + 1) • xm x t
          = x i * (D (xm x t) - (Multiset.count i t) • xm x (t.erase i))
            + xm x t * (D (x i) - 1)
            + (x i * ((Multiset.count i t) • xm x (t.erase i))
                - (Multiset.count i t) • xm x t) := by
        simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
        ring
      rw [hrw, hkey, sub_self, add_zero]
      exact add_mem herr1 herr2
    · have hcount : Multiset.count i (a ::ₘ t) = Multiset.count i t :=
        Multiset.count_cons_of_ne hia t
      have herase : (a ::ₘ t).erase i = a ::ₘ t.erase i :=
        Multiset.erase_cons_tail t (fun h => hia h.symm)
      have hDxa : D (x a) ∈ J := by simpa [if_neg hia] using hD a
      have herr2 : xm x t * D (x a) ∈ J ^ (Multiset.card t + 1) := by
        rw [pow_succ]
        exact Ideal.mul_mem_mul (xm_mem_pow x J hx t) hDxa
      rw [hcard, hcount, herase, hleib, xm_cons]
      have hrw : x a * D (xm x t) + xm x t * D (x a)
          - (Multiset.count i t) • (x a * xm x (t.erase i))
          = x a * (D (xm x t) - (Multiset.count i t) • xm x (t.erase i))
            + xm x t * D (x a) := by
        simp only [smul_eq_mul, nsmul_eq_mul]
        ring
      rw [hrw]
      exact add_mem herr1 herr2



/-- Iterated derivations along a list, applied outermost-first. -/
def dl (D : σ → Derivation K A A) : List σ → (A →ₗ[K] A)
  | [] => LinearMap.id
  | i :: L => (D i).toLinearMap ∘ₗ dl D L

@[simp] lemma dl_nil (D : σ → Derivation K A A) (a : A) : dl D [] a = a := rfl

@[simp] lemma dl_cons (D : σ → Derivation K A A) (i : σ) (L : List σ) (a : A) :
    dl D (i :: L) a = D i (dl D L a) := rfl

/-- Iterating the filtration-lowering property of a derivation. -/
lemma dl_mem_pow (D : σ → Derivation K A A) (J : Ideal A) (L : List σ) :
    ∀ (n : ℕ) (a : A), a ∈ J ^ (L.length + n) → dl D L a ∈ J ^ n := by
  induction L with
  | nil => intro n a ha; simpa using ha
  | cons i L ih =>
    intro n a ha
    rw [dl_cons]
    refine CartierTheorem.derivation_mem_pow (D i) J n _ (ih (n + 1) a ?_)
    have hlen : (i :: L).length + n = L.length + (n + 1) := by
      simp only [List.length_cons]; omega
    rwa [hlen] at ha

/-- The natural-number coefficient produced by the iterated congruence. -/
def kap : List σ → Multiset σ → ℕ
  | [], _ => 1
  | i :: L, s => kap L s * Multiset.count i (s - (L : Multiset σ))

lemma erase_sub_cons (s t : Multiset σ) (i : σ) : (s - t).erase i = s - (i ::ₘ t) := by
  ext j
  rcases eq_or_ne j i with rfl | hji
  · simp [Multiset.count_erase_self, Multiset.count_sub, Multiset.count_cons_self]
    omega
  · simp [Multiset.count_erase_of_ne hji, Multiset.count_sub,
      Multiset.count_cons_of_ne (Ne.symm hji)]

lemma card_le_card_sub_add (s t : Multiset σ) :
    Multiset.card s ≤ Multiset.card (s - t) + Multiset.card t := by
  have := Multiset.card_le_card (Multiset.le_sub_add (s := s) (t := t))
  simpa using this

/-- **The iterated congruence.** -/
lemma dl_sub_kap_mem_pow (x : σ → A) (J : Ideal A) (hx : ∀ i, x i ∈ J)
    (D : σ → Derivation K A A)
    (hD : ∀ i j, D i (x j) - (if i = j then 1 else 0) ∈ J)
    (L : List σ) : ∀ (s : Multiset σ) (n : ℕ), Multiset.card s = L.length + n →
      dl D L (xm x s) - (kap L s) • xm x (s - (L : Multiset σ)) ∈ J ^ (n + 1) := by
  induction L with
  | nil => intro s n _; simp [dl, kap]
  | cons i L ih =>
    intro s n hs
    have hs' : Multiset.card s = L.length + (n + 1) := by
      simp only [List.length_cons] at hs; omega
    have hIH := ih s (n + 1) hs'
    -- the error already accumulated
    have hDrho : D i (dl D L (xm x s) - (kap L s) • xm x (s - (L : Multiset σ)))
        ∈ J ^ (n + 1) := by
      have := CartierTheorem.derivation_mem_pow (D i) J (n + 1) _ hIH
      exact this
    -- the fresh one-step error
    have hcard : n + 1 ≤ Multiset.card (s - (L : Multiset σ)) := by
      have h1 := card_le_card_sub_add s (L : Multiset σ)
      have h2 : Multiset.card (L : Multiset σ) = L.length := by simp
      omega
    have hstep := sub_smul_erase_mem_pow x J hx (D i) i (fun j => hD i j)
      (s - (L : Multiset σ))
    have hstep' : D i (xm x (s - (L : Multiset σ)))
        - (Multiset.count i (s - (L : Multiset σ))) • xm x ((s - (L : Multiset σ)).erase i)
        ∈ J ^ (n + 1) := Ideal.pow_le_pow_right hcard hstep
    have hexp : dl D (i :: L) (xm x s)
        - (kap (i :: L) s) • xm x (s - ((i :: L : List σ) : Multiset σ))
        = D i (dl D L (xm x s) - (kap L s) • xm x (s - (L : Multiset σ)))
          + (kap L s) • (D i (xm x (s - (L : Multiset σ)))
            - (Multiset.count i (s - (L : Multiset σ)))
              • xm x ((s - (L : Multiset σ)).erase i)) := by
      rw [erase_sub_cons, ← Multiset.cons_coe]
      show D i (dl D L (xm x s)) - _ = _
      rw [map_sub, map_nsmul]
      simp only [kap, smul_sub, smul_smul]
      ring_nf
    rw [hexp]
    exact add_mem hDrho (nsmul_mem hstep' _)


lemma not_dvd_kap (p : ℕ) (hp : p.Prime) :
    ∀ (L : List σ) (s : Multiset σ), (L : Multiset σ) ≤ s →
      (∀ i, Multiset.count i s < p) → ¬ p ∣ kap L s := by
  intro L
  induction L with
  | nil =>
    intro s _ _ h
    rw [kap] at h
    exact Nat.Prime.one_lt hp |>.ne' (Nat.dvd_one.mp h)
  | cons i L ih =>
    intro s hle hlt h
    have hcons : ((i :: L : List σ) : Multiset σ) = i ::ₘ (L : Multiset σ) :=
      (Multiset.cons_coe i L).symm
    have hleL : (L : Multiset σ) ≤ s :=
      le_trans (Multiset.le_cons_self _ i) (hcons ▸ hle)
    rw [kap] at h
    rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h2
    · exact ih s hleL hlt h1
    · have hcount : Multiset.count i ((i :: L : List σ) : Multiset σ) ≤ Multiset.count i s :=
        Multiset.count_le_of_le i hle
      have hci : Multiset.count i (L : Multiset σ) + 1 ≤ Multiset.count i s := by
        rw [hcons] at hcount; simpa [Multiset.count_cons_self] using hcount
      have hpos : 0 < Multiset.count i (s - (L : Multiset σ)) := by
        rw [Multiset.count_sub]; omega
      have hlt' : Multiset.count i (s - (L : Multiset σ)) < p := by
        have := hlt i
        rw [Multiset.count_sub]; omega
      exact absurd (Nat.le_of_dvd hpos h2) (by omega)

/-- **LINEAR INDEPENDENCE OF THE BOX MONOMIALS.**  This is Milne 2017, Lemma 11.27, in the
only form the height-one case needs. -/
theorem eq_zero_of_sum_smul_xm_eq_zero (p : ℕ) (hp : p.Prime) [CharP K p]
    (x : σ → A) (e : A →ₐ[K] K)
    (D : σ → Derivation K A A)
    (hx : ∀ i, e (x i) = 0)
    (hD : ∀ i j, e (D i (x j)) = if i = j then 1 else 0)
    (T : Finset (Multiset σ)) (hT : ∀ s ∈ T, ∀ i, Multiset.count i s < p)
    (c : Multiset σ → K) (hsum : ∑ s ∈ T, c s • xm x s = 0) :
    ∀ s ∈ T, c s = 0 := by
  classical
  set J : Ideal A := RingHom.ker (e : A →+* K) with hJ
  have hxJ : ∀ i, x i ∈ J := fun i => by simpa [hJ, RingHom.mem_ker] using hx i
  have hDJ : ∀ i j, D i (x j) - (if i = j then 1 else 0) ∈ J := by
    intro i j
    simp only [hJ, RingHom.mem_ker, map_sub]
    rw [show ((e : A →+* K) : A → K) = (e : A → K) from rfl, hD i j]
    by_cases h : i = j <;> simp [h]
  have hJmem : ∀ a : A, a ∈ J → e a = 0 := fun a ha => by
    simpa [hJ, RingHom.mem_ker] using ha
  by_contra hcon
  push_neg at hcon
  obtain ⟨s₁, hs₁T, hs₁⟩ := hcon
  set T' : Finset (Multiset σ) := T.filter (fun s => c s ≠ 0) with hT'
  have hT'ne : T'.Nonempty := ⟨s₁, by simp [hT', hs₁T, hs₁]⟩
  obtain ⟨s₀, hs₀T', hs₀min⟩ := T'.exists_min_image (fun s => Multiset.card s) hT'ne
  have hs₀T : s₀ ∈ T := (Finset.mem_filter.mp hs₀T').1
  have hs₀c : c s₀ ≠ 0 := by simpa using (Finset.mem_filter.mp hs₀T').2
  set L₀ : List σ := s₀.toList with hL₀
  have hL₀coe : (L₀ : Multiset σ) = s₀ := Multiset.coe_toList s₀
  have hL₀len : L₀.length = Multiset.card s₀ := by
    rw [hL₀, ← Multiset.coe_card, Multiset.coe_toList]
  -- apply `e ∘ dl D L₀` to the relation
  have happ : ∑ s ∈ T, c s * e (dl D L₀ (xm x s)) = 0 := by
    have h1 : e (dl D L₀ (∑ s ∈ T, c s • xm x s)) = 0 := by rw [hsum]; simp
    rw [map_sum, map_sum] at h1
    simpa [map_smul, smul_eq_mul] using h1
  have hone : ∀ s ∈ T, s ≠ s₀ → c s * e (dl D L₀ (xm x s)) = 0 := by
    intro s hsT hne
    by_cases hc : c s = 0
    · simp [hc]
    · have hsT' : s ∈ T' := Finset.mem_filter.mpr ⟨hsT, hc⟩
      have hcard : Multiset.card s₀ ≤ Multiset.card s := hs₀min s hsT'
      have hzero : e (dl D L₀ (xm x s)) = 0 := by
        rcases lt_or_eq_of_le hcard with hlt | heq
        · have hrw : L₀.length + (Multiset.card s - Multiset.card s₀) = Multiset.card s := by
            omega
          have h1 : xm x s ∈ J ^ (L₀.length + (Multiset.card s - Multiset.card s₀)) := by
            rw [hrw]; exact xm_mem_pow x J hxJ s
          have h2 := dl_mem_pow D J L₀ _ _ h1
          refine hJmem _ ?_
          have h3 : J ^ (Multiset.card s - Multiset.card s₀) ≤ J ^ 1 :=
            Ideal.pow_le_pow_right (by omega)
          simpa using h3 h2
        · have hlen : Multiset.card s = L₀.length + 0 := by omega
          have h1 := dl_sub_kap_mem_pow x J hxJ D hDJ L₀ s 0 hlen
          have hne0 : s - s₀ ≠ 0 := by
            intro h0
            exact hne (Multiset.eq_of_le_of_card_le
              (tsub_eq_zero_iff_le.mp h0) (by omega))
          have hcpos : 1 ≤ Multiset.card (s - s₀) := Multiset.card_pos.mpr hne0
          have h2 : xm x (s - s₀) ∈ J := by
            have h3 : J ^ Multiset.card (s - s₀) ≤ J ^ 1 := Ideal.pow_le_pow_right hcpos
            simpa using h3 (xm_mem_pow x J hxJ (s - s₀))
          refine hJmem _ ?_
          have h4 : dl D L₀ (xm x s) - kap L₀ s • xm x (s - s₀) ∈ J := by
            simpa [hL₀coe] using h1
          have h5 : kap L₀ s • xm x (s - s₀) ∈ J := nsmul_mem h2 _
          simpa using add_mem h4 h5
      simp [hzero]
  rw [Finset.sum_eq_single s₀ hone (fun h => absurd hs₀T h)] at happ
  -- the diagonal value
  have hdiag : e (dl D L₀ (xm x s₀)) = (kap L₀ s₀ : K) := by
    have hlen : Multiset.card s₀ = L₀.length + 0 := by omega
    have h1 := dl_sub_kap_mem_pow x J hxJ D hDJ L₀ s₀ 0 hlen
    have h2 : dl D L₀ (xm x s₀) - kap L₀ s₀ • (1 : A) ∈ J := by
      simpa [hL₀coe] using h1
    have h3 := hJmem _ h2
    rw [map_sub, map_nsmul] at h3
    simpa using sub_eq_zero.mp h3
  rw [hdiag] at happ
  have hkap : (kap L₀ s₀ : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K p]
    exact not_dvd_kap p hp L₀ s₀ (le_of_eq hL₀coe) (hT s₀ hs₀T)
  exact hs₀c (by
    rcases mul_eq_zero.mp happ with h | h
    · exact h
    · exact absurd h hkap)

end HeightOneCore
```

## STEP 1 IS ALSO VERIFIED, AND IT IS HERE

Elaborated 2026-08-01 in the same worktree, `0 errors, 0 sorry`, against the header

    module
    public import Fermat.FLT.GroupScheme.Cartier
    public import Mathlib.LinearAlgebra.Dimension.Finite
    public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
    @[expose] public section
    open Bialgebra HopfAlgebra Coalgebra CartierTheorem
    namespace Step1
    variable {K A : Type} [Field K] [CommRing A] [HopfAlgebra K A] [Module.Finite K A]
    local notation "ε" => (Bialgebra.counitAlgHom K A)

`exists_generators_and_derivations` below produces, in one shot, EVERYTHING the core lemma
needs plus the input to step 2:

* `x : Fin r -> A` lifting a `k`-basis of `I/I²` (with `r = finrank k (A ⧸ W)`),
* derivations `D i` of `A` with `ε (D i (x j)) = δᵢⱼ`,
* and `∀ a ∈ I, ∃ c, a - ∑ cᵢ xᵢ ∈ I²`, which is the hypothesis of step 2.

The trick that makes it short is to take the quotient by `W := I² + k·1` **as a `k`-submodule of
`A`**, not by `I²` inside `I`: then `A ⧸ W ≅ I/I²`, `Module.finBasis` gives a basis, every class
has a representative in `I` (subtract `ε(a)·1`), the dual functionals are
`b.coord i ∘ₗ W.mkQ` and they kill `1` and `I²` BY CONSTRUCTION -- which is exactly the
hypothesis `pointDerivation_hmul` needs.  No `Ideal.Cotangent`, no `IsLocalRing.CotangentSpace`,
and no residue-field bookkeeping anywhere.

```lean
namespace Step1
variable {K A : Type} [Field K] [CommRing A] [HopfAlgebra K A] [Module.Finite K A]
local notation "ε" => (Bialgebra.counitAlgHom K A)


variable {K A : Type} [Field K] [CommRing A] [HopfAlgebra K A] [Module.Finite K A]

local notation "ε" => (Bialgebra.counitAlgHom K A)

/-- The `k`-subspace `k·1 + I²`, whose quotient is `I/I²`. -/
noncomputable def W : Submodule K A :=
  Submodule.restrictScalars K (RingHom.ker (ε : A →+* K) * RingHom.ker (ε : A →+* K))
    ⊔ (K ∙ (1 : A))

/-- Every class in `A ⧸ W` has a representative in the augmentation ideal. -/
lemma exists_rep_mem_ker (v : A ⧸ (W (K := K) (A := A))) :
    ∃ a : A, ε a = 0 ∧ Submodule.Quotient.mk a = v := by
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  refine ⟨b - algebraMap K A (ε b), by simp, ?_⟩
  rw [Submodule.Quotient.eq]
  have hrw : b - algebraMap K A (ε b) - b = -(algebraMap K A (ε b)) := by ring
  rw [hrw]
  refine neg_mem ?_
  rw [Algebra.algebraMap_eq_smul_one]
  exact Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))

/-- A functional killing `W` kills `1` and `I²`, hence is a POINT DERIVATION. -/
lemma pointDerivation_hmul (D : A →ₗ[K] K) (hW : ∀ y ∈ (W (K := K) (A := A)), D y = 0) :
    (∀ a b : A, D (a * b) = ε a * D b + D a * ε b) ∧ D 1 = 0 := by
  have hone : D 1 = 0 :=
    hW 1 (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  have hDII : ∀ y ∈ RingHom.ker (ε : A →+* K) * RingHom.ker (ε : A →+* K), D y = 0 :=
    fun y hy => hW y (Submodule.mem_sup_left hy)
  refine ⟨?_, hone⟩
  intro a b
  have hlin : ∀ (c : K) (z : A), D (algebraMap K A c * z) = c * D z := by
    intro c z; rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have hmemI : ∀ z : A, z ∈ RingHom.ker (ε : A →+* K) ↔ ε z = 0 := fun _ => RingHom.mem_ker
  have ha : a - algebraMap K A (ε a) ∈ RingHom.ker (ε : A →+* K) := by
    rw [hmemI]; simp
  have hb : b - algebraMap K A (ε b) ∈ RingHom.ker (ε : A →+* K) := by
    rw [hmemI]; simp
  have hprod : D ((a - algebraMap K A (ε a)) * (b - algebraMap K A (ε b))) = 0 :=
    hDII _ (Ideal.mul_mem_mul ha hb)
  have hexp : (a - algebraMap K A (ε a)) * (b - algebraMap K A (ε b))
      = a * b - algebraMap K A (ε a) * b - algebraMap K A (ε b) * a
        + algebraMap K A (ε a * ε b) * 1 := by
    rw [map_mul]; ring
  rw [hexp] at hprod
  simp only [map_add, map_sub, hlin, hone, mul_zero, add_zero] at hprod
  linear_combination hprod

/-- `W ∩ ker ε = I²`. -/
lemma mem_sq_of_mem_W_of_counit_eq_zero (a : A) (haW : a ∈ (W (K := K) (A := A)))
    (ha : ε a = 0) :
    a ∈ RingHom.ker (ε : A →+* K) * RingHom.ker (ε : A →+* K) := by
  obtain ⟨z, hz, u, hu, rfl⟩ := Submodule.mem_sup.mp haW
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
  have hzI : ε z = 0 := by
    have : z ∈ RingHom.ker (ε : A →+* K) := Ideal.mul_le_left hz
    simpa [RingHom.mem_ker] using this
  have hc : c = 0 := by
    have := ha
    rw [map_add, hzI, zero_add] at this
    simpa [Algebra.smul_def] using this
  have hz' : z ∈ RingHom.ker (ε : A →+* K) * RingHom.ker (ε : A →+* K) :=
    (Submodule.restrictScalars_mem K _ _).mp hz
  simpa [hc] using hz'

/-- **STEP 1: the generators and the dual invariant derivations.** -/
lemma exists_generators_and_derivations :
    ∃ (r : ℕ) (x : Fin r → A) (D : Fin r → Derivation K A A),
      (∀ i, ε (x i) = 0) ∧
      (∀ i j, ε (D i (x j)) = if i = j then 1 else 0) ∧
      (∀ a : A, ε a = 0 → ∃ c : Fin r → K,
          a - ∑ i, c i • x i ∈ RingHom.ker (ε : A →+* K) * RingHom.ker (ε : A →+* K)) := by
  classical
  haveI : Module.Finite K (A ⧸ (W (K := K) (A := A))) :=
    Module.Finite.of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)
  set b := Module.finBasis K (A ⧸ (W (K := K) (A := A))) with hbdef
  choose x hx hxb using fun i => exists_rep_mem_ker (K := K) (A := A) (b i)
  -- the functionals
  set d : Fin (Module.finrank K (A ⧸ (W (K := K) (A := A)))) → (A →ₗ[K] K) :=
    fun i => (b.coord i).comp (Submodule.mkQ (W (K := K) (A := A))) with hddef
  have hdW : ∀ i, ∀ y ∈ (W (K := K) (A := A)), d i y = 0 := by
    intro i y hy
    simp only [hddef, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [(Submodule.Quotient.mk_eq_zero _).mpr hy, map_zero]
  have hdual : ∀ i j, d i (x j) = if i = j then 1 else 0 := by
    intro i j
    simp only [hddef, LinearMap.comp_apply, Submodule.mkQ_apply, hxb j,
      Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  refine ⟨_, x, fun i => pointDerivation (d i) (pointDerivation_hmul (d i) (hdW i)).1
    (pointDerivation_hmul (d i) (hdW i)).2, hx, ?_, ?_⟩
  · intro i j
    rw [counit_pointDerivation]
    exact hdual i j
  · intro a ha
    refine ⟨fun i => b.repr (Submodule.Quotient.mk a) i, ?_⟩
    have hcount : ε (a - ∑ i, (b.repr (Submodule.Quotient.mk a)) i • x i) = 0 := by
      rw [map_sub, map_sum, ha]
      simp [hx]
    refine mem_sq_of_mem_W_of_counit_eq_zero _ ?_ hcount
    refine (Submodule.Quotient.mk_eq_zero _).mp ?_
    rw [← Submodule.mkQ_apply, map_sub, map_sum]
    simp only [map_smul, Submodule.mkQ_apply, hxb]
    rw [Module.Basis.sum_repr, sub_self]

end Step1
```

## WHAT IS LEFT AFTER THIS (steps 2-4), and the one place I hit friction

With the core and step 1 above, the height-one leaf needs only:

* **step 2** -- `Algebra.adjoin K (Set.range x) = ⊤`, hence `Surjective (aeval x)`.  The
  induction that works is on the FILTRATION, and the naive form is FALSE, so use this one:

      ∀ n, ∀ a ∈ I ^ n, ∃ m, m ∈ S ∧ m ∈ I ^ n ∧ a - m ∈ I ^ (n+1)

  (`S := Algebra.adjoin K (Set.range x)`).  The `m ∈ I ^ n` conjunct is load-bearing: without it
  the product step needs `mᵤ * z ∈ I^(n+2)` for `z ∈ I²` and an arbitrary `mᵤ ∈ S`, which is
  false.  `Submodule.mul_induction_on` on `I^(n+1) = I^n * I` is the step, the base case is
  `m = algebraMap K A (ε a)`, and then chain `I ⊆ S ⊔ I² ⊆ S ⊔ I³ ⊆ … ⊆ S ⊔ I^N = S` using
  nilpotence.  **I got the `key` induction to within two small errors and ran out of budget; the
  chaining step after it is untouched.**  Nilpotence of `I`: `isArtinian_of_tower k inferInstance`
  then `IsArtinianRing.isNilpotent_jacobson_bot` rewritten by
  `IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal A) bot_ne_top` (this is elaborated and
  recorded on the leaf's own docstring in `ModThree.lean`).
* **step 3** -- `finrank k A ≤ p ^ r` from surjectivity of `aeval x` and `x i ^ p = 0`.  Do NOT
  re-derive it: `algEquiv_monomialQuotient_of_surjective_aeval` in `ModThree.lean` contains
  exactly this argument in its `hspan`/`hle` steps (span by standard monomials, then
  `finrank_le_of_span_eq_top`, then `LinearMap.finrank_le_finrank_of_surjective`).
* **step 4** -- `finrank k A ≥ p ^ r` from the core lemma.  The core is stated for a
  `Finset (Multiset σ)`; to feed `LinearIndependent.fintype_card_le_finrank` (which gives
  `Fintype.card ι ≤ finrank`) index the box by `ι := Fin r → Fin p`, whose card is `p ^ r`, and
  push a relation over `Finset ι` forward along the injective `f : ι → Multiset σ` with
  `Finset.sum_image`.  `f m` is the multiset with `count i = m i`.

Finally note `x i ^ p = 0` is immediate from the leaf's height-one hypothesis `_hh` applied to
`x i`, since `ε (x i) = 0`.
