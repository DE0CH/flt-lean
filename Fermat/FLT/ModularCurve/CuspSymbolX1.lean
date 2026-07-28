/-
ModularCurve/CuspSymbolX1.lean — own work for the Fermat project (not
vendored from the FLT project).

# Cusp symbols for `Γ₁(N)`, and the count of the Galois-fixed ones

This module is pure finite arithmetic.  It carries no schemes, no moduli
and no geometry; it exists so that the ONE genuinely geometric obligation
left in the `Γ₁` cusp cluster —
`Fermat.exists_cuspSymbolEmbedding_x1_finiteField` in `ModularCurve/X1.lean` —
can be stated without also carrying the level-`25` arithmetic, and so that
that arithmetic can be PROVEN here rather than assumed there.

## What a cusp symbol is

The cusps of `X_1(N)` over `ℚ̄` are `Γ_1(N)∖ℙ¹(ℚ)`.  Writing a point of
`ℙ¹(ℚ)` as a primitive column vector `(a, c)` and reducing mod `N`, the
subgroup `Γ_1(N)` — matrices `[[α, β], [γ, δ]]` with `α ≡ δ ≡ 1` and
`γ ≡ 0 (mod N)` — acts by

    (a, c) ↦ (α a + β c, γ a + δ c) ≡ (a + β c, c)   (mod N),

so `c` is an invariant mod `N` and `a` matters only modulo `gcd(c, N)`;
`-I` identifies `(a, c)` with `(-a, -c)`.  That is exactly `cuspRelX1`
below, and `CuspSymbolX1 N` is the quotient.  Primitivity of `(a, c)` is
`IsCoprime c a` in `ZMod N`, which is preserved by the relation, so it
descends to `IsPrimitiveCuspSymbolX1`.

The classical count `#cusps = ½ Σ_{d ∣ N} φ(d) φ(N/d)` (`28` at `N = 25`)
is a consequence and is NOT needed here — nothing below counts all cusps,
only the Galois-fixed ones.

## The Galois action, and WHICH coordinate it moves

`cuspFrobX1 N t` is `(c, a) ↦ (c, t a)`: the cyclotomic character moves the
coordinate that lives modulo `gcd(c, N)`, and fixes the coordinate `c` that
records which Néron polygon the cusp degenerates to.  This is not a
convention that can be chosen freely, and getting it backwards would make
`exists_cuspSymbolEmbedding_x1_finiteField` false, so here is the check.

At the cusp `(a : 0)` the Tate curve degenerates to the Néron `1`-gon and
the `Γ₁`-structure is the root of unity `ζ_N^a` in `μ_N ⊆ Ḡ_m/q^ℤ`; Galois
acts on roots of unity by `ζ ↦ ζ^t`, hence by `a ↦ t a`.  At the cusp
`(0 : c)` with `c` a unit the level structure is `q^{1/N}` in the component
group, on which Galois acts trivially — those cusps are individually
rational.  So the rational family is `{c a unit}`, of size `φ(N)/2`, and the
family `{c = 0}` is the `μ_N`-family defined over `ℚ(ζ_N)⁺`.  That is the
Deligne–Rapoport description quoted in `IsX1Compactification.CuspLocus`'s
docstring — "(Néron `N`-gon, generator of the component group `ℤ/N`)"
rational, "(Néron `1`-gon, generator of `μ_N`)" not — and it is confirmed
numerically: at `(N, t) = (25, 3)` the orbit sizes of `cuspFrobX1` on the
`28` symbols are `1` ten times, `4` twice and `10` once, i.e. `10` rational
cusps, `8` cusps with residue field `𝔽_{3^4}` and `10` with `𝔽_{3^10}` —
exactly the residue degrees `card_cuspLocusPoints_x1_finiteField_le`'s
docstring computes from `ord_25(3) = 20` and `ord_5(3) = 4`.

Note the two prose conventions in `X1.lean` (`numRationalCuspsX1` says the
rational orbit lies over `∞` of `X_0(N)`, `CuspLocus` says the literature
disagrees about that) are about the NAME of the rational family, not about
which coordinate Galois moves; nothing here depends on that name.

## The main theorem, and why its hypotheses are both load-bearing

`card_fixedCuspSymbolX1`: for `2 < N` and `t : ZMod N` with `t - 1` and
`t + 1` both units, the `σ_t`-fixed primitive cusp symbols number exactly
`φ(N)/2`.

Both unit hypotheses are REFUTED if dropped, at `N = 25`:

* `t = 1` (i.e. `ℓ ≡ 1 mod N`): `t - 1 = 0`.  Every symbol is fixed, so the
  count is `28`, not `10`.
* `t = -1` (i.e. `ℓ ≡ -1 mod N`): `t + 1 = 0`.  The fixed count is `20`,
  not `10` — the whole `c = 0` family becomes fixed, because `a ↦ -a` is
  absorbed by the `±` identification.

Both were checked by exhaustive enumeration over `(ZMod 25)²`.  The second
is the reason the leaf above CANNOT be generalised over all `(N, ℓ)` with
`ℓ ∤ N`: `card_cuspLocusPoints_x1_finiteField_le`'s bound `≤ φ(N)/2` is
FALSE for any prime `ℓ ≡ ±1 (mod N)`, and the arithmetic hypothesis that
excludes those is exactly `IsUnit (t - 1) ∧ IsUnit (t + 1)`.

## Where the geometry went

Everything in this module is proven — the module has no `sorry`.  What is
left open is one statement in `X1.lean`, that the `𝔽_ℓ`-rational points of
the cusp locus of `X_1(N)_{𝔽_ℓ}` inject into the Frobenius-fixed cusp
symbols.  That is the hard direction of Ogg's description of the cusps, and
it is now geometry ONLY: no level, no prime, no counting.
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Fermat

/-! ### The symbol set -/

/-- **The `Γ_1(N)`-equivalence on pairs `(c, a) ∈ (ℤ/N)²`.**

`(c, a) ~ (c, a + j c)` (the unipotent part of `Γ_1(N)`) and
`(c, a) ~ (-c, -(a + j c))` (that, composed with `-I`).  Stated as a single
`∃ j` with a disjunction rather than as a generated equivalence, because in
this form reflexivity, symmetry and transitivity are one-line computations
— the composite of two steps is again a step with parameter `j + k`. -/
def cuspRelX1 (N : ℕ) (p q : ZMod N × ZMod N) : Prop :=
  ∃ j : ZMod N, q = (p.1, p.2 + j * p.1) ∨ q = (-p.1, -(p.2 + j * p.1))

theorem cuspRelX1_refl (N : ℕ) (p : ZMod N × ZMod N) : cuspRelX1 N p p :=
  ⟨0, Or.inl (by simp)⟩

theorem cuspRelX1_symm {N : ℕ} {p q : ZMod N × ZMod N} (h : cuspRelX1 N p q) :
    cuspRelX1 N q p := by
  obtain ⟨j, hj | hj⟩ := h <;> subst hj <;> refine ⟨-j, ?_⟩
  · exact Or.inl (by simp)
  · exact Or.inr (by simp)

theorem cuspRelX1_trans {N : ℕ} {p q r : ZMod N × ZMod N}
    (h₁ : cuspRelX1 N p q) (h₂ : cuspRelX1 N q r) : cuspRelX1 N p r := by
  obtain ⟨j, hj | hj⟩ := h₁ <;> subst hj <;> obtain ⟨k, hk | hk⟩ := h₂ <;> subst hk <;>
      refine ⟨j + k, ?_⟩
  · exact Or.inl (by simp [Prod.ext_iff]; ring)
  · exact Or.inr (by simp [Prod.ext_iff]; ring)
  · exact Or.inr (by simp [Prod.ext_iff]; ring)
  · exact Or.inl (by simp [Prod.ext_iff]; ring)

instance cuspSetoidX1 (N : ℕ) : Setoid (ZMod N × ZMod N) where
  r := cuspRelX1 N
  iseqv := ⟨cuspRelX1_refl N, cuspRelX1_symm, cuspRelX1_trans⟩

/-- **The cusp symbols of `Γ_1(N)`**, i.e. `Γ_1(N)∖ℙ¹(ℚ)` written mod `N`.

An `abbrev` rather than a `def` so that `Quotient.mk`, `Quotient.sound`,
`Quotient.exact` and `Quotient.inductionOn` apply without unfolding
obligations at every use. -/
abbrev CuspSymbolX1 (N : ℕ) : Type := Quotient (cuspSetoidX1 N)

/-- Primitivity is preserved by the relation, in both directions. -/
theorem cuspRelX1_isCoprime {N : ℕ} {p q : ZMod N × ZMod N} (h : cuspRelX1 N p q) :
    IsCoprime p.1 p.2 → IsCoprime q.1 q.2 := by
  obtain ⟨j, hj | hj⟩ := h <;> subst hj <;> intro hp
  · simpa [mul_comm] using hp.add_mul_left_right j
  · simpa [mul_comm] using (hp.add_mul_left_right j).neg_neg

/-- **A cusp symbol is primitive when a representing pair is.**

`IsCoprime c a` in `ZMod N` is the mod-`N` shadow of `gcd(a, c) = 1` for the
integral column vector, i.e. `gcd(a, c, N) = 1`, which is what makes `(a, c)`
the reduction of an actual point of `ℙ¹(ℚ)`. -/
def IsPrimitiveCuspSymbolX1 (N : ℕ) (s : CuspSymbolX1 N) : Prop :=
  Quotient.liftOn s (fun p => IsCoprime p.1 p.2) fun _ _ h =>
    propext ⟨cuspRelX1_isCoprime h, cuspRelX1_isCoprime (cuspRelX1_symm h)⟩

/-- **The Galois action `σ_t` on cusp symbols**, `(c, a) ↦ (c, t a)`.

Well defined for EVERY `t`, not only for units — the relation's parameter
transforms by `j ↦ t j` — although only unit `t` arises geometrically (over
`𝔽_ℓ` with `ℓ ∤ N` the Frobenius parameter is `ℓ`, a unit mod `N`), and only
unit `t` preserves primitivity.  Keeping the definition total is what lets
`CuspSymbolX1` avoid carrying primitivity in its type. -/
def cuspFrobX1 (N : ℕ) (t : ZMod N) : CuspSymbolX1 N → CuspSymbolX1 N :=
  Quotient.map (fun p => (p.1, t * p.2)) <| by
    rintro p q ⟨j, hj | hj⟩ <;> subst hj <;> refine ⟨t * j, ?_⟩
    · exact Or.inl (by simp [Prod.ext_iff]; ring)
    · exact Or.inr (by simp [Prod.ext_iff]; ring)

@[simp] theorem cuspFrobX1_mk (N : ℕ) (t : ZMod N) (p : ZMod N × ZMod N) :
    cuspFrobX1 N t (Quotient.mk _ p) = Quotient.mk _ (p.1, t * p.2) := rfl

@[simp] theorem isPrimitiveCuspSymbolX1_mk (N : ℕ) (p : ZMod N × ZMod N) :
    IsPrimitiveCuspSymbolX1 N (Quotient.mk _ p) ↔ IsCoprime p.1 p.2 := Iff.rfl

/-! ### The symbols with unit first coordinate -/

/-- **A symbol with unit `c` has a representative with `a = 0`**: the shift
`a ↦ a + j c` is transitive on the second coordinate when `c` is invertible. -/
theorem cuspSymbol_eq_of_isUnit {N : ℕ} {c : ZMod N} (a : ZMod N) (hc : IsUnit c) :
    (Quotient.mk (cuspSetoidX1 N) (c, a)) = Quotient.mk _ (c, 0) := by
  obtain ⟨w, hw⟩ := hc.exists_left_inv
  refine Quotient.sound ⟨-(a * w), Or.inl ?_⟩
  have hw' : w * c = 1 := hw
  simp only [Prod.mk.injEq, true_and]
  linear_combination a * hw'

/-- **The easy direction: every symbol with unit `c` is `σ_t`-fixed**, for
every `t`.  These are the `φ(N)/2` rational cusps. -/
theorem cuspFrob_fixed_of_isUnit {N : ℕ} (t : ZMod N) {c : ZMod N} (a : ZMod N) (hc : IsUnit c) :
    cuspFrobX1 N t (Quotient.mk _ (c, a)) = Quotient.mk _ (c, a) := by
  rw [cuspFrobX1_mk, cuspSymbol_eq_of_isUnit (t * a) hc, cuspSymbol_eq_of_isUnit a hc]

/-- **The hard direction: a `σ_t`-fixed primitive symbol has unit first
coordinate**, provided `t - 1` and `t + 1` are units.

This is the whole arithmetic content of Ogg's description at a fixed
`(N, ℓ)`, and the proof is three lines of ring theory rather than a case
analysis on `gcd(c, N)`.  Fixedness says `(c, t a) ∼ (c, a)`, and the two
branches of the relation give

* `a = t a + j c`, i.e. `(t - 1) a = -j c`;
* `a = -(t a + j c)`, i.e. `(t + 1) a = -j c`.

In both cases the unit hypothesis makes `a` a multiple of `c`, and a
primitive pair `(c, k c)` forces `c` to be a unit.  Note no localness of
`ZMod N` is used, so the statement holds at composite `N` as well. -/
theorem isUnit_fst_of_cuspFrob_fixed {N : ℕ} {t : ZMod N} (ht1 : IsUnit (t - 1))
    (ht2 : IsUnit (t + 1)) {c a : ZMod N} (hprim : IsCoprime c a)
    (hfix : cuspFrobX1 N t (Quotient.mk _ (c, a)) = Quotient.mk _ (c, a)) : IsUnit c := by
  have key : ∀ u : ZMod N, IsUnit u → ∀ j : ZMod N, u * a = (-j) * c → IsUnit c := by
    intro u hu j hj
    obtain ⟨w, hw⟩ := hu.exists_left_inv
    have hac : a = (w * (-j)) * c := by
      calc a = (w * u) * a := by rw [hw, one_mul]
        _ = w * (u * a) := by ring
        _ = w * ((-j) * c) := by rw [hj]
        _ = (w * (-j)) * c := by ring
    obtain ⟨x, y, hxy⟩ := hprim
    exact IsUnit.of_mul_eq_one (x + y * (w * (-j))) (by rw [← hxy, hac]; ring)
  rw [cuspFrobX1_mk] at hfix
  obtain ⟨j, hj | hj⟩ := Quotient.exact hfix
  · refine key (t - 1) ht1 j ?_
    have h2 := congrArg Prod.snd hj
    simp only at h2
    linear_combination -h2
  · refine key (t + 1) ht2 j ?_
    have h2 := congrArg Prod.snd hj
    simp only at h2
    linear_combination h2

/-! ### Counting the fixed primitive symbols -/

/-- **The `σ_t`-fixed primitive cusp symbols** — the combinatorial stand-in
for the `𝔽_ℓ`-rational cusps of `X_1(N)_{𝔽_ℓ}`. -/
def FixedCuspSymbolX1 (N : ℕ) (t : ZMod N) : Type :=
  {s : CuspSymbolX1 N // IsPrimitiveCuspSymbolX1 N s ∧ cuspFrobX1 N t s = s}

instance (N : ℕ) [NeZero N] (t : ZMod N) : Finite (FixedCuspSymbolX1 N t) :=
  Subtype.finite

/-- **`u ↦ [(u, 0)]`**, the parametrisation of the rational cusps by units.

Primitivity is `isCoprime_zero_right`, and fixedness is trivial rather than
an appeal to `cuspFrob_fixed_of_isUnit`, because `t * 0 = 0`. -/
def cuspOfUnit (N : ℕ) (t : ZMod N) (u : (ZMod N)ˣ) : FixedCuspSymbolX1 N t :=
  ⟨Quotient.mk _ ((u : ZMod N), 0),
    by simpa using isCoprime_zero_right.mpr u.isUnit,
    by simp⟩

/-- **`cuspOfUnit` is exactly two-to-one**: its fibres are the `±` pairs. -/
theorem cuspOfUnit_eq_iff {N : ℕ} {t : ZMod N} {u v : (ZMod N)ˣ} :
    cuspOfUnit N t u = cuspOfUnit N t v ↔ (v = u ∨ v = -u) := by
  constructor
  · intro h
    obtain ⟨j, hj | hj⟩ := Quotient.exact (congrArg Subtype.val h)
    · refine Or.inl (Units.ext ?_)
      have h1 := congrArg Prod.fst hj
      simp only at h1
      exact h1
    · refine Or.inr (Units.ext ?_)
      have h1 := congrArg Prod.fst hj
      simp only at h1
      simpa using h1
  · rintro (rfl | rfl)
    · rfl
    · refine Subtype.ext (Quotient.sound ⟨0, Or.inr ?_⟩)
      simp

/-- **`cuspOfUnit` is onto the fixed primitive symbols** — this is where
`isUnit_fst_of_cuspFrob_fixed` is consumed. -/
theorem cuspOfUnit_surjective {N : ℕ} {t : ZMod N} (ht1 : IsUnit (t - 1)) (ht2 : IsUnit (t + 1)) :
    Function.Surjective (cuspOfUnit N t) := by
  rintro ⟨s, hp, hf⟩
  induction s using Quotient.inductionOn with
  | h p =>
    obtain ⟨c, a⟩ := p
    have hc : IsUnit c := isUnit_fst_of_cuspFrob_fixed ht1 ht2 hp hf
    refine ⟨hc.unit, Subtype.ext ?_⟩
    simpa [cuspOfUnit] using (cuspSymbol_eq_of_isUnit a hc).symm

/-- `⟨-1⟩` is `{1, -1}`. -/
theorem eq_one_or_neg_one_of_mem_zpowers_neg_one {G : Type*} [Group G] [HasDistribNeg G] {x : G}
    (hx : x ∈ Subgroup.zpowers (-1 : G)) : x = 1 ∨ x = -1 := by
  obtain ⟨n, rfl⟩ := hx
  rcases Int.even_or_odd n with he | ho
  · exact Or.inl he.neg_one_zpow
  · exact Or.inr ho.neg_one_zpow

/-- **The fixed primitive symbols are `(ℤ/N)ˣ/±1`.**

Assembled from `cuspOfUnit_eq_iff` and `cuspOfUnit_surjective`; the point of
routing through the GROUP quotient rather than an ad hoc `±`-quotient is
that Lagrange then supplies the count. -/
noncomputable def fixedCuspSymbolEquiv (N : ℕ) [NeZero N] (t : ZMod N)
    (ht1 : IsUnit (t - 1)) (ht2 : IsUnit (t + 1)) :
    ((ZMod N)ˣ ⧸ Subgroup.zpowers (-1 : (ZMod N)ˣ)) ≃ FixedCuspSymbolX1 N t :=
  Equiv.ofBijective
    (Quotient.lift (cuspOfUnit N t) (by
      intro u v huv
      have huv' := QuotientGroup.leftRel_apply.mp huv
      rcases eq_one_or_neg_one_of_mem_zpowers_neg_one huv' with h | h
      · have : v = u := by
          have := congrArg (fun z => u * z) h
          simpa [mul_inv_cancel_left] using this
        exact cuspOfUnit_eq_iff.2 (Or.inl this)
      · have : v = -u := by
          have := congrArg (fun z => u * z) h
          simpa [mul_inv_cancel_left] using this
        exact cuspOfUnit_eq_iff.2 (Or.inr this)))
    ⟨by
      intro x y hxy
      induction x using Quotient.inductionOn with
      | h u =>
        induction y using Quotient.inductionOn with
        | h v =>
          rcases cuspOfUnit_eq_iff.1 hxy with h | h
          · rw [h]
          · refine Quotient.sound (QuotientGroup.leftRel_apply.mpr ?_)
            rw [h]
            exact ⟨-1, by simp⟩,
     by
      rintro y
      obtain ⟨u, rfl⟩ := cuspOfUnit_surjective ht1 ht2 y
      exact ⟨Quotient.mk _ u, rfl⟩⟩

/-- **`#{σ_t`-fixed primitive cusp symbols`} = φ(N)/2`** (PROVEN).

The arithmetic half of Ogg's description of the cusps of `X_1(N)`, with the
geometry entirely removed.  `2 < N` makes `-1 ≠ 1`, so `⟨-1⟩` has order `2`
and Lagrange turns `φ(N) = #(ℤ/N)ˣ` into `φ(N)/2` classes.

**Both unit hypotheses are refuted if dropped** — see the module docstring:
at `N = 25`, `t = 1` gives `28` fixed symbols and `t = -1` gives `20`,
against `φ(25)/2 = 10`. -/
theorem card_fixedCuspSymbolX1 (N : ℕ) [NeZero N] (hN : 2 < N) (t : ZMod N)
    (ht1 : IsUnit (t - 1)) (ht2 : IsUnit (t + 1)) :
    Nat.card (FixedCuspSymbolX1 N t) = N.totient / 2 := by
  haveI : Fact (2 < N) := ⟨hN⟩
  have hne : (-1 : (ZMod N)ˣ) ≠ 1 := fun h => ZMod.neg_one_ne_one (by
    simpa using congrArg (Units.val) h)
  have hord : orderOf (-1 : (ZMod N)ˣ) = 2 := orderOf_eq_prime (by simp) hne
  have hHcard : Nat.card (Subgroup.zpowers (-1 : (ZMod N)ˣ)) = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_zpowers, hord]
  have hG : Nat.card ((ZMod N)ˣ) = N.totient := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have hlag := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.zpowers (-1 : (ZMod N)ˣ))
  rw [hG, hHcard] at hlag
  have := Nat.card_congr (fixedCuspSymbolEquiv N t ht1 ht2)
  omega

end Fermat
