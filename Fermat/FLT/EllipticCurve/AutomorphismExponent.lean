/-
AutomorphismExponent.lean — own work for the Fermat project (not vendored
from the FLT project).

**The automorphism group of an elliptic curve has exponent dividing `12`.**

Opened 2026-07-28 while decomposing
`WeierstrassCurve.not_eight_dvd_orderOf_isogenyCharacter_of_padicValRat_j_nonneg`
(leaf `B₀²` of `FreyCurve/MazurTorsion.lean`), which is the one place in the
Frey-curve isogeny-character analysis where the wild residue characteristics
`q = 2, 3` cost anything.

THE STATEMENT.  For a Weierstrass curve `W` over a field `F` with `Δ ≠ 0`, the
stabiliser of `W` inside the group `WeierstrassCurve.VariableChange F` of
admissible changes of variables IS `Aut(W, O)` — the automorphism group of the
elliptic curve fixing the origin.  Silverman *AEC* III.10.1 and Appendix A.1
classify it: it is cyclic of order `2, 4, 6` in residue characteristic `≥ 5`,
of order `12` (dicyclic, `ℤ/3 ⋊ ℤ/4`) in characteristic `3` at `j = 0`, and of
order `24` (`SL₂(𝔽₃) = Q₈ ⋊ ℤ/3`) in characteristic `2` at `j = 0`.  Every one
of those groups has element orders in `{1, 2, 3, 4, 6}`, hence **exponent
dividing `12`** — and that is the only consequence of the classification this
development needs.

WHY EXPONENT AND NOT ORDER.  `|Aut|` is `8`-divisible at `q = 2` (`Q₈` and
`SL₂(𝔽₃)`), so no bound on the ORDER of the group excludes an element of order
`8`; the exponent does, and it is what a CHARACTER of the group sees.  This is
exactly the distinction that makes `B₀²` true where the naive
`e ∈ {1, 2, 3, 4, 6}` reading of Serre–Tate is false at `q = 2, 3`.

THE CUT, and why it is by CHARACTERISTIC.  Write `K` for the kernel of the
group homomorphism `C ↦ C.u` restricted to the stabiliser.  The discriminant
identity `(C • W).Δ = u⁻¹¹² Δ` gives `u¹² = 1` for free, so `C¹²` always lies
in `K`; but `exponent(G) ∣ exponent(K) · exponent(G/K)` is the only uniform
composition available and the two factors are characteristic-dependent:

| `char F` | `u`-image | `K`            | product |
|----------|-----------|----------------|---------|
| `≠ 2, 3` | `μ₂/μ₄/μ₆` | trivial       | `12 · 1` |
| `3`      | `μ₄`      | `ℤ/3`          | `4 · 3`  |
| `2`      | `μ₃`      | `Q₈`           | `3 · 4`  |

so the product is `12` in every row but through three different
factorisations.  A single uniform argument would give only `12 · 12 = 144`.
Hence the three-way split below.

ALL THREE ROWS ARE NOW PROVEN (2026-07-28), and none of them consumes the
classification — only finite coefficient comparisons:

* tame: `K` really is trivial, by three one-line coefficient comparisons
  (`a₁ ⟹ 2s = 0`, `a₂ ⟹ 3r = 0`, `a₃ ⟹ 2t = 0`);
* the two wild rows: the `u`-image bound is one comparison each (`a₁`/`a₃` in
  characteristic `2`, `b₂`/`b₄` in characteristic `3`), and the kernel bound is
  PURE GROUP THEORY — `K` is the Heisenberg group of `F`, of exponent `4` when
  `2 = 0` and `3` when `3 = 0`, with no curve hypothesis whatsoever.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

@[expose] public section

/-- The `u`-coefficient of a composite change of variables is the product of the
`u`-coefficients: `C ↦ C.u` is a group homomorphism. -/
theorem WeierstrassCurve.VariableChange.mul_u {R : Type*} [CommRing R]
    (C C' : WeierstrassCurve.VariableChange R) : (C * C').u = C.u * C'.u := rfl

/-- `C ↦ C.u` commutes with powers. -/
theorem WeierstrassCurve.VariableChange.pow_u {R : Type*} [CommRing R]
    (C : WeierstrassCurve.VariableChange R) (n : ℕ) : (C ^ n).u = C.u ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, WeierstrassCurve.VariableChange.one_def]
  | succ k ih => rw [pow_succ, pow_succ, WeierstrassCurve.VariableChange.mul_u, ih]

/-- The stabiliser of `W` is closed under powers. -/
theorem WeierstrassCurve.VariableChange.smul_pow_eq_self {R : Type*} [CommRing R]
    {W : WeierstrassCurve R} {C : WeierstrassCurve.VariableChange R} (hC : C • W = W) (n : ℕ) :
    C ^ n • W = W := by
  induction n with
  | zero => rw [pow_zero, one_smul]
  | succ k ih => rw [pow_succ, mul_smul, hC, ih]

/-- **The `u`-coefficient of an automorphism is a twelfth root of unity.**  This
is nothing but the discriminant identity `(C • W).Δ = u⁻¹¹² Δ` together with
`Δ ≠ 0`; no classification is involved. -/
theorem WeierstrassCurve.VariableChange.u_pow_twelve_eq_one_of_smul_eq
    {F : Type*} [Field F] {W : WeierstrassCurve F} [W.IsElliptic]
    {C : WeierstrassCurve.VariableChange F} (hC : C • W = W) : C.u ^ 12 = 1 := by
  have hΔ : W.Δ ≠ 0 := isUnit_iff_ne_zero.mp W.isUnit_Δ
  have h : ((C.u⁻¹ : Fˣ) : F) ^ 12 * W.Δ = W.Δ := by
    rw [← WeierstrassCurve.variableChange_Δ, hC]
  have h1 : ((C.u⁻¹ : Fˣ) : F) ^ 12 = 1 :=
    mul_right_cancel₀ hΔ (by rw [h, one_mul])
  have h2 : (C.u⁻¹) ^ 12 = (1 : Fˣ) := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, h1, Units.val_one]
  rw [inv_pow, inv_eq_one] at h2
  exact h2

/-- **The kernel of `C ↦ C.u` on the stabiliser is TRIVIAL away from `2` and
`3`** (PROVEN).  Three coefficient comparisons, in order: `a₁` gives `2s = 0`,
then `a₂` gives `3r = 0`, then `a₃` gives `2t = 0`.  `Δ ≠ 0` is not needed.

This is exactly the step that FAILS in characteristics `2` and `3`, where the
kernel is `Q₈` respectively `ℤ/3` — see the module docstring. -/
theorem WeierstrassCurve.VariableChange.eq_one_of_smul_eq_of_u_eq_one
    {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {W : WeierstrassCurve F} {C : WeierstrassCurve.VariableChange F}
    (hC : C • W = W) (hu : C.u = 1) : C = 1 := by
  have hu1 : ((C.u⁻¹ : Fˣ) : F) = 1 := by rw [hu, inv_one, Units.val_one]
  have hs : C.s = 0 := by
    have h : (C • W).a₁ = W.a₁ := by rw [hC]
    rw [WeierstrassCurve.variableChange_a₁, hu1, one_mul] at h
    have h' : 2 * C.s = 0 := by linear_combination h
    exact (mul_eq_zero.mp h').resolve_left h2
  have hr : C.r = 0 := by
    have h : (C • W).a₂ = W.a₂ := by rw [hC]
    rw [WeierstrassCurve.variableChange_a₂, hu1, one_pow, one_mul, hs] at h
    have h' : 3 * C.r = 0 := by linear_combination h
    exact (mul_eq_zero.mp h').resolve_left h3
  have ht : C.t = 0 := by
    have h : (C • W).a₃ = W.a₃ := by rw [hC]
    rw [WeierstrassCurve.variableChange_a₃, hu1, one_pow, one_mul, hr] at h
    have h' : 2 * C.t = 0 := by linear_combination h
    exact (mul_eq_zero.mp h').resolve_left h2
  refine WeierstrassCurve.VariableChange.ext ?_ hr hs ht
  rw [hu]
  rfl

/-- **Exponent `12`, away from the wild characteristics** (PROVEN).  `C¹²`
stabilises `W` and has `u`-coefficient `u¹² = 1`, hence is trivial by the
kernel computation above. -/
theorem WeierstrassCurve.VariableChange.pow_twelve_eq_one_of_smul_eq_of_tame
    {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {W : WeierstrassCurve F} [W.IsElliptic]
    {C : WeierstrassCurve.VariableChange F} (hC : C • W = W) : C ^ 12 = 1 :=
  WeierstrassCurve.VariableChange.eq_one_of_smul_eq_of_u_eq_one h2 h3
    (WeierstrassCurve.VariableChange.smul_pow_eq_self hC 12)
    (by rw [WeierstrassCurve.VariableChange.pow_u]
        exact WeierstrassCurve.VariableChange.u_pow_twelve_eq_one_of_smul_eq hC)

/-! ### The kernel of `C ↦ C.u`, as a group

The following two lemmas are PURE GROUP THEORY: no Weierstrass curve, no
`Δ ≠ 0`, no stabiliser hypothesis.  The kernel of `C ↦ C.u` is the Heisenberg
group of `R`, `(r, s, t) · (r', s', t') = (r + r', s + s', t + r s' + t')`,
whose exponent is `4` when `2 = 0` and `3` when `3 = 0`.  That is strictly
stronger than the classification statements they replace (in characteristic `2`
the kernel really is `Q₈` for the stabiliser, of exponent `4`; here every
`u = 1` element, stabilising or not, is killed by `4`), and it is what makes
the two wild rows finite computations rather than classification proofs. -/

/-- The square of a change of variables with `u = 1`, componentwise. -/
theorem WeierstrassCurve.VariableChange.sq_of_u_eq_one {R : Type*} [CommRing R]
    {C : WeierstrassCurve.VariableChange R} (hu : C.u = 1) :
    C ^ 2 = ⟨1, 2 * C.r, 2 * C.s, 2 * C.t + C.r * C.s⟩ := by
  rw [pow_two, WeierstrassCurve.VariableChange.mul_def]
  refine WeierstrassCurve.VariableChange.ext ?_ ?_ ?_ ?_ <;> dsimp only <;> rw [hu] <;>
    simp only [Units.val_one, one_pow, mul_one, one_mul] <;> ring

/-- **The kernel of `C ↦ C.u` has exponent dividing `3` in characteristic `3`.**
`C² = (1, 2r, 2s, 2t + rs)` and `C³ = (1, 3r, 3s, 3t + 3rs)`. -/
theorem WeierstrassCurve.VariableChange.pow_three_eq_one_of_u_eq_one_of_three_eq_zero
    {R : Type*} [CommRing R] (h3 : (3 : R) = 0)
    {C : WeierstrassCurve.VariableChange R} (hu : C.u = 1) : C ^ 3 = 1 := by
  have hsq := WeierstrassCurve.VariableChange.sq_of_u_eq_one hu
  have hu2 : (C ^ 2).u = 1 := by rw [hsq]
  have hr2 : (C ^ 2).r = 2 * C.r := by rw [hsq]
  have hs2 : (C ^ 2).s = 2 * C.s := by rw [hsq]
  have ht2 : (C ^ 2).t = 2 * C.t + C.r * C.s := by rw [hsq]
  have hpow : C ^ 3 = C ^ 2 * C := pow_succ C 2
  rw [hpow, WeierstrassCurve.VariableChange.mul_def,
    WeierstrassCurve.VariableChange.one_def]
  refine WeierstrassCurve.VariableChange.ext ?_ ?_ ?_ ?_ <;> dsimp only <;>
    simp only [hu, hu2, hr2, hs2, ht2, Units.val_one, one_pow, one_mul, mul_one]
  · linear_combination C.r * h3
  · linear_combination C.s * h3
  · linear_combination (C.t + C.r * C.s) * h3

/-- **The kernel of `C ↦ C.u` has exponent dividing `4` in characteristic `2`.**
`C² = (1, 0, 0, rs)` and the square of that is `(1, 0, 0, 2rs) = 1`. -/
theorem WeierstrassCurve.VariableChange.pow_four_eq_one_of_u_eq_one_of_two_eq_zero
    {R : Type*} [CommRing R] (h2 : (2 : R) = 0)
    {C : WeierstrassCurve.VariableChange R} (hu : C.u = 1) : C ^ 4 = 1 := by
  have hsq := WeierstrassCurve.VariableChange.sq_of_u_eq_one hu
  have hu2 : (C ^ 2).u = 1 := by rw [hsq]
  have hr2 : (C ^ 2).r = 2 * C.r := by rw [hsq]
  have hs2 : (C ^ 2).s = 2 * C.s := by rw [hsq]
  have ht2 : (C ^ 2).t = 2 * C.t + C.r * C.s := by rw [hsq]
  have hpow : C ^ 4 = (C ^ 2) ^ 2 := by rw [← pow_mul]
  rw [hpow, WeierstrassCurve.VariableChange.sq_of_u_eq_one hu2,
    WeierstrassCurve.VariableChange.one_def]
  refine WeierstrassCurve.VariableChange.ext ?_ ?_ ?_ ?_ <;> dsimp only <;>
    simp only [hr2, hs2, ht2]
  · linear_combination (2 * C.r) * h2
  · linear_combination (2 * C.s) * h2
  · linear_combination (2 * C.t + 3 * C.r * C.s) * h2

/-- `u⁻ⁿ = 1` in `F` promotes to `uⁿ = 1` in `Fˣ`. -/
theorem WeierstrassCurve.VariableChange.u_pow_eq_one_of_val_inv_pow_eq_one {F : Type*} [Field F]
    {C : WeierstrassCurve.VariableChange F} {n : ℕ}
    (h : ((C.u⁻¹ : Fˣ) : F) ^ n = 1) : C.u ^ n = 1 := by
  have h2 : (C.u⁻¹) ^ n = (1 : Fˣ) :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])
  rw [inv_pow, inv_eq_one] at h2
  exact h2

/-- **`Aut(W) ↪ μ₃` in characteristic `2`** (PROVEN).  Split on `a₁`, which is
the reduction-type invariant in characteristic `2` (`b₂ = a₁²`, so `j ≠ 0` iff
`a₁ ≠ 0`).

* `a₁ ≠ 0` (ordinary): the `a₁`-comparison reads `u⁻¹a₁ = a₁` because `2s = 0`,
  so `u = 1` outright.
* `a₁ = 0` (supersingular): then `b₂ = b₄ = 0` and `b₆ = a₃²`, so
  `Δ = −27 b₆² = a₃⁴`; hence `a₃ ≠ 0`, and the `a₃`-comparison reads
  `u⁻³a₃ = a₃`, i.e. `u³ = 1`. -/
theorem WeierstrassCurve.VariableChange.u_pow_three_eq_one_of_smul_eq_of_two_eq_zero
    {F : Type*} [Field F] (h2 : (2 : F) = 0)
    {W : WeierstrassCurve F} [W.IsElliptic]
    {C : WeierstrassCurve.VariableChange F} (hC : C • W = W) : C.u ^ 3 = 1 := by
  have hΔ : W.Δ ≠ 0 := isUnit_iff_ne_zero.mp W.isUnit_Δ
  refine WeierstrassCurve.VariableChange.u_pow_eq_one_of_val_inv_pow_eq_one ?_
  by_cases ha : W.a₁ = 0
  · have hb₂ : W.b₂ = 0 := by
      simp only [WeierstrassCurve.b₂, ha]; linear_combination (2 * W.a₂) * h2
    have hb₄ : W.b₄ = 0 := by
      simp only [WeierstrassCurve.b₄, ha]; linear_combination W.a₄ * h2
    have hb₆ : W.b₆ = W.a₃ ^ 2 := by
      simp only [WeierstrassCurve.b₆]; linear_combination (2 * W.a₆) * h2
    have hΔ2 : W.Δ = W.a₃ ^ 4 := by
      simp only [WeierstrassCurve.Δ, hb₂, hb₄, hb₆]
      linear_combination (-14 * W.a₃ ^ 4) * h2
    have ha₃ : W.a₃ ≠ 0 := fun h => hΔ (by rw [hΔ2, h]; ring)
    have h : (C • W).a₃ = W.a₃ := by rw [hC]
    rw [WeierstrassCurve.variableChange_a₃] at h
    have h' : (((C.u⁻¹ : Fˣ) : F) ^ 3 - 1) * W.a₃ = 0 := by
      linear_combination h - ((C.u⁻¹ : Fˣ) : F) ^ 3 * C.r * ha
        - ((C.u⁻¹ : Fˣ) : F) ^ 3 * C.t * h2
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right ha₃)
  · have h : (C • W).a₁ = W.a₁ := by rw [hC]
    rw [WeierstrassCurve.variableChange_a₁] at h
    have h' : (((C.u⁻¹ : Fˣ) : F) - 1) * W.a₁ = 0 := by
      linear_combination h - ((C.u⁻¹ : Fˣ) : F) * C.s * h2
    have hv : ((C.u⁻¹ : Fˣ) : F) = 1 := sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right ha)
    rw [hv, one_pow]

/-- **`Aut(W) ↪ μ₄` in characteristic `3`** (PROVEN).  Split on `b₂`, which is
the `j = 0` invariant in characteristic `3` (`c₄ = b₂² − 24b₄ = b₂²`).

* `b₂ ≠ 0` (`j ≠ 0`): `(C • W).b₂ = u⁻²(b₂ + 12r) = u⁻²b₂` since `12 = 0`, so
  `u² = 1`.
* `b₂ = 0` (`j = 0`): then `Δ = −8b₄³ = b₄³`, so `b₄ ≠ 0`, and
  `(C • W).b₄ = u⁻⁴(b₄ + r b₂ + 6r²) = u⁻⁴b₄` since `6 = 0`, so `u⁴ = 1`. -/
theorem WeierstrassCurve.VariableChange.u_pow_four_eq_one_of_smul_eq_of_three_eq_zero
    {F : Type*} [Field F] (h3 : (3 : F) = 0)
    {W : WeierstrassCurve F} [W.IsElliptic]
    {C : WeierstrassCurve.VariableChange F} (hC : C • W = W) : C.u ^ 4 = 1 := by
  have hΔ : W.Δ ≠ 0 := isUnit_iff_ne_zero.mp W.isUnit_Δ
  refine WeierstrassCurve.VariableChange.u_pow_eq_one_of_val_inv_pow_eq_one ?_
  by_cases hb : W.b₂ = 0
  · have hΔ3 : W.Δ = W.b₄ ^ 3 := by
      simp only [WeierstrassCurve.Δ, hb]
      linear_combination (-3 * W.b₄ ^ 3 - 9 * W.b₆ ^ 2) * h3
    have hb₄ : W.b₄ ≠ 0 := fun h => hΔ (by rw [hΔ3, h]; ring)
    have h : (C • W).b₄ = W.b₄ := by rw [hC]
    rw [WeierstrassCurve.variableChange_b₄] at h
    have h' : (((C.u⁻¹ : Fˣ) : F) ^ 4 - 1) * W.b₄ = 0 := by
      linear_combination h - ((C.u⁻¹ : Fˣ) : F) ^ 4 * C.r * hb
        - 2 * ((C.u⁻¹ : Fˣ) : F) ^ 4 * C.r ^ 2 * h3
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right hb₄)
  · have h : (C • W).b₂ = W.b₂ := by rw [hC]
    rw [WeierstrassCurve.variableChange_b₂] at h
    have h' : (((C.u⁻¹ : Fˣ) : F) ^ 2 - 1) * W.b₂ = 0 := by
      linear_combination h - 4 * ((C.u⁻¹ : Fˣ) : F) ^ 2 * C.r * h3
    have hv2 : ((C.u⁻¹ : Fˣ) : F) ^ 2 = 1 :=
      sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right hb)
    calc ((C.u⁻¹ : Fˣ) : F) ^ 4 = (((C.u⁻¹ : Fˣ) : F) ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hv2, one_pow]

/-- **Exponent `12` in characteristic `2`** (PROVEN 2026-07-28; the classical
statement is Silverman *AEC* Appendix A.1.2(c), Table 3.1, but the proof here
does NOT go through the classification).

In characteristic `2` the stabiliser of an elliptic `W` is `ℤ/2` when `j ≠ 0`
and `SL₂(𝔽₃) = Q₈ ⋊ μ₃` of order `24` when `j = 0`; the element orders are
`1, 2, 3, 4, 6`, so the exponent is `12`.  What is actually proven is the
composition `3 · 4` of the two lemmas above, both of which are finite
computations:

* `u³ = 1` (`u_pow_three_eq_one_of_smul_eq_of_two_eq_zero`), from the `a₁`- or
  `a₃`-comparison according to whether `a₁ ≠ 0` or `a₁ = 0`;
* the kernel of `C ↦ C.u` has exponent dividing `4`
  (`pow_four_eq_one_of_u_eq_one_of_two_eq_zero`), which is the Heisenberg group
  law and needs no curve at all.

Then `C³` lies in the kernel by `pow_u`, and `C¹² = (C³)⁴ = 1`.

NOT VACUOUS: the hypotheses are satisfiable — `y² + y = x³` over `𝔽₄` has a
stabiliser of order `24`, and `y² + xy = x³ + 1` one of order `2`. -/
theorem WeierstrassCurve.VariableChange.pow_twelve_eq_one_of_smul_eq_of_two_eq_zero
    {F : Type*} [Field F] (h2 : (2 : F) = 0)
    {W : WeierstrassCurve F} [W.IsElliptic]
    {C : WeierstrassCurve.VariableChange F} (hC : C • W = W) : C ^ 12 = 1 := by
  have hu : (C ^ 3).u = 1 := by
    rw [WeierstrassCurve.VariableChange.pow_u]
    exact WeierstrassCurve.VariableChange.u_pow_three_eq_one_of_smul_eq_of_two_eq_zero h2 hC
  have h12 : C ^ 12 = (C ^ 3) ^ 4 := by rw [← pow_mul]
  rw [h12]
  exact WeierstrassCurve.VariableChange.pow_four_eq_one_of_u_eq_one_of_two_eq_zero h2 hu

/-- **Exponent `12` in characteristic `3`** (PROVEN 2026-07-28; classically
Silverman *AEC* Appendix A.1.2(c), Table 3.1, but again the proof does not go
through the classification).

In characteristic `3` the stabiliser of an elliptic `W` is `ℤ/2` when `j ≠ 0`
and the dicyclic group `ℤ/3 ⋊ ℤ/4` of order `12` when `j = 0`; the element
orders are `1, 2, 3, 4, 6`, so the exponent is `12`.  What is proven here is
the composition `4 · 3`:

* `u⁴ = 1` (`u_pow_four_eq_one_of_smul_eq_of_three_eq_zero`), from the `b₂`- or
  `b₄`-comparison according to whether `b₂ ≠ 0` or `b₂ = 0`;
* the kernel of `C ↦ C.u` has exponent dividing `3`
  (`pow_three_eq_one_of_u_eq_one_of_three_eq_zero`) — with `3 = 0` the `3r`
  term of the `a₂`-comparison vanishes, which is exactly why `r` is no longer
  forced to be `0` and the kernel becomes the group of translations
  `x ↦ x + r`; its exponent is `3` by the Heisenberg group law.

Then `C⁴` lies in the kernel by `pow_u`, and `C¹² = (C⁴)³ = 1`.

NOT VACUOUS: `y² = x³ − x` over `𝔽₉` has a stabiliser of order `12`. -/
theorem WeierstrassCurve.VariableChange.pow_twelve_eq_one_of_smul_eq_of_three_eq_zero
    {F : Type*} [Field F] (h3 : (3 : F) = 0)
    {W : WeierstrassCurve F} [W.IsElliptic]
    {C : WeierstrassCurve.VariableChange F} (hC : C • W = W) : C ^ 12 = 1 := by
  have hu : (C ^ 4).u = 1 := by
    rw [WeierstrassCurve.VariableChange.pow_u]
    exact WeierstrassCurve.VariableChange.u_pow_four_eq_one_of_smul_eq_of_three_eq_zero h3 hC
  have h12 : C ^ 12 = (C ^ 4) ^ 3 := by rw [← pow_mul]
  rw [h12]
  exact WeierstrassCurve.VariableChange.pow_three_eq_one_of_u_eq_one_of_three_eq_zero h3 hu

/-- **The automorphism group of an elliptic curve has exponent dividing `12`**
(PROVEN 2026-07-28 from the three characteristic cases above): an admissible
change of variables fixing an elliptic Weierstrass curve over a field has
twelfth power the identity.

The case split is exhaustive because `2 = 0` and `3 = 0` cannot both hold in a
field (`3 − 2 = 1 ≠ 0`).

This is the geometric half of `MazurTorsion.lean`'s leaf `B₀²`: it is what
excludes an element of order `8` in the image of inertia at a prime of
potentially good reduction, and it is the only place Kraus's classification of
the semistability defect is consumed. -/
theorem WeierstrassCurve.VariableChange.pow_twelve_eq_one_of_smul_eq
    {F : Type*} [Field F] {W : WeierstrassCurve F} [W.IsElliptic]
    {C : WeierstrassCurve.VariableChange F} (hC : C • W = W) : C ^ 12 = 1 := by
  by_cases h2 : (2 : F) = 0
  · exact WeierstrassCurve.VariableChange.pow_twelve_eq_one_of_smul_eq_of_two_eq_zero h2 hC
  · by_cases h3 : (3 : F) = 0
    · exact WeierstrassCurve.VariableChange.pow_twelve_eq_one_of_smul_eq_of_three_eq_zero h3 hC
    · exact WeierstrassCurve.VariableChange.pow_twelve_eq_one_of_smul_eq_of_tame h2 h3 hC
