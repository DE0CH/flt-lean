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
Hence the three-way split below, of which the tame row is PROVEN here (its `K`
really is trivial, by three one-line coefficient comparisons) and the two wild
rows are stated as leaves.
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

/-- **Exponent `12` in characteristic `2`** (sorry leaf; Silverman *AEC*
Appendix A.1.2(c), Table 3.1; Kraus, *Manuscripta Math.* 69 (1990)).

The classification input.  In characteristic `2` the stabiliser of an elliptic
`W` is `ℤ/2` when `j ≠ 0` and `SL₂(𝔽₃) = Q₈ ⋊ μ₃` of order `24` when `j = 0`
(equivalently `a₁ = 0` for a curve in the normal form `y² + a₃y = x³ + a₄x +
a₆`); the element orders are `1, 2, 3, 4, 6`, so the exponent is `12`.

Proof route (not formalised), and it is a finite computation rather than a
theory build.  From `(C • W).a₁ = W.a₁` and `2 = 0` one gets `(u − 1)a₁ = 0`.

* `a₁ ≠ 0` (ordinary, `j ≠ 0`): `u = 1`, and then `(C • W).a₃ = W.a₃` forces
  `r a₁ = 0`, so `r = 0`; `(C • W).a₂ = W.a₂` forces `s(a₁ + s) = 0`.  The
  resulting group has order `2`, so already `C² = 1`.
* `a₁ = 0` (supersingular, `j = 0`): `Δ = a₃⁴`, so `a₃ ≠ 0`, and
  `(C • W).a₃ = W.a₃` reads `u⁻³a₃ = a₃`, i.e. **`u³ = 1`**.  The kernel
  `u = 1` is `Q₈`, of exponent `4`, so `C¹² = (C³)⁴ = 1` once `C³` is shown to
  lie in that kernel — which is `pow_u` plus `u³ = 1`.

So the honest residue is: in characteristic `2` with `a₁ = 0`, an admissible
change of variables with `u = 1` stabilising `W` satisfies `C⁴ = 1`.  A prover
who prefers to cut further should open exactly that lemma.

NOT VACUOUS: the hypotheses are satisfiable — `y² + y = x³` over `𝔽₄` has a
stabiliser of order `24`, and `y² + xy = x³ + 1` one of order `2`. -/
theorem WeierstrassCurve.VariableChange.pow_twelve_eq_one_of_smul_eq_of_two_eq_zero
    {F : Type*} [Field F] (h2 : (2 : F) = 0)
    {W : WeierstrassCurve F} [W.IsElliptic]
    {C : WeierstrassCurve.VariableChange F} (hC : C • W = W) : C ^ 12 = 1 :=
  sorry

/-- **Exponent `12` in characteristic `3`** (sorry leaf; Silverman *AEC*
Appendix A.1.2(c), Table 3.1; Kraus, *Manuscripta Math.* 69 (1990)).

The classification input.  In characteristic `3` the stabiliser of an elliptic
`W` is `ℤ/2` when `j ≠ 0` and the dicyclic group `ℤ/3 ⋊ ℤ/4` of order `12` when
`j = 0` (normal form `y² = x³ + a₄x + a₆`); the element orders are
`1, 2, 3, 4, 6`, so the exponent is `12`.

Proof route (not formalised).  With `3 = 0`, `(C • W).a₂ = W.a₂` reads
`u⁻²(a₂ − s a₁ − s²) = a₂` — the `3r` term vanishes, which is precisely why
`r` is no longer forced to be `0` and the kernel of `C ↦ C.u` becomes the
group `ℤ/3` of translations `x ↦ x + r`.  That kernel has exponent `3`
(`r ↦ 3r = 0`), while the `u`-image satisfies `u⁴ = 1` at `j = 0`; the product
`4 · 3` is `12`.  As in characteristic `2`, the honest residue is the kernel
statement: with `3 = 0` and `C.u = 1`, a stabilising `C` satisfies `C³ = 1`.

NOT VACUOUS: `y² = x³ − x` over `𝔽₉` has a stabiliser of order `12`. -/
theorem WeierstrassCurve.VariableChange.pow_twelve_eq_one_of_smul_eq_of_three_eq_zero
    {F : Type*} [Field F] (h3 : (3 : F) = 0)
    {W : WeierstrassCurve F} [W.IsElliptic]
    {C : WeierstrassCurve.VariableChange F} (hC : C • W = W) : C ^ 12 = 1 :=
  sorry

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
