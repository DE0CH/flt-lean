/-
GenusOneKernelPolynomials.lean — own work for the Fermat project (not vendored).

**The six explicit kernel-polynomial certificates at the genus-one isogeny
primes**, cut 2026-07-27 out of the sorry leaf
`MazurIsogenyPrimeJ.exists_kernelPolynomial_of_genusOneJTable` in
`Fermat/FLT/FreyCurve/MazurTorsion.lean`.

## What this file does

`Fermat/FLT/EllipticCurve/KernelPolynomial.lean` reduces "`E/ℚ` carries a
Galois-stable cyclic subgroup of prime order `p`" to a purely polynomial
certificate `WeierstrassCurve.IsKernelPolynomial E p f m`.  This file supplies
that certificate for each of the six rows of
`MazurIsogenyPrimeJ.genusOneJTable`, i.e. for each `j`-invariant at which a
curve over `ℚ` admits a rational `p`-isogeny with `p ∈ {11, 17, 19}`:

| `p` | `j₀` | model `[a₁,a₂,a₃,a₄,a₆]` | conductor | `m` |
|-----|------|--------------------------|-----------|-----|
| 11 | `−24729001` | `[1,1,1,−30,−76]` | `121` | 2 |
| 11 | `−32768` | `[0,−1,1,−7,10]` | `121` | 2 |
| 11 | `−121` | `[1,1,0,−2,−7]` | `121` | 2 |
| 17 | `−297756989/2` | `[1,0,1,−3041,64278]` | `14450` | 3 |
| 17 | `−882216989/131072` | `[1,1,0,−660,−7600]` | `14450` | 3 |
| 19 | `−884736` | `[0,0,1,−38,90]` | `361` | 2 |

The model is free — only `j(E) = j₀` is demanded, and a rational cyclic
`p`-isogeny is invariant under quadratic twisting — so the minimal twists above
are used rather than `WeierstrassCurve.ofJ j₀`; their small coefficients are
what keeps the certificates writable.  `m` is `znprimroot p` in each case.

**`m = 2` is NOT usable at `p = 17`**: it has order `8`, hence order `4` in
`(ℤ/17)ˣ/±1`, too small to reach all `8` abscissae, so the `generates` field
would be unprovable.  `m = 3` is used there.

**A TRAP FOR ANYONE REGENERATING THIS TABLE.**  At `j₀ = −882216989/131072`
the kernel polynomial is **REDUCIBLE**: the `17`-division polynomial factors
with degrees `[4, 4, 136]` and there is NO irreducible rational factor of
degree `8`, so `f` is the PRODUCT of the two quartics.  A search that looks
only for an irreducible factor of degree `(p−1)/2` finds nothing there and
wrongly concludes the row is false.  The other five rows do have an
irreducible factor of the right degree (`[5, 55]`, `[5, 55]`, `[5, 55]`,
`[8, 68, 68]`, `[9, 171]`).

## How the two divisibilities are verified, and why it fits in a default budget

The two hard fields are `dvd_ΨSq` (`f ∣ ΨSq p`) and `dvd_multComp` (the root
set of `f` is stable under `x(P) ↦ x(m ⬝ P)`).  Written out naively they are
polynomial identities of degree `120`, `288`, `360` and `20`, `72`, `36`
respectively, with coefficients running to hundreds of digits; `ring` does not
survive the first kind at all and needs roughly `4·10⁶` heartbeats for the
second at `p = 17`.

Both are instead verified **modulo `f`**, which is what makes them cheap:

* `ΨSq p = preΨ'ₚ ²` for odd `p` (`WeierstrassCurve.ΨSq_ofNat`), so it suffices
  that `f ∣ preΨ'ₚ`.  The remainders `rₙ := preΨ'ₙ mod f` are computed along
  mathlib's own `preNormEDS'` recursion, one lemma per `n`, each step an
  identity in degree `≤ 38` instead of `≤ 180`; the chain ends at `r_p = 0`.
* For `dvd_multComp` the powers `Φₘ^i` and `ΨSqₘ^j` are reduced modulo `f`
  BEFORE being multiplied, so every `ring` call is an identity in degree
  `≤ 2·deg f` rather than `deg f · deg Φₘ`.

Every step is a `Dvd` witness supplied explicitly, so nothing here needs a
`set_option maxHeartbeats` bump.  The reason each step is a separate top-level
lemma rather than a `have` inside one proof is the same budget: a single
tactic block carrying the whole chain exceeds the default limit on `whnf`
alone, while the split chain does not.

## Provenance of the constants

Every kernel polynomial, cofactor and remainder below was computed in PARI/GP
(2026-07-27) as an *untrusted searcher*: `f ∣ elldivpol(E, p)`, `disc f ≠ 0`
and the `ellxn(E, m)` stability divisibility were all confirmed there first,
and the recursion was re-run against mathlib's own `preNormEDS'` shape rather
than against PARI's normalisation so that the two agree term by term.  None of
that is a proof; the Lean kernel re-checks every identity below through `ring`
against an explicit witness.
-/
module

public import Fermat.FLT.EllipticCurve.KernelPolynomial

@[expose] public section

open Polynomial WeierstrassCurve

namespace GenusOneKernel

/-! ### Generic machinery: congruences modulo `f`, one step at a time

Each lemma below is the same two lines — pass to the quotient `F[X] ⧸ (f)`,
where `Ideal.Quotient.mk` is a ring hom, and rewrite.  Working in the quotient
is what lets a step be stated with SMALL representatives on both sides: the
caller supplies the reduced remainder and the explicit cofactor, and never has
to write the full unreduced product. -/

variable {F : Type*} [Field F]

theorem dvd_sub_iff_mk_eq {f a b : F[X]} :
    f ∣ a - b ↔
      Ideal.Quotient.mk (Ideal.span {f}) a = Ideal.Quotient.mk (Ideal.span {f}) b := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]

theorem j_eq_of_Δ_c₄ (E : WeierstrassCurve F) [E.IsElliptic] {d c jv : F}
    (hΔ : E.Δ = d) (hc : E.c₄ = c) (hd : d ≠ 0) (hj : c ^ 3 = jv * d) : E.j = jv := by
  have h1 : (E.Δ' : F) = d := by rw [WeierstrassCurve.coe_Δ', hΔ]
  have h2 : ((E.Δ'⁻¹ : Fˣ) : F) = d⁻¹ := by rw [Units.val_inv_eq_inv_val, h1]
  rw [WeierstrassCurve.j, h2, hc, hj]
  field_simp

theorem step_preΨ'_odd_even (E : WeierstrassCurve F) {f : F[X]} (m n : ℕ)
    (hm : Even m) (hn : n = 2 * (m + 2) + 1) {r1 r2 r3 r4 r5 : F[X]}
    (h1 : f ∣ E.preΨ' (m + 1) - r1) (h2 : f ∣ E.preΨ' (m + 2) - r2)
    (h3 : f ∣ E.preΨ' (m + 3) - r3) (h4 : f ∣ E.preΨ' (m + 4) - r4)
    (h5 : f ∣ (r4 * r2 ^ 3 * E.Ψ₂Sq ^ 2 - r1 * r3 ^ 3) - r5) :
    f ∣ E.preΨ' n - r5 := by
  subst hn
  rw [dvd_sub_iff_mk_eq] at h1 h2 h3 h4 h5 ⊢
  rw [E.preΨ'_odd m, if_pos hm, if_pos hm, mul_one]
  simp only [map_sub, map_mul, map_pow] at h5 ⊢
  rw [h1, h2, h3, h4]
  exact h5

theorem step_preΨ'_odd_odd (E : WeierstrassCurve F) {f : F[X]} (m n : ℕ)
    (hm : ¬ Even m) (hn : n = 2 * (m + 2) + 1) {r1 r2 r3 r4 r5 : F[X]}
    (h1 : f ∣ E.preΨ' (m + 1) - r1) (h2 : f ∣ E.preΨ' (m + 2) - r2)
    (h3 : f ∣ E.preΨ' (m + 3) - r3) (h4 : f ∣ E.preΨ' (m + 4) - r4)
    (h5 : f ∣ (r4 * r2 ^ 3 - r1 * r3 ^ 3 * E.Ψ₂Sq ^ 2) - r5) :
    f ∣ E.preΨ' n - r5 := by
  subst hn
  rw [dvd_sub_iff_mk_eq] at h1 h2 h3 h4 h5 ⊢
  rw [E.preΨ'_odd m, if_neg hm, if_neg hm, mul_one]
  simp only [map_sub, map_mul, map_pow] at h5 ⊢
  rw [h1, h2, h3, h4]
  exact h5

theorem step_preΨ'_even (E : WeierstrassCurve F) {f : F[X]} (m n : ℕ)
    (hn : n = 2 * (m + 3)) {r1 r2 r3 r4 r5 r6 : F[X]}
    (h1 : f ∣ E.preΨ' (m + 1) - r1) (h2 : f ∣ E.preΨ' (m + 2) - r2)
    (h3 : f ∣ E.preΨ' (m + 3) - r3) (h4 : f ∣ E.preΨ' (m + 4) - r4)
    (h5 : f ∣ E.preΨ' (m + 5) - r5)
    (h6 : f ∣ (r2 ^ 2 * r3 * r5 - r1 * r3 * r4 ^ 2) - r6) :
    f ∣ E.preΨ' n - r6 := by
  subst hn
  rw [dvd_sub_iff_mk_eq] at h1 h2 h3 h4 h5 h6 ⊢
  rw [E.preΨ'_even m]
  simp only [map_sub, map_mul, map_pow] at h6 ⊢
  rw [h1, h2, h3, h4, h5]
  exact h6

theorem dvd_sub_add {f a b x y z : F[X]} (ha : f ∣ a - x) (hb : f ∣ b - y)
    (h : f ∣ x + y - z) : f ∣ a + b - z := by
  rw [dvd_sub_iff_mk_eq] at ha hb h ⊢
  rw [map_add, ha, hb, ← map_add]
  exact h

theorem dvd_sub_pow_succ {f a x y z : F[X]} (n : ℕ) (hx : f ∣ a ^ n - x) (ha : f ∣ a - y)
    (h : f ∣ x * y - z) : f ∣ a ^ (n + 1) - z := by
  rw [dvd_sub_iff_mk_eq] at hx ha h ⊢
  rw [pow_succ, map_mul, hx, ha, ← map_mul]
  exact h

theorem dvd_sub_const_mul₂ {f c a b x y z : F[X]} (ha : f ∣ a - x) (hb : f ∣ b - y)
    (h : f ∣ c * x * y - z) : f ∣ c * a * b - z := by
  rw [dvd_sub_iff_mk_eq] at ha hb h ⊢
  rw [map_mul, map_mul, ha, hb, ← map_mul, ← map_mul]
  exact h

theorem generates_aux_11_2 : ∀ k : ZMod 11, k ≠ 0 →
    ∃ i ∈ Finset.range 11, ((2 : ℕ) : ZMod 11) ^ i = k ∨ ((2 : ℕ) : ZMod 11) ^ i = -k := by
  decide

theorem generates_aux_17_3 : ∀ k : ZMod 17, k ≠ 0 →
    ∃ i ∈ Finset.range 17, ((3 : ℕ) : ZMod 17) ^ i = k ∨ ((3 : ℕ) : ZMod 17) ^ i = -k := by
  decide

theorem generates_aux_19_2 : ∀ k : ZMod 19, k ≠ 0 →
    ∃ i ∈ Finset.range 19, ((2 : ℕ) : ZMod 19) ^ i = k ∨ ((2 : ℕ) : ZMod 19) ^ i = -k := by
  decide

/-! #### Row 1: `p = 11`, `j₀ = -24729001`, model `[1, 1, 1, -30, -76]`, multiplier `m = 2` -/

/-- The minimal twist of conductor-level model at row 1 of `genusOneJTable`: `[a₁, a₂, a₃, a₄, a₆] = [1, 1, 1, -30, -76]`. -/
noncomputable def curve₁ : WeierstrassCurve ℚ := ⟨1, 1, 1, -30, -76⟩

lemma curve₁_Δ : curve₁.Δ = -121 := by
  norm_num [curve₁, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

lemma curve₁_c₄ : curve₁.c₄ = 1441 := by
  norm_num [curve₁, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]

noncomputable instance : curve₁.IsElliptic :=
  ⟨by rw [curve₁_Δ]; exact isUnit_iff_ne_zero.mpr (by norm_num)⟩

lemma curve₁_j : curve₁.j = (-24729001 : ℚ) :=
  j_eq_of_Δ_c₄ curve₁ curve₁_Δ curve₁_c₄ (by norm_num) (by norm_num)

/-- The kernel polynomial at row 1, monic of degree `(p-1)/2 = 5`. -/
noncomputable def ker₁ : ℚ[X] :=
  (-439) + (-230) * X + (62) * X ^ 2 + (63) * X ^ 3 + (14) * X ^ 4 + X ^ 5

lemma curve₁_Ψ₂Sq : curve₁.Ψ₂Sq =
    (-303) + (-118) * X + (5) * X ^ 2 + (4) * X ^ 3
    := by
  simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, curve₁]
  norm_num [Polynomial.C_eq_natCast, map_ofNat]
  ring

lemma curve₁_Ψ₃ : curve₁.Ψ₃ =
    (-1249) + (-909) * X + (-177) * X ^ 2 + (5) * X ^ 3 + (3) * X ^ 4
    := by
  simp only [WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, curve₁]
  norm_num [Polynomial.C_eq_natCast, map_ofNat]
  ring

lemma curve₁_preΨ₄ : curve₁.preΨ₄ =
    (-18118) + (-24122) * X + (-12490) * X ^ 2 + (-3030) * X ^ 3 + (-295) * X ^ 4 + (5) * X ^ 5
      + (2) * X ^ 6
    := by
  simp only [WeierstrassCurve.preΨ₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, curve₁]
  norm_num [Polynomial.C_eq_natCast, map_ofNat]
  ring

/-! ##### The chain of remainders modulo `ker₁`

`preΨ'ₙ ≡ rₙ (mod ker₁)` for `n = 1, …, 11`, each `rₙ` of degree `< 5`; the chain ends
at `r_11 = 0`, which is exactly `ker₁ ∣ preΨ'_11`.  Every step is one application of a
`step_preΨ'_*` lemma against an explicit cofactor. -/

lemma pre₁_1 : ker₁ ∣ curve₁.preΨ' 1 - 1 := by simp

lemma pre₁_2 : ker₁ ∣ curve₁.preΨ' 2 - 1 := by simp

lemma pre₁_3 : ker₁ ∣ curve₁.preΨ' 3 -
    ((-1249) + (-909) * X + (-177) * X ^ 2 + (5) * X ^ 3 + (3) * X ^ 4) := by
  rw [WeierstrassCurve.preΨ'_three, curve₁_Ψ₃]
  exact ⟨
    0
    , by rw [ker₁]; ring⟩

lemma pre₁_4 : ker₁ ∣ curve₁.preΨ' 4 -
    ((-28215) + (-28534) * X + (-10604) * X ^ 2 + (-1705) * X ^ 3 + (-99) * X ^ 4) := by
  rw [WeierstrassCurve.preΨ'_four, curve₁_preΨ₄]
  exact ⟨
    (-23) + (2) * X
    , by rw [ker₁]; ring⟩

lemma pre₁_5 : ker₁ ∣ curve₁.preΨ' 5 -
    ((2722509438) + (2852112538) * X + (1108229199) * X ^ 2 + (188899876) * X ^ 3
      + (11882321) * X ^ 4) :=
  step_preΨ'_odd_even curve₁ 0 5 (by decide) (by norm_num)
    pre₁_1 pre₁_2 pre₁_3 pre₁_4
    (by rw [curve₁_Ψ₂Sq]; exact ⟨
      (7663916) + (3354363) * X + (475579) * X ^ 2 + (-89157) * X ^ 3 + (-22293) * X ^ 4
        + (1269) * X ^ 5 + (243) * X ^ 6 + (-27) * X ^ 7
      , by rw [ker₁]; ring⟩)

lemma pre₁_6 : ker₁ ∣ curve₁.preΨ' 6 -
    ((3146486129600) + (3294899658611) * X + (1279627856188) * X ^ 2 + (217976231539) * X ^ 3
      + (13700113438) * X ^ 4) :=
  step_preΨ'_even curve₁ 0 6 (by norm_num)
    pre₁_1 pre₁_2 pre₁_3 pre₁_4 pre₁_5
    (⟨
      (12648265883) + (8401136480) * X + (2782079916) * X ^ 2 + (431175998) * X ^ 3
        + (17245525) * X ^ 4 + (-4018773) * X ^ 5 + (-650133) * X ^ 6 + (-29403) * X ^ 7
      , by rw [ker₁]; ring⟩)

lemma pre₁_7 : ker₁ ∣ curve₁.preΨ' 7 -
    ((-9603283573266404571) + (-10056030463255190194) * X + (-3905317780655013503) * X ^ 2
      + (-665222931277359103) * X ^ 3 + (-41808392946207745) * X ^ 4) :=
  step_preΨ'_odd_odd curve₁ 1 7 (by decide) (by norm_num)
    pre₁_2 pre₁_3 pre₁_4 pre₁_5
    (by rw [curve₁_Ψ₂Sq]; exact ⟨
      (-14489313039165756) + (5815315836417516) * X + (11539164345818824) * X ^ 2
        + (6965388481906261) * X ^ 3 + (2057318068702402) * X ^ 4 + (176837503676009) * X ^ 5
        + (-80510475774971) * X ^ 6 + (-29944817858703) * X ^ 7 + (-3764442866470) * X ^ 8
        + (69181721444) * X ^ 9 + (81046370878) * X ^ 10 + (10529050950) * X ^ 11
        + (623578824) * X ^ 12 + (15524784) * X ^ 13
      , by rw [ker₁]; ring⟩)

lemma pre₁_11 : ker₁ ∣ curve₁.preΨ' 11 -
    (0) :=
  step_preΨ'_odd_odd curve₁ 3 11 (by decide) (by norm_num)
    pre₁_4 pre₁_5 pre₁_6 pre₁_7
    (by rw [curve₁_Ψ₂Sq]; exact ⟨
      (257617735369203575227096491324354278902838808)
        + (808096601821048248581039788967989519819155576) * X
        + (1139335968065970587365159753695393404234061300) * X ^ 2
        + (941113321926019567905199912304223719653776829) * X ^ 3
        + (491674843366205445650194638335408298443472558) * X ^ 4
        + (157261960155980026794322811139218093314722641) * X ^ 5
        + (21131262727795058687447602704145401050103119) * X ^ 6
        + (-6185555185428769447056971609285930415225567) * X ^ 7
        + (-4292702201467467439626217177240556421645705) * X ^ 8
        + (-1207319329352577534011855320760194672553095) * X ^ 9
        + (-192913004268895481456883420638188504378595) * X ^ 10
        + (-13208129889576983471670824315686924906210) * X ^ 11
        + (1512164424483077935128404263118258496367) * X ^ 12
        + (523832671592904840951706169461310521050) * X ^ 13
        + (68568485876764640645952310391860379124) * X ^ 14
        + (5141884604003163183025463465609714152) * X ^ 15
        + (217724170787476112919677712690643840) * X ^ 16
        + (4073124328516653143705112467576448) * X ^ 17
      , by rw [ker₁]; ring⟩)

lemma ker₁_dvd_preΨ' : ker₁ ∣ curve₁.preΨ' 11 := by
  simpa using pre₁_11

lemma ker₁_coeff_0 : C (ker₁.coeff 0) = (-439 : ℚ[X]) := by
  rw [ker₁]; simp [Polynomial.coeff_X, map_ofNat]

lemma ker₁_coeff_1 : C (ker₁.coeff 1) = (-230 : ℚ[X]) := by
  rw [ker₁]; simp [Polynomial.coeff_X, map_ofNat]

lemma ker₁_coeff_2 : C (ker₁.coeff 2) = (62 : ℚ[X]) := by
  rw [ker₁]; simp [Polynomial.coeff_X, map_ofNat]

lemma ker₁_coeff_3 : C (ker₁.coeff 3) = (63 : ℚ[X]) := by
  rw [ker₁]; simp [Polynomial.coeff_X, map_ofNat]

lemma ker₁_coeff_4 : C (ker₁.coeff 4) = (14 : ℚ[X]) := by
  rw [ker₁]; simp [Polynomial.coeff_X, map_ofNat]

lemma ker₁_coeff_5 : C (ker₁.coeff 5) = (1 : ℚ[X]) := by
  rw [ker₁]; simp [Polynomial.coeff_X]

lemma ker₁_natDegree : ker₁.natDegree = 5 := by
  rw [ker₁]; compute_degree!

lemma ker₁_monic : ker₁.Monic := by
  rw [ker₁]; monicity!

lemma curve₁_Φ : curve₁.Φ (2 : ℤ) =
    (1249) + (606) * X + (59) * X ^ 2 + X ^ 4
    := by
  rw [WeierstrassCurve.Φ_two, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, curve₁]
  norm_num [Polynomial.C_eq_natCast, map_ofNat]
  ring

lemma curve₁_ΨSq : curve₁.ΨSq (2 : ℤ) =
    (-303) + (-118) * X + (5) * X ^ 2 + (4) * X ^ 3
    := by
  rw [WeierstrassCurve.ΨSq_two, curve₁_Ψ₂Sq]

/-! ##### The stability divisibility at row 1

The root set of `ker₁` is carried into itself by `x(P) ↦ x(2 ⬝ P)`, written
multiplied-out as a divisibility so that no rational function appears.  Every power
`Φ^i` and `ΨSq^j` is reduced modulo `ker₁` BEFORE being multiplied, so each `ring`
call below is an identity in degree `≤ 10` rather than the degree-`20` identity the
unreduced sum would need — which is what keeps this inside the default heartbeat
budget. -/

lemma phi₁_red : ker₁ ∣ curve₁.Φ (2 : ℤ) -
    ((1249) + (606) * X + (59) * X ^ 2 + X ^ 4) := by
  rw [curve₁_Φ]
  exact ⟨
    0
    , by rw [ker₁]; ring⟩

lemma psi₁_red : ker₁ ∣ curve₁.ΨSq (2 : ℤ) -
    ((-303) + (-118) * X + (5) * X ^ 2 + (4) * X ^ 3) := by
  rw [curve₁_ΨSq]
  exact ⟨
    0
    , by rw [ker₁]; ring⟩

lemma phi₁_pow_0 : ker₁ ∣ curve₁.Φ (2 : ℤ) ^ 0 - 1 := by simp

lemma phi₁_pow_1 : ker₁ ∣ curve₁.Φ (2 : ℤ) ^ 1 -
    ((1249) + (606) * X + (59) * X ^ 2 + X ^ 4) := by
  rw [pow_one]; exact phi₁_red

lemma phi₁_pow_2 : ker₁ ∣ curve₁.Φ (2 : ℤ) ^ 2 -
    ((909403) + (1283117) * X + (658086) * X ^ 2 + (146531) * X ^ 3 + (12012) * X ^ 4) :=
  dvd_sub_pow_succ 1 phi₁_pow_1 phi₁_red ⟨
    (-1482) + (251) * X + (-14) * X ^ 2 + X ^ 3
    , by rw [ker₁]; ring⟩

lemma phi₁_pow_3 : ker₁ ∣ curve₁.Φ (2 : ℤ) ^ 3 -
    ((3350476866) + (3714784865) * X + (1540881628) * X ^ 2 + (283397301) * X ^ 3
      + (19499183) * X ^ 4) :=
  dvd_sub_pow_succ 2 phi₁_pow_2 phi₁_red ⟨
    (5044721) + (912956) * X + (-21637) * X ^ 2 + (12012) * X ^ 3
    , by rw [ker₁]; ring⟩

lemma phi₁_pow_4 : ker₁ ∣ curve₁.Φ (2 : ℤ) ^ 4 -
    ((9429371015075) + (9996143268001) * X + (3940216934599) * X ^ 2 + (683554315862) * X ^ 3
      + (43959397647) * X ^ 4) :=
  dvd_sub_pow_succ 3 phi₁_pow_3 phi₁_red ⟨
    (11946754919) + (1317162550) * X + (10408739) * X ^ 2 + (19499183) * X ^ 3
    , by rw [ker₁]; ring⟩

lemma phi₁_pow_5 : ker₁ ∣ curve₁.Φ (2 : ℤ) ^ 5 -
    ((25210146622216270) + (26470980144419294) * X + (10314560496397278) * X ^ 2
      + (1764285865203719) * X ^ 3 + (111473940054818) * X ^ 4) :=
  dvd_sub_pow_succ 4 phi₁_pow_4 phi₁_red ⟨
    (30598774998605) + (2810660860755) * X + (68122748804) * X ^ 2 + (43959397647) * X ^ 3
    , by rw [ker₁]; ring⟩

lemma psi₁_pow_0 : ker₁ ∣ curve₁.ΨSq (2 : ℤ) ^ 0 - 1 := by simp

lemma psi₁_pow_1 : ker₁ ∣ curve₁.ΨSq (2 : ℤ) ^ 1 -
    ((-303) + (-118) * X + (5) * X ^ 2 + (4) * X ^ 3) := by
  rw [pow_one]; exact psi₁_red

lemma psi₁_pow_2 : ker₁ ∣ curve₁.ΨSq (2 : ℤ) ^ 2 -
    ((11033) + (36212) * X + (25982) * X ^ 2 + (6996) * X ^ 3 + (649) * X ^ 4) :=
  dvd_sub_pow_succ 1 psi₁_pow_1 psi₁_red ⟨
    (-184) + (16) * X
    , by rw [ker₁]; ring⟩

lemma psi₁_pow_3 : ker₁ ∣ curve₁.ΨSq (2 : ℤ) ^ 3 -
    ((-16342667) + (-21330375) * X + (-10291259) * X ^ 2 + (-2180706) * X ^ 3
      + (-171556) * X ^ 4) :=
  dvd_sub_pow_succ 2 psi₁_pow_2 psi₁_red ⟨
    (-29612) + (-5115) * X + (2596) * X ^ 2
    , by rw [ker₁]; ring⟩

lemma psi₁_pow_4 : ker₁ ∣ curve₁.ΨSq (2 : ℤ) ^ 4 -
    ((9796503035) + (10941398259) * X + (4574158644) * X ^ 2 + (848373955) * X ^ 3
      + (58901469) * X ^ 4) :=
  dvd_sub_pow_succ 3 psi₁_pow_3 psi₁_red ⟨
    (11035706) + (26532) * X + (-686224) * X ^ 2
    , by rw [ker₁]; ring⟩

lemma psi₁_pow_5 : ker₁ ∣ curve₁.ΨSq (2 : ℤ) ^ 5 -
    ((-5035298076732) + (-5383147667458) * X + (-2143135190559) * X ^ 2 + (-376251066345) * X ^ 3
      + (-24549621514) * X ^ 4) :=
  dvd_sub_pow_succ 4 psi₁_pow_4 psi₁_red ⟨
    (-4708331793) + (389520901) * X + (235605876) * X ^ 2
    , by rw [ker₁]; ring⟩

lemma term₁_0 : ker₁ ∣
    (-439) * curve₁.Φ (2 : ℤ) ^ 0 * curve₁.ΨSq (2 : ℤ) ^ 5
    -
    ((2210495855685348) + (2363201826014062) * X + (940836348655401) * X ^ 2
      + (165174218125455) * X ^ 3 + (10777283844646) * X ^ 4) :=
  dvd_sub_const_mul₂ phi₁_pow_0 psi₁_pow_5 ⟨
    0
    , by rw [ker₁]; ring⟩

lemma term₁_1 : ker₁ ∣
    (-230) * curve₁.Φ (2 : ℤ) ^ 1 * curve₁.ΨSq (2 : ℤ) ^ 4
    -
    ((-6394367302407700) + (-6788750800396070) * X + (-2680663828348880) * X ^ 2
      + (-466034985654260) * X ^ 3 + (-30049083437340) * X ^ 4) :=
  dvd_sub_const_mul₂ phi₁_pow_1 psi₁_pow_4 ⟨
    (-8155184226750) + (-921381224060) * X + (-5463279470) * X ^ 2 + (-13547337870) * X ^ 3
    , by rw [ker₁]; ring⟩

lemma term₁_2 : ker₁ ∣
    (62) * curve₁.Φ (2 : ℤ) ^ 2 * curve₁.ΨSq (2 : ℤ) ^ 3
    -
    ((-9484453655401208) + (-10023211818113120) * X + (-3936163413646640) * X ^ 2
      + (-679761420513934) * X ^ 3 + (-43470825527206) * X ^ 4) :=
  dvd_sub_const_mul₂ phi₁_pow_2 psi₁_pow_3 ⟨
    (-19505706812614) + (-6911427510988) * X + (-1393926364600) * X ^ 2 + (-127765301664) * X ^ 3
    , by rw [ker₁]; ring⟩

lemma term₁_3 : ker₁ ∣
    (63) * curve₁.Φ (2 : ℤ) ^ 3 * curve₁.ΨSq (2 : ℤ) ^ 2
    -
    ((52908629764523148) + (55743489409143690) * X + (21810313407289869) * X ^ 2
      + (3749624259462774) * X ^ 3 + (238441563612252) * X ^ 4) :=
  dvd_sub_const_mul₂ phi₁_pow_3 psi₁_pow_2 ⟨
    (115215908097906) + (43321483135161) * X + (9019808020377) * X ^ 2 + (797263095321) * X ^ 3
    , by rw [ker₁]; ring⟩

lemma term₁_4 : ker₁ ∣
    (14) * curve₁.Φ (2 : ℤ) ^ 4 * curve₁.ΨSq (2 : ℤ) ^ 1
    -
    ((-64450451284615858) + (-67765708761067856) * X + (-26448883010347028) * X ^ 2
      + (-4533287936623754) * X ^ 3 + (-287172878547170) * X ^ 4) :=
  dvd_sub_const_mul₂ phi₁_pow_4 psi₁_pow_1 ⟨
    (-55697174119972) + (6892031768314) * X + (2461726268232) * X ^ 2
    , by rw [ker₁]; ring⟩

lemma term₁_5 : ker₁ ∣
    (1) * curve₁.Φ (2 : ℤ) ^ 5 * curve₁.ΨSq (2 : ℤ) ^ 0
    -
    ((25210146622216270) + (26470980144419294) * X + (10314560496397278) * X ^ 2
      + (1764285865203719) * X ^ 3 + (111473940054818) * X ^ 4) :=
  dvd_sub_const_mul₂ phi₁_pow_5 psi₁_pow_0 ⟨
    0
    , by rw [ker₁]; ring⟩

lemma sum₁_1 : ker₁ ∣
    (-439) * curve₁.Φ (2 : ℤ) ^ 0 * curve₁.ΨSq (2 : ℤ) ^ 5
      + (-230) * curve₁.Φ (2 : ℤ) ^ 1 * curve₁.ΨSq (2 : ℤ) ^ 4
    -
    ((-4183871446722352) + (-4425548974382008) * X + (-1739827479693479) * X ^ 2
      + (-300860767528805) * X ^ 3 + (-19271799592694) * X ^ 4) :=
  dvd_sub_add term₁_0 term₁_1 ⟨0, by ring⟩

lemma sum₁_2 : ker₁ ∣
    (-439) * curve₁.Φ (2 : ℤ) ^ 0 * curve₁.ΨSq (2 : ℤ) ^ 5
      + (-230) * curve₁.Φ (2 : ℤ) ^ 1 * curve₁.ΨSq (2 : ℤ) ^ 4
      + (62) * curve₁.Φ (2 : ℤ) ^ 2 * curve₁.ΨSq (2 : ℤ) ^ 3
    -
    ((-13668325102123560) + (-14448760792495128) * X + (-5675990893340119) * X ^ 2
      + (-980622188042739) * X ^ 3 + (-62742625119900) * X ^ 4) :=
  dvd_sub_add sum₁_1 term₁_2 ⟨0, by ring⟩

lemma sum₁_3 : ker₁ ∣
    (-439) * curve₁.Φ (2 : ℤ) ^ 0 * curve₁.ΨSq (2 : ℤ) ^ 5
      + (-230) * curve₁.Φ (2 : ℤ) ^ 1 * curve₁.ΨSq (2 : ℤ) ^ 4
      + (62) * curve₁.Φ (2 : ℤ) ^ 2 * curve₁.ΨSq (2 : ℤ) ^ 3
      + (63) * curve₁.Φ (2 : ℤ) ^ 3 * curve₁.ΨSq (2 : ℤ) ^ 2
    -
    ((39240304662399588) + (41294728616648562) * X + (16134322513949750) * X ^ 2
      + (2769002071420035) * X ^ 3 + (175698938492352) * X ^ 4) :=
  dvd_sub_add sum₁_2 term₁_3 ⟨0, by ring⟩

lemma sum₁_4 : ker₁ ∣
    (-439) * curve₁.Φ (2 : ℤ) ^ 0 * curve₁.ΨSq (2 : ℤ) ^ 5
      + (-230) * curve₁.Φ (2 : ℤ) ^ 1 * curve₁.ΨSq (2 : ℤ) ^ 4
      + (62) * curve₁.Φ (2 : ℤ) ^ 2 * curve₁.ΨSq (2 : ℤ) ^ 3
      + (63) * curve₁.Φ (2 : ℤ) ^ 3 * curve₁.ΨSq (2 : ℤ) ^ 2
      + (14) * curve₁.Φ (2 : ℤ) ^ 4 * curve₁.ΨSq (2 : ℤ) ^ 1
    -
    ((-25210146622216270) + (-26470980144419294) * X + (-10314560496397278) * X ^ 2
      + (-1764285865203719) * X ^ 3 + (-111473940054818) * X ^ 4) :=
  dvd_sub_add sum₁_3 term₁_4 ⟨0, by ring⟩

lemma sum₁_5 : ker₁ ∣
    (-439) * curve₁.Φ (2 : ℤ) ^ 0 * curve₁.ΨSq (2 : ℤ) ^ 5
      + (-230) * curve₁.Φ (2 : ℤ) ^ 1 * curve₁.ΨSq (2 : ℤ) ^ 4
      + (62) * curve₁.Φ (2 : ℤ) ^ 2 * curve₁.ΨSq (2 : ℤ) ^ 3
      + (63) * curve₁.Φ (2 : ℤ) ^ 3 * curve₁.ΨSq (2 : ℤ) ^ 2
      + (14) * curve₁.Φ (2 : ℤ) ^ 4 * curve₁.ΨSq (2 : ℤ) ^ 1
      + (1) * curve₁.Φ (2 : ℤ) ^ 5 * curve₁.ΨSq (2 : ℤ) ^ 0
    -
    (0) :=
  dvd_sub_add sum₁_4 term₁_5 ⟨0, by ring⟩

/-- **The stability divisibility at row 1**, assembled from the reduced terms. -/
lemma ker₁_dvd_multComp : ker₁ ∣
    ∑ i ∈ Finset.range (ker₁.natDegree + 1), C (ker₁.coeff i) *
      curve₁.Φ (2 : ℤ) ^ i * curve₁.ΨSq (2 : ℤ) ^
        (ker₁.natDegree - i) := by
  rw [ker₁_natDegree]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num only
  rw [ker₁_coeff_0, ker₁_coeff_1, ker₁_coeff_2, ker₁_coeff_3, ker₁_coeff_4, ker₁_coeff_5]
  simpa using sum₁_5

/-- **The kernel-polynomial certificate at row 1.** -/
theorem curve₁_isKernelPolynomial : curve₁.IsKernelPolynomial 11 ker₁ 2 where
  monic := ker₁_monic
  natDegree_eq := ker₁_natDegree
  dvd_ΨSq := by
    rw [WeierstrassCurve.ΨSq_ofNat, if_neg (by decide), mul_one]
    exact dvd_pow ker₁_dvd_preΨ' (by norm_num)
  mult_ne_zero := by decide
  generates := by
    intro k hk
    obtain ⟨i, -, hi⟩ := generates_aux_11_2 k hk
    exact ⟨i, hi⟩
  dvd_multComp := ker₁_dvd_multComp


/-! #### Row 2: `p = 11`, `j₀ = -32768`, model `[0, -1, 1, -7, 10]`, multiplier `m = 2` -/

/-- The minimal twist of conductor-level model at row 2 of `genusOneJTable`: `[a₁, a₂, a₃, a₄, a₆] = [0, -1, 1, -7, 10]`. -/
noncomputable def curve₂ : WeierstrassCurve ℚ := ⟨0, -1, 1, -7, 10⟩

lemma curve₂_Δ : curve₂.Δ = -1331 := by
  norm_num [curve₂, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

lemma curve₂_c₄ : curve₂.c₄ = 352 := by
  norm_num [curve₂, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]

noncomputable instance : curve₂.IsElliptic :=
  ⟨by rw [curve₂_Δ]; exact isUnit_iff_ne_zero.mpr (by norm_num)⟩

lemma curve₂_j : curve₂.j = (-32768 : ℚ) :=
  j_eq_of_Δ_c₄ curve₂ curve₂_Δ curve₂_c₄ (by norm_num) (by norm_num)

/-- The kernel polynomial at row 2, monic of degree `(p-1)/2 = 5`. -/
noncomputable def ker₂ : ℚ[X] :=
  (43) + (-73) * X + (20) * X ^ 2 + (17) * X ^ 3 + (-9) * X ^ 4 + X ^ 5

lemma curve₂_Ψ₂Sq : curve₂.Ψ₂Sq =
    (41) + (-28) * X + (-4) * X ^ 2 + (4) * X ^ 3
    := by
  simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, curve₂]
  norm_num [Polynomial.C_eq_natCast, map_ofNat]
  ring

lemma curve₂_Ψ₃ : curve₂.Ψ₃ =
    (-90) + (123) * X + (-42) * X ^ 2 + (-4) * X ^ 3 + (3) * X ^ 4
    := by
  simp only [WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, curve₂]
  norm_num [Polynomial.C_eq_natCast, map_ofNat]
  ring

lemma curve₂_preΨ₄ : curve₂.preΨ₄ =
    (-421) + (934) * X + (-900) * X ^ 2 + (410) * X ^ 3 + (-70) * X ^ 4 + (-4) * X ^ 5
      + (2) * X ^ 6
    := by
  simp only [WeierstrassCurve.preΨ₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, curve₂]
  norm_num [Polynomial.C_eq_natCast, map_ofNat]
  ring

/-! ##### The chain of remainders modulo `ker₂`

`preΨ'ₙ ≡ rₙ (mod ker₂)` for `n = 1, …, 11`, each `rₙ` of degree `< 5`; the chain ends
at `r_11 = 0`, which is exactly `ker₂ ∣ preΨ'_11`.  Every step is one application of a
`step_preΨ'_*` lemma against an explicit cofactor. -/

lemma pre₂_1 : ker₂ ∣ curve₂.preΨ' 1 - 1 := by simp

lemma pre₂_2 : ker₂ ∣ curve₂.preΨ' 2 - 1 := by simp

lemma pre₂_3 : ker₂ ∣ curve₂.preΨ' 3 -
    ((-90) + (123) * X + (-42) * X ^ 2 + (-4) * X ^ 3 + (3) * X ^ 4) := by
  rw [WeierstrassCurve.preΨ'_three, curve₂_Ψ₃]
  exact ⟨
    0
    , by rw [ker₂]; ring⟩

lemma pre₂_4 : ker₂ ∣ curve₂.preΨ' 4 -
    ((-1023) + (1870) * X + (-1034) * X ^ 2 + (132) * X ^ 3 + (22) * X ^ 4) := by
  rw [WeierstrassCurve.preΨ'_four, curve₂_preΨ₄]
  exact ⟨
    (14) + (2) * X
    , by rw [ker₂]; ring⟩

lemma pre₂_5 : ker₂ ∣ curve₂.preΨ' 5 -
    ((-10482956) + (13952873) * X + (2035099) * X ^ 2 + (-7115526) * X ^ 3 + (1932612) * X ^ 4) :=
  step_preΨ'_odd_even curve₂ 0 5 (by decide) (by norm_num)
    pre₂_1 pre₂_2 pre₂_3 pre₂_4
    (by rw [curve₂_Ψ₂Sq]; exact ⟨
      (220751) + (108496) * X + (1799) * X ^ 2 + (-8027) * X ^ 3 + (3236) * X ^ 4 + (586) * X ^ 5
        + (-135) * X ^ 6 + (-27) * X ^ 7
      , by rw [ker₂]; ring⟩)

lemma pre₂_6 : ker₂ ∣ curve₂.preΨ' 6 -
    ((-6093203534) + (8615906398) * X + (165560428) * X ^ 2 + (-3503986607) * X ^ 3
      + (999482506) * X ^ 4) :=
  step_preΨ'_even curve₂ 0 6 (by norm_num)
    pre₂_1 pre₂_2 pre₂_3 pre₂_4 pre₂_5
    (⟨
      (165833888) + (10970707) * X + (7247174) * X ^ 2 + (2834304) * X ^ 3 + (217800) * X ^ 4
        + (-104544) * X ^ 5 + (-28556) * X ^ 6 + (-1452) * X ^ 7
      , by rw [ker₂]; ring⟩)

lemma pre₂_7 : ker₂ ∣ curve₂.preΨ' 7 -
    ((-15421921292575281) + (23577864288138237) * X + (-3223934419480852) * X ^ 2
      + (-6576792844350344) * X ^ 3 + (2076971428757225) * X ^ 4) :=
  step_preΨ'_odd_odd curve₂ 1 7 (by decide) (by norm_num)
    pre₂_2 pre₂_3 pre₂_4 pre₂_5
    (by rw [curve₂_Ψ₂Sq]; exact ⟨
      (358868908016256) + (59668245400203) * X + (12407998918447) * X ^ 2
        + (347039297891) * X ^ 3 + (927003026114) * X ^ 4 + (1799774207) * X ^ 5
        + (-61429887904) * X ^ 6 + (30010667929) * X ^ 7 + (-1045777348) * X ^ 8
        + (-1261366073) * X ^ 9 + (182163322) * X ^ 10 + (30714156) * X ^ 11
        + (-4259200) * X ^ 12 + (-170368) * X ^ 13
      , by rw [ker₂]; ring⟩)

lemma pre₂_11 : ker₂ ∣ curve₂.preΨ' 11 -
    (0) :=
  step_preΨ'_odd_odd curve₂ 3 11 (by decide) (by norm_num)
    pre₂_4 pre₂_5 pre₂_6 pre₂_7
    (by rw [curve₂_Ψ₂Sq]; exact ⟨
      (404115745294878113116223386122488808) + (-1528101680323116457226156521684876576) * X
        + (1571373100536007326493517183164029940) * X ^ 2
        + (907423689434449327706021226506401721) * X ^ 3
        + (-2715051987386239772290909511055943069) * X ^ 4
        + (1144646960466157058381487299864538353) * X ^ 5
        + (990982549401413328087266476322369332) * X ^ 6
        + (-1013918896778897347965667088041121294) * X ^ 7
        + (131850956544720308135971245830862558) * X ^ 8
        + (182838566472484403168687257069174660) * X ^ 9
        + (-87664118096226956388732465239629128) * X ^ 10
        + (10334660729862632973736913248038656) * X ^ 11
        + (1358965476547059834244350935411552) * X ^ 12
        + (-115399417729691072275858111392544) * X ^ 13
        + (-111444633565715545045870405495328) * X ^ 14
        + (25078821491211091814699284355648) * X ^ 15
        + (-872518342983905640154013816704) * X ^ 16 + (-351453809084060388316726796032) * X ^ 17
      , by rw [ker₂]; ring⟩)

lemma ker₂_dvd_preΨ' : ker₂ ∣ curve₂.preΨ' 11 := by
  simpa using pre₂_11

lemma ker₂_coeff_0 : C (ker₂.coeff 0) = (43 : ℚ[X]) := by
  rw [ker₂]; simp [Polynomial.coeff_X, map_ofNat]

lemma ker₂_coeff_1 : C (ker₂.coeff 1) = (-73 : ℚ[X]) := by
  rw [ker₂]; simp [Polynomial.coeff_X, map_ofNat]

lemma ker₂_coeff_2 : C (ker₂.coeff 2) = (20 : ℚ[X]) := by
  rw [ker₂]; simp [Polynomial.coeff_X, map_ofNat]

lemma ker₂_coeff_3 : C (ker₂.coeff 3) = (17 : ℚ[X]) := by
  rw [ker₂]; simp [Polynomial.coeff_X, map_ofNat]

lemma ker₂_coeff_4 : C (ker₂.coeff 4) = (-9 : ℚ[X]) := by
  rw [ker₂]; simp [Polynomial.coeff_X, map_ofNat]

lemma ker₂_coeff_5 : C (ker₂.coeff 5) = (1 : ℚ[X]) := by
  rw [ker₂]; simp [Polynomial.coeff_X]

lemma ker₂_natDegree : ker₂.natDegree = 5 := by
  rw [ker₂]; compute_degree!

lemma ker₂_monic : ker₂.Monic := by
  rw [ker₂]; monicity!

lemma curve₂_Φ : curve₂.Φ (2 : ℤ) =
    (90) + (-82) * X + (14) * X ^ 2 + X ^ 4
    := by
  rw [WeierstrassCurve.Φ_two, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, curve₂]
  norm_num [Polynomial.C_eq_natCast, map_ofNat]
  ring

lemma curve₂_ΨSq : curve₂.ΨSq (2 : ℤ) =
    (41) + (-28) * X + (-4) * X ^ 2 + (4) * X ^ 3
    := by
  rw [WeierstrassCurve.ΨSq_two, curve₂_Ψ₂Sq]

/-! ##### The stability divisibility at row 2

The root set of `ker₂` is carried into itself by `x(P) ↦ x(2 ⬝ P)`, written
multiplied-out as a divisibility so that no rational function appears.  Every power
`Φ^i` and `ΨSq^j` is reduced modulo `ker₂` BEFORE being multiplied, so each `ring`
call below is an identity in degree `≤ 10` rather than the degree-`20` identity the
unreduced sum would need — which is what keeps this inside the default heartbeat
budget. -/

lemma phi₂_red : ker₂ ∣ curve₂.Φ (2 : ℤ) -
    ((90) + (-82) * X + (14) * X ^ 2 + X ^ 4) := by
  rw [curve₂_Φ]
  exact ⟨
    0
    , by rw [ker₂]; ring⟩

lemma psi₂_red : ker₂ ∣ curve₂.ΨSq (2 : ℤ) -
    ((41) + (-28) * X + (-4) * X ^ 2 + (4) * X ^ 3) := by
  rw [curve₂_ΨSq]
  exact ⟨
    0
    , by rw [ker₂]; ring⟩

lemma phi₂_pow_0 : ker₂ ∣ curve₂.Φ (2 : ℤ) ^ 0 - 1 := by simp

lemma phi₂_pow_1 : ker₂ ∣ curve₂.Φ (2 : ℤ) ^ 1 -
    ((90) + (-82) * X + (14) * X ^ 2 + X ^ 4) := by
  rw [pow_one]; exact phi₂_red

lemma phi₂_pow_2 : ker₂ ∣ curve₂.Φ (2 : ℤ) ^ 2 -
    ((-13013) + (17127) * X + (5753) * X ^ 2 + (-11869) * X ^ 3 + (3124) * X ^ 4) :=
  dvd_sub_pow_succ 1 phi₂_pow_1 phi₂_red ⟨
    (491) + (92) * X + (9) * X ^ 2 + X ^ 3
    , by rw [ker₂]; ring⟩

lemma phi₂_pow_3 : ker₂ ∣ curve₂.Φ (2 : ℤ) ^ 3 -
    ((-24371820) + (35863674) * X + (-2148355) * X ^ 2 + (-12272909) * X ^ 3 + (3656741) * X ^ 4) :=
  dvd_sub_pow_succ 2 phi₂_pow_2 phi₂_red ⟨
    (539550) + (142604) * X + (16247) * X ^ 2 + (3124) * X ^ 3
    , by rw [ker₂]; ring⟩

lemma phi₂_pow_4 : ker₂ ∣ curve₂.Φ (2 : ℤ) ^ 4 -
    ((-32027070372) + (48451256326) * X + (-5637546332) * X ^ 2 + (-14324095555) * X ^ 3
      + (4444905113) * X ^ 4) :=
  dvd_sub_pow_succ 3 phi₂_pow_3 phi₂_red ⟨
    (693804804) + (172621262) * X + (20637760) * X ^ 2 + (3656741) * X ^ 3
    , by rw [ker₂]; ring⟩

lemma phi₂_pow_5 : ker₂ ∣ curve₂.Φ (2 : ℤ) ^ 5 -
    ((-40176614610517) + (61177832986710) * X + (-7892314723315) * X ^ 2
      + (-17452233314538) * X ^ 3 + (5473780612421) * X ^ 4) :=
  dvd_sub_pow_succ 4 phi₂_pow_4 phi₂_red ⟨
    (867306471559) + (212148192487) * X + (25680050462) * X ^ 2 + (4444905113) * X ^ 3
    , by rw [ker₂]; ring⟩

lemma psi₂_pow_0 : ker₂ ∣ curve₂.ΨSq (2 : ℤ) ^ 0 - 1 := by simp

lemma psi₂_pow_1 : ker₂ ∣ curve₂.ΨSq (2 : ℤ) ^ 1 -
    ((41) + (-28) * X + (-4) * X ^ 2 + (4) * X ^ 3) := by
  rw [pow_one]; exact psi₂_red

lemma psi₂_pow_2 : ker₂ ∣ curve₂.ΨSq (2 : ℤ) ^ 2 -
    ((-3135) + (5192) * X + (-616) * X ^ 2 + (-1672) * X ^ 3 + (528) * X ^ 4) :=
  dvd_sub_pow_succ 1 psi₂_pow_1 psi₂_red ⟨
    (112) + (16) * X
    , by rw [ker₂]; ring⟩

lemma psi₂_pow_3 : ker₂ ∣ curve₂.ΨSq (2 : ℤ) ^ 3 -
    ((-2081079) + (3176492) * X + (-411884) * X ^ 2 + (-906532) * X ^ 3 + (284592) * X ^ 4) :=
  dvd_sub_pow_succ 2 psi₂_pow_2 psi₂_red ⟨
    (45408) + (10208) * X + (2112) * X ^ 2
    , by rw [ker₂]; ring⟩

lemma psi₂_pow_4 : ker₂ ∣ curve₂.ΨSq (2 : ℤ) ^ 4 -
    ((-1116683711) + (1703743888) * X + (-226057040) * X ^ 2 + (-480927568) * X ^ 3
      + (151329376) * X ^ 4) :=
  dvd_sub_pow_succ 3 psi₂_pow_3 psi₂_red ⟨
    (23985104) + (5480816) * X + (1138368) * X ^ 2
    , by rw [ker₂]; ring⟩

lemma psi₂_pow_5 : ker₂ ∣ curve₂.ΨSq (2 : ℤ) ^ 5 -
    ((-594521215959) + (907188043124) * X + (-120687109972) * X ^ 2 + (-255801168524) * X ^ 3
      + (80515192736) * X ^ 4) :=
  dvd_sub_pow_succ 4 psi₂_pow_4 psi₂_red ⟨
    (12761329856) + (2918829760) * X + (605317504) * X ^ 2
    , by rw [ker₂]; ring⟩

lemma term₂_0 : ker₂ ∣
    (43) * curve₂.Φ (2 : ℤ) ^ 0 * curve₂.ΨSq (2 : ℤ) ^ 5
    -
    ((-25564412286237) + (39009085854332) * X + (-5189545728796) * X ^ 2
      + (-10999450246532) * X ^ 3 + (3462153287648) * X ^ 4) :=
  dvd_sub_const_mul₂ phi₂_pow_0 psi₂_pow_5 ⟨
    0
    , by rw [ker₂]; ring⟩

lemma term₂_1 : ker₂ ∣
    (-73) * curve₂.Φ (2 : ℤ) ^ 1 * curve₂.ΨSq (2 : ℤ) ^ 4
    -
    ((100882300339414) + (-153932678828126) * X + (20468807444690) * X ^ 2
      + (43412405080880) * X ^ 3 + (-13663604686985) * X ^ 4) :=
  dvd_sub_const_mul₂ phi₂_pow_1 psi₂_pow_4 ⟨
    (-2175481124608) + (-529197890848) * X + (-64315687568) * X ^ 2 + (-11047044448) * X ^ 3
    , by rw [ker₂]; ring⟩

lemma term₂_2 : ker₂ ∣
    (20) * curve₂.Φ (2 : ℤ) ^ 2 * curve₂.ΨSq (2 : ℤ) ^ 3
    -
    ((-64239362570900) + (98012626946300) * X + (-13017819971420) * X ^ 2
      + (-27654128409380) * X ^ 3 + (8702654908640) * X ^ 4) :=
  dvd_sub_const_mul₂ phi₂_pow_2 psi₂_pow_3 ⟨
    (1506534516080) + (242437816720) * X + (35835205120) * X ^ 2 + (17781308160) * X ^ 3
    , by rw [ker₂]; ring⟩

lemma term₂_3 : ker₂ ∣
    (17) * curve₂.Φ (2 : ℤ) ^ 3 * curve₂.ΨSq (2 : ℤ) ^ 2
    -
    ((-126877608280324) + (193543317224026) * X + (-25630971765619) * X ^ 2
      + (-54669418877029) * X ^ 3 + (17198357832821) * X ^ 4) :=
  dvd_sub_const_mul₂ phi₂_pow_3 psi₂_pow_2 ⟨
    (2980848940168) + (465026664696) * X + (81305327576) * X ^ 2 + (32822907216) * X ^ 3
    , by rw [ker₂]; ring⟩

lemma term₂_4 : ker₂ ∣
    (-9) * curve₂.Φ (2 : ℤ) ^ 4 * curve₂.ΨSq (2 : ℤ) ^ 1
    -
    ((155975697408564) + (-237810184183242) * X + (31261844744460) * X ^ 2
      + (67362825766599) * X ^ 3 + (-21173341954545) * X ^ 4) :=
  dvd_sub_const_mul₂ phi₂_pow_4 psi₂_pow_1 ⟨
    (-3352504847472) + (-764465232564) * X + (-160016584068) * X ^ 2
    , by rw [ker₂]; ring⟩

lemma term₂_5 : ker₂ ∣
    (1) * curve₂.Φ (2 : ℤ) ^ 5 * curve₂.ΨSq (2 : ℤ) ^ 0
    -
    ((-40176614610517) + (61177832986710) * X + (-7892314723315) * X ^ 2
      + (-17452233314538) * X ^ 3 + (5473780612421) * X ^ 4) :=
  dvd_sub_const_mul₂ phi₂_pow_5 psi₂_pow_0 ⟨
    0
    , by rw [ker₂]; ring⟩

lemma sum₂_1 : ker₂ ∣
    (43) * curve₂.Φ (2 : ℤ) ^ 0 * curve₂.ΨSq (2 : ℤ) ^ 5
      + (-73) * curve₂.Φ (2 : ℤ) ^ 1 * curve₂.ΨSq (2 : ℤ) ^ 4
    -
    ((75317888053177) + (-114923592973794) * X + (15279261715894) * X ^ 2
      + (32412954834348) * X ^ 3 + (-10201451399337) * X ^ 4) :=
  dvd_sub_add term₂_0 term₂_1 ⟨0, by ring⟩

lemma sum₂_2 : ker₂ ∣
    (43) * curve₂.Φ (2 : ℤ) ^ 0 * curve₂.ΨSq (2 : ℤ) ^ 5
      + (-73) * curve₂.Φ (2 : ℤ) ^ 1 * curve₂.ΨSq (2 : ℤ) ^ 4
      + (20) * curve₂.Φ (2 : ℤ) ^ 2 * curve₂.ΨSq (2 : ℤ) ^ 3
    -
    ((11078525482277) + (-16910966027494) * X + (2261441744474) * X ^ 2 + (4758826424968) * X ^ 3
      + (-1498796490697) * X ^ 4) :=
  dvd_sub_add sum₂_1 term₂_2 ⟨0, by ring⟩

lemma sum₂_3 : ker₂ ∣
    (43) * curve₂.Φ (2 : ℤ) ^ 0 * curve₂.ΨSq (2 : ℤ) ^ 5
      + (-73) * curve₂.Φ (2 : ℤ) ^ 1 * curve₂.ΨSq (2 : ℤ) ^ 4
      + (20) * curve₂.Φ (2 : ℤ) ^ 2 * curve₂.ΨSq (2 : ℤ) ^ 3
      + (17) * curve₂.Φ (2 : ℤ) ^ 3 * curve₂.ΨSq (2 : ℤ) ^ 2
    -
    ((-115799082798047) + (176632351196532) * X + (-23369530021145) * X ^ 2
      + (-49910592452061) * X ^ 3 + (15699561342124) * X ^ 4) :=
  dvd_sub_add sum₂_2 term₂_3 ⟨0, by ring⟩

lemma sum₂_4 : ker₂ ∣
    (43) * curve₂.Φ (2 : ℤ) ^ 0 * curve₂.ΨSq (2 : ℤ) ^ 5
      + (-73) * curve₂.Φ (2 : ℤ) ^ 1 * curve₂.ΨSq (2 : ℤ) ^ 4
      + (20) * curve₂.Φ (2 : ℤ) ^ 2 * curve₂.ΨSq (2 : ℤ) ^ 3
      + (17) * curve₂.Φ (2 : ℤ) ^ 3 * curve₂.ΨSq (2 : ℤ) ^ 2
      + (-9) * curve₂.Φ (2 : ℤ) ^ 4 * curve₂.ΨSq (2 : ℤ) ^ 1
    -
    ((40176614610517) + (-61177832986710) * X + (7892314723315) * X ^ 2
      + (17452233314538) * X ^ 3 + (-5473780612421) * X ^ 4) :=
  dvd_sub_add sum₂_3 term₂_4 ⟨0, by ring⟩

lemma sum₂_5 : ker₂ ∣
    (43) * curve₂.Φ (2 : ℤ) ^ 0 * curve₂.ΨSq (2 : ℤ) ^ 5
      + (-73) * curve₂.Φ (2 : ℤ) ^ 1 * curve₂.ΨSq (2 : ℤ) ^ 4
      + (20) * curve₂.Φ (2 : ℤ) ^ 2 * curve₂.ΨSq (2 : ℤ) ^ 3
      + (17) * curve₂.Φ (2 : ℤ) ^ 3 * curve₂.ΨSq (2 : ℤ) ^ 2
      + (-9) * curve₂.Φ (2 : ℤ) ^ 4 * curve₂.ΨSq (2 : ℤ) ^ 1
      + (1) * curve₂.Φ (2 : ℤ) ^ 5 * curve₂.ΨSq (2 : ℤ) ^ 0
    -
    (0) :=
  dvd_sub_add sum₂_4 term₂_5 ⟨0, by ring⟩

/-- **The stability divisibility at row 2**, assembled from the reduced terms. -/
lemma ker₂_dvd_multComp : ker₂ ∣
    ∑ i ∈ Finset.range (ker₂.natDegree + 1), C (ker₂.coeff i) *
      curve₂.Φ (2 : ℤ) ^ i * curve₂.ΨSq (2 : ℤ) ^
        (ker₂.natDegree - i) := by
  rw [ker₂_natDegree]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num only
  rw [ker₂_coeff_0, ker₂_coeff_1, ker₂_coeff_2, ker₂_coeff_3, ker₂_coeff_4, ker₂_coeff_5]
  simpa using sum₂_5

/-- **The kernel-polynomial certificate at row 2.** -/
theorem curve₂_isKernelPolynomial : curve₂.IsKernelPolynomial 11 ker₂ 2 where
  monic := ker₂_monic
  natDegree_eq := ker₂_natDegree
  dvd_ΨSq := by
    rw [WeierstrassCurve.ΨSq_ofNat, if_neg (by decide), mul_one]
    exact dvd_pow ker₂_dvd_preΨ' (by norm_num)
  mult_ne_zero := by decide
  generates := by
    intro k hk
    obtain ⟨i, -, hi⟩ := generates_aux_11_2 k hk
    exact ⟨i, hi⟩
  dvd_multComp := ker₂_dvd_multComp


/-! #### Row 3: `p = 11`, `j₀ = -121`, model `[1, 1, 0, -2, -7]`, multiplier `m = 2` -/

/-- The minimal twist of conductor-level model at row 3 of `genusOneJTable`: `[a₁, a₂, a₃, a₄, a₆] = [1, 1, 0, -2, -7]`. -/
noncomputable def curve₃ : WeierstrassCurve ℚ := ⟨1, 1, 0, -2, -7⟩

lemma curve₃_Δ : curve₃.Δ = -14641 := by
  norm_num [curve₃, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

lemma curve₃_c₄ : curve₃.c₄ = 121 := by
  norm_num [curve₃, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]

noncomputable instance : curve₃.IsElliptic :=
  ⟨by rw [curve₃_Δ]; exact isUnit_iff_ne_zero.mpr (by norm_num)⟩

lemma curve₃_j : curve₃.j = (-121 : ℚ) :=
  j_eq_of_Δ_c₄ curve₃ curve₃_Δ curve₃_c₄ (by norm_num) (by norm_num)

/-- The kernel polynomial at row 3, monic of degree `(p-1)/2 = 5`. -/
noncomputable def ker₃ : ℚ[X] :=
  (1) + (-76) * X + (-37) * X ^ 2 + (30) * X ^ 3 + (14) * X ^ 4 + X ^ 5

lemma curve₃_Ψ₂Sq : curve₃.Ψ₂Sq =
    (-28) + (-8) * X + (5) * X ^ 2 + (4) * X ^ 3
    := by
  simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, curve₃]
  norm_num [Polynomial.C_eq_natCast, map_ofNat]
  ring

lemma curve₃_Ψ₃ : curve₃.Ψ₃ =
    (-39) + (-84) * X + (-12) * X ^ 2 + (5) * X ^ 3 + (3) * X ^ 4
    := by
  simp only [WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, curve₃]
  norm_num [Polynomial.C_eq_natCast, map_ofNat]
  ring

lemma curve₃_preΨ₄ : curve₃.preΨ₄ =
    (-628) + (-307) * X + (-390) * X ^ 2 + (-280) * X ^ 3 + (-20) * X ^ 4 + (5) * X ^ 5
      + (2) * X ^ 6
    := by
  simp only [WeierstrassCurve.preΨ₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, curve₃]
  norm_num [Polynomial.C_eq_natCast, map_ofNat]
  ring

/-! ##### The chain of remainders modulo `ker₃`

`preΨ'ₙ ≡ rₙ (mod ker₃)` for `n = 1, …, 11`, each `rₙ` of degree `< 5`; the chain ends
at `r_11 = 0`, which is exactly `ker₃ ∣ preΨ'_11`.  Every step is one application of a
`step_preΨ'_*` lemma against an explicit cofactor. -/

lemma pre₃_1 : ker₃ ∣ curve₃.preΨ' 1 - 1 := by simp

lemma pre₃_2 : ker₃ ∣ curve₃.preΨ' 2 - 1 := by simp

lemma pre₃_3 : ker₃ ∣ curve₃.preΨ' 3 -
    ((-39) + (-84) * X + (-12) * X ^ 2 + (5) * X ^ 3 + (3) * X ^ 4) := by
  rw [WeierstrassCurve.preΨ'_three, curve₃_Ψ₃]
  exact ⟨
    0
    , by rw [ker₃]; ring⟩

lemma pre₃_4 : ker₃ ∣ curve₃.preΨ' 4 -
    ((-605) + (-2057) * X + (-1089) * X ^ 2 + (484) * X ^ 3 + (242) * X ^ 4) := by
  rw [WeierstrassCurve.preΨ'_four, curve₃_preΨ₄]
  exact ⟨
    (-23) + (2) * X
    , by rw [ker₃]; ring⟩

lemma pre₃_5 : ker₃ ∣ curve₃.preΨ' 5 -
    ((95181141) + (-7275478925) * X + (-2877981370) * X ^ 2 + (3129865134) * X ^ 3
      + (1055206152) * X ^ 4) :=
  step_preΨ'_odd_even curve₃ 0 5 (by decide) (by norm_num)
    pre₃_1 pre₃_2 pre₃_3 pre₃_4
    (by rw [curve₃_Ψ₂Sq]; exact ⟨
      (-95596142) + (8671697) * X + (-791236) * X ^ 2 + (63556) * X ^ 3 + (-6948) * X ^ 4
        + (1379) * X ^ 5 + (243) * X ^ 6 + (-27) * X ^ 7
      , by rw [ker₃]; ring⟩)

lemma pre₃_6 : ker₃ ∣ curve₃.preΨ' 6 -
    ((1011988277201) + (-77000282361772) * X + (-30463612373315) * X ^ 2
      + (33119733267786) * X ^ 3 + (11165739752409) * X ^ 4) :=
  step_preΨ'_even curve₃ 0 6 (by norm_num)
    pre₃_1 pre₃_2 pre₃_3 pre₃_4 pre₃_5
    (⟨
      (-1015686066725) + (84017568833) * X + (-8767660363) * X ^ 2 + (1269974981) * X ^ 3
        + (172353852) * X ^ 4 + (-14816692) * X ^ 5 + (1464100) * X ^ 6 + (-175692) * X ^ 7
      , by rw [ker₃]; ring⟩)

lemma pre₃_7 : ker₃ ∣ curve₃.preΨ' 7 -
    ((634672158999474008589) + (-48292604706515311995567) * X
      + (-19106088123384060727522) * X ^ 2 + (20771758621968570235635) * X ^ 3
      + (7002855850648851755606) * X ^ 4) :=
  step_preΨ'_odd_odd curve₃ 1 7 (by decide) (by norm_num)
    pre₃_2 pre₃_3 pre₃_4 pre₃_5
    (by rw [curve₃_Ψ₂Sq]; exact ⟨
      (-634672164471911133568) + (57520603612090091902) * X + (-5213204072187438800) * X ^ 2
        + (472397968775273024) * X ^ 3 + (-42828836386999795) * X ^ 4
        + (3895345813030760) * X ^ 5 + (-343647183106436) * X ^ 6 + (32136247635514) * X ^ 7
        + (-3723465138239) * X ^ 8 + (23235794076) * X ^ 9 + (-8698364510) * X ^ 10
        + (15324324752) * X ^ 11 + (1247178944) * X ^ 12 + (-226759808) * X ^ 13
      , by rw [ker₃]; ring⟩)

lemma pre₃_11 : ker₃ ∣ curve₃.preΨ' 11 -
    (0) :=
  step_preΨ'_odd_odd curve₃ 3 11 (by decide) (by norm_num)
    pre₃_4 pre₃_5 pre₃_6 pre₃_7
    (by rw [curve₃_Ψ₂Sq]; exact ⟨
      (547762246777929049611638854050832194318838489)
        + (-125619717044061467161141771172701624173398175210) * X
        + (9557049190173864581951553665648741087980437474905) * X ^ 2
        + (-237628248102437943112137235224660948792959678691969) * X ^ 3
        + (-275236967476714919806525568508115675904985794165666) * X ^ 4
        + (219596457030272840223937100901304031708143864000980) * X ^ 5
        + (321528386684923096564628537437996483749951639931239) * X ^ 6
        + (-30159049483705654332880220551837154696354268233914) * X ^ 7
        + (-125595141450677118919163143455240317875308143771189) * X ^ 8
        + (-20767624034452644909891942758426239884722821497222) * X ^ 9
        + (15462842936058502611913847987504865338083453240396) * X ^ 10
        + (5231140084108707790491562024693660779095829572410) * X ^ 11
        + (270466789710076768727331434936854366017063152295) * X ^ 12
        + (-24278200388010063837056738874201706071304591905) * X ^ 13
        + (2443495673984657387846613789600434934569009988) * X ^ 14
        + (-187230819279860843270382676218592189852457058) * X ^ 15
        + (3241735455676566402480797125390618592384880) * X ^ 16
        + (-5390112781126379932609440314882193978413088) * X ^ 17
      , by rw [ker₃]; ring⟩)

lemma ker₃_dvd_preΨ' : ker₃ ∣ curve₃.preΨ' 11 := by
  simpa using pre₃_11

lemma ker₃_coeff_0 : C (ker₃.coeff 0) = (1 : ℚ[X]) := by
  rw [ker₃]; simp [Polynomial.coeff_X]

lemma ker₃_coeff_1 : C (ker₃.coeff 1) = (-76 : ℚ[X]) := by
  rw [ker₃]; simp [Polynomial.coeff_X, Polynomial.coeff_one, map_ofNat]

lemma ker₃_coeff_2 : C (ker₃.coeff 2) = (-37 : ℚ[X]) := by
  rw [ker₃]; simp [Polynomial.coeff_X, Polynomial.coeff_one, map_ofNat]

lemma ker₃_coeff_3 : C (ker₃.coeff 3) = (30 : ℚ[X]) := by
  rw [ker₃]; simp [Polynomial.coeff_X, Polynomial.coeff_one, map_ofNat]

lemma ker₃_coeff_4 : C (ker₃.coeff 4) = (14 : ℚ[X]) := by
  rw [ker₃]; simp [Polynomial.coeff_X, Polynomial.coeff_one, map_ofNat]

lemma ker₃_coeff_5 : C (ker₃.coeff 5) = (1 : ℚ[X]) := by
  rw [ker₃]; simp [Polynomial.coeff_X, Polynomial.coeff_one]

lemma ker₃_natDegree : ker₃.natDegree = 5 := by
  rw [ker₃]; compute_degree!

lemma ker₃_monic : ker₃.Monic := by
  rw [ker₃]; monicity!

lemma curve₃_Φ : curve₃.Φ (2 : ℤ) =
    (39) + (56) * X + (4) * X ^ 2 + X ^ 4
    := by
  rw [WeierstrassCurve.Φ_two, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, curve₃]
  norm_num [Polynomial.C_eq_natCast, map_ofNat]
  ring

lemma curve₃_ΨSq : curve₃.ΨSq (2 : ℤ) =
    (-28) + (-8) * X + (5) * X ^ 2 + (4) * X ^ 3
    := by
  rw [WeierstrassCurve.ΨSq_two, curve₃_Ψ₂Sq]

/-! ##### The stability divisibility at row 3

The root set of `ker₃` is carried into itself by `x(P) ↦ x(2 ⬝ P)`, written
multiplied-out as a divisibility so that no rational function appears.  Every power
`Φ^i` and `ΨSq^j` is reduced modulo `ker₃` BEFORE being multiplied, so each `ring`
call below is an identity in degree `≤ 10` rather than the degree-`20` identity the
unreduced sum would need — which is what keeps this inside the default heartbeat
budget. -/

lemma phi₃_red : ker₃ ∣ curve₃.Φ (2 : ℤ) -
    ((39) + (56) * X + (4) * X ^ 2 + X ^ 4) := by
  rw [curve₃_Φ]
  exact ⟨
    0
    , by rw [ker₃]; ring⟩

lemma psi₃_red : ker₃ ∣ curve₃.ΨSq (2 : ℤ) -
    ((-28) + (-8) * X + (5) * X ^ 2 + (4) * X ^ 3) := by
  rw [curve₃_ΨSq]
  exact ⟨
    0
    , by rw [ker₃]; ring⟩

lemma phi₃_pow_0 : ker₃ ∣ curve₃.Φ (2 : ℤ) ^ 0 - 1 := by simp

lemma phi₃_pow_1 : ker₃ ∣ curve₃.Φ (2 : ℤ) ^ 1 -
    ((39) + (56) * X + (4) * X ^ 2 + X ^ 4) := by
  rw [pow_one]; exact phi₃_red

lemma phi₃_pow_2 : ker₃ ∣ curve₃.Φ (2 : ℤ) ^ 2 -
    ((3388) + (-137698) * X + (-52393) * X ^ 2 + (61831) * X ^ 3 + (20570) * X ^ 4) :=
  dvd_sub_pow_succ 1 phi₃_pow_1 phi₃_red ⟨
    (-1867) + (174) * X + (-14) * X ^ 2 + X ^ 3
    , by rw [ker₃]; ring⟩

lemma phi₃_pow_3 : ker₃ ∣ curve₃.Φ (2 : ℤ) ^ 3 -
    ((27429248) + (-2082340183) * X + (-823513658) * X ^ 2 + (896050496) * X ^ 3
      + (302047823) * X ^ 4) :=
  dvd_sub_pow_succ 2 phi₃_pow_2 phi₃_red ⟨
    (-27297116) + (2578873) * X + (-226149) * X ^ 2 + (20570) * X ^ 3
    , by rw [ker₃]; ring⟩

lemma phi₃_pow_4 : ker₃ ∣ curve₃.Φ (2 : ℤ) ^ 4 -
    ((403217590864) + (-30680891753149) * X + (-12138283096588) * X ^ 2
      + (13196610900121) * X ^ 3 + (4449013421523) * X ^ 4) :=
  dvd_sub_pow_succ 3 phi₃_pow_3 phi₃_red ⟨
    (-402147850192) + (37979909308) * X + (-3332619026) * X ^ 2 + (302047823) * X ^ 3
    , by rw [ker₃]; ring⟩

lemma phi₃_pow_5 : ker₃ ∣ curve₃.Φ (2 : ℤ) ^ 5 -
    ((5939354619407484) + (-451929230174892943) * X + (-178797548573031047) * X ^ 2
      + (194385151040627272) * X ^ 3 + (65533746978316188) * X ^ 4) :=
  dvd_sub_pow_succ 4 phi₃_pow_4 phi₃_red ⟨
    (-5923629133363788) + (559441445960628) * X + (-49089577001201) * X ^ 2
      + (4449013421523) * X ^ 3
    , by rw [ker₃]; ring⟩

lemma psi₃_pow_0 : ker₃ ∣ curve₃.ΨSq (2 : ℤ) ^ 0 - 1 := by simp

lemma psi₃_pow_1 : ker₃ ∣ curve₃.ΨSq (2 : ℤ) ^ 1 -
    ((-28) + (-8) * X + (5) * X ^ 2 + (4) * X ^ 3) := by
  rw [pow_one]; exact psi₃_red

lemma psi₃_pow_2 : ker₃ ∣ curve₃.ΨSq (2 : ℤ) ^ 2 -
    ((968) + (-13552) * X + (-5808) * X ^ 2 + (5808) * X ^ 3 + (2057) * X ^ 4) :=
  dvd_sub_pow_succ 1 psi₃_pow_1 psi₃_red ⟨
    (-184) + (16) * X
    , by rw [ker₃]; ring⟩

lemma psi₃_pow_3 : ker₃ ∣ curve₃.ΨSq (2 : ℤ) ^ 3 -
    ((-913066) + (67786499) * X + (26840946) * X ^ 2 + (-29155555) * X ^ 3 + (-9836090) * X ^ 4) :=
  dvd_sub_pow_succ 2 psi₃_pow_2 psi₃_red ⟨
    (885962) + (-81675) * X + (8228) * X ^ 2
    , by rw [ker₃]; ring⟩

lemma psi₃_pow_4 : ker₃ ∣ curve₃.ΨSq (2 : ℤ) ^ 4 -
    ((4195217499) + (-319169261290) * X + (-126274774417) * X ^ 2 + (137281966063) * X ^ 3
      + (46282836380) * X ^ 4) :=
  dvd_sub_pow_succ 3 psi₃_pow_3 psi₃_red ⟨
    (-4169651651) + (385018370) * X + (-39344360) * X ^ 2
    , by rw [ker₃]; ring⟩

lemma psi₃_pow_5 : ker₃ ∣ curve₃.ΨSq (2 : ℤ) ^ 5 -
    ((-19732728841771) + (1501474443503980) * X + (594031058206806) * X ^ 2
      + (-645818643857068) * X ^ 3 + (-217727141071495) * X ^ 4) :=
  dvd_sub_pow_succ 4 psi₃_pow_4 psi₃_red ⟨
    (19615262751799) + (-1811296791128) * X + (185131345520) * X ^ 2
    , by rw [ker₃]; ring⟩

lemma term₃_0 : ker₃ ∣
    (1) * curve₃.Φ (2 : ℤ) ^ 0 * curve₃.ΨSq (2 : ℤ) ^ 5
    -
    ((-19732728841771) + (1501474443503980) * X + (594031058206806) * X ^ 2
      + (-645818643857068) * X ^ 3 + (-217727141071495) * X ^ 4) :=
  dvd_sub_const_mul₂ phi₃_pow_0 psi₃_pow_5 ⟨
    0
    , by rw [ker₃]; ring⟩

lemma term₃_1 : ker₃ ∣
    (-76) * curve₃.Φ (2 : ℤ) ^ 1 * curve₃.ΨSq (2 : ℤ) ^ 4
    -
    ((-4695816346642388) + (357307483066197444) * X + (141362188968404448) * X ^ 2
      + (-153686156368169480) * X ^ 3 + (-51812753097762448) * X ^ 4) :=
  dvd_sub_const_mul₂ phi₃_pow_1 psi₃_pow_4 ⟨
    (4683381721975352) + (-442309351282876) * X + (38811508487532) * X ^ 2
      + (-3517495564880) * X ^ 3
    , by rw [ker₃]; ring⟩

lemma term₃_2 : ker₃ ∣
    (-37) * curve₃.Φ (2 : ℤ) ^ 2 * curve₃.ΨSq (2 : ℤ) ^ 3
    -
    ((7158295463911053) + (-544679116319346327) * X + (-215492357114546237) * X ^ 2
      + (234279000076055022) * X ^ 3 + (78983301189396791) * X ^ 4) :=
  dvd_sub_const_mul₂ phi₃_pow_2 psi₃_pow_3 ⟨
    (-7158181005609557) + (644210536254835) * X + (-60113609589220) * X ^ 2
      + (7486149738100) * X ^ 3
    , by rw [ker₃]; ring⟩

lemma term₃_3 : ker₃ ∣
    (30) * curve₃.Φ (2 : ℤ) ^ 3 * curve₃.ΨSq (2 : ℤ) ^ 2
    -
    ((18173542361863680) + (-1382836183215112560) * X + (-547093910095331940) * X ^ 2
      + (594789609784128990) * X ^ 3 + (200523507559005180) * X ^ 4) :=
  dvd_sub_const_mul₂ phi₃_pow_3 psi₃_pow_2 ⟨
    (-18172745816501760) + (1635878366997600) * X + (-153027107414940) * X ^ 2
      + (18639371157330) * X ^ 3
    , by rw [ker₃]; ring⟩

lemma term₃_4 : ker₃ ∣
    (14) * curve₃.Φ (2 : ℤ) ^ 4 * curve₃.ΨSq (2 : ℤ) ^ 1
    -
    ((-26555643369698058) + (2020635572199650406) * X + (799427595756297970) * X ^ 2
      + (-869121785888784736) * X ^ 3 + (-293010075487884216) * X ^ 4) :=
  dvd_sub_const_mul₂ phi₃_pow_4 psi₃_pow_1 ⟨
    (26397582074079370) + (-2437585372560646) * X + (249144751605288) * X ^ 2
    , by rw [ker₃]; ring⟩

lemma term₃_5 : ker₃ ∣
    (1) * curve₃.Φ (2 : ℤ) ^ 5 * curve₃.ΨSq (2 : ℤ) ^ 0
    -
    ((5939354619407484) + (-451929230174892943) * X + (-178797548573031047) * X ^ 2
      + (194385151040627272) * X ^ 3 + (65533746978316188) * X ^ 4) :=
  dvd_sub_const_mul₂ phi₃_pow_5 psi₃_pow_0 ⟨
    0
    , by rw [ker₃]; ring⟩

lemma sum₃_1 : ker₃ ∣
    (1) * curve₃.Φ (2 : ℤ) ^ 0 * curve₃.ΨSq (2 : ℤ) ^ 5
      + (-76) * curve₃.Φ (2 : ℤ) ^ 1 * curve₃.ΨSq (2 : ℤ) ^ 4
    -
    ((-4715549075484159) + (358808957509701424) * X + (141956220026611254) * X ^ 2
      + (-154331975012026548) * X ^ 3 + (-52030480238833943) * X ^ 4) :=
  dvd_sub_add term₃_0 term₃_1 ⟨0, by ring⟩

lemma sum₃_2 : ker₃ ∣
    (1) * curve₃.Φ (2 : ℤ) ^ 0 * curve₃.ΨSq (2 : ℤ) ^ 5
      + (-76) * curve₃.Φ (2 : ℤ) ^ 1 * curve₃.ΨSq (2 : ℤ) ^ 4
      + (-37) * curve₃.Φ (2 : ℤ) ^ 2 * curve₃.ΨSq (2 : ℤ) ^ 3
    -
    ((2442746388426894) + (-185870158809644903) * X + (-73536137087934983) * X ^ 2
      + (79947025064028474) * X ^ 3 + (26952820950562848) * X ^ 4) :=
  dvd_sub_add sum₃_1 term₃_2 ⟨0, by ring⟩

lemma sum₃_3 : ker₃ ∣
    (1) * curve₃.Φ (2 : ℤ) ^ 0 * curve₃.ΨSq (2 : ℤ) ^ 5
      + (-76) * curve₃.Φ (2 : ℤ) ^ 1 * curve₃.ΨSq (2 : ℤ) ^ 4
      + (-37) * curve₃.Φ (2 : ℤ) ^ 2 * curve₃.ΨSq (2 : ℤ) ^ 3
      + (30) * curve₃.Φ (2 : ℤ) ^ 3 * curve₃.ΨSq (2 : ℤ) ^ 2
    -
    ((20616288750290574) + (-1568706342024757463) * X + (-620630047183266923) * X ^ 2
      + (674736634848157464) * X ^ 3 + (227476328509568028) * X ^ 4) :=
  dvd_sub_add sum₃_2 term₃_3 ⟨0, by ring⟩

lemma sum₃_4 : ker₃ ∣
    (1) * curve₃.Φ (2 : ℤ) ^ 0 * curve₃.ΨSq (2 : ℤ) ^ 5
      + (-76) * curve₃.Φ (2 : ℤ) ^ 1 * curve₃.ΨSq (2 : ℤ) ^ 4
      + (-37) * curve₃.Φ (2 : ℤ) ^ 2 * curve₃.ΨSq (2 : ℤ) ^ 3
      + (30) * curve₃.Φ (2 : ℤ) ^ 3 * curve₃.ΨSq (2 : ℤ) ^ 2
      + (14) * curve₃.Φ (2 : ℤ) ^ 4 * curve₃.ΨSq (2 : ℤ) ^ 1
    -
    ((-5939354619407484) + (451929230174892943) * X + (178797548573031047) * X ^ 2
      + (-194385151040627272) * X ^ 3 + (-65533746978316188) * X ^ 4) :=
  dvd_sub_add sum₃_3 term₃_4 ⟨0, by ring⟩

lemma sum₃_5 : ker₃ ∣
    (1) * curve₃.Φ (2 : ℤ) ^ 0 * curve₃.ΨSq (2 : ℤ) ^ 5
      + (-76) * curve₃.Φ (2 : ℤ) ^ 1 * curve₃.ΨSq (2 : ℤ) ^ 4
      + (-37) * curve₃.Φ (2 : ℤ) ^ 2 * curve₃.ΨSq (2 : ℤ) ^ 3
      + (30) * curve₃.Φ (2 : ℤ) ^ 3 * curve₃.ΨSq (2 : ℤ) ^ 2
      + (14) * curve₃.Φ (2 : ℤ) ^ 4 * curve₃.ΨSq (2 : ℤ) ^ 1
      + (1) * curve₃.Φ (2 : ℤ) ^ 5 * curve₃.ΨSq (2 : ℤ) ^ 0
    -
    (0) :=
  dvd_sub_add sum₃_4 term₃_5 ⟨0, by ring⟩

/-- **The stability divisibility at row 3**, assembled from the reduced terms. -/
lemma ker₃_dvd_multComp : ker₃ ∣
    ∑ i ∈ Finset.range (ker₃.natDegree + 1), C (ker₃.coeff i) *
      curve₃.Φ (2 : ℤ) ^ i * curve₃.ΨSq (2 : ℤ) ^
        (ker₃.natDegree - i) := by
  rw [ker₃_natDegree]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num only
  rw [ker₃_coeff_0, ker₃_coeff_1, ker₃_coeff_2, ker₃_coeff_3, ker₃_coeff_4, ker₃_coeff_5]
  simpa using sum₃_5

/-- **The kernel-polynomial certificate at row 3.** -/
theorem curve₃_isKernelPolynomial : curve₃.IsKernelPolynomial 11 ker₃ 2 where
  monic := ker₃_monic
  natDegree_eq := ker₃_natDegree
  dvd_ΨSq := by
    rw [WeierstrassCurve.ΨSq_ofNat, if_neg (by decide), mul_one]
    exact dvd_pow ker₃_dvd_preΨ' (by norm_num)
  mult_ne_zero := by decide
  generates := by
    intro k hk
    obtain ⟨i, -, hi⟩ := generates_aux_11_2 k hk
    exact ⟨i, hi⟩
  dvd_multComp := ker₃_dvd_multComp


/-! #### Row 4: `p = 17`, `j₀ = -297756989/2`, model `[1, 0, 1, -3041, 64278]`, multiplier `m = 3` -/

/-- The minimal twist of conductor-level model at row 4 of `genusOneJTable`: `[a₁, a₂, a₃, a₄, a₆] = [1, 0, 1, -3041, 64278]`. -/
noncomputable def curve₄ : WeierstrassCurve ℚ := ⟨1, 0, 1, -3041, 64278⟩

lemma curve₄_Δ : curve₄.Δ = -20880250 := by
  norm_num [curve₄, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

lemma curve₄_c₄ : curve₄.c₄ = 145945 := by
  norm_num [curve₄, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]

noncomputable instance : curve₄.IsElliptic :=
  ⟨by rw [curve₄_Δ]; exact isUnit_iff_ne_zero.mpr (by norm_num)⟩

lemma curve₄_j : curve₄.j = ((-297756989 : ℚ) / 2) :=
  j_eq_of_Δ_c₄ curve₄ curve₄_Δ curve₄_c₄ (by norm_num) (by norm_num)

/-- The kernel polynomial at row 4, monic of degree `(p-1)/2 = 8`. -/
noncomputable def ker₄ : ℚ[X] :=
  (-2252576338909) + (437271444481) * X + (-33006143963) * X ^ 2 + (1127218758) * X ^ 3
    + (-9242705) * X ^ 4 + (-543828) * X ^ 5 + (18372) * X ^ 6 + (-226) * X ^ 7 + X ^ 8

lemma curve₄_Ψ₂Sq : curve₄.Ψ₂Sq =
    (257113) + (-12162) * X + X ^ 2 + (4) * X ^ 3
    := by
  simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, curve₄]
  norm_num [Polynomial.C_eq_natCast, map_ofNat]
  ring

lemma curve₄_Ψ₃ : curve₄.Ψ₃ =
    (-9180362) + (771339) * X + (-18243) * X ^ 2 + X ^ 3 + (3) * X ^ 4
    := by
  simp only [WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, curve₄]
  norm_num [Polynomial.C_eq_natCast, map_ofNat]
  ring

lemma curve₄_preΨ₄ : curve₄.preΨ₄ =
    (-10281313447) + (1554323791) * X + (-91803620) * X ^ 2 + (2571130) * X ^ 3
      + (-30405) * X ^ 4 + X ^ 5 + (2) * X ^ 6
    := by
  simp only [WeierstrassCurve.preΨ₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, curve₄]
  norm_num [Polynomial.C_eq_natCast, map_ofNat]
  ring

/-! ##### The chain of remainders modulo `ker₄`

`preΨ'ₙ ≡ rₙ (mod ker₄)` for `n = 1, …, 17`, each `rₙ` of degree `< 8`; the chain ends
at `r_17 = 0`, which is exactly `ker₄ ∣ preΨ'_17`.  Every step is one application of a
`step_preΨ'_*` lemma against an explicit cofactor. -/

lemma pre₄_1 : ker₄ ∣ curve₄.preΨ' 1 - 1 := by simp

lemma pre₄_2 : ker₄ ∣ curve₄.preΨ' 2 - 1 := by simp

lemma pre₄_3 : ker₄ ∣ curve₄.preΨ' 3 -
    ((-9180362) + (771339) * X + (-18243) * X ^ 2 + X ^ 3 + (3) * X ^ 4) := by
  rw [WeierstrassCurve.preΨ'_three, curve₄_Ψ₃]
  exact ⟨
    0
    , by rw [ker₄]; ring⟩

lemma pre₄_4 : ker₄ ∣ curve₄.preΨ' 4 -
    ((-10281313447) + (1554323791) * X + (-91803620) * X ^ 2 + (2571130) * X ^ 3
      + (-30405) * X ^ 4 + X ^ 5 + (2) * X ^ 6) := by
  rw [WeierstrassCurve.preΨ'_four, curve₄_preΨ₄]
  exact ⟨
    0
    , by rw [ker₄]; ring⟩

lemma pre₄_5 : ker₄ ∣ curve₄.preΨ' 5 -
    ((858050507180671167375) + (-174390123409761897750) * X + (14456643119422335625) * X ^ 2
      + (-621963444526560625) * X ^ 3 + (14371078292848125) * X ^ 4 + (-157129591998375) * X ^ 5
      + (295987983875) * X ^ 6 + (5376664375) * X ^ 7) :=
  step_preΨ'_odd_even curve₄ 0 5 (by decide) (by norm_num)
    pre₄_1 pre₄_2 pre₄_3 pre₄_4
    (by rw [curve₄_Ψ₂Sq]; exact ⟨
      (339169910) + (839485) * X + (-23860) * X ^ 2 + (1135) * X ^ 3 + (5) * X ^ 4
      , by rw [ker₄]; ring⟩)

lemma pre₄_6 : ker₄ ∣ curve₄.preΨ' 6 -
    ((21263507738839888229733053125) + (-4569396925979780022090768750) * X
      + (409605022532660402801437500) * X ^ 2 + (-19796364233126338583312500) * X ^ 3
      + (553772972473825859578125) * X ^ 4 + (-8865446470600644253125) * X ^ 5
      + (73557611261003759375) * X ^ 6 + (-231986552808515625) * X ^ 7) :=
  step_preΨ'_even curve₄ 0 6 (by norm_num)
    pre₄_1 pre₄_2 pre₄_3 pre₄_4 pre₄_5
    (⟨
      (12505817284955813) + (-438974845059447) * X + (9624280033236) * X ^ 2
        + (-16570014821) * X ^ 3 + (-1844179340) * X ^ 4 + (19468971) * X ^ 5 + (41761) * X ^ 6
        + (-2728) * X ^ 7 + (-12) * X ^ 8
      , by rw [ker₄]; ring⟩)

lemma pre₄_7 : ker₄ ∣ curve₄.preΨ' 7 -
    ((-23826945101463804464463431792841636316406250)
      + (5286093564932683460395333492789508175781250) * X
      + (-493400105979641391435148514008382113281250) * X ^ 2
      + (25123990221886655543198608002068222656250) * X ^ 3
      + (-753270153082237496487532891376962890625) * X ^ 4
      + (13275869780524728520487280993226562500) * X ^ 5
      + (-126967183772417687167377004917968750) * X ^ 6
      + (505750581311806560431184494140625) * X ^ 7) :=
  step_preΨ'_odd_odd curve₄ 1 7 (by decide) (by norm_num)
    pre₄_2 pre₄_3 pre₄_4 pre₄_5
    (by rw [curve₄_Ψ₂Sq]; exact ⟨
      (-10314813819910553633801380637293) + (227665374450800540858806275514) * X
        + (-123287465567913205353790690) * X ^ 2 + (-217449164379072564767166190) * X ^ 3
        + (8028172505350774330586065) * X ^ 4 + (-45882772369398267966568) * X ^ 5
        + (-4987059421609287451851) * X ^ 6 + (153588774508268049040) * X ^ 7
        + (-1130143419344733785) * X ^ 8 + (-26836776240311765) * X ^ 9
        + (604950708875319) * X ^ 10 + (-2086926748572) * X ^ 11 + (-55606524410) * X ^ 12
        + (502627940) * X ^ 13 + (2371960) * X ^ 14 + (-29184) * X ^ 15 + (-128) * X ^ 16
      , by rw [ker₄]; ring⟩)

lemma pre₄_8 : ker₄ ∣ curve₄.preΨ' 8 -
    ((-4958163396721291925725774145608894911379023858154296875)
      + (1089200596920201883553249130371218597067899978027343750) * X
      + (-100433505301341929727588358483659918766838856933593750) * X ^ 2
      + (5036771003243923550514635254782736250460461425781250) * X ^ 3
      + (-148114781970278847541059260719212634095166015625000) * X ^ 4
      + (2545230034503088293253711877022695935920166015625) * X ^ 5
      + (-23523486171126997421991497118426873289794921875) * X ^ 6
      + (89254170022090777188639399319753516601562500) * X ^ 7) :=
  step_preΨ'_even curve₄ 1 8 (by norm_num)
    pre₄_2 pre₄_3 pre₄_4 pre₄_5 pre₄_6
    (⟨
      (-2196288809739576472683543575525947609018750)
        + (54695828436020192597218506767111857284375) * X
        + (-1185901133676825629451907892589923950000) * X ^ 2
        + (15983356865905410099575157762599187500) * X ^ 3
        + (236150664453965568006133639894390625) * X ^ 4
        + (-22630869577051786388128116137450000) * X ^ 5
        + (717150647346027115616730421043750) * X ^ 6
        + (-12634827529239370225844737503125) * X ^ 7 + (104896604751512819184671109375) * X ^ 8
        + (347869520412264109453859375) * X ^ 9 + (-15682085738903938162731250) * X ^ 10
        + (98338440663055153496875) * X ^ 11 + (317626948661258996875) * X ^ 12
        + (-4175757950553281250) * X ^ 13
      , by rw [ker₄]; ring⟩)

lemma pre₄_9 : ker₄ ∣ curve₄.preΨ' 9 -
    ((34701963257396130075917285711679059021993530670115363126963131713867187500)
      + (-7605964654242784621559396121076204578157029279526955927158632659912109375) * X
      + (699338955795334828825520902711806113036395216254432342050491333007812500) * X ^ 2
      + (-34945278180574757878240655379510682293900101391158071279632568359375000) * X ^ 3
      + (1022799490667950295325275978946550673608841251279563657466888427734375) * X ^ 4
      + (-17465294423785837524791444567788463141648761399585654642486572265625) * X ^ 5
      + (159992448313029022745154395562692364533286935524673453521728515625) * X ^ 6
      + (-599039994023574429300270118755892611348637196777500152587890625) * X ^ 7) :=
  step_preΨ'_odd_even curve₄ 2 9 (by decide) (by norm_num)
    pre₄_3 pre₄_4 pre₄_5 pre₄_6
    (by rw [curve₄_Ψ₂Sq]; exact ⟨
      (15403558459282351747771408103326168505626799576183974092378125)
        + (-385145945273731668247646234326191997472321315962637831425000) * X
        + (9596624449094027382658137966683613385885348834341109153125) * X ^ 2
        + (-221459858983878671352753109592852695247806220096357593750) * X ^ 3
        + (4033250979438355171093842524128868084904242814530671875) * X ^ 4
        + (-25895651338579868038590686204729982135818246875725000) * X ^ 5
        + (-1295730882183978766480824944886236120300010297478125) * X ^ 6
        + (20982970585709485946930132219834169939078487334375) * X ^ 7
        + (2578182092566890209904316912520874437014137171875) * X ^ 8
        + (-183811393408784962947020870263156404581399015625) * X ^ 9
        + (6329805192955722162566729030485829745640371875) * X ^ 10
        + (-129037558205138639408804631671041055743481250) * X ^ 11
        + (1277846822109147239550090541374525010659375) * X ^ 12
        + (8223613356817748749446303523138502078125) * X ^ 13
        + (-476377826024963272371562108915311781250) * X ^ 14
        + (6728802502958347227340751631084100000) * X ^ 15
        + (-27973627146470035443105670785178125) * X ^ 16
        + (-418430131709060049713355195678125) * X ^ 17
        + (6189652796258027944417769640625) * X ^ 18 + (-15216216313735733374434468750) * X ^ 19
        + (-245719037782164545892762500) * X ^ 20 + (1562191002603937971075000) * X ^ 21
        + (2645078684244761200000) * X ^ 22 + (-29694278759490000000) * X ^ 23
      , by rw [ker₄]; ring⟩)

lemma pre₄_10 : ker₄ ∣ curve₄.preΨ' 10 -
    ((34636585646257324649115724203292643317446062648294651619876909224780778394699096679687500)
      + (-7596107144987730357370580762970455765612031666143483788448946120534267235279083251953125) * X
      + (698949497110188886805147290024084715350491008260083792509929071095893056392669677734375) * X ^ 2
      + (-34958755660347318236162281841283341618293317293377839427754943132377221584320068359375) * X ^ 3
      + (1024452188740914353535203800950013200167151346977514253661726847945287227630615234375) * X ^ 4
      + (-17522507907837303084269741777877235863806495865278409929594467645097255706787109375) * X ^ 5
      + (160892239638458053375482476616643425974154111029916291895631704856395721435546875) * X ^ 6
      + (-604540154888237926551748834794621722209113737428053072277656118869781494140625) * X ^ 7) :=
  step_preΨ'_even curve₄ 2 10 (by norm_num)
    pre₄_3 pre₄_4 pre₄_5 pre₄_6 pre₄_7
    (⟨
      (15375809728411688286560977672734367250917559497078274147183316715448242187500)
        + (-386989283057564538879894526213035605533213826577349987874376392903808593750) * X
        + (9726197829289781858150888019369148076148899641910851670754806327636718750) * X ^ 2
        + (-236781159379392067929902979647238734305463077484251453274750010986328125) * X ^ 3
        + (5197426211873729600676593681907005276903243107651863125549711914062500) * X ^ 4
        + (-81790810439119718449392628034901285936775926223150227437616943359375) * X ^ 5
        + (-143424717716672901497344557066203202013178090610292343282226562500) * X ^ 6
        + (71535926616537753556086221786205957620716191346039483706787109375) * X ^ 7
        + (-3054071758325068631041167525386733253532610272917363516845703125) * X ^ 8
        + (80090603522775179619574153428081377786921669865287452392578125) * X ^ 9
        + (-1444991681517369745343814376434976888858799123792157714843750) * X ^ 10
        + (17799581180702141170200498807211646834149188612218505859375) * X ^ 11
        + (-140229785503255863654752853758995370722847373843750000000) * X ^ 12
        + (658980333491706563915718548080077260566194929199218750) * X ^ 13
        + (-3558567159720344975242144078211152380187724609375000) * X ^ 14
        + (48756824047303640337939388180979866217893798828125) * X ^ 15
        + (-332908138158641394659639902277957087260009765625) * X ^ 16
        + (-530855436421389605373702680470703237548828125) * X ^ 17
        + (10877004532698924401446537234793178710937500) * X ^ 18
      , by rw [ker₄]; ring⟩)

lemma pre₄_17 : ker₄ ∣ curve₄.preΨ' 17 -
    (0) :=
  step_preΨ'_odd_even curve₄ 6 17 (by decide) (by norm_num)
    pre₄_7 pre₄_8 pre₄_9 pre₄_10
    (by rw [curve₄_Ψ₂Sq]; exact ⟨
      (-318130700226166479061337112560989113695943750581768856973395826123842548547697930882205494900310255268093323078199980946856982766486388083473789468778113298966755122058125647859886378599897449469452870713977551381246300366001378279179334640502929687500)
        + (206414710108240786926376769590558653456379861982446539134980921695377681127023678509107658911743517593476595970767438276947389283127924886523335684770718161331853391599951828025127845089373793239345375810793094518980073104330585920251905918121337890625) * X
        + (-62886139051305563845757223179917030310145380845058069643480854422642717928070398160026026457192178068745633833402396055050030696681274716657140532033635203622946303653585561397213925944681202359287390010717230748316097788119805045425891876220703125000) * X ^ 2
        + (11922810423352939157600882833491391027205622867952100827754739686386867023800921142548929167091651574573122865534131866782630293620650762946270254422738439398615972918369030226084143129215004897837929434397242517418291640751704107969999313354492187500) * X ^ 3
        + (-1569517799184600179601814155681220013366145735093659088939912449084640345126924317272621233938602683435710124683889724326675552649345038943473439579533630417897873967896848761781693272291153403573830725412725999035057355968092451803386211395263671875) * X ^ 4
        + (151151448522055485472560548222718761180415723181873972587953806705970463118906059559895184211156950746381075353237099216068645337482643731528392089831846619604521081097232261090751594715861925434135303775944850213086567691789241507649421691894531250) * X ^ 5
        + (-10871418606650678940825097864456500019117484437818031590771376674415651651257758539144661983628570757769755379197713422698831293224203925124580453062964822845364686253896703364594800627116958482878398503871611446847111892566317692399024963378906250) * X ^ 6
        + (577878496651115580884993089500980098477534372119714964266540589400601256951330413320657673837005618516235679489177220974889200372364042809477359757696850053281092430603195849731411715166841813908731488535618081581191063378355465829372406005859375) * X ^ 7
        + (-21044769745343381350577489708636639435444018870667063655648811157344496113632134135610351120219142809505496633116620611341971136044376529003472616711807465011530260470558091417552565789272561423353070221030358677438698578043840825557708740234375) * X ^ 8
        + (339935387322257174362215480394202388352496916049390076361737814524478207619132895704852675232766484091197573106309949273573311065897725237558501030436294904503484226573282602155969850127728414963133718465493338101168774301186203956604003906250) * X ^ 9
        + (16509836315739176665562179383153679012999783487567303564497512010071025186874459178398271689737329337673532657480913495188304036069634143903523911422001876530285433569092566497799354163789103411851150925160336413455297588370740413665771484375) * X ^ 10
        + (-1686962294757535107545618134943869890455360321914034888791390215064744632349256352738350017164835665038175413956564840465698563321632046975998609053573507541587787805807342283912090781260265519349327893727785721011969144456088542938232421875) * X ^ 11
        + (83037312251055785345296119579125440261094544263546264255636561993368225600112383545073646049376383088387128256083866456649697615191022389365012446728214293000332038664251867344387521782169124469702728430497984390967758372426033020019531250) * X ^ 12
        + (-2878109262207615359627617248109740919246036737573914230914876160237656047109016237644233662964047782816361766993772587705356432768469611823354230212102683670876045880921212761527894898204287242206918240317037316344794817268848419189453125) * X ^ 13
        + (75693235714618733369623239064649732728068926439072147190396853945643935039812925046195269853559704530761557138587040918425431687943412408925965207045767128824783448349433702138608315099348311311706904991325473019969649612903594970703125) * X ^ 14
        + (-1526484038985061239144845138714665111353254445954034772760526290753981735628006030529340933694062966962481096901255107833292302970398536324224535438647420979463031334795507150965810440069219965773805736120039000525139272212982177734375) * X ^ 15
        + (22794882012867460641958896355174557086258660387390672578994517065569413174468861653197932862197987439531554703041733026499666921308008233614555819793963926447224087044503176676017972855402335979890793282720551360398530960083007812500) * X ^ 16
        + (-218034416965693984214481135026373385742168036461541551250257563155964949642980921158921630709767063032986501659395794744250683601803313746884838327028418644840467268669383787682695002126564760847049484482340631075203418731689453125) * X ^ 17
        + (264381343285674383666228942935917102617385775967017408396548083394728660966274493301719719589897281496190151578751137740618997262056770996497788097224125481014830904349303950245910378921615491165653111238498240709304809570312500) * X ^ 18
        + (35327537047734695699350009655741989327007846899816616691663477495895181017170189305661483505703406417633625688975959893716197112981194838925053279814195578767686774511717105938963971608193781470674821321154013276100158691406250) * X ^ 19
        + (-763679744350435432645514885982273321274399374744463723774154515440333026326469002653289739413930175357912958586306444466371929614902286594224964192410337854986429657579947713435808009076188884733937811688520014286041259765625) * X ^ 20
        + (9657696255626396939418060921737532285840512892696200476900036354509570581213532029244554632486510256784820696670398967574993751397456007306889899498037042158832296948657624281093438310674681446243994287215173244476318359375) * X ^ 21
        + (-84594546305104509920934884071200411626870108019827090139857720128668367371131343165231272051046505579044119473898250109719803849359531688101448717151865954554859202906583932969924816136497724983200896531343460083007812500) * X ^ 22
        + (523510965149863219184375311662136679852133184224655369336916077944642905846568899547627636573488489010740417636163189671492670537163432014113774200924361093069190010082354174231644705628241354133933782577514648437500000) * X ^ 23
        + (-2205736628069408834879516072011349917416945259479541916294334295022348846092458361375317589229122416114255947530420622034202086331436471286999978150503874787478868663607109785296245263452874496579170227050781250000000) * X ^ 24
        + (5710446764577436510809664072017986202107696458245113178441482021478067936294876727537533551234585801362151638053405694243928849255118814959003420744728321696105347267532662769440321426372975111007690429687500000000) * X ^ 25
        + (-6877501330481191057096248907087567993544849299826386761572018102678231975531634478963793195265303876298963863646246015562708532655208685314251731793284179665391937910250419463409343734383583068847656250000000000) * X ^ 26
      , by rw [ker₄]; ring⟩)

lemma ker₄_dvd_preΨ' : ker₄ ∣ curve₄.preΨ' 17 := by
  simpa using pre₄_17

lemma ker₄_coeff_0 : C (ker₄.coeff 0) = (-2252576338909 : ℚ[X]) := by
  rw [ker₄]; simp [Polynomial.coeff_X, map_ofNat]

lemma ker₄_coeff_1 : C (ker₄.coeff 1) = (437271444481 : ℚ[X]) := by
  rw [ker₄]; simp [Polynomial.coeff_X, map_ofNat]

lemma ker₄_coeff_2 : C (ker₄.coeff 2) = (-33006143963 : ℚ[X]) := by
  rw [ker₄]; simp [Polynomial.coeff_X, map_ofNat]

lemma ker₄_coeff_3 : C (ker₄.coeff 3) = (1127218758 : ℚ[X]) := by
  rw [ker₄]; simp [Polynomial.coeff_X, map_ofNat]

lemma ker₄_coeff_4 : C (ker₄.coeff 4) = (-9242705 : ℚ[X]) := by
  rw [ker₄]; simp [Polynomial.coeff_X, map_ofNat]

lemma ker₄_coeff_5 : C (ker₄.coeff 5) = (-543828 : ℚ[X]) := by
  rw [ker₄]; simp [Polynomial.coeff_X, map_ofNat]

lemma ker₄_coeff_6 : C (ker₄.coeff 6) = (18372 : ℚ[X]) := by
  rw [ker₄]; simp [Polynomial.coeff_X, map_ofNat]

lemma ker₄_coeff_7 : C (ker₄.coeff 7) = (-226 : ℚ[X]) := by
  rw [ker₄]; simp [Polynomial.coeff_X, map_ofNat]

lemma ker₄_coeff_8 : C (ker₄.coeff 8) = (1 : ℚ[X]) := by
  rw [ker₄]; simp [Polynomial.coeff_X]

lemma ker₄_natDegree : ker₄.natDegree = 8 := by
  rw [ker₄]; compute_degree!

lemma ker₄_monic : ker₄.Monic := by
  rw [ker₄]; monicity!

lemma curve₄_Φ : curve₄.Φ (3 : ℤ) =
    (2643459344298511) + (-440399140566753) * X + (28355528919213) * X ^ 2
      + (-808097103280) * X ^ 3 + (4800676803) * X ^ 4 + (273868182) * X ^ 5 + (-6164631) * X ^ 6
      + (36486) * X ^ 7 + X ^ 9
    := by
  rw [WeierstrassCurve.Φ_three, curve₄_Ψ₃, curve₄_preΨ₄, curve₄_Ψ₂Sq]
  ring

lemma curve₄_ΨSq : curve₄.ΨSq (3 : ℤ) =
    (84279046451044) + (-14162342489436) * X + (929918540853) * X ^ 2 + (-28161435478) * X ^ 3
      + (279267555) * X ^ 4 + (4591548) * X ^ 5 + (-109457) * X ^ 6 + (6) * X ^ 7 + (9) * X ^ 8
    := by
  rw [WeierstrassCurve.ΨSq_three, curve₄_Ψ₃]
  ring

/-! ##### The stability divisibility at row 4

The root set of `ker₄` is carried into itself by `x(P) ↦ x(3 ⬝ P)`, written
multiplied-out as a divisibility so that no rational function appears.  Every power
`Φ^i` and `ΨSq^j` is reduced modulo `ker₄` BEFORE being multiplied, so each `ring`
call below is an identity in degree `≤ 16` rather than the degree-`72` identity the
unreduced sum would need — which is what keeps this inside the default heartbeat
budget. -/

lemma phi₄_red : ker₄ ∣ curve₄.Φ (3 : ℤ) -
    ((3152541596891945) + (-536969910680550) * X + (35377646010370) * X ^ 2
      + (-1029842398625) * X ^ 3 + (5762309375) * X ^ 4 + (406016015) * X ^ 5
      + (-9772875) * X ^ 6 + (69190) * X ^ 7) := by
  rw [curve₄_Φ]
  exact ⟨
    (226) + X
    , by rw [ker₄]; ring⟩

lemma psi₄_red : ker₄ ∣ curve₄.ΨSq (3 : ℤ) -
    ((104552233501225) + (-18097785489765) * X + (1226973836520) * X ^ 2 + (-38306404300) * X ^ 3
      + (362451900) * X ^ 4 + (9486000) * X ^ 5 + (-274805) * X ^ 6 + (2040) * X ^ 7) := by
  rw [curve₄_ΨSq]
  exact ⟨
    (9)
    , by rw [ker₄]; ring⟩

lemma phi₄_pow_0 : ker₄ ∣ curve₄.Φ (3 : ℤ) ^ 0 - 1 := by simp

lemma phi₄_pow_1 : ker₄ ∣ curve₄.Φ (3 : ℤ) ^ 1 -
    ((3152541596891945) + (-536969910680550) * X + (35377646010370) * X ^ 2
      + (-1029842398625) * X ^ 3 + (5762309375) * X ^ 4 + (406016015) * X ^ 5
      + (-9772875) * X ^ 6 + (69190) * X ^ 7) := by
  rw [pow_one]; exact phi₄_red

lemma phi₄_pow_2 : ker₄ ∣ curve₄.Φ (3 : ℤ) ^ 2 -
    ((368765049644670088951470058165625) + (-67956723234676620155246984693750) * X
      + (4760914324501804159325464340625) * X ^ 2 + (-143116965647488319877669984375) * X ^ 3
      + (568298080988784593579000000) * X ^ 4 + (73718808336378102059753125) * X ^ 5
      + (-1756302827005304042871875) * X ^ 6 + (12708184336323767900000) * X ^ 7) :=
  dvd_sub_pow_succ 1 phi₄_pow_1 phi₄_red ⟨
    (159296057996564091400) + (2257208342813499350) * X + (-9419095734947725) * X ^ 2
      + (1025847019271700) * X ^ 3 + (2620285410725) * X ^ 4 + (-270450563900) * X ^ 5
      + (4787256100) * X ^ 6
    , by rw [ker₄]; ring⟩

lemma phi₄_pow_3 : ker₄ ∣ curve₄.Φ (3 : ℤ) ^ 3 -
    ((70928351289199531469541886572743698254949998046875)
      + (-12980198929614628095024490906993599635929287109375) * X
      + (896897564885623739725539175316079299340105468750) * X ^ 2
      + (-25918111578647262200312059584544895068505859375) * X ^ 3
      + (36653966132157429104885431430835436816406250) * X ^ 4
      + (16008819682928097791112330334853870162109375) * X ^ 5
      + (-362204602783003185160351264608527041015625) * X ^ 6
      + (2578963142670050742223378800857632812500) * X ^ 7) :=
  dvd_sub_pow_succ 2 phi₄_pow_2 phi₄_red ⟨
    (30971560397595563063579368514943781250) + (432851992177258874530344873124296875) * X
      + (-277964355544622884651272109937500) * X ^ 2
      + (167301735657977380751437975656250) * X ^ 3 + (649023837034424303879454546875) * X ^ 4
      + (-46996973620312550715791531250) * X ^ 5 + (879279274230241501001000000) * X ^ 6
    , by rw [ker₄]; ring⟩

lemma phi₄_pow_4 : ker₄ ∣ curve₄.Φ (3 : ℤ) ^ 4 -
    ((13958799352769647950122945289654592102935352790703199788376464843750)
      + (-2547907670354133186157265839798119279954010456233938306456298828125) * X
      + (175138125914518653600347635364153889696276995954448592053222656250) * X ^ 2
      + (-4983420466609501471067080719653161972240204757490095855712890625) * X ^ 3
      + (1919477849331340661468032320437624019181904588305456542968750) * X ^ 4
      + (3283837408382609972672849954318857664506805479237061767578125) * X ^ 5
      + (-73058905194006722847677099617200075568470068348526611328125) * X ^ 6
      + (517347122984354903814870408449250100262608195227050781250) * X ^ 7) :=
  dvd_sub_pow_succ 3 phi₄_pow_3 phi₄_red ⟨
    (6097549076442802402750068763695452913046384727255859375)
      + (87625633903897186883834076677891004250299854677734375) * X
      + (-48402558758564392524236519955268818994767128906250) * X ^ 2
      + (31994796864595329733261295739873083971221074218750) * X ^ 3
      + (170332748932788548254692080867834906996376953125) * X ^ 4
      + (-9937728965334539275548566190412771409238281250) * X ^ 5
      + (178438459841340810854435579231339614296875000) * X ^ 6
    , by rw [ker₄]; ring⟩

lemma phi₄_pow_5 : ker₄ ∣ curve₄.Φ (3 : ℤ) ^ 5 -
    ((2770108816732501356658373695544063309803938199412061273670327115505614192962646484375)
      + (-505158617674227076728782460282645389589945734588308402779420621394400803375244140625) * X
      + (34658238521466626189674630187047487390582647661410174536394965521075643920898437500) * X ^ 2
      + (-980602002813386422985903357825281499642360705551749554145852540553543090820312500) * X ^ 3
      + (3949684482514596522103177267397133427851157042844701842346246051788330078125) * X ^ 4
      + (661164269913462367541303971365187689092514681382743013071684196746826171875000) * X ^ 5
      + (-14624960815335611253757940383750173948028536331389049922201741136169433593750) * X ^ 6
      + (103365052750776267221493043692391266050422991854588300988210614013671875000) * X ^ 7) :=
  dvd_sub_pow_succ 4 phi₄_pow_4 phi₄_red ⟨
    (1210215642436594157025973680820451046318702127724952532507817852783203125)
      + (17562985059223769039720142760370894605473521271501577312943218994140625) * X
      + (-9158755696936253032653234958367238503671352359924980231774902343750) * X ^ 2
      + (6283106985024993183773728296991436412656270561045832206286621093750) * X ^ 3
      + (36836590114706953424102682806549756034493430842408719598388671875) * X ^ 4
      + (-2021188493630074014791630480791121439385992502690440698242187500) * X ^ 5
      + (35795247439287515794950883560603614437169861027759643554687500) * X ^ 6
    , by rw [ker₄]; ring⟩

lemma phi₄_pow_6 : ker₄ ∣ curve₄.Φ (3 : ℤ) ^ 6 -
    ((551362685693725197428565514312599455497246076598634209333125153570291083980628502003967285156250000000)
      + (-100513557579804505997768912904797582495146438438298915891368309658527488626284789040916919708251953125) * X
      + (6891477082714268552665582656299597270785694776532023678163239251747698588618127669780254364013671875) * X ^ 2
      + (-194589296864693019293227711451740093705475221340708341824456838220309018222991095249652862548828125) * X ^ 3
      + (-25833351549432330834828136970730497356448431538545399893805701731170363064737851619720458984375) * X ^ 4
      + (132268340448729559241480651758276911457894360124292224258012816685516347102772037029266357421875) * X ^ 5
      + (-2919886086852622859508977587930684463383818617770083292263537353511441969203156948089599609375) * X ^ 6
      + (20623082437348378276712535220181401380377849370664784274111631170334033477396965026855468750) * X ^ 7) :=
  dvd_sub_pow_succ 5 phi₄_pow_5 phi₄_red ⟨
    (240892969107485649380610972868234278948167978894763022655512121055197082829151153564453125)
      + (3508008802983601214372027226939368775918281601027749052019880342239331131557464599609375) * X
      + (-1791417353562046714869245344461220262128347842397052526012620585867643924713134765625) * X ^ 2
      + (1245913586597802202724828915727827563278915027016599987002186062348810760498046875000) * X ^ 3
      + (7546219488388947267050368792089612320924216943322698870612680232301765441894531250) * X ^ 4
      + (-405761650754090111203307289891652145912120727039032018882707194945480346679687500) * X ^ 5
      + (7151827999826209929055103693076551698028766806418964545374292383605957031250000) * X ^ 6
    , by rw [ker₄]; ring⟩

lemma phi₄_pow_7 : ker₄ ∣ curve₄.Φ (3 : ℤ) ^ 7 -
    ((109858909133593259049019769210105942646735569434699352001004667023681217173876289502306926537764769324362277984619140625)
      + (-20024965707835076674651701825625069341386748709125747147521923573974182239639424484399028333119550633430480957031250000) * X
      + (1372639581038618003463567397014010784732112292188639448467454506203838996342211135983354488003920966088771820068359375) * X ^ 2
      + (-38730354760688841728348594844774371025066140621236346121222951894477090458939902546273548643352994322776794433593750) * X ^ 3
      + (-7021433170371177004620046934203621738431398430795507639539065084853531253202951823356733454038202762603759765625) * X ^ 4
      + (26401623248985408355668842285933519454883772087424772386498264353842954817922686601243041934397220611572265625000) * X ^ 5
      + (-582415646494242826661853786429710045790731701947720703640472647481447637982798787208681320446729660034179687500) * X ^ 6
      + (4112615741129817585000308921335703005403006434203110012626099909118333936843070525039155220389366149902343750) * X ^ 7) :=
  dvd_sub_pow_succ 6 phi₄_pow_6 phi₄_red ⟨
    (47998690860943830559159443895449452753581417687978641827111771936622709750007208167636623909473419189453125)
      + (699834005315797493973200325652607193870579446507715528182945433592869479294871558510675492286682128906250) * X
      + (-354718843023367088444184404219889077788953804896764422890683051290682257992196656177203655242919921875) * X ^ 2
      + (247918791172941607714563209675022022933020724971964318134820097427812604444370316527805328369140625000) * X ^ 3
      + (1518667845716966655714389659873200126095455061652300958536762988535402191411853527777194976806640625) * X ^ 4
      + (-81091822436363657790195866462991008535900976893724674797345727050591825825534595518112182617187500) * X ^ 5
      + (1426911073840134292965740311884351161508343397956296423925783760675411776301096010208129882812500) * X ^ 6
    , by rw [ker₄]; ring⟩

lemma phi₄_pow_8 : ker₄ ∣ curve₄.Φ (3 : ℤ) ^ 8 -
    ((21897507798007198071451039795731595079903573538550613730409272277200856595551503340183643275784060460485932881377217732369899749755859375)
      + (-3991289883487655613270683783878062546934033972395233803817204160092100115260471684414386918222592873512964152905563823878765106201171875) * X
      + (273565720391386881104761358876742368586752760113957035461747305113443129971885329989079679741533808547545182448328845202922821044921875) * X ^ 2
      + (-7716965413944296160831255529460275822327413921669970258393903040349573745193745550148021318732736038430764419297687709331512451171875) * X ^ 3
      + (-1531349483623129466768009155316737294623583884629761648168160990204860984824289687011757438958774130632306209765374660491943359375) * X ^ 4
      + (5265793227952392344400823071568353970445574889953284846467586434516038466396771459636852962980894909843922247923910617828369140625) * X ^ 5
      + (-116133597837840875118981755977668178709064943175375534100372224306112938534185016049798426935270680656022080220282077789306640625) * X ^ 6
      + (819986752962634720334961030060939952002791823164869051127455209950879036204708424725019008207091588411415740847587585449218750) * X ^ 7) :=
  dvd_sub_pow_succ 7 phi₄_pow_7 phi₄_red ⟨
    (9567344131658750062289269649696103654322006447136102074932525341560420137095522276190002185762990830936381220817565917968750)
      + (139554413928120898174338149715314255250343213589864546865155093542800746784001199929520195612850267012400925159454345703125) * X
      + (-70547763290777302520409000176573401353847584245124508025075703408354083542919945597717459399947156070172786712646484375) * X ^ 2
      + (49392987391603718585410457165024963289327763238029458845687470990577807007791918698957438927973870140314102172851562500) * X ^ 3
      + (303767764013941615337025344479250642900273996630502277275820098523670232946041236013310096523453822731971740722656250) * X ^ 4
      + (-16180692554928237420148826948279188823882145532177535168694031915677359174676187728554926804256656765937805175781250) * X ^ 5
      + (284551883128772078706171374267217290943834015182513181773599852711897525090172049627459149698740243911743164062500) * X ^ 6
    , by rw [ker₄]; ring⟩

lemma psi₄_pow_0 : ker₄ ∣ curve₄.ΨSq (3 : ℤ) ^ 0 - 1 := by simp

lemma psi₄_pow_1 : ker₄ ∣ curve₄.ΨSq (3 : ℤ) ^ 1 -
    ((104552233501225) + (-18097785489765) * X + (1226973836520) * X ^ 2 + (-38306404300) * X ^ 3
      + (362451900) * X ^ 4 + (9486000) * X ^ 5 + (-274805) * X ^ 6 + (2040) * X ^ 7) := by
  rw [pow_one]; exact psi₄_red

lemma psi₄_pow_2 : ker₄ ∣ curve₄.ΨSq (3 : ℤ) ^ 2 -
    ((391391403993170019511895693750) + (-73419300041777113556876759375) * X
      + (5321356375988386900067800000) * X ^ 2 + (-174829017958254153307750000) * X ^ 3
      + (1638082762120915228187500) * X ^ 4 + (52188074914610675778125) * X ^ 5
      + (-1516784803210898159375) * X ^ 6 + (11571517992881850000) * X ^ 7) :=
  dvd_sub_pow_succ 1 psi₄_pow_1 psi₄_red ⟨
    (168900040318875625) + (1873495817754500) * X + (-8102720917400) * X ^ 2
      + (1153955744050) * X ^ 3 + (-3070559975) * X ^ 4 + (-180682800) * X ^ 5
      + (4161600) * X ^ 6
    , by rw [ker₄]; ring⟩

lemma psi₄_pow_3 : ker₄ ∣ curve₄.ΨSq (3 : ℤ) ^ 3 -
    ((2281248652125493617207124266849633111939453125)
      + (-423541509349275441807339835658235201445312500) * X
      + (30104945998606603405376101785549939761718750) * X ^ 2
      + (-941129596588117546777231282880005810546875) * X ^ 3
      + (6032122163538182527376223673195458984375) * X ^ 4
      + (392706320568749169457441726278126953125) * X ^ 5
      + (-10020889163453530294507473885478515625) * X ^ 6
      + (73959274658641787281142723771484375) * X ^ 7) :=
  dvd_sub_pow_succ 2 psi₄_pow_2 psi₄_red ⟨
    (994562434119278298943758764296875) + (11591932254210882700992476937500) * X
      + (-8087348941493108393992531250) * X ^ 2 + (5983536050847325082537953125) * X ^ 3
      + (-12899965923374919698328125) * X ^ 4 + (-939219345145880910375000) * X ^ 5
      + (23605896705478974000000) * X ^ 6
    , by rw [ker₄]; ring⟩

lemma psi₄_pow_4 : ker₄ ∣ curve₄.ΨSq (3 : ℤ) ^ 4 -
    ((13588513175815419186869171549947086410233752913713131103515625)
      + (-2505545192467840987123531179418253048497479746929398193359375) * X
      + (175727488951551845383380078630743487477254788369202880859375) * X ^ 2
      + (-5298630383576397201471073299315770411677556194464111328125) * X ^ 3
      + (22061145509778050540380749332740997123385638604736328125) * X ^ 4
      + (2688375266083050750308060841947112515844469481201171875) * X ^ 5
      + (-64344851889886043492756934463224448645467878417968750) * X ^ 6
      + (466230868033920375291602886642386113449099121093750) * X ^ 7) :=
  dvd_sub_pow_succ 3 psi₄_pow_3 psi₄_red ⟨
    (5926548771496865001700407926201503821168554687500)
      + (76149742943982969426414587632585370308457031250) * X
      + (-88192370383987075104584831675490196962890625) * X ^ 2
      + (35605460714842093215078930352014745048828125) * X ^ 3
      + (-22572453174133787578355780345401181640625) * X ^ 4
      + (-6668808377393048546491631564793779296875) * X ^ 5
      + (150876920303629246053531156493828125000) * X ^ 6
    , by rw [ker₄]; ring⟩

lemma psi₄_pow_5 : ker₄ ∣ curve₄.ΨSq (3 : ℤ) ^ 5 -
    ((82091026028507010911126101963331497812936829773417351726513761093139648437500)
      + (-15069637490186027509802201205324847313344798529677721827933251448059082031250) * X
      + (1047726206105374487667207088505505114466967658142778701534672652435302734375) * X ^ 2
      + (-30823941329820812766240519991634893178039587383271540543088680267333984375) * X ^ 3
      + (79740371929780882891146532343656526280132712589299109240322113037109375) * X ^ 4
      + (17588799220235501899345610563700715843507787885361559496841430664062500) * X ^ 5
      + (-406685497423498601316687553927982843257371285328330363579559326171875) * X ^ 6
      + (2915734330055714466809196744434918245130889714519075369262695312500) * X ^ 7) :=
  dvd_sub_pow_succ 4 psi₄_pow_4 psi₄_red ⟨
    (35812467365739128121527366791738705537752223842516543060302734375)
      + (487448158308686742001308030037644390515239994126988214111328125) * X
      + (-687372120552506682013340329358434383610650376168499755859375) * X ^ 2
      + (214962253122920238373486062955714848822561579755792236328125) * X ^ 3
      + (73119600002285632551607786588506742818601908215332031250) * X ^ 4
      + (-44434992147070367632792482711133097398561497155761718750) * X ^ 5
      + (951110970789197565594869888750467671436162207031250000) * X ^ 6
    , by rw [ker₄]; ring⟩

lemma psi₄_pow_6 : ker₄ ∣ curve₄.ΨSq (3 : ℤ) ^ 6 -
    ((500365902521746474388730353590795054632066606428519869516882425533823278681330680847167968750)
      + (-91598779528820260338208378065131337788875405289377824872267352973420137179835796356201171875) * X
      + (6333336036080729913918614053953197523168269808118863920825294179908191915679454803466796875) * X ^ 2
      + (-183365468380794714007220005421503005112686819707408953441684840478902941594123840332031250) * X ^ 3
      + (282292398893412985408570061291538698874802190068096548129733638575130429267883300781250) * X ^ 4
      + (112337581027708110316603514777276329770663804694685212818750213166249568462371826171875) * X ^ 5
      + (-2547223442449792026947807514877315860081046176923171344374244603604788303375244140625) * X ^ 6
      + (18149445513068001029318621005305989926356010870553228440208028401325702667236328125) * X ^ 7) :=
  dvd_sub_pow_succ 5 psi₄_pow_5 psi₄_red ⟨
    (218320282383080654350040506257784841284074694861353480674259653194618225097656250)
      + (3075445491465973732651200319556742878114583163999055183240007782535552978515625) * X
      + (-4778024361829123271807988273218626553535750148051167028891803554534912109375) * X ^ 2
      + (1309726052944718037507010146938982314257918598272058860677391975402832031250) * X ^ 3
      + (1242938531976425796921542368977403121280747483511201904779170989990234375) * X ^ 4
      + (-286626631786011162959831854313248000863086176086333940307662963867187500) * X ^ 5
      + (5948098033313657512290761358647233220067015017618913753295898437500000) * X ^ 6
    , by rw [ker₄]; ring⟩

lemma psi₄_pow_7 : ker₄ ∣ curve₄.ΨSq (3 : ℤ) ^ 7 -
    ((3066745072730388034781018928154937844688673254281098325506112832793033214013304809681020241081714630126953125)
      + (-560449253598260039181037017604756744296738900438064874495188108096156060981092014878492623269557952880859375) * X
      + (38617791041139056506610840825914501836014851926554619338417769230986715823227104500674454569816589355468750) * X ^ 2
      + (-1106819398021819987351215519624801442817914570849562603419389508792844753079579152805556356906890869140625) * X ^ 3
      + (961632467074357447845276842956090497090672518173098780476656176556404303425081923927366733551025390625) * X ^ 4
      + (707865676686720613332348579970576911075098749918310540957483065561884950482304646145999431610107421875) * X ^ 5
      + (-15869843165381621199620232629294296195788976405977571480558766683000959336457302808165550231933593750) * X ^ 6
      + (112661218038204128154509419357635191483990074679317176302529567931898554994198224842548370361328125) * X ^ 7) :=
  dvd_sub_pow_succ 6 psi₄_pow_6 psi₄_red ⟨
    (1338214669125875402894743868074550957093122331252446386279871109645835914304776370525360107421875)
      + (19242934769094080868908305742033727511921015445073423926866893735059277373559725284576416015625) * X
      + (-31503687520194532686704172716444380419450355164674046597649960947156625393590927124023437500) * X ^ 2
      + (8025340366209991134803960884979641993646820552090182010361243582544601942784786224365234375) * X ^ 3
      + (10625265816562075056758262586091247909557917931689554166426607298430779693126678466796875) * X ^ 4
      + (-1816273837471356563278373947426563320630422516445789043961316822032875902652740478515625) * X ^ 5
      + (37024868846658722099809986850824219449766262175928586018024377938704433441162109375000) * X ^ 6
    , by rw [ker₄]; ring⟩

lemma psi₄_pow_8 : ker₄ ∣ curve₄.ΨSq (3 : ℤ) ^ 8 -
    ((18859791566043424000835623242850996070104802866351161905869301140809895153006804782512797651203114139162003993988037109375000)
      + (-3443035032257098017337851313362227513843780542615378744825104351000320849213770604999106504120037859248556196689605712890625) * X
      + (236743250605211650182311030436765556766232941200960166898376926214604075995527408515887851935076796700991690158843994140625) * X ^ 2
      + (-6742811509979184873773913815645667910568901044872605740705332485819584019222731043078901875661885368637740612030029296875) * X ^ 3
      + (3030817160531586249843838350752443817819621268399929795112053866715958916359835086676690853393378667533397674560546875) * X ^ 4
      + (4425794629016535096886430586497538820169567658196714386063466085391744377235496165385148362071938812732696533203125000) * X ^ 5
      + (-98563410159353660628763815644094457958037927112763089651447783717593744519363673031581679947530105710029602050781250) * X ^ 6
      + (698179858108589538940413644071859525954330847007216450034751689978503906205365440449908404558524489402770996093750) * X ^ 7) :=
  dvd_sub_pow_succ 7 psi₄_pow_7 psi₄_red ⟨
    (8230201213997362127240766182416570370804131966134352627276823566897910776470057151264414246700704097747802734375)
      + (119815897912426948468476736709978686251598992757824013618154752175190625250012799198731936714053153991699218750) * X
      + (-202065249420073065224860203019423896126924982444605293084512090787661677205355563560634998977184295654296875) * X ^ 2
      + (49346619506748279180886859128430408770749252780149058990335085493375367935644975500884164869785308837890625) * X ^ 3
      + (76624180082738004502157391855031561822806839262951638982409911906228004824642532631403207778930664062500) * X ^ 4
      + (-11393018116033561440370212849691174353388620310291611491638289949524829657028391325105726718902587890625) * X ^ 5
      + (229828884797936421435199215489575790627339752345807039657160318581073052188164378678798675537109375000) * X ^ 6
    , by rw [ker₄]; ring⟩

lemma term₄_0 : ker₄ ∣
    (-2252576338909) * curve₄.Φ (3 : ℤ) ^ 0 * curve₄.ΨSq (3 : ℤ) ^ 8
    -
    ((-42483120238424931718317089561088562935000623544622469513481377242819970714920212700156749718586245206733200098017208278179168701171875000)
      + (7755699247697124570723659718002083764503332288844199308738549288490189230406297220516249302266884605652586563383217342197895050048828125) * X
      + (-533282244709703557482744603333976625092032011845933918387487506306813677554953939333283086671543561870475150587640888988971710205078125) * X ^ 2
      + (15188697665102378381761714073035213385975318743050638965704994006281062728314062972851055550298502874838435596532188355922698974609375) * X ^ 3
      + (-6827147023372811486927598365109948500528833051717264710306136782502631786817092264801182966284063778094281635247170925140380859375) * X ^ 4
      + (-9969440262193182487768941415493583644676668042078127576691574047150621516326320154743385871357805884468877710402011871337890625000) * X ^ 5
      + (222021605607143005140888050822027713853693893804635269294125593537959378600428506455811197749803144737356236949563026428222656250) * X ^ 6
      + (-1572703428678251720992213257465460742285942843684440630522200687632678913949237610541088931744830340765912458300590515136718750) * X ^ 7) :=
  dvd_sub_const_mul₂ phi₄_pow_0 psi₄_pow_8 ⟨
    0
    , by rw [ker₄]; ring⟩

lemma term₄_1 : ker₄ ∣
    (437271444481) * curve₄.Φ (3 : ℤ) ^ 1 * curve₄.ΨSq (3 : ℤ) ^ 7
    -
    ((265094438463533635452712699049029878837661009636392827525415879615683250400380377652453300900248973558188746136422673799097537994384765625)
      + (-48363599845725905581136418438122758417319788488178679086938766664943860991621704233946322603669792112331724066944081149995326995849609375) * X
      + (3321053577230034063055786775517535384632866614900428991960761586375894217477752726983817987254009240191716242189216427505016326904296875) * X ^ 2
      + (-94211242411512648623388334478385270824490694661289499383580342520100208319489258967185441806462259830326788396381773054599761962890625) * X ^ 3
      + (17049607577944574451180033466140115204334978768014696492826042553982918794173300537677814193904070820999612553976476192474365234375) * X ^ 4
      + (62852522229176273344937816873591918470574539499150813426600639251180097307439295115406190770057050112941211985610425472259521484375) * X ^ 5
      + (-1393987993776878326297943735093650136555411245045514933812613703942848414576650152374106080421555216623241962492465972900390625000) * X ^ 6
      + (9860977442628642453268221243228663530322303964937005828097708212308903924159586713520529565668645637110377661883831024169921875) * X ^ 7) :=
  dvd_sub_const_mul₂ phi₄_pow_1 psi₄_pow_7 ⟨
    (115808230569327661110283614677499662225984173683682212519996916759715277692118620823396233666415230502738040685653686523437500)
      + (1673060986378920471495764834091672554907800540804707136349169970198472633750948873942264217005048534727612137794494628906250) * X
      + (-896231115690004992384140432170984615026707758490574619978238694603045474338074103069956492327906962294876575469970703125) * X ^ 2
      + (604210943631034117404594380611312525795856021607170814387575659504027547279918631997452171384464805179834365844726562500) * X ^ 3
      + (3391004785180913663959646764335165506491445053141298843142635197840167519807915760248394515842878092825412750244140625) * X ^ 4
      + (-191254546576393741370099470811799802753962736813761548928579479307734138806992999214283959440031908452510833740234375) * X ^ 5
      + (3408543886224479777437549963559649316264716766182647329084672667738313569981830768369708941586157679557800292968750) * X ^ 6
    , by rw [ker₄]; ring⟩

lemma term₄_2 : ker₄ ∣
    (-33006143963) * curve₄.Φ (3 : ℤ) ^ 2 * curve₄.ΨSq (3 : ℤ) ^ 6
    -
    ((-644082700604138792470886421402300806966655696276485987658663608942366943817861149126668722819179392719415541677648829482495784759521484375)
      + (117460204268253964349801763008058293562179304268869583383887180527374655994918637016170722669754944665395821371647400222718715667724609375) * X
      + (-8059466292066899733197044216888428007669165319451415456475142498581954665461504381535826485482392380731032733777174167335033416748046875) * X ^ 2
      + (228088643252335664457524197495237492959763311340004572481699866587785186991158026744107757590636443634348580761756747961044311523437500) * X ^ 3
      + (-4854271200202113103638181597126021520409132510871881168323301372068050853101315881686850866216697135428804497234523296356201171875) * X ^ 4
      + (-153629338604894262553668854352764336712303418725635631394364356890909294497980973797392788239288237826721909063309431076049804687500) * X ^ 5
      + (3399153675691171075123377310905958740699841459739827298836671376013209606828292209978636828903342229079845249466598033905029296875) * X ^ 6
      + (-24026295252384298717307094042500314240711791229430383536646911157613289435981834635719352719437444814826151169836521148681640625) * X ^ 7) :=
  dvd_sub_const_mul₂ phi₄_pow_2 psi₄_pow_6 ⟨
    (-283227911009463385661368529094487070716256901633103425619224141310190851622823666756688728674200940532159604132175445556640625)
      + (-3828720221875433839733424507743814941913978406738240722060693692585464113825735990643362603244345771185676753520965576171875) * X
      + (-10755032242232355222389545025881842610226531919423580370793835909069149229451208184033006290183466462841629981994628906250) * X ^ 2
      + (-1197547203509392930220994323623876540079920145454919761297799833888309149813219271634975450960464069220423698425292968750) * X ^ 3
      + (-8667754242412299822524361656594354645843402586559360789671759612253212274267205000196938230838063099980354309082031250) * X ^ 4
      + (400047624396845155379692217148817450838148226651992505335918436175360109459148753333419252237609322369098663330078125) * X ^ 5
      + (-7612751556567425792943790118515870543020095278699097205111226789186454565266117789264922855981302261352539062500000) * X ^ 6
    , by rw [ker₄]; ring⟩

lemma term₄_3 : ker₄ ∣
    (1127218758) * curve₄.Φ (3 : ℤ) ^ 3 * curve₄.ΨSq (3 : ℤ) ^ 5
    -
    ((708592378944020485157756117688523181775009313180572761457907510781952443566174307043900484452407657828237191725994541868567466735839843750)
      + (-129195174081126576538847086843755762685370009319071997144867574995163001392586520275376342438608670697135012635734327137470245361328125000) * X
      + (8860550415711651304799895951849987333781229205649259483337151660399175364961349991696830060940050947013565033635513484477996826171875000) * X ^ 2
      + (-250409427031887676150723843155817285247378037017908651554766592590298352060962751830005115335639464490360021745072677731513977050781250) * X ^ 3
      + (-18308681958326666071445317882596299102897897538108410948792152299158450594618055167584756037536139026977928217500448226928710937500) * X ^ 4
      + (169611831736656687942604401423427255812832065324069078676436871579922469598797398021238029044819720895937321306392550468444824218750) * X ^ 5
      + (-3747540155882793202884777006760761007281359212024814530223075057788949554311409877420057234000804873985128056257963180541992187500) * X ^ 6
      + (26476501011014007447732188271854227561431929689399966620048798753252649205117384231578756406871941697735122591257095336914062500) * X ^ 7) :=
  dvd_sub_const_mul₂ phi₄_pow_3 psi₄_pow_5 ⟨
    (311656055400213187606273006151726812101692215866383580050275671595004461532910081951163883083889921219967350363731384277343750)
      + (4212545535727066804510921336791872112506097955047383119886271521447354218354660924608059172469203773085048794746398925781250) * X
      + (12766860152203886801648523242674760081650128478520717612929558503533416686065445758115187743043253881475329399108886718750) * X ^ 2
      + (1272233729473235794355576692903397390423858008546201381030387637501200432911191970284067438184452462467551231384277343750) * X ^ 3
      + (10764926354536880764327242397046623573934955413037553144165264624703299208796577608786055757971984425187110900878906250) * X ^ 4
      + (-457082893065440950549524197197325952929697708182048269098793672169184001089812195374596581630162286758422851562500000) * X ^ 5
      + (8476201901546417390970573467931399534932751435859960390998373212626238367180109747703212904644536972045898437500000) * X ^ 6
    , by rw [ker₄]; ring⟩

lemma term₄_4 : ker₄ ∣
    (-9242705) * curve₄.Φ (3 : ℤ) ^ 4 * curve₄.ΨSq (3 : ℤ) ^ 4
    -
    ((-187253917279599136475183936791663217769658012781115600842347279441983540532710797606903702421588155768609766298745973967015743255615234375)
      + (34136769364680015307250960247112205266583107972665660799124115950747649808047840286281436558312717344249879580389423295855522155761718750) * X
      + (-2340554018906211662314887386916433891118152905511739556595805678829367064129765902942312437642548974650829349054366350173950195312500000) * X ^ 2
      + (66092360852745149198152900387902263267213042871028531708336172890666103176407210199692676221117749082780959065849892795085906982421875) * X ^ 3
      + (8507209629311288445998587895910569194622332666737230190311817549200085838126355350925558104684580151515945699065923690795898437500) * X ^ 4
      + (-44914298420434989291604587009241151488496234176451826505742150623083553823127805404001643160294902977061774555593729019165039062500) * X ^ 5
      + (991562990224097292284812115038212063618120383684928765900495871707893967066126413281337455200029846519509058445692062377929687500) * X ^ 6
      + (-7003522650997669295726450195075476237717270619918479186902028630913208029862562379675047623469730685465378686785697937011718750) * X ^ 7) :=
  dvd_sub_const_mul₂ phi₄_pow_4 psi₄_pow_4 ⟨
    (-82350490855108615192806113020268359474172724478625237412927780242214632745921100395727958190297634603973932564258575439453125)
      + (-1116947852087845223951834129416984315499186571751073159657428706298259857703647759498725487767857604510352015495300292968750) * X
      + (-3204565239506347894156118991496147933503871680486362855454208021183815071630126258680866544500943046331405639648437500000) * X ^ 2
      + (-343358481242902406164254136515358269458762671350696082001231276055262479584882232028215118804909232802689075469970703125) * X ^ 3
      + (-2678635590224899047795539097618873736687279078289870745956840766774493271880737917302390245921748384833335876464843750) * X ^ 4
      + (118667255787041812468839653465424607386025285342462193791180046134562338580416685622984348175261810421943664550781250) * X ^ 5
      + (-2229370006239543133659683719545904707923299671665825597336110777206774874224091514647218147176951169967651367187500) * X ^ 6
    , by rw [ker₄]; ring⟩

lemma term₄_5 : ker₄ ∣
    (-543828) * curve₄.Φ (3 : ℤ) ^ 5 * curve₄.ΨSq (3 : ℤ) ^ 3
    -
    ((-355185764809384018248746080797747767638087165769799561744952341767780385192160554305086160440621930596267942146529804915189743041992187500)
      + (64745985955625928614605562206257033300971334127555605118983898285307064598497726780489604946552016775595154303902582824230194091796875000) * X
      + (-4438536073615921197944397254420299406111021650945986341408567967387467833570234494930546488716068551861087109628205001354217529296875000) * X ^ 2
      + (125274427921132764497619533427837715487202801897554998054892175495025379821435480052142740844733391900580839096724987030029296875000000) * X ^ 3
      + (20219139567515198166636734379317773350479274947278849622528051008238791865719157582290558892336472906156461175531148910522460937500) * X ^ 4
      + (-85296827985352426278380350519098095954823346612256816725901540567267065324583362707967149161272177062693311110138893127441406250000) * X ^ 5
      + (1882180079420674476959546473132795861658624069936270915742844519213949995075766925799358832726896183476085930317640304565429687500) * X ^ 6
      + (-13291936605979339446924631047533144207647586442188724063129775759052122356513853178315848227458355251293422281742095947265625000) * X ^ 7) :=
  dvd_sub_const_mul₂ phi₄_pow_5 psi₄_pow_3 ⟨
    (-156154152311727134832753970801875755861168015182027501278949671545003991468043807731009190499294497622795462608337402343750000)
      + (-2131123580053044122806559290937689034368934186104502432613628896027425652396784963532522403308730623133891820907592773437500) * X
      + (-5178439211593362297499634716373824688358560598103308578165077949606926955313312923535722876719961120241880416870117187500) * X ^ 2
      + (-691371032367592982474564608339232708440202421092411250377436325919151260470424616510680122816368061763048171997070312500) * X ^ 3
      + (-4087353198049266160232670894605095116102022204213394406962309748496720271975251937954942952552630579471588134765625000) * X ^ 4
      + (211949051941922599306929749693549587597166997045846195127161318361237035545252541650451961554492723941802978515625000) * X ^ 5
      + (-4157458647271656416689635044331297882434976993935147481837698833686320678500412740868245210164499282836914062500000) * X ^ 6
    , by rw [ker₄]; ring⟩

lemma term₄_6 : ker₄ ∣
    (18372) * curve₄.Φ (3 : ℤ) ^ 6 * curve₄.ΨSq (3 : ℤ) ^ 2
    -
    ((386885240491847540303209902706001872108367055340847156644483745016794206536165558889122884267608773731459360093801783770322799682617187500)
      + (-70521151976167459538199891266277069677488708623529988711065202822359758522245145866980617650072509019665250478455349057912826538085937500) * X
      + (4833988689206170240281074705385380944962749930128412822829665812608427102643770994408773331685374172995953985630840063095092773437500000) * X ^ 2
      + (-136397093486945007776050829711819395084381866894113667094822649954492474918603969055468689513690524849313950902644544839859008789062500) * X ^ 3
      + (-24631230938567171612481448987058380685908613234123722234799344578846218684171763513847225037851115497975415524095296859741210937500) * X ^ 4
      + (92975011120656093293550357937193933450421753097865425265352178968439402617973228562311292157990280125232971672713756561279296875000) * X ^ 5
      + (-2051035151612958329990283702090614001528942275410387283413790917627564103409303879871985529328120071296987975388765335083007812500) * X ^ 6
      + (14483038704864199141785477358778566231265146297224276658343240804018047311883691174532808547448976898461069911718368530273437500) * X ^ 7) :=
  dvd_sub_const_mul₂ phi₄_pow_6 psi₄_pow_2 ⟨
    (169992280266224595075861130843177896678404653981513939354707275355549847245608146632176859622359649585082048177719116210937500)
      + (2343132928480674124623468470868243914493750377920545923760125297434013245548400313244516649223256361571538448333740234375000) * X
      + (3883521938272325367498129249322211963962185904012934890658915777032380172308120436985889922791333414101600646972656250000) * X ^ 2
      + (832014963299299997024561496053811805843469076681571111440156911322794697437436207798160569253464624059200286865234375000) * X ^ 3
      + (2475146599932076453918611764138841507590844322144847742102765197425237812045656964755912191538443154096603393554687500) * X ^ 4
      + (-204582672239018136845365735324350081680019885225262719205320482220581205714617200252232231208544456958770751953125000) * X ^ 5
      + (4384300868315519897127177160386427300328184628591243688638625714538839554898392798979932265833854675292968750000000) * X ^ 6
    , by rw [ker₄]; ring⟩

lemma term₄_7 : ker₄ ∣
    (-226) * curve₄.Φ (3 : ℤ) ^ 7 * curve₄.ΨSq (3 : ℤ) ^ 1
    -
    ((-153464062765861980071996230686486172491539453324339739598771800296679916840619033186844977496073741287344780616654400527477264404296875000)
      + (27972556950250564429072135152604037432875461745240850135955004590639161389843340757259656133687001311751509514716697484254837036132812500) * X
      + (-1917319773240506338302445330070508101973226623036983060722322713391336574338300324336532561108414699635356100856512412428855895996093750) * X ^ 2
      + (54090598652973672175935917491469541878423537643343047080930279125482876326934945434013037767738897715882710942532867193222045898437500) * X ^ 3
      + (10376723829320830677445200245838929354931473837420264404723184911358416405513703044037841155921665690436716655269265174865722656250) * X ^ 4
      + (-36895253041566586314070666009184293903974265254616200012157654105647472828588231094487398503634822293009554773196578025817871093750) * X ^ 5
      + (813778548167384884783362250023698944244497868490430031775714543192462063260934870200802956105679438748583599179983139038085937500) * X ^ 6
      + (-5746045973429924582170459361348001846659580639504090740416286744319180741057882740105776026086294729367121309041976928710937500) * X ^ 7) :=
  dvd_sub_const_mul₂ phi₄_pow_7 psi₄_pow_1 ⟨
    (-66975855798356436804809265954191941093295157950681921110409883928538997683980112438336631642978372952339097857475280761718750)
      + (-992895156655869842154312600447559140131047042329227227530165634113400240274356266431777023142374246184211969375610351562500) * X
      + (1745400057681413428500313725976648127018197779064993497922820180733495238349812808742908402853497170481085777282714843750) * X ^ 2
      + (-401448379627310257321746288535491233314172726864705797845347685274001905244840044282046896076957180118560791015625000000) * X ^ 3
      + (-760605461515451259399078672071411175431027533111046748711278366609799215220138670085339166468718814849853515625000000) * X ^ 4
      + (95420573343561296189168717471473768789621211726094693542882201448975058931068504788559677600717967748641967773437500) * X ^ 5
      + (-1896080361290491099388542425092612513611002086425001840221137102099916678242129234864052122808313369750976562500000) * X ^ 6
    , by rw [ker₄]; ring⟩

lemma term₄_8 : ker₄ ∣
    (1) * curve₄.Φ (3 : ℤ) ^ 8 * curve₄.ΨSq (3 : ℤ) ^ 0
    -
    ((21897507798007198071451039795731595079903573538550613730409272277200856595551503340183643275784060460485932881377217732369899749755859375)
      + (-3991289883487655613270683783878062546934033972395233803817204160092100115260471684414386918222592873512964152905563823878765106201171875) * X
      + (273565720391386881104761358876742368586752760113957035461747305113443129971885329989079679741533808547545182448328845202922821044921875) * X ^ 2
      + (-7716965413944296160831255529460275822327413921669970258393903040349573745193745550148021318732736038430764419297687709331512451171875) * X ^ 3
      + (-1531349483623129466768009155316737294623583884629761648168160990204860984824289687011757438958774130632306209765374660491943359375) * X ^ 4
      + (5265793227952392344400823071568353970445574889953284846467586434516038466396771459636852962980894909843922247923910617828369140625) * X ^ 5
      + (-116133597837840875118981755977668178709064943175375534100372224306112938534185016049798426935270680656022080220282077789306640625) * X ^ 6
      + (819986752962634720334961030060939952002791823164869051127455209950879036204708424725019008207091588411415740847587585449218750) * X ^ 7) :=
  dvd_sub_const_mul₂ phi₄_pow_8 psi₄_pow_0 ⟨
    0
    , by rw [ker₄]; ring⟩

lemma sum₄_1 : ker₄ ∣
    (-2252576338909) * curve₄.Φ (3 : ℤ) ^ 0 * curve₄.ΨSq (3 : ℤ) ^ 8
      + (437271444481) * curve₄.Φ (3 : ℤ) ^ 1 * curve₄.ΨSq (3 : ℤ) ^ 7
    -
    ((222611318225108703734395609487941315902660386091770358011934502372863279685460164952296551181662728351455546038405465520918369293212890625)
      + (-40607900598028781010412758720120674652816456199334479778200217376453671761215407013430073301402907506679137503560863807797431945800781250) * X
      + (2787771332520330505573042172183558759540834603054495073573274080069080539922798787650534900582465678321241091601575538516044616699218750) * X ^ 2
      + (-79022544746410270241626620405350057438515375918238860417875348513819145591175195994334386256163756955488352799849584698677062988281250) * X ^ 3
      + (10222460554571762964252435101030166703806145716297431782519905771480287007356208272876631227620007042905330918729305267333984375000) * X ^ 4
      + (52883081966983090857168875458098334825897871457072685849909065204029475791112974960662804898699244228472334275208413600921630859375) * X ^ 5
      + (-1171966388169735321157055684271622422701717351240879664518488110404889035976221645918294882671752071885885725542902946472167968750) * X ^ 6
      + (8288274013950390732276007985763202788036361121252565197575507524676225010210349102979440633923815296344465203583240509033203125) * X ^ 7) :=
  dvd_sub_add term₄_0 term₄_1 ⟨0, by ring⟩

lemma sum₄_2 : ker₄ ∣
    (-2252576338909) * curve₄.Φ (3 : ℤ) ^ 0 * curve₄.ΨSq (3 : ℤ) ^ 8
      + (437271444481) * curve₄.Φ (3 : ℤ) ^ 1 * curve₄.ΨSq (3 : ℤ) ^ 7
      + (-33006143963) * curve₄.Φ (3 : ℤ) ^ 2 * curve₄.ΨSq (3 : ℤ) ^ 6
    -
    ((-421471382379030088736490811914359491063995310184715629646729106569503664132400984174372171637516664367959995639243363961577415466308593750)
      + (76852303670225183339389004287937618909362848069535103605686963150920984233703230002740649368352037158716683868086536414921283721923828125) * X
      + (-5271694959546569227624002044704869248128330716396920382901868418512874125538705593885291584899926702409791642175598628818988800048828125) * X ^ 2
      + (149066098505925394215897577089887435521247935421765712063824518073966041399982830749773371334472686678860227961907163262367248535156250) * X ^ 3
      + (5368189354369649860614253503904145183397013205425550614196604399412236154254892391189780361403309907476526421494781970977783203125) * X ^ 4
      + (-100746256637911171696499978894666001886405547268562945544455291686879818706867998836729983340588993598249574788101017475128173828125) * X ^ 5
      + (2227187287521435753966321626634336317998124108498947634318183265608320570852070564060341946231590157193959523923695087432861328125) * X ^ 6
      + (-15738021238433907985031086056737111452675430108177818339071403632937064425771485532739912085513629518481685966253280639648437500) * X ^ 7) :=
  dvd_sub_add sum₄_1 term₄_2 ⟨0, by ring⟩

lemma sum₄_3 : ker₄ ∣
    (-2252576338909) * curve₄.Φ (3 : ℤ) ^ 0 * curve₄.ΨSq (3 : ℤ) ^ 8
      + (437271444481) * curve₄.Φ (3 : ℤ) ^ 1 * curve₄.ΨSq (3 : ℤ) ^ 7
      + (-33006143963) * curve₄.Φ (3 : ℤ) ^ 2 * curve₄.ΨSq (3 : ℤ) ^ 6
      + (1127218758) * curve₄.Φ (3 : ℤ) ^ 3 * curve₄.ΨSq (3 : ℤ) ^ 5
    -
    ((287120996564990396421265305774163690711014002995857131811178404212448779433773322869528312814890993460277196086751177906990051269531250000)
      + (-52342870410901393199458082555818143776007161249536893539180611844242017158883290272635693070256633538418328767647790722548961639404296875) * X
      + (3588855456165082077175893907145118085652898489252339100435283241886301239422644397811538476040124244603773391459914855659008026123046875) * X ^ 2
      + (-101343328525962281934826266065929849726130101596142939490942074516332310660979921080231744001166777811499793783165514469146728515625000) * X ^ 3
      + (-12940492603957016210831064378692153919500884332682860334595547899746214440363162776394975676132829119501401796005666255950927734375) * X ^ 4
      + (68865575098745516246104422528761253926426518055506133131981579893042650891929399184508045704230727297687746518291532993316650390625) * X ^ 5
      + (-1520352868361357448918455380126424689283235103525866895904891792180628983459339313359715287769214716791168532334268093109130859375) * X ^ 6
      + (10738479772580099462701102215117116108756499581222148280977395120315584779345898698838844321358312179253436625003814697265625000) * X ^ 7) :=
  dvd_sub_add sum₄_2 term₄_3 ⟨0, by ring⟩

lemma sum₄_4 : ker₄ ∣
    (-2252576338909) * curve₄.Φ (3 : ℤ) ^ 0 * curve₄.ΨSq (3 : ℤ) ^ 8
      + (437271444481) * curve₄.Φ (3 : ℤ) ^ 1 * curve₄.ΨSq (3 : ℤ) ^ 7
      + (-33006143963) * curve₄.Φ (3 : ℤ) ^ 2 * curve₄.ΨSq (3 : ℤ) ^ 6
      + (1127218758) * curve₄.Φ (3 : ℤ) ^ 3 * curve₄.ΨSq (3 : ℤ) ^ 5
      + (-9242705) * curve₄.Φ (3 : ℤ) ^ 4 * curve₄.ΨSq (3 : ℤ) ^ 4
    -
    ((99867079285391259946081368982500472941355990214741530968831124770465238901062525262624610393302837691667429788005203939974308013916015625)
      + (-18206101046221377892207122308705938509424053276871232740056495893494367350835449986354256511943916194168449187258367426693439483642578125) * X
      + (1248301437258870414861006520228684194534745583740599543839477563056934175292878494869226038397575269952944042405548505485057830810546875) * X ^ 2
      + (-35250967673217132736673365678027586458917058725114407782605901625666207484572710880539067780049028728718834717315621674060821533203125) * X ^ 3
      + (-4433282974645727764832476482781584724878551665945630144283730350546128602236807425469417571448248967985456096939742565155029296875) * X ^ 4
      + (23951276678310526954499835519520102437930283879054306626239429269959097068801593780506402543935824320625971962697803974151611328125) * X ^ 5
      + (-528789878137260156633643265088212625665114719840938130004395920472735016393212900078377832569184870271659473888576030731201171875) * X ^ 6
      + (3734957121582430166974652020041639871039228961303669094075366489402376749483336319163796697888581493788057938218116760253906250) * X ^ 7) :=
  dvd_sub_add sum₄_3 term₄_4 ⟨0, by ring⟩

lemma sum₄_5 : ker₄ ∣
    (-2252576338909) * curve₄.Φ (3 : ℤ) ^ 0 * curve₄.ΨSq (3 : ℤ) ^ 8
      + (437271444481) * curve₄.Φ (3 : ℤ) ^ 1 * curve₄.ΨSq (3 : ℤ) ^ 7
      + (-33006143963) * curve₄.Φ (3 : ℤ) ^ 2 * curve₄.ΨSq (3 : ℤ) ^ 6
      + (1127218758) * curve₄.Φ (3 : ℤ) ^ 3 * curve₄.ΨSq (3 : ℤ) ^ 5
      + (-9242705) * curve₄.Φ (3 : ℤ) ^ 4 * curve₄.ΨSq (3 : ℤ) ^ 4
      + (-543828) * curve₄.Φ (3 : ℤ) ^ 5 * curve₄.ΨSq (3 : ℤ) ^ 3
    -
    ((-255318685523992758302664711815247294696731175555058030776121216997315146291098029042461550047319092904600512358524600975215435028076171875)
      + (46539884909404550722398439897551094791547280850684372378927402391812697247662276794135348434608100581426705116644215397536754608154296875) * X
      + (-3190234636357050783083390734191615211576276067205386797569090404330533658277356000061320450318493281908143067222656495869159698486328125) * X ^ 2
      + (90023460247915631760946167749810129028285743172440590272286273869359172336862769171603673064684363171862004379409365355968475341796875) * X ^ 3
      + (15785856592869470401804257896536188625600723281333219478244320657692663263482350156821141320888223938171005078591406345367431640625) * X ^ 4
      + (-61345551307041899323880514999577993516893062733202510099662111297307968255781768927460746617336352742067339147441089153289794921875) * X ^ 5
      + (1353390201283414320325903208044583235993509350095332785738448598741214978682554025720981000157711313204426456429064273834228515625) * X ^ 6
      + (-9556979484396909279949979027491504336608357480885054969054409269649745607030516859152051529569773757505364343523979187011718750) * X ^ 7) :=
  dvd_sub_add sum₄_4 term₄_5 ⟨0, by ring⟩

lemma sum₄_6 : ker₄ ∣
    (-2252576338909) * curve₄.Φ (3 : ℤ) ^ 0 * curve₄.ΨSq (3 : ℤ) ^ 8
      + (437271444481) * curve₄.Φ (3 : ℤ) ^ 1 * curve₄.ΨSq (3 : ℤ) ^ 7
      + (-33006143963) * curve₄.Φ (3 : ℤ) ^ 2 * curve₄.ΨSq (3 : ℤ) ^ 6
      + (1127218758) * curve₄.Φ (3 : ℤ) ^ 3 * curve₄.ΨSq (3 : ℤ) ^ 5
      + (-9242705) * curve₄.Φ (3 : ℤ) ^ 4 * curve₄.ΨSq (3 : ℤ) ^ 4
      + (-543828) * curve₄.Φ (3 : ℤ) ^ 5 * curve₄.ΨSq (3 : ℤ) ^ 3
      + (18372) * curve₄.Φ (3 : ℤ) ^ 6 * curve₄.ΨSq (3 : ℤ) ^ 2
    -
    ((131566554967854782000545190890754577411635879785789125868362528019479060245067529846661334220289680826858847735277182795107364654541015625)
      + (-23981267066762908815801451368725974885941427772845616332137800430547061274582869072845269215464408438238545361811133660376071929931640625) * X
      + (1643754052849119457197683971193765733386473862923026025260575408277893444366414994347452881366880891087810918408183567225933074951171875) * X ^ 2
      + (-46373633239029376015104661962009266056096123721673076822536376085133302581741199883865016449006161677451946523235179483890533447265625) * X ^ 3
      + (-8845374345697701210677191090522192060307889952790502756555023921153555420689413357026083716962891559804410445503890514373779296875) * X ^ 4
      + (31629459813614193969669842937615939933528690364662915165690067671131434362191459634850545540653927383165632525272667407989501953125) * X ^ 5
      + (-697644950329544009664380494046030765535432925315054497675342318886349124726749854151004529170408758092561518959701061248779296875) * X ^ 6
      + (4926059220467289861835498331287061894656788816339221689288831534368301704853174315380757017879203140955705568194389343261718750) * X ^ 7) :=
  dvd_sub_add sum₄_5 term₄_6 ⟨0, by ring⟩

lemma sum₄_7 : ker₄ ∣
    (-2252576338909) * curve₄.Φ (3 : ℤ) ^ 0 * curve₄.ΨSq (3 : ℤ) ^ 8
      + (437271444481) * curve₄.Φ (3 : ℤ) ^ 1 * curve₄.ΨSq (3 : ℤ) ^ 7
      + (-33006143963) * curve₄.Φ (3 : ℤ) ^ 2 * curve₄.ΨSq (3 : ℤ) ^ 6
      + (1127218758) * curve₄.Φ (3 : ℤ) ^ 3 * curve₄.ΨSq (3 : ℤ) ^ 5
      + (-9242705) * curve₄.Φ (3 : ℤ) ^ 4 * curve₄.ΨSq (3 : ℤ) ^ 4
      + (-543828) * curve₄.Φ (3 : ℤ) ^ 5 * curve₄.ΨSq (3 : ℤ) ^ 3
      + (18372) * curve₄.Φ (3 : ℤ) ^ 6 * curve₄.ΨSq (3 : ℤ) ^ 2
      + (-226) * curve₄.Φ (3 : ℤ) ^ 7 * curve₄.ΨSq (3 : ℤ) ^ 1
    -
    ((-21897507798007198071451039795731595079903573538550613730409272277200856595551503340183643275784060460485932881377217732369899749755859375)
      + (3991289883487655613270683783878062546934033972395233803817204160092100115260471684414386918222592873512964152905563823878765106201171875) * X
      + (-273565720391386881104761358876742368586752760113957035461747305113443129971885329989079679741533808547545182448328845202922821044921875) * X ^ 2
      + (7716965413944296160831255529460275822327413921669970258393903040349573745193745550148021318732736038430764419297687709331512451171875) * X ^ 3
      + (1531349483623129466768009155316737294623583884629761648168160990204860984824289687011757438958774130632306209765374660491943359375) * X ^ 4
      + (-5265793227952392344400823071568353970445574889953284846467586434516038466396771459636852962980894909843922247923910617828369140625) * X ^ 5
      + (116133597837840875118981755977668178709064943175375534100372224306112938534185016049798426935270680656022080220282077789306640625) * X ^ 6
      + (-819986752962634720334961030060939952002791823164869051127455209950879036204708424725019008207091588411415740847587585449218750) * X ^ 7) :=
  dvd_sub_add sum₄_6 term₄_7 ⟨0, by ring⟩

lemma sum₄_8 : ker₄ ∣
    (-2252576338909) * curve₄.Φ (3 : ℤ) ^ 0 * curve₄.ΨSq (3 : ℤ) ^ 8
      + (437271444481) * curve₄.Φ (3 : ℤ) ^ 1 * curve₄.ΨSq (3 : ℤ) ^ 7
      + (-33006143963) * curve₄.Φ (3 : ℤ) ^ 2 * curve₄.ΨSq (3 : ℤ) ^ 6
      + (1127218758) * curve₄.Φ (3 : ℤ) ^ 3 * curve₄.ΨSq (3 : ℤ) ^ 5
      + (-9242705) * curve₄.Φ (3 : ℤ) ^ 4 * curve₄.ΨSq (3 : ℤ) ^ 4
      + (-543828) * curve₄.Φ (3 : ℤ) ^ 5 * curve₄.ΨSq (3 : ℤ) ^ 3
      + (18372) * curve₄.Φ (3 : ℤ) ^ 6 * curve₄.ΨSq (3 : ℤ) ^ 2
      + (-226) * curve₄.Φ (3 : ℤ) ^ 7 * curve₄.ΨSq (3 : ℤ) ^ 1
      + (1) * curve₄.Φ (3 : ℤ) ^ 8 * curve₄.ΨSq (3 : ℤ) ^ 0
    -
    (0) :=
  dvd_sub_add sum₄_7 term₄_8 ⟨0, by ring⟩

/-- **The stability divisibility at row 4**, assembled from the reduced terms. -/
lemma ker₄_dvd_multComp : ker₄ ∣
    ∑ i ∈ Finset.range (ker₄.natDegree + 1), C (ker₄.coeff i) *
      curve₄.Φ (3 : ℤ) ^ i * curve₄.ΨSq (3 : ℤ) ^
        (ker₄.natDegree - i) := by
  rw [ker₄_natDegree]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num only
  rw [ker₄_coeff_0, ker₄_coeff_1, ker₄_coeff_2, ker₄_coeff_3, ker₄_coeff_4, ker₄_coeff_5,
    ker₄_coeff_6, ker₄_coeff_7, ker₄_coeff_8]
  simpa using sum₄_8

/-- **The kernel-polynomial certificate at row 4.** -/
theorem curve₄_isKernelPolynomial : curve₄.IsKernelPolynomial 17 ker₄ 3 where
  monic := ker₄_monic
  natDegree_eq := ker₄_natDegree
  dvd_ΨSq := by
    rw [WeierstrassCurve.ΨSq_ofNat, if_neg (by decide), mul_one]
    exact dvd_pow ker₄_dvd_preΨ' (by norm_num)
  mult_ne_zero := by decide
  generates := by
    intro k hk
    obtain ⟨i, -, hi⟩ := generates_aux_17_3 k hk
    exact ⟨i, hi⟩
  dvd_multComp := ker₄_dvd_multComp


/-! #### Row 5: `p = 17`, `j₀ = -882216989/131072`, model `[1, 1, 0, -660, -7600]`, multiplier `m = 3` -/

/-- The minimal twist of conductor-level model at row 5 of `genusOneJTable`: `[a₁, a₂, a₃, a₄, a₆] = [1, 1, 0, -660, -7600]`. -/
noncomputable def curve₅ : WeierstrassCurve ℚ := ⟨1, 1, 0, -660, -7600⟩

lemma curve₅_Δ : curve₅.Δ = -4734976000 := by
  norm_num [curve₅, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

lemma curve₅_c₄ : curve₅.c₄ = 31705 := by
  norm_num [curve₅, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]

noncomputable instance : curve₅.IsElliptic :=
  ⟨by rw [curve₅_Δ]; exact isUnit_iff_ne_zero.mpr (by norm_num)⟩

lemma curve₅_j : curve₅.j = ((-882216989 : ℚ) / 131072) :=
  j_eq_of_Δ_c₄ curve₅ curve₅_Δ curve₅_c₄ (by norm_num) (by norm_num)

/-- The kernel polynomial at row 5, monic of degree `(p-1)/2 = 8`. -/
noncomputable def ker₅ : ℚ[X] :=
  (41943040000) + (12615680000) * X + (339968000) * X ^ 2 + (-122880000) * X ^ 3
    + (-8729600) * X ^ 4 + (-17600) * X ^ 5 + (10840) * X ^ 6 + (230) * X ^ 7 + X ^ 8

lemma curve₅_Ψ₂Sq : curve₅.Ψ₂Sq =
    (-30400) + (-2640) * X + (5) * X ^ 2 + (4) * X ^ 3
    := by
  simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, curve₅]
  norm_num [Polynomial.C_eq_natCast, map_ofNat]
  ring

lemma curve₅_Ψ₃ : curve₅.Ψ₃ =
    (-473600) + (-91200) * X + (-3960) * X ^ 2 + (5) * X ^ 3 + (3) * X ^ 4
    := by
  simp only [WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, curve₅]
  norm_num [Polynomial.C_eq_natCast, map_ofNat]
  ring

lemma curve₅_preΨ₄ : curve₅.preΨ₄ =
    (-299008000) + (-42496000) * X + (-4736000) * X ^ 2 + (-304000) * X ^ 3 + (-6600) * X ^ 4
      + (5) * X ^ 5 + (2) * X ^ 6
    := by
  simp only [WeierstrassCurve.preΨ₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, curve₅]
  norm_num [Polynomial.C_eq_natCast, map_ofNat]
  ring

/-! ##### The chain of remainders modulo `ker₅`

`preΨ'ₙ ≡ rₙ (mod ker₅)` for `n = 1, …, 17`, each `rₙ` of degree `< 8`; the chain ends
at `r_17 = 0`, which is exactly `ker₅ ∣ preΨ'_17`.  Every step is one application of a
`step_preΨ'_*` lemma against an explicit cofactor. -/

lemma pre₅_1 : ker₅ ∣ curve₅.preΨ' 1 - 1 := by simp

lemma pre₅_2 : ker₅ ∣ curve₅.preΨ' 2 - 1 := by simp

lemma pre₅_3 : ker₅ ∣ curve₅.preΨ' 3 -
    ((-473600) + (-91200) * X + (-3960) * X ^ 2 + (5) * X ^ 3 + (3) * X ^ 4) := by
  rw [WeierstrassCurve.preΨ'_three, curve₅_Ψ₃]
  exact ⟨
    0
    , by rw [ker₅]; ring⟩

lemma pre₅_4 : ker₅ ∣ curve₅.preΨ' 4 -
    ((-299008000) + (-42496000) * X + (-4736000) * X ^ 2 + (-304000) * X ^ 3 + (-6600) * X ^ 4
      + (5) * X ^ 5 + (2) * X ^ 6) := by
  rw [WeierstrassCurve.preΨ'_four, curve₅_preΨ₄]
  exact ⟨
    0
    , by rw [ker₅]; ring⟩

lemma pre₅_5 : ker₅ ∣ curve₅.preΨ' 5 -
    ((-197509561450496000000) + (-58194431787008000000) * X + (-1247931216281600000) * X ^ 2
      + (586288220364800000) * X ^ 3 + (37600726295040000) * X ^ 4 + (-141500919840000) * X ^ 5
      + (-50134401004000) * X ^ 6 + (-780573105000) * X ^ 7) :=
  step_preΨ'_odd_even curve₅ 0 5 (by decide) (by norm_num)
    pre₅_1 pre₅_2 pre₅_3 pre₅_4
    (by rw [curve₅_Ψ₂Sq]; exact ⟨
      (4704939300) + (-28311650) * X + (163655) * X ^ 2 + (-1125) * X ^ 3 + (5) * X ^ 4
      , by rw [ker₅]; ring⟩)

lemma pre₅_6 : ker₅ ∣ curve₅.preΨ' 6 -
    ((-78105593394527364710400000000) + (-23021360921563018035200000000) * X
      + (-494155515878665256960000000) * X ^ 2 + (231807474505812623360000000) * X ^ 3
      + (14857300310877318144000000) * X ^ 4 + (-56877117284909760000000) * X ^ 5
      + (-19842363940732308800000) * X ^ 6 + (-308544063114636400000) * X ^ 7) :=
  step_preΨ'_even curve₅ 0 6 (by norm_num)
    pre₅_1 pre₅_2 pre₅_3 pre₅_4 pre₅_5
    (⟨
      (1864413649211160000) + (-10821607591580000) * X + (83967052946000) * X ^ 2
        + (-529740445500) * X ^ 3 + (-10967908350) * X ^ 4 + (65194125) * X ^ 5
        + (-391455) * X ^ 6 + (2680) * X ^ 7 + (-12) * X ^ 8
      , by rw [ker₅]; ring⟩)

lemma pre₅_7 : ker₅ ∣ curve₅.preΨ' 7 -
    ((-87805321119813434665327924103610368000000000000)
      + (-25880254319974308589980807606042624000000000000) * X
      + (-555505691418206898318998406705971200000000000) * X ^ 2
      + (260594848806203412953059727173222400000000000) * X ^ 3
      + (16702117970993351578503729809244160000000000) * X ^ 4
      + (-63959324510703135651399672499200000000000) * X ^ 5
      + (-22306891297314770029235882373248000000000) * X ^ 6
      + (-346860725322791962264845550944000000000) * X ^ 7) :=
  step_preΨ'_odd_odd curve₅ 1 7 (by decide) (by norm_num)
    pre₅_2 pre₅_3 pre₅_4 pre₅_5
    (by rw [curve₅_Ψ₂Sq]; exact ⟨
      (2093441990395045194889245961600000000) + (-12634752061255238762180094400000000) * X
        + (76255805029046913167586400000000) * X ^ 2 + (-460225633299136201892080000000) * X ^ 3
        + (2778197788136530517336000000) * X ^ 4 + (-16751851655685307100000000) * X ^ 5
        + (100833365341003058800000) * X ^ 6 + (-640071644557999000000) * X ^ 7
        + (3298926030715360000) * X ^ 8 + (-6570916349572500) * X ^ 9
        + (544779006995750) * X ^ 10 + (-3894446503625) * X ^ 11 + (-104667180550) * X ^ 12
        + (605146900) * X ^ 13 + (-3658120) * X ^ 14 + (28160) * X ^ 15 + (-128) * X ^ 16
      , by rw [ker₅]; ring⟩)

lemma pre₅_8 : ker₅ ∣ curve₅.preΨ' 8 -
    ((-982951961090365520136435455898633449343287296000000000000000)
      + (-289721014767707541008298770925047355285700608000000000000000) * X
      + (-6218705218607132777744614912049617065161523200000000000000) * X ^ 2
      + (2917274424922927115055654619582892136464384000000000000000) * X ^ 3
      + (186974768756728112510647965864066461962731520000000000000) * X ^ 4
      + (-716003798670349055211491382660401133199360000000000000) * X ^ 5
      + (-249718379932425529406525807205695298587648000000000000) * X ^ 6
      + (-3882992803048228146141168798224979718400000000000000) * X ^ 7) :=
  step_preΨ'_even curve₅ 1 8 (by norm_num)
    pre₅_2 pre₅_3 pre₅_4 pre₅_5 pre₅_6
    (⟨
      (23435400989228918688295665296548401382400000000000)
        + (-141441935807483550929874181571510028800000000000) * X
        + (853658190944739125702016853902219520000000000) * X ^ 2
        + (-5152162370166200485779308981612160000000000) * X ^ 3
        + (31095510887862208079250882337856000000000) * X ^ 4
        + (-187675723679424259759784762016000000000) * X ^ 5
        + (1131751036570415073150053929600000000) * X ^ 6
        + (-6880911183177679488800667200000000) * X ^ 7
        + (41394965134910729301305760000000) * X ^ 8 + (-172433618163807994627280000000) * X ^ 9
        + (3832243260472320654512000000) * X ^ 10 + (6521451764130606979000000) * X ^ 11
        + (-330776000764305734400000) * X ^ 12 + (-5553793136063455200000) * X ^ 13
      , by rw [ker₅]; ring⟩)

lemma pre₅_9 : ker₅ ∣ curve₅.preΨ' 9 -
    ((-37360388048259911328770022828170406862861728597196548940706611200000000000000000000)
      + (-11011819464147955405621182083921591762155424187125031613392486400000000000000000000) * X
      + (-236362761682897963434893041883820100163544772831517734233702400000000000000000000) * X ^ 2
      + (110880804833514631112885690820516292847466286915976528889118720000000000000000000) * X ^ 3
      + (7106603570164704179383465899327010601730668655276249968541696000000000000000000) * X ^ 4
      + (-27214127262777572479269250460841792909368462529298804572160000000000000000000) * X ^ 5
      + (-9491385079192376948785306600089486931448165933797472473907200000000000000000) * X ^ 6
      + (-147586172725594317511857420979135853987937698569669837209600000000000000000) * X ^ 7) :=
  step_preΨ'_odd_even curve₅ 2 9 (by decide) (by norm_num)
    pre₅_3 pre₅_4 pre₅_5 pre₅_6
    (by rw [curve₅_Ψ₂Sq]; exact ⟨
      (890741063314912502328900031966072926414305157506554634240000000000000000)
        + (-5375975453680130914873925640236311053812892479432888320000000000000000) * X
        + (32446143182169756783697073067091886937979360419555328000000000000000) * X ^ 2
        + (-195825337462809252278961216103558227495904330130432000000000000000) * X ^ 3
        + (1181883547192406930791844450840952406939113304985600000000000000) * X ^ 4
        + (-7133135718079766657341511122368587641410193254400000000000000) * X ^ 5
        + (43051305431712525893467709374802192363623203840000000000000) * X ^ 6
        + (-259831826768113676012549652893190436962183680000000000000) * X ^ 7
        + (1568156479464991681297247890461283532376320000000000000) * X ^ 8
        + (-9465943319342910433922995057177631434368000000000000) * X ^ 9
        + (57147965235662428395462361422842420083200000000000) * X ^ 10
        + (-340802225801569551005706921012417900800000000000) * X ^ 11
        + (2176029892355557045322337780483615360000000000) * X ^ 12
        + (-14711946463663253323764278061057600000000000) * X ^ 13
        + (-64088949967318288368531265008800000000000) * X ^ 14
        + (-1898919745718236177739338636488000000000) * X ^ 15
        + (40610515493629735375240493576800000000) * X ^ 16
        + (876255721247820504093782429700000000) * X ^ 17
        + (3306437540413632874273448010000000) * X ^ 18
        + (-20883665674544138380635460000000) * X ^ 19
        + (117632128990890244183736000000) * X ^ 20 + (-577210510602360341040000000) * X ^ 21
        + (6148778232894425497600000) * X ^ 22 + (-39493640078673459200000) * X ^ 23
      , by rw [ker₅]; ring⟩)

lemma pre₅_10 : ker₅ ∣ curve₅.preΨ' 10 -
    ((-15475795400289861334705902876584970220225240323460798540602727202401804091392000000000000000000000000)
      + (-4561426524583985965734673323248811078440099215730811515119746264168660992000000000000000000000000000) * X
      + (-97908558533357379324072155352678614002709834873900106246175101660425722265600000000000000000000000) * X ^ 2
      + (45930161303634160337990877206306726745576823385474903710810693285839896576000000000000000000000000) * X ^ 3
      + (2943768750495107730527226494836609204408975653951050010473648904030545510400000000000000000000000) * X ^ 4
      + (-11272909290239878337180497759866664256949918588665639447564408772414668800000000000000000000000) * X ^ 5
      + (-3931616913646767395380707029949594500198452115380895723393183939843850240000000000000000000000) * X ^ 6
      + (-61134627672035574586853517784668651561715787835173773915651400820785152000000000000000000000) * X ^ 7) :=
  step_preΨ'_even curve₅ 2 10 (by norm_num)
    pre₅_3 pre₅_4 pre₅_5 pre₅_6 pre₅_7
    (⟨
      (368971714980360563148819211276951907273032108426555669755821362557747200000000000000000000)
        + (-2226890579687319836734579533313775985742323653202215666359932325068800000000000000000000) * X
        + (13440167504885662109274183722696969572818258009593996235491729408000000000000000000000) * X ^ 2
        + (-81116739280329041683990324172185977156681452492530787090382028800000000000000000000) * X ^ 3
        + (489571680585446879453155286059897595572650609316359247677997056000000000000000000) * X ^ 4
        + (-2954759174827688349169364836452400151268089888207094527188992000000000000000000) * X ^ 5
        + (17833143129739289131641329104352107315855344329562680035737600000000000000000) * X ^ 6
        + (-107630185935022289583477061257517695772453654057744940646400000000000000000) * X ^ 7
        + (649579144406418445067804918804334710759165652227061800960000000000000000) * X ^ 8
        + (-3921063809223420799730540089878253272996215867328000000000000000000000) * X ^ 9
        + (23658512731428561619974460247137999262611720472795136000000000000000) * X ^ 10
        + (-141985850384592005480800388972771622412787282738176000000000000000) * X ^ 11
        + (898190649507406550955836684958696612201054765772800000000000000) * X ^ 12
        + (-4880174611262788230964648531358019040459422259200000000000000) * X ^ 13
        + (15678788869886520195972785057853093223652459520000000000000) * X ^ 14
        + (-565312760493657314998987987729295913746410240000000000000) * X ^ 15
        + (2801301183915205648931727878089533033499328000000000000) * X ^ 16
        + (118462483174026257168742769270621233965664000000000000) * X ^ 17
        + (1083000613471055397016453296183175044480000000000000) * X ^ 18
      , by rw [ker₅]; ring⟩)

lemma pre₅_17 : ker₅ ∣ curve₅.preΨ' 17 -
    (0) :=
  step_preΨ'_odd_even curve₅ 6 17 (by decide) (by norm_num)
    pre₅_7 pre₅_8 pre₅_9 pre₅_10
    (by rw [curve₅_Ψ₂Sq]; exact ⟨
      (-109167603833727590011522646722723885673229689753644407956281020488602183546374822002601793103824012819052219763249846904653003952253164528623888269236123664656722894487535512865233599930591029052713005473445497641369600000000000000000000000000000000000000000000000000000000000000000000)
        + (-95871169700067790924505499636026676601689546744538048234406598634140317579352983562712596735244796744158094540127440318033348835052238838049434935213903586254095550198770619202992270174675697464317946439995143854489600000000000000000000000000000000000000000000000000000000000000000000) * X
        + (-29945139273219332974519880665654930658998145476712092659338674474469690611812415639101376566791910863901926148945060931851112543283343819444337694427143629808777016450189026114744250166334145883265618484036480154992640000000000000000000000000000000000000000000000000000000000000000000) * X ^ 2
        + (-2864026988669036131011620058119576787562170033592162239753142141327008420360256491242831313728663384715566367833668454654832894090583833004240499679740016074532804574494519208915993818771543175228535271935265944371200000000000000000000000000000000000000000000000000000000000000000000) * X ^ 3
        + (459451427473516547268689644943029582919422656160506828705758863619603657175529535217654040583272465847793278851118817224276037182943787871908308491022004154101365896770373890571091167608144628185396907267361452589056000000000000000000000000000000000000000000000000000000000000000000) * X ^ 4
        + (126588125843756143188663447197843298314819274109084239498767866027227659994359370063130766603831872400485222287050202969093232307151924180567639671719167494042409112399536933740451336129954998493982570307995666743296000000000000000000000000000000000000000000000000000000000000000000) * X ^ 5
        + (5924974910039357068091525898103437894047879258474410724201596717011676200965945968696463015187943305326095013775887453299952597341490298071195802782291562396639617830464285338755450909430858287919837029144930654617600000000000000000000000000000000000000000000000000000000000000000) * X ^ 6
        + (-1058652053638382609437787306805451109955542484869017448466696529985674018897358238656192534218771636246959815552668960252446388239689422176653820481795106292758911597862608645161566026412759953052452262437517157990400000000000000000000000000000000000000000000000000000000000000000) * X ^ 7
        + (-138724702846607883714245407294738751528311097983362582259691596797211915921640076862943439036018363547891207759407916427779623504088054716791186035442638840442492788092586178219920871451075055565320931177634998517760000000000000000000000000000000000000000000000000000000000000000) * X ^ 8
        + (-1587559402086236475554290816996225294287639349364296180444521617975237866108090464055962695910988675544678683841665350891263492587129086117704546226140836924624039998545133664461390199767406874882104297487094251520000000000000000000000000000000000000000000000000000000000000000) * X ^ 9
        + (695619037157611522432563704441599427733302054018279369415083222101361571963117505972801859394643273348598443134949312513385065920817102153631647951280659901873738100721822148142813931917638716443028552975474753536000000000000000000000000000000000000000000000000000000000000000) * X ^ 10
        + (44428619384768329154855711943229714411193731728192758486873087439587935855917890113859251411850292555317042899900420599159534411585671176990755390225222870239783567158188570930806722984240173842916583940410048512000000000000000000000000000000000000000000000000000000000000000) * X ^ 11
        + (-184998132528415156334856258158390956201090825404402267586389722162606723795550334253503221845896957750506394276297306360688366826857278888698065420346003245990216527731702175736385985267685548931536387804076441600000000000000000000000000000000000000000000000000000000000000) * X ^ 12
        + (-117433594239675406493305484581296851474193057457172477201583798293062559105398681783623503591517506955149607956467536133284391655067432416279683621710978629086771699372836162940744281052416272356084344059592704000000000000000000000000000000000000000000000000000000000000000) * X ^ 13
        + (-3714022562390560894125949770896824395842147471628049637061838506953768815666011793600784346330696251862924631071153899906864503357576482628354874301214356699269204688213560553534658843306543157508115110465372160000000000000000000000000000000000000000000000000000000000000) * X ^ 14
        + (61288729386367181935414117048469334924267541982415411585351202199407648299551195662381989331891485105910037374176503369070918336602646369353756882383844303041713913056034742474665386172104142007996836007116800000000000000000000000000000000000000000000000000000000000000) * X ^ 15
        + (5883712368927503148975620780133929506344231153478371022261845091133738816672711676120090628866297781579519673197595847925043820923966524719306927812763209954313796679968473796462776198247448891641120501530624000000000000000000000000000000000000000000000000000000000000) * X ^ 16
        + (88595446768582768797728585196916948714794233270680870861958115130251722022884847214602019560435261107832374334688742450474542620399673070811808168675876895217406504018422533937511791141068900811073745059840000000000000000000000000000000000000000000000000000000000000) * X ^ 17
        + (-1831819115135181104566141866481574234013467535266449276178729885777972761636294492783750535864014368688692612771462168195193871769188318266305629307379740468183065369045488513372683536509073648617175960780800000000000000000000000000000000000000000000000000000000000) * X ^ 18
        + (-76154168410039137867399550406838632684174393832693081049855192181638264701039018953779348854385464026970421946252878563084760361112849252831662348694300546345961794165668366113499248163633702800049622220800000000000000000000000000000000000000000000000000000000000) * X ^ 19
        + (-837933721225785817882993395847036038727796920543763913099594152908587633758594074237067775696496075427373296938423388324462487961018871298118231696786891608579477508476293100334802850425704328619622400000000000000000000000000000000000000000000000000000000000000) * X ^ 20
        + (-1665433554180219141469919443223361407235256715405345758994853968688838413919651796771004568629237939398668548273416644773392970142886936678196939284030514162502755514005664611761151609610790525384785920000000000000000000000000000000000000000000000000000000000) * X ^ 21
        + (9582396203878773672141673936077495500193398746949397524530594739837541566303592548911012457312289816357085106893552823540543719273264700240294537813058286947198896912297194227160541563783839754485760000000000000000000000000000000000000000000000000000000000) * X ^ 22
        + (-70927753810276483995262610445918344567322079515228836453110454994192498655181171536119498816368376522495781228535342284223475831151676601721609567762294724536834260472074061567793856937191964409856000000000000000000000000000000000000000000000000000000000) * X ^ 23
        + (412129427341087456787997460521278948633523502373438865483492746690409984017478212692775991862036280770441470905472223128724061395385161408537515643680893348079496143030936422931578051022657945600000000000000000000000000000000000000000000000000000000000) * X ^ 24
        + (1703314322769035583832554589749956878896814186390790054267203680067278102193386669909868612528286282423576348181150394956048512770597314550091026650100061134113914554625668705382878916116480000000000000000000000000000000000000000000000000000000000000) * X ^ 25
        + (57267339988255831519658128390001526053225296649800536953714473210542370442317972539200707162200851707098857058340462541600087674894015912810545664013390816584864779819929216219221065728000000000000000000000000000000000000000000000000000000000000000) * X ^ 26
      , by rw [ker₅]; ring⟩)

lemma ker₅_dvd_preΨ' : ker₅ ∣ curve₅.preΨ' 17 := by
  simpa using pre₅_17

lemma ker₅_coeff_0 : C (ker₅.coeff 0) = (41943040000 : ℚ[X]) := by
  rw [ker₅]; simp [Polynomial.coeff_X, map_ofNat]

lemma ker₅_coeff_1 : C (ker₅.coeff 1) = (12615680000 : ℚ[X]) := by
  rw [ker₅]; simp [Polynomial.coeff_X, map_ofNat]

lemma ker₅_coeff_2 : C (ker₅.coeff 2) = (339968000 : ℚ[X]) := by
  rw [ker₅]; simp [Polynomial.coeff_X, map_ofNat]

lemma ker₅_coeff_3 : C (ker₅.coeff 3) = (-122880000 : ℚ[X]) := by
  rw [ker₅]; simp [Polynomial.coeff_X, map_ofNat]

lemma ker₅_coeff_4 : C (ker₅.coeff 4) = (-8729600 : ℚ[X]) := by
  rw [ker₅]; simp [Polynomial.coeff_X, map_ofNat]

lemma ker₅_coeff_5 : C (ker₅.coeff 5) = (-17600 : ℚ[X]) := by
  rw [ker₅]; simp [Polynomial.coeff_X, map_ofNat]

lemma ker₅_coeff_6 : C (ker₅.coeff 6) = (10840 : ℚ[X]) := by
  rw [ker₅]; simp [Polynomial.coeff_X, map_ofNat]

lemma ker₅_coeff_7 : C (ker₅.coeff 7) = (230 : ℚ[X]) := by
  rw [ker₅]; simp [Polynomial.coeff_X, map_ofNat]

lemma ker₅_coeff_8 : C (ker₅.coeff 8) = (1 : ℚ[X]) := by
  rw [ker₅]; simp [Polynomial.coeff_X]

lemma ker₅_natDegree : ker₅.natDegree = 8 := by
  rw [ker₅]; compute_degree!

lemma ker₅_monic : ker₅.Monic := by
  rw [ker₅]; monicity!

lemma curve₅_Φ : curve₅.Φ (3 : ℤ) =
    (-9089843200000) + (-1856962560000) * X + (-168284160000) * X ^ 2 + (-8267776000) * X ^ 3
      + (-91968000) * X ^ 4 + (15120000) * X ^ 5 + (736200) * X ^ 6 + (7920) * X ^ 7 + X ^ 9
    := by
  rw [WeierstrassCurve.Φ_three, curve₅_Ψ₃, curve₅_preΨ₄, curve₅_Ψ₂Sq]
  ring

lemma curve₅_ΨSq : curve₅.ΨSq (3 : ℤ) =
    (224296960000) + (86384640000) * X + (12068352000) * X ^ 2 + (717568000) * X ^ 3
      + (11928000) * X ^ 4 + (-586800) * X ^ 5 + (-23735) * X ^ 6 + (30) * X ^ 7 + (9) * X ^ 8
    := by
  rw [WeierstrassCurve.ΨSq_three, curve₅_Ψ₃]
  ring

/-! ##### The stability divisibility at row 5

The root set of `ker₅` is carried into itself by `x(P) ↦ x(3 ⬝ P)`, written
multiplied-out as a divisibility so that no rational function appears.  Every power
`Φ^i` and `ΨSq^j` is reduced modulo `ker₅` BEFORE being multiplied, so each `ring`
call below is an identity in degree `≤ 16` rather than the degree-`72` identity the
unreduced sum would need — which is what keeps this inside the default heartbeat
budget. -/

lemma phi₅_red : ker₅ ∣ curve₅.Φ (3 : ℤ) -
    ((557056000000) + (1002700800000) * X + (-102707200000) * X ^ 2 + (-36870144000) * X ^ 3
      + (-1976896000) * X ^ 4 + (19801600) * X ^ 5 + (3247000) * X ^ 6 + (49980) * X ^ 7) := by
  rw [curve₅_Φ]
  exact ⟨
    (-230) + X
    , by rw [ker₅]; ring⟩

lemma psi₅_red : ker₅ ∣ curve₅.ΨSq (3 : ℤ) -
    ((-153190400000) + (-27156480000) * X + (9008640000) * X ^ 2 + (1823488000) * X ^ 3
      + (90494400) * X ^ 4 + (-428400) * X ^ 5 + (-121295) * X ^ 6 + (-2040) * X ^ 7) := by
  rw [curve₅_ΨSq]
  exact ⟨
    (9)
    , by rw [ker₅]; ring⟩

lemma phi₅_pow_0 : ker₅ ∣ curve₅.Φ (3 : ℤ) ^ 0 - 1 := by simp

lemma phi₅_pow_1 : ker₅ ∣ curve₅.Φ (3 : ℤ) ^ 1 -
    ((557056000000) + (1002700800000) * X + (-102707200000) * X ^ 2 + (-36870144000) * X ^ 3
      + (-1976896000) * X ^ 4 + (19801600) * X ^ 5 + (3247000) * X ^ 6 + (49980) * X ^ 7) := by
  rw [pow_one]; exact phi₅_red

lemma phi₅_pow_2 : ker₅ ∣ curve₅.Φ (3 : ℤ) ^ 2 -
    ((-1370025301413315534127104000000000) + (-403809261260880671145984000000000) * X
      + (-8667540070933336372019200000000) * X ^ 2 + (4066059234643620764057600000000) * X ^ 3
      + (260602989634327667015680000000) * X ^ 4 + (-997956307214338457600000000) * X ^ 5
      + (-348054194898728562688000000) * X ^ 6 + (-5412064551358617600000000) * X ^ 7) :=
  dvd_sub_pow_succ 1 phi₅_pow_1 phi₅_red ⟨
    (32663948577013657600000) + (-197140226508569600000) * X + (1189749356373760000) * X ^ 2
      + (-7190923247040000) * X ^ 3 + (42937146160000) * X ^ 4 + (-249969972000) * X ^ 5
      + (2498000400) * X ^ 6
    , by rw [ker₅]; ring⟩

lemma phi₅_pow_3 : ker₅ ∣ curve₅.Φ (3 : ℤ) ^ 3 -
    ((147901792975988217875254002868666184499200000000000000)
      + (43593440211903006704058720606713775390720000000000000) * X
      + (935709666625446430920560571190513500160000000000000) * X ^ 2
      + (-438953412911992141592179566446523711488000000000000) * X ^ 3
      + (-28133524968725527819999057766908952576000000000000) * X ^ 4
      + (107734914617266951831568115297786265600000000000) * X ^ 5
      + (37574365373966804863284136696296243200000000000) * X ^ 6
      + (584262121056928859258889121982054400000000000) * X ^ 7) :=
  dvd_sub_pow_succ 2 phi₅_pow_2 phi₅_red ⟨
    (-3526253550986505321964023138222080000000000)
      + (21282305420317439265790151360512000000000) * X
      + (-128443795808991907833960333312000000000) * X ^ 2
      + (776413554418236049299321651200000000) * X ^ 3
      + (-4621390367658523495722188800000000) * X ^ 4
      + (27245124584387967848693760000000) * X ^ 5 + (-270494986276903707648000000000) * X ^ 6
    , by rw [ker₅]; ring⟩

lemma phi₅_pow_4 : ker₅ ∣ curve₅.Φ (3 : ℤ) ^ 4 -
    ((-15966811285060182505456639320358316668217588341117288448000000000000000000)
      + (-4706151420645965880006509678946817274028674519020863488000000000000000000) * X
      + (-101015000318827276116555391902362345345520720896694681600000000000000000) * X ^ 2
      + (47387433011279318827039565651822046760591237084243558400000000000000000) * X ^ 3
      + (3037168616556693498812700771511416206325063205854904320000000000000000) * X ^ 4
      + (-11630576045706226310055605701387466865479580752281600000000000000000) * X ^ 5
      + (-4056359216546175649608551583564696418148315496972288000000000000000) * X ^ 6
      + (-63074306539586800413741698408469843133419587895296000000000000000) * X ^ 7) :=
  dvd_sub_pow_succ 3 phi₅_pow_3 phi₅_red ⟨
    (380678447901004879319399166514296781783707104051200000000000000)
      + (-2297541818250412625933643375316686727451718451200000000000000) * X
      + (13866213567849221144637650217613718287338700800000000000000) * X ^ 2
      + (-83818109653366654902763731342571316539555840000000000000) * X ^ 3
      + (498904485158227352599633980926124326125568000000000000) * X ^ 4
      + (-2941260897935111095644079881675891277824000000000000) * X ^ 5
      + (29201420810425304385759278316663078912000000000000) * X ^ 6
    , by rw [ker₅]; ring⟩

lemma phi₅_pow_5 : ker₅ ∣ curve₅.Φ (3 : ℤ) ^ 5 -
    ((1723705017247668314439632287999929534547167131707496530675528072848998400000000000000000000000)
      + (508054906572669330615172661612058414621967348995651428176562983649935360000000000000000000000) * X
      + (10905124370684956868247857081792861090102673627914181437753774498119680000000000000000000000) * X ^ 2
      + (-5115733791659332399440896266751791411140545588008457199652115339804672000000000000000000000) * X ^ 3
      + (-327879041664655066256657883960533650822241236478035877986105676529664000000000000000000000) * X ^ 4
      + (1255584595167262578272377319666177813438950045896272035703535802777600000000000000000000) * X ^ 5
      + (437906267475065841469361680837872403194496738446129442085522112512000000000000000000000) * X ^ 6
      + (6809217989783073230112996163865057581091006720696611088124178595840000000000000000000) * X ^ 7) :=
  dvd_sub_pow_succ 4 phi₅_pow_4 phi₅_red ⟨
    (-41096330312301548520329411357869701571194877186730227985977180160000000000000000000)
      + (248032264473503452862369323895176757468838356852761694071422976000000000000000000) * X
      + (-1496933950706445327120264733732046541802009760956586154524672000000000000000000) * X ^ 2
      + (9048625524929213302628619262020808086123791700025013593702400000000000000000) * X ^ 3
      + (-53859480696640326386422464354166971831341303562824266547200000000000000000) * X ^ 4
      + (317525276418149905565271617005859127122645320256884572160000000000000000) * X ^ 5
      + (-3152453840848548284678810086455322759808311003006894080000000000000000) * X ^ 6
    , by rw [ker₅]; ring⟩

lemma phi₅_pow_6 : ker₅ ∣ curve₅.Φ (3 : ℤ) ^ 6 -
    ((-186083428521813681203575535838074210166115833749581543493952339592909400832691729858560000000000000000000000000000)
      + (-54847318970696073667316326492547612067350754858230810630405490399511923998030582251520000000000000000000000000000) * X
      + (-1177268100428270997977277852050051449516689008036966085354378154400122818089111781376000000000000000000000000000) * X ^ 2
      + (552271574214537482583698931467754396809096984540113753414895922783598016253052269363200000000000000000000000000) * X ^ 3
      + (35396344271729330334736772950843847452959828018779379654078463601645795312568526438400000000000000000000000000) * X ^ 4
      + (-135547256595544800830522465507552134498855108607531308522681856516902861142134620160000000000000000000000000) * X ^ 5
      + (-47274387907198549269212819282067996938132483492845000990112880017950184904847261696000000000000000000000000) * X ^ 6
      + (-735092499245877189528033476815784661709030981897226249996299372351349950808850432000000000000000000000000) * X ^ 7) :=
  dvd_sub_pow_succ 5 phi₅_pow_5 phi₅_red ⟨
    (4436574685144755918776813898242903089289774430901724748954857039091500448743424000000000000000000000000)
      + (-26776445908915683939033637256644880957935099231736564434899834907386968014848000000000000000000000000) * X
      + (161602245761831084630633193033093092191910074515156977029528597657725750476800000000000000000000000) * X ^ 2
      + (-976848848405300868220304298246456865416922616740575104030381124362772152320000000000000000000000) * X ^ 3
      + (5814426903762515762505349250151308315266522154263474602724641572319657984000000000000000000000) * X ^ 4
      + (-34278598418522910474625340749747678240210112847456377383849079546576896000000000000000000000) * X ^ 5
      + (340324715129358000041047548269975577902928515900416622184446446220083200000000000000000000) * X ^ 6
    , by rw [ker₅]; ring⟩

lemma phi₅_pow_7 : ker₅ ∣ curve₅.Φ (3 : ℤ) ^ 7 -
    ((20088728653655476283111900264604945190903293090805822453572022093793614403424610247550889740425442099200000000000000000000000000000000)
      + (5921069473704604906982170768126355624865215662392558111336611269645019316409193637458508653945547653120000000000000000000000000000000) * X
      + (127092560632477834457069943608625160140875521379047079043078478469153005361141219802818232665065390080000000000000000000000000000000) * X ^ 2
      + (-59620751217094261319936728620555148280159764291659510531701879220290865486710433568354933296343285760000000000000000000000000000000) * X ^ 3
      + (-3821229870142831069678163071594122987793659691440860576009006424761030447557057922881158353768153088000000000000000000000000000000) * X ^ 4
      + (14633071193527106227429234488966205853441704613985583480587596563808866540076956524948177219590553600000000000000000000000000000) * X ^ 5
      + (5103529951481072729492196568182373925769734702727124618829088112957472269976921721842830543945728000000000000000000000000000000) * X ^ 6
      + (79357274691210858667306829464766063355776744493661784028484279188068735654684100063258423192453120000000000000000000000000000) * X ^ 7) :=
  dvd_sub_pow_succ 6 phi₅_pow_6 phi₅_red ⟨
    (-478952616627558866542800480393026325290621764876881702870820006999033186142262206978960371220480000000000000000000000000000)
      + (2890664474781183537937135452452242629024790373010620075647819116129320565928839797359333343232000000000000000000000000000) * X
      + (-17445850448473503608902570951775039115702832729776112684710036608513120066689805741803438080000000000000000000000000000) * X ^ 2
      + (105456201055267714019242046130089497354751467127867194465811578568917484041926057253247385600000000000000000000000000) * X ^ 3
      + (-627699335045876530883685541116474793600799439854185145206027640057362325225512730047283200000000000000000000000000) * X ^ 4
      + (3700563063177909917627774622449559716672909626108687850983633999605724692707455763742720000000000000000000000000) * X ^ 5
      + (-36739923112308941932611113171252917392217368475223367974815042630120470541426344591360000000000000000000000000) * X ^ 6
    , by rw [ker₅]; ring⟩

lemma phi₅_pow_8 : ker₅ ∣ curve₅.Φ (3 : ℤ) ^ 8 -
    ((-2168688647484219595638089925822170694290031227383133619284742688642641732001066070009565320788244100051915552891863040000000000000000000000000000000000000)
      + (-639211986481380209355930372845013745871953518348038709054554246990120597970731595082915589329967175835431028956069888000000000000000000000000000000000000) * X
      + (-13720340305019757873181129287658769610942151253193635469048447834099801008151408573676939058497542027226441727344640000000000000000000000000000000000000) * X ^ 2
      + (6436387715131252482610614184475454278125464403812017978953699624499652206934650693739149098546428322898303816564736000000000000000000000000000000000000) * X ^ 3
      + (412522762474487862493048137921437889525338825075361595218776576062388635664331791510059106508493961704527393959444480000000000000000000000000000000000) * X ^ 4
      + (-1579720445348141250170391394556954147164867282757610070374375486780649428647788956315817604173925597821822440570880000000000000000000000000000000000) * X ^ 5
      + (-550954102606124495494352053694038327008909141098283345718693752629776176377813633698624537152385991784417764311040000000000000000000000000000000000) * X ^ 6
      + (-8567053878085963646551806629606707139195593827335482826318733149551623447739670494930639781640286516143720497152000000000000000000000000000000000) * X ^ 7) :=
  dvd_sub_pow_succ 7 phi₅_pow_7 phi₅_red ⟨
    (51705566851491127598972199492153010561223115340398751623074315103045894419702571275798440142821133978232160256000000000000000000000000000000000)
      + (-312063114506907713999982841562322191144760311835306477699572049277226754525033516472102885137948215064972492800000000000000000000000000000000) * X
      + (1883375422387784316949721975008447736977042701432205598418002877024294593570411998472577137389232504753356800000000000000000000000000000000) * X ^ 2
      + (-11384576394970441345803821371172320556428360811763696464895334705769976384600440695820496796170430300815360000000000000000000000000000000) * X ^ 3
      + (67763592480984493247993932427967875809357669175789384527893685604525149941028507232298352395224377982976000000000000000000000000000000) * X ^ 4
      + (-399496117587959631611393667679421348173817558839218170931471904569251695120649783304076107274222829568000000000000000000000000000000) * X ^ 5
      + (3966276589066718716191995336649007846521721689793215965743644273819675408021111321161655991158806937600000000000000000000000000000) * X ^ 6
    , by rw [ker₅]; ring⟩

lemma psi₅_pow_0 : ker₅ ∣ curve₅.ΨSq (3 : ℤ) ^ 0 - 1 := by simp

lemma psi₅_pow_1 : ker₅ ∣ curve₅.ΨSq (3 : ℤ) ^ 1 -
    ((-153190400000) + (-27156480000) * X + (9008640000) * X ^ 2 + (1823488000) * X ^ 3
      + (90494400) * X ^ 4 + (-428400) * X ^ 5 + (-121295) * X ^ 6 + (-2040) * X ^ 7) := by
  rw [pow_one]; exact psi₅_red

lemma psi₅_pow_2 : ker₅ ∣ curve₅.ΨSq (3 : ℤ) ^ 2 -
    ((-2484693370309839106867200000000) + (-732353112107489936998400000000) * X
      + (-15719566142273990696960000000) * X ^ 2 + (7374252407636327895040000000) * X ^ 3
      + (472632941854509532928000000) * X ^ 4 + (-1809887048170300016000000) * X ^ 5
      + (-631235233447638963600000) * X ^ 6 + (-9815397417337495500000) * X ^ 7) :=
  dvd_sub_pow_succ 1 psi₅_pow_1 psi₅_red ⟨
    (59239706844738430000) + (-357534037096875000) * X + (2157556157215500) * X ^ 2
      + (-13045908455750) * X ^ 3 + (77674017025) * X ^ 4 + (-462284400) * X ^ 5
      + (4161600) * X ^ 6
    , by rw [ker₅]; ring⟩

lemma psi₅_pow_3 : ker₅ ∣ curve₅.ΨSq (3 : ℤ) ^ 3 -
    ((-11423291345754770477018125709137149952000000000000)
      + (-3366967758030630578955448563523846144000000000000) * X
      + (-72270145763864289703024425628750643200000000000) * X ^ 2
      + (33902852845878393058291832260635033600000000000) * X ^ 3
      + (2172911131343220371355843774458664960000000000) * X ^ 4
      + (-8320976324290805762858809804159360000000000) * X ^ 5
      + (-2902080591207182031154352306397456000000000) * X ^ 6
      + (-45125865595962349599969386873580000000000) * X ^ 7) :=
  dvd_sub_pow_succ 2 psi₅_pow_2 psi₅_red ⟨
    (272352498206757110408079682010800000000) + (-1643753692660306971897796764600000000) * X
      + (9920171533619246226093436620000000) * X ^ 2
      + (-59980190984404419704304830000000) * X ^ 3 + (356643362461343836528107000000) * X ^ 4
      + (-2127105962245617886183500000) * X ^ 5 + (20023410731368490820000000) * X ^ 6
    , by rw [ker₅]; ring⟩

lemma psi₅_pow_4 : ker₅ ∣ curve₅.ΨSq (3 : ℤ) ^ 4 -
    ((-52518052344963190902504516537693507504168547637002240000000000000000)
      + (-15479478165065325411344060114301831781451867910307840000000000000000) * X
      + (-332258644488053092402638191399580907599171582492672000000000000000) * X ^ 2
      + (155866794123659832301235512119546556028275298828288000000000000000) * X ^ 3
      + (9989858183772143434521428374842293599754953689907200000000000000) * X ^ 4
      + (-38255302869521690858314187475025412872716598656000000000000000) * X ^ 5
      + (-13342180969087778459473890241960193129716091249280000000000000) * X ^ 6
      + (-207464074906913299297765162918239596656699485920000000000000) * X ^ 7) :=
  dvd_sub_pow_succ 3 psi₅_pow_3 psi₅_red ⟨
    (1252127983448547398453142829425120166234307376000000000000)
      + (-7557081393321142849809284445527317857616632000000000000) * X
      + (45607528707427408239398088193333580878469600000000000) * X ^ 2
      + (-275756148466521574158964616540442492430000000000000) * X ^ 3
      + (1639651305133610520305011278870476625720000000000) * X ^ 4
      + (-9779269864100629894022470835202039660000000000) * X ^ 5
      + (92056765815763193183937549222103200000000000) * X ^ 6
    , by rw [ker₅]; ring⟩

lemma psi₅_pow_5 : ker₅ ∣ curve₅.ΨSq (3 : ℤ) ^ 5 -
    ((-241449310759822426668219416133321721586386417957766352887059002163200000000000000000000)
      + (-71166183188345026492775637686686145248927761758631371951205095833600000000000000000000) * X
      + (-1527543713515629309627130174160665119356582220850334058980890378240000000000000000000) * X ^ 2
      + (716590359526349339496796736398361589246147180465364436120089395200000000000000000000) * X ^ 3
      + (45927909839776940332049985334847826028149175560810369708239208448000000000000000000) * X ^ 4
      + (-175876981310791800397500349958010571576221989066453051714624512000000000000000000) * X ^ 5
      + (-61340058421416721766537438634349193343369096121881947212430976000000000000000000) * X ^ 6
      + (-953806465720972591528123638603087631488948892130951954004140800000000000000000) * X ^ 7) :=
  dvd_sub_pow_succ 4 psi₅_pow_4 psi₅_red ⟨
    (5756600351454827132560458559139957709366557834728904552900480000000000000000)
      + (-34743331336586881264578527800504604017434610978938774543040000000000000000) * X
      + (209678498729081176361818824882537033935788188390908960480000000000000000) * X ^ 2
      + (-1267776107683739984582035306881087252489820864519496496000000000000000) * X ^ 3
      + (7538220856144568826679267518071415331261883412374545600000000000000) * X ^ 4
      + (-44959739803550603334862252911471352890228208500466400000000000000) * X ^ 5
      + (423226712810103130567440932353208777179666951276800000000000000) * X ^ 6
    , by rw [ker₅]; ring⟩

lemma psi₅_pow_6 : ker₅ ∣ curve₅.ΨSq (3 : ℤ) ^ 6 -
    ((-1110052011896141978080850077885156393120780178642090352954200797021549290655318016000000000000000000000000)
      + (-327183227728381739990435375966139011918364013967659980291596262794801505024081920000000000000000000000000) * X
      + (-7022811401329904977247792684902826903034265948782152533016935103588364583226572800000000000000000000000) * X ^ 2
      + (3294490954620560656314417287607035613494284977179306881772290294577889396863795200000000000000000000000) * X ^ 3
      + (211151436131216990366300342955824315188289984498363872835803826646683282020106240000000000000000000000) * X ^ 4
      + (-808586267386237799187623597981887436176332968602276125645650445616953709322240000000000000000000000) * X ^ 5
      + (-282008074681366698090244733226118722533679062985527188341729229676067517400064000000000000000000000) * X ^ 6
      + (-4385081004792398507161113645512477099933677898994372111263211156524059355904000000000000000000000) * X ^ 7) :=
  dvd_sub_pow_succ 5 psi₅_pow_5 psi₅_red ⟨
    (26465703222366773440893925384529972990770054749232775556364333685190025702400000000000000000000)
      + (-159730855013772693005295296266170035054207309806979541496086258567033638400000000000000000000) * X
      + (963987176575986623594996610203925021504014203093442241397569696278045440000000000000000000) * X ^ 2
      + (-5828541877131637603470781181402258926075672157796902439884353982343040000000000000000000) * X ^ 3
      + (34656620891349238819604152930283066109153948748642439165882880378560000000000000000000) * X ^ 4
      + (-206700319276964857051855479674134848012689808228179667244451413984000000000000000000) * X ^ 5
      + (1945765190070784086717372222750298768237455739947141986168447232000000000000000000) * X ^ 6
    , by rw [ker₅]; ring⟩

lemma psi₅_pow_7 : ker₅ ∣ curve₅.ΨSq (3 : ℤ) ^ 7 -
    ((-5103412659315469323684537628101263992857812154653345627928857202502008174867834717505268649820160000000000000000000000000000)
      + (-1504209720274750245777964919536463924878192217909691615341495149171431586603350970955979428986880000000000000000000000000000) * X
      + (-32287049818783912250662216394757599360406706953324176787901040284819423168471583752242151292928000000000000000000000000000) * X ^ 2
      + (15146269421278195214874113025649545329677654147266385772493044785365235265977732301832614576128000000000000000000000000000) * X ^ 3
      + (970758937992461994224847091223783162474155934844533162031034173511763957668656550162753100185600000000000000000000000000) * X ^ 4
      + (-3717437875797170064549173806305120529647076271555755931228392939514114004587543498054577356800000000000000000000000000) * X ^ 5
      + (-1296519048598168748525271293110316962841249034374650418874989106849670458076650407672286453760000000000000000000000000) * X ^ 6
      + (-20160206613881732172115210694268554165732120295357590252369756128952890328219798043678423040000000000000000000000000) * X ^ 7) :=
  dvd_sub_pow_succ 6 psi₅_pow_6 psi₅_red ⟨
    (121674843534583593532068388631294244864370204910824525503686313812666176579422454183332864000000000000000000000000)
      + (-734355200319064008079714842027361695347597855189895237996028261501833143368099687079424000000000000000000000000) * X
      + (4431886350939701501737780823492944480341909021670483781363227708160416449283074052454400000000000000000000000) * X ^ 2
      + (-26796451051238646392034165094829075221730518257752890436815167747179126870309636172800000000000000000000000) * X ^ 3
      + (159332207761951786509560042454847267253296341046112565483999152491566444130928340480000000000000000000000) * X ^ 4
      + (-950295134622311338529787987060736151483720920959161565151899848871325134719650560000000000000000000000) * X ^ 5
      + (8945565249776492954608671836845453283864702913948519106976950759309081086044160000000000000000000000) * X ^ 6
    , by rw [ker₅]; ring⟩

lemma psi₅_pow_8 : ker₅ ∣ curve₅.ΨSq (3 : ℤ) ^ 8 -
    ((-23462703091518004016821312161471796979069487042872511867758040980040560619820982316626903216461651174571062067200000000000000000000000000000000)
      + (-6915534449239640776321729015656391258431299483603848415226152971980854824442544048842543694558419394296492851200000000000000000000000000000000) * X
      + (-148438214616332362346042928215604178618224142953015544514986887519662571637986648780234228425331800344604180480000000000000000000000000000000) * X ^ 2
      + (69634271437351357622872061854806317647127506695872042005040176314563580658409691970948545917935814843480145920000000000000000000000000000000) * X ^ 3
      + (4463019210092555195044366227029728954693419772234439723422279641549572951026373463852749701191329232351920128000000000000000000000000000000) * X ^ 4
      + (-17090748282285980259120911241633879569431996841114314094168424883835011274536854017697192630227877786746880000000000000000000000000000000) * X ^ 5
      + (-5960686215375832013227430054298213319838434831267122908806039731813411533373654608672272833254643046601523200000000000000000000000000000) * X ^ 6
      + (-92685615219015186559428097898724404311891496689257820217819810052665630453916335468628502777620894637670400000000000000000000000000000) * X ^ 7) :=
  dvd_sub_pow_succ 7 psi₅_pow_7 psi₅_red ⟨
    (559394451935573355255646325217141867708047833785006975268505074041208434438338647553931491970557159137280000000000000000000000000000)
      + (-3376163986533182689794702205218587938252176706730189858815937322428394687164015180916929714497328885760000000000000000000000000000) * X
      + (20375392022756192518606296331306507420523089178379262241110112216378077428907154904286115244007438336000000000000000000000000000) * X ^ 2
      + (-123195441343349827435643510461087397363724969876390487338372549938603766157082972246973597262121984000000000000000000000000000) * X ^ 3
      + (732522438061312717185383785003550479645138776872940532432975202160476695723730596946795786383667200000000000000000000000000) * X ^ 4
      + (-4368937822862259784348188938644454732832885281232095582245722228070027575162942006734477402060800000000000000000000000000) * X ^ 5
      + (41126821492318733631115029816307850498093525402529484114834302503063896269568388009103983001600000000000000000000000000) * X ^ 6
    , by rw [ker₅]; ring⟩

lemma term₅_0 : ker₅ ∣
    (41943040000) * curve₅.Φ (3 : ℤ) ^ 0 * curve₅.ΨSq (3 : ℤ) ^ 8
    -
    ((-984097094275663303197696968841098039564990657818683480169850223147480435699576254145574866684179693681081039127052288000000000000000000000000000000000000)
      + (-290058538025836222666893332972836644808034331492775558233767143149911873135786602742364763882611566991753571517595648000000000000000000000000000000000000) * X
      + (-6225949973181412927174572379864214687951319956844049104213875622712708028714939529255315452212828715125746926039859200000000000000000000000000000000000) * X ^ 2
      + (2920673032267685486830427805258615573326174898445228892699080316768792846098904046725173699377818599412681499528396800000000000000000000000000000000000) * X ^ 3
      + (187192593249680446247953654434957002735864293243619994697089611896699400267817223249314434827055969645705880005509120000000000000000000000000000000000) * X ^ 4
      + (-716837938833852161447518745044299476135869020786731320624270011639687231288350249538434058377353087124635857715200000000000000000000000000000000000) * X ^ 5
      + (-250009300358957137164078627864632133202516265665230186848968076713039192480752530197725486336112823489329551638528000000000000000000000000000000000) * X ^ 6
      + (-3887516466555762730469555087290113639029837521297408323708825005831356644753831015214104037141864288623595094016000000000000000000000000000000000) * X ^ 7) :=
  dvd_sub_const_mul₂ phi₅_pow_0 psi₅_pow_8 ⟨
    0
    , by rw [ker₅]; ring⟩

lemma term₅_1 : ker₅ ∣
    (12615680000) * curve₅.Φ (3 : ℤ) ^ 1 * curve₅.ΨSq (3 : ℤ) ^ 7
    -
    ((6950500909214662774045821825916282008797921166367017401412803667391739017883251821034425264016364818720866112781680640000000000000000000000000000000000000)
      + (2048631323068735760323537766210931246852751873472851667630832009788273234546445194931763393749586398746506647375446016000000000000000000000000000000000000) * X
      + (43972765696634338422172241497843137001261963462454606892628964417180203477172221592918466418707121553662169789235200000000000000000000000000000000000000) * X ^ 2
      + (-20628188706559537350785804907047023614736789345001502112222218220303564838224682517493840366240223586966457901540966400000000000000000000000000000000000) * X ^ 3
      + (-1322107642780721316673129698145279404687830499440684996549705499549108599726617004616176620129231529632573345601945600000000000000000000000000000000000) * X ^ 4
      + (5062897527699232503136457518481212986014407201327480358788262973801148897371651821109930246988324977074265695191040000000000000000000000000000000000) * X ^ 5
      + (1765770755309531580635637171870417471687487895223118113233969728206489964334758727082825005655339804843793281187840000000000000000000000000000000000) * X ^ 6
      + (27456830116210018542138054871894988940201611295427130043573355079391701345705782237896709158060826845032942141440000000000000000000000000000000000) * X ^ 7) :=
  dvd_sub_const_mul₂ phi₅_pow_1 psi₅_pow_7 ⟨
    (-165712855936994813208057226983109059533171809947090717113703711412387374538821871822851217047671807684835803136000000000000000000000000000000000)
      + (1000141243709076095035987590268351367803954895948891233601308757715300031681790921769272043381670482737207705600000000000000000000000000000000) * X
      + (-6036091257675150623024587070387572277482717573686867925130102074978790671230781275536847218030455631642624000000000000000000000000000000000) * X ^ 2
      + (36486799834572203987932391028825136409352396932107585430811674453176119877329816426653593855828715655659520000000000000000000000000000000) * X ^ 3
      + (-217177745499385595376827007301924733276555661599092095051891730587382357888519702973409795302384499425280000000000000000000000000000000) * X ^ 4
      + (1280358124133651518420257577188267578014446053224620687634457403197940336856846172195594162766522351616000000000000000000000000000000) * X ^ 5
      + (-12711649074423282236636938854148466272608818900479487472866903928345401804806678770347976938703814656000000000000000000000000000000) * X ^ 6
    , by rw [ker₅]; ring⟩

lemma term₅_2 : ker₅ ∣
    (339968000) * curve₅.Φ (3 : ℤ) ^ 2 * curve₅.ΨSq (3 : ℤ) ^ 6
    -
    ((-4398158491696531648277880725967725242763198901898668957740769158612374902663429382880004752222610703216904810923032576000000000000000000000000000000000000)
      + (-1296338978672016916616679493311604371776766114329592854661274029739812355985823509623886451376810306896337816852103168000000000000000000000000000000000000) * X
      + (-27825216538801438268111066994073800748946118123873250921731875199386501057946238825900621330376847104095468239454208000000000000000000000000000000000000) * X ^ 2
      + (13053166169332169785515439199113346851443468956464851829798735096678766343692443070267763884582342937837811440759603200000000000000000000000000000000000) * X ^ 3
      + (836607178674541442016886301040772314976002372954431738012786496748436928992469358808010129861063795036018796155371520000000000000000000000000000000000) * X ^ 4
      + (-3203715249431677627766675621237023562905178400736516441894887757415016228695453454524359967573263312844594232688640000000000000000000000000000000000) * X ^ 5
      + (-1117349633255642740529302378627404260296027881974156227106053867009059557523738346377095601840727257376945283792896000000000000000000000000000000000) * X ^ 6
      + (-17374214047016472945187986339154821335621550235942521084740705231137211083411589909957449461598827202279538425856000000000000000000000000000000000) * X ^ 7) :=
  dvd_sub_const_mul₂ phi₅_pow_2 psi₅_pow_6 ⟨
    (104860282152167377742948089324318327199783330674261113590983399232972916575706897478946472522785460496790401843200000000000000000000000000000000)
      + (-632869741645043801834639878876352360229009953590690024861692714791292259809513576687057087324167882077005414400000000000000000000000000000000) * X
      + (3819697779778383521258507683333932801999723549313182706018984105273637233536778952863049583570000052842659840000000000000000000000000000000) * X ^ 2
      + (-23089974764925931985697066407641882201281778924463013040212249897383535466971367824201234571959186929745920000000000000000000000000000000) * X ^ 3
      + (137012378499322274628998920514506196511560883018831558347455490647678924519698100114685233106123432656896000000000000000000000000000000) * X ^ 4
      + (-817944919367546819006881744434923018616208731219653225834640846466923915481266526568472240928025739264000000000000000000000000000000) * X ^ 5
      + (8068236661770061287223895508450095886988886290489837048103025610211642331431594056944822598710067200000000000000000000000000000000) * X ^ 6
    , by rw [ker₅]; ring⟩

lemma term₅_3 : ker₅ ∣
    (-122880000) * curve₅.Φ (3 : ℤ) ^ 3 * curve₅.ΨSq (3 : ℤ) ^ 5
    -
    ((-37328576868289916151338649387129569780741678992146240329917531192968667306860291631606556117466392278590832637273702400000000000000000000000000000000000000)
      + (-11002443250755347940351535396696623202918408719112104769391803803208403681033995574583162820080008252323181910892216320000000000000000000000000000000000000) * X
      + (-236161506322798727311809477214208241636772624292730761990522903196608136770688851052024303098741600658022482145443840000000000000000000000000000000000000) * X ^ 2
      + (110786393361309884316245290169296988688403512160537682390811861904236955480179813068896027233482862911611658450239488000000000000000000000000000000000000) * X ^ 3
      + (7100552523669847202286073714285496867823307298920349491351330701543488428151015519704405929765738054357891617390592000000000000000000000000000000000000) * X ^ 4
      + (-27190955300565501954675090950497158029307240200344284833094362274742255371667733153237569013321808556121176355635200000000000000000000000000000000000) * X ^ 5
      + (-9483303467231369003618147115210986515661613814295176652023481931846463036593059328632617888082107458690035063193600000000000000000000000000000000000) * X ^ 6
      + (-147460507802210971098533273815445534293780705186189076420414186773829127037581129138141774233663095868071555891200000000000000000000000000000000000) * X ^ 7) :=
  dvd_sub_const_mul₂ phi₅_pow_3 psi₅_pow_5 ⟨
    (889982730303556839474066708906381657219285779463538496091044645736596657374196563721241944933225079553382154240000000000000000000000000000000000)
      + (-5371367776576868018477861158991367266404396493088886658309232013146237266746133111430126330354933908524498944000000000000000000000000000000000) * X
      + (32418995918053852997243168610785028696920475752918292944191089872947782601112048166263824867974947065036800000000000000000000000000000000000) * X ^ 2
      + (-195971995886136467948817166360418005587944895138638771123610281673093772149383592693576934457001224699904000000000000000000000000000000000) * X ^ 3
      + (1162867848304622290580363419744320280863856368148150772666893661771080295522927493966972315742780155494400000000000000000000000000000000) * X ^ 4
      + (-6942159929190418951161575787072059497322447574604191937949980858220782764577648720940150530468164403200000000000000000000000000000000) * X ^ 5
      + (68477704856364853807882549087980215964640061261608562414002284368230784554234476710781037468817817600000000000000000000000000000000) * X ^ 6
    , by rw [ker₅]; ring⟩

lemma term₅_4 : ker₅ ∣
    (-8729600) * curve₅.Φ (3 : ℤ) ^ 4 * curve₅.ΨSq (3 : ℤ) ^ 4
    -
    ((62270445065633297248797753768504739463545043658711344155579668648051967701795978295100917798779018082630285314127560704000000000000000000000000000000000000)
      + (18353955481649079367744873494385443453619811686375893238889045186496337389951080222323758127195614085120877513358180352000000000000000000000000000000000000) * X
      + (393957748723699187771781071285873502831426374867673699772483866358743579341091710285198087635148680223349388844466176000000000000000000000000000000000000) * X ^ 2
      + (-184810635727327963604049945146734506429707863144283468096429801346035441180405893566827752600426118573736282696135475200000000000000000000000000000000000) * X ^ 3
      + (-11844934978928462020979060044333528583035283358676247756584220468864727150239940546231345673487827005635525718573056000000000000000000000000000000000000) * X ^ 4
      + (45359159935301401081272514166224350535029914333832064676742547032493824396822486593665341475780801608975415362191360000000000000000000000000000000000) * X ^ 5
      + (15819770726341485506208682286279319566501150989159596022429566005268765648852503343577598483276412213508792737857536000000000000000000000000000000000) * X ^ 6
      + (245989325627045552779652140656279836387582507041167577609826611545426602605899278910203826200657512132830392483840000000000000000000000000000000000) * X ^ 7) :=
  dvd_sub_const_mul₂ phi₅_pow_4 psi₅_pow_4 ⟨
    (-1484643277783464962128653213116325761828258259669343621169237234202832805755890024271640532948467661833882723942400000000000000000000000000000000)
      + (8960359331104756664794592740289315731067184495541888243793683803903455616581524389542434968817694486640879206400000000000000000000000000000000) * X
      + (-54080425072755918683055281106542345003246901544013797263201378032444774232814842547091797176344645322953195520000000000000000000000000000000) * X ^ 2
      + (326914777578801142075599083215229451906984943466753974036515305624648815499524989926126633529418842573373440000000000000000000000000000000) * X ^ 3
      + (-1939862286257075497350922032121194211744289098757842364588444935514866292824038997515061117411477153644544000000000000000000000000000000) * X ^ 4
      + (11580709064607313464424741566557366135702341035027696872633625845426376411403271011516729389688444420096000000000000000000000000000000) * X ^ 5
      + (-114232513431321153057318348456425713331681461999514988269672749105913852918005201071975988564613660672000000000000000000000000000000) * X ^ 6
    , by rw [ker₅]; ring⟩

lemma term₅_5 : ker₅ ∣
    (-17600) * curve₅.Φ (3 : ℤ) ^ 5 * curve₅.ΨSq (3 : ℤ) ^ 3
    -
    ((-2948001420306319925362176529215737768549762691945550217888436848277693355871024099112188372518309389946275170541895680000000000000000000000000000000000000)
      + (-868911194887252619668945031758217113283999295633976518404255296047193017885101234081001551786873798084330704085188608000000000000000000000000000000000000) * X
      + (-18650709844036571736306383519113174232394704004250608241637110350998825767980142923350603934457749181524436821475328000000000000000000000000000000000000) * X ^ 2
      + (8749287339084089940441733359058287919317381605175715419588688112439192234765536896025034376130062627713856662038118400000000000000000000000000000000000) * X ^ 3
      + (560761772370704458963773746720070025472711233924162819508214710777913834035981315005571007540300226383998649106432000000000000000000000000000000000000) * X ^ 4
      + (-2147388986416105318457427084019871600141829401282024415057719831699178654170476024553685272612937582821702023249920000000000000000000000000000000000) * X ^ 5
      + (-748938063972720398765282910011643799175879376048472052539493930115346860838817084020632290212846194261982110023680000000000000000000000000000000000) * X ^ 6
      + (-11645602991345007878017139472632103130011231753961573792756771805247014933495186859195177802046751054860950437888000000000000000000000000000000000) * X ^ 7) :=
  dvd_sub_const_mul₂ phi₅_pow_5 psi₅_pow_3 ⟨
    (70285839244296288341689892783770673120425339390039496282766833497208380239455867628860968207539543322744848384000000000000000000000000000000000)
      + (-424200469527881763137069697738638098855563043525316035032675276284953766776413029647540551576624440742510592000000000000000000000000000000000) * X
      + (2560270281627423507416939241146970484018679376444969708512264678404358363336208329178727151497249155553689600000000000000000000000000000000) * X ^ 2
      + (-15476767953169469630963424634260354396393217593503039397337776530736355478223610560379817572318735016919040000000000000000000000000000000) * X ^ 3
      + (91836773754522175984654932331544373208208626094317254374732809712384870071402816162443464920645784043520000000000000000000000000000000) * X ^ 4
      + (-548252814552452676248563830719160360170859291406105014125463025050409464437100537535730720602740228096000000000000000000000000000000) * X ^ 5
      + (5407984662441854134341808498930365169435099156827139974874021073554200913235868049062169299092766720000000000000000000000000000000) * X ^ 6
    , by rw [ker₅]; ring⟩

lemma term₅_6 : ker₅ ∣
    (10840) * curve₅.Φ (3 : ℤ) ^ 6 * curve₅.ΨSq (3 : ℤ) ^ 2
    -
    ((-42635533133281595240467085357770675194948650347796496653367224750651094581612304150196499976937582690833719351218012160000000000000000000000000000000000000)
      + (-12566646604819256251261944133913562519157794387606659099975334674631774464859815354137242563636912875590623909728223232000000000000000000000000000000000000) * X
      + (-269736287112106231113953964261976084560060874331470651724090329704967478959489656002140285250095680469392088305028300800000000000000000000000000000000000) * X ^ 2
      + (126536753906773949650514562297251232079937864235770759668126130591230571010836937909013774655401439949712260975715942400000000000000000000000000000000000) * X ^ 3
      + (8110029039030998253357433017221303158273924848744568582465175405821482151794123725745922215501939754649187184311009280000000000000000000000000000000000) * X ^ 4
      + (-31056658809504429051255132661997871829337389917083913054273724178451418381775991266106676493841089793770688306216960000000000000000000000000000000000) * X ^ 5
      + (-10831532651692812715977939705859310181104545015211168692097157357649885909187626006355099165998394319134028413796352000000000000000000000000000000000) * X ^ 6
      + (-168424780522304319579786551099701001972019882883725791344392056535171606317804797454295372892688342926602696392704000000000000000000000000000000000) * X ^ 7) :=
  dvd_sub_const_mul₂ phi₅_pow_6 psi₅_pow_2 ⟨
    (1016510442382498415762593553456180501446088234981564300115617696645651015917832858501044642651369688214039166976000000000000000000000000000000000)
      + (-6135008297275615792885387463905252832308657024473664321353792636794550342013744672800117143106296686023226163200000000000000000000000000000000) * X
      + (37027963306554189520486342058126148016607707003661776119519542313029963092406287952346430021006799943520747520000000000000000000000000000000) * X ^ 2
      + (-223833084393698158481336833497555249939016366937610650842561684124663854968233749546490109495385913923993600000000000000000000000000000000) * X ^ 3
      + (1328191318250568682744839900131459987767930215065250344941743577638372953242455451869133374774241388396544000000000000000000000000000000) * X ^ 4
      + (-7929119233119212627241399717571295343003210893065343659886706430332698925593970510159717708769800486912000000000000000000000000000000) * X ^ 5
      + (78213039201647282418359571417709659839956279028197861584212185898182977350437811182538312970707927040000000000000000000000000000000) * X ^ 6
    , by rw [ker₅]; ring⟩

lemma term₅_7 : ker₅ ∣
    (230) * curve₅.Φ (3 : ℤ) ^ 7 * curve₅.ΨSq (3 : ℤ) ^ 1
    -
    ((21242109680486285841438003300325955248515347993910411701376082546856245595028461471815046343821935954969577135066316800000000000000000000000000000000000000)
      + (6261023748923275031853516500901482897344392806674402603201111997482605366373728452995052219147983491854274781297770496000000000000000000000000000000000000) * X
      + (134389495675610613036583280873177645644379453632234650786131711132849668774707305028231514070526446378375105531084800000000000000000000000000000000000000) * X ^ 2
      + (-63043837090011530707322316960672395346109213770921285971326176079514924103877709600345329980854613188483832247169843200000000000000000000000000000000000) * X ^ 3
      + (-4040623247761076327712978829145229271084035014745561468119447534436573628939181383175760530387533226509230456753356800000000000000000000000000000000000) * X ^ 4
      + (15473219267099073779363264772647615123948052687831535099788529534433232002051654689501270687131251344454938158694400000000000000000000000000000000000) * X ^ 5
      + (5396545737466609404704783333118278178260852609909773020670313182488315119814544858621371480690822026384152167710720000000000000000000000000000000000) * X ^ 6
      + (83913519964262926556756116915655456181874683071857146138931311875949635513181143723633982850060828878718722113536000000000000000000000000000000000) * X ^ 7) :=
  dvd_sub_const_mul₂ phi₅_pow_7 psi₅_pow_1 ⟨
    (-506451377589425391406419141779512450608037686862881960341108876823008753470353181130453383614981042958583726080000000000000000000000000000000000)
      + (3056631856163752484561653879397225485282536012858091087195832391109240976710252563791935052272729365927270809600000000000000000000000000000000) * X
      + (-18446992677785692980471226140206860161955529279360209850202895763428459539681753014186189207882432686483046400000000000000000000000000000000) * X ^ 2
      + (111535787967133159408639617661123661457677897049933822268683383639245705384353264236134998127140502304194560000000000000000000000000000000) * X ^ 3
      + (-663193917257591463774821249100067392786855471875513646819138471064531615767568410325389394409168924835840000000000000000000000000000000) * X ^ 4
      + (3955446056597594845791619346344900726540887384885935812504251182113116310853688849588165904557857046528000000000000000000000000000000) * X ^ 5
      + (-37234433285116134886700364384868236926530448516426109066164823795041850769177779749680852161899003904000000000000000000000000000000) * X ^ 6
    , by rw [ker₅]; ring⟩

lemma term₅_8 : ker₅ ∣
    (1) * curve₅.Φ (3 : ℤ) ^ 8 * curve₅.ΨSq (3 : ℤ) ^ 0
    -
    ((-2168688647484219595638089925822170694290031227383133619284742688642641732001066070009565320788244100051915552891863040000000000000000000000000000000000000)
      + (-639211986481380209355930372845013745871953518348038709054554246990120597970731595082915589329967175835431028956069888000000000000000000000000000000000000) * X
      + (-13720340305019757873181129287658769610942151253193635469048447834099801008151408573676939058497542027226441727344640000000000000000000000000000000000000) * X ^ 2
      + (6436387715131252482610614184475454278125464403812017978953699624499652206934650693739149098546428322898303816564736000000000000000000000000000000000000) * X ^ 3
      + (412522762474487862493048137921437889525338825075361595218776576062388635664331791510059106508493961704527393959444480000000000000000000000000000000000) * X ^ 4
      + (-1579720445348141250170391394556954147164867282757610070374375486780649428647788956315817604173925597821822440570880000000000000000000000000000000000) * X ^ 5
      + (-550954102606124495494352053694038327008909141098283345718693752629776176377813633698624537152385991784417764311040000000000000000000000000000000000) * X ^ 6
      + (-8567053878085963646551806629606707139195593827335482826318733149551623447739670494930639781640286516143720497152000000000000000000000000000000000) * X ^ 7) :=
  dvd_sub_const_mul₂ phi₅_pow_8 psi₅_pow_0 ⟨
    0
    , by rw [ker₅]; ring⟩

lemma sum₅_1 : ker₅ ∣
    (41943040000) * curve₅.Φ (3 : ℤ) ^ 0 * curve₅.ΨSq (3 : ℤ) ^ 8
      + (12615680000) * curve₅.Φ (3 : ℤ) ^ 1 * curve₅.ΨSq (3 : ℤ) ^ 7
    -
    ((5966403814938999470848124857075183969232930508548333921242953444244258582183675566888850397332185125039785073654628352000000000000000000000000000000000000)
      + (1758572785042899537656644433238094602044717541980076109397064866638361361410658592189398629866974831754753075857850368000000000000000000000000000000000000) * X
      + (37746815723452925494997669117978922313310643505610557788415088794467495448457282063663150966494292838536422863195340800000000000000000000000000000000000) * X ^ 2
      + (-17707515674291851863955377101788408041410614446556273219523137903534771992125778470768666666862404987553776402012569600000000000000000000000000000000000) * X ^ 3
      + (-1134915049531040870425176043710322401951966206197065001852615887652409199458799781366862185302175559986867465596436480000000000000000000000000000000000) * X ^ 4
      + (4346059588865380341688938773436913509878538180540749038163992962161461666083301571571496188610971889949629837475840000000000000000000000000000000000) * X ^ 5
      + (1515761454950574443471558544005785338484971629557887926385001651493450771854006196885099519319226981354463729549312000000000000000000000000000000000) * X ^ 6
      + (23569313649654255811668499784604875301171773774129721719864530073560344700951951222682605120918962556409347047424000000000000000000000000000000000) * X ^ 7) :=
  dvd_sub_add term₅_0 term₅_1 ⟨0, by ring⟩

lemma sum₅_2 : ker₅ ∣
    (41943040000) * curve₅.Φ (3 : ℤ) ^ 0 * curve₅.ΨSq (3 : ℤ) ^ 8
      + (12615680000) * curve₅.Φ (3 : ℤ) ^ 1 * curve₅.ΨSq (3 : ℤ) ^ 7
      + (339968000) * curve₅.Φ (3 : ℤ) ^ 2 * curve₅.ΨSq (3 : ℤ) ^ 6
    -
    ((1568245323242467822570244131107458726469731606649664963502184285631883679520246184008845645109574421822880262731595776000000000000000000000000000000000000)
      + (462233806370882621039964939926490230267951427650483254735790836898549005424835082565512178490164524858415259005747200000000000000000000000000000000000000) * X
      + (9921599184651487226886602123905121564364525381737306866683213595080994390511043237762529636117445734440954623741132800000000000000000000000000000000000) * X ^ 2
      + (-4654349504959682078439937902675061189967145490091421389724402806856005648433335400500902782280062049715964961252966400000000000000000000000000000000000) * X ^ 3
      + (-298307870856499428408289742669550086975963833242633263839829390903972270466330422558852055441111764950848669441064960000000000000000000000000000000000) * X ^ 4
      + (1142344339433702713922263152199889946973359779804232596269105204746445437387848117047136221037708577105035604787200000000000000000000000000000000000) * X ^ 5
      + (398411821694931702942256165378381078188943747583731699278947784484391214330267850508003917478499723977518445756416000000000000000000000000000000000) * X ^ 6
      + (6195099602637782866480513445450053965550223538187200635123824842423133617540361312725155659320135354129808621568000000000000000000000000000000000) * X ^ 7) :=
  dvd_sub_add sum₅_1 term₅_2 ⟨0, by ring⟩

lemma sum₅_3 : ker₅ ∣
    (41943040000) * curve₅.Φ (3 : ℤ) ^ 0 * curve₅.ΨSq (3 : ℤ) ^ 8
      + (12615680000) * curve₅.Φ (3 : ℤ) ^ 1 * curve₅.ΨSq (3 : ℤ) ^ 7
      + (339968000) * curve₅.Φ (3 : ℤ) ^ 2 * curve₅.ΨSq (3 : ℤ) ^ 6
      + (-122880000) * curve₅.Φ (3 : ℤ) ^ 3 * curve₅.ΨSq (3 : ℤ) ^ 5
    -
    ((-35760331545047448328768405256022111054271947385496575366415346907336783627340045447597710472356817856767952374542106624000000000000000000000000000000000000)
      + (-10540209444384465319311570456770132972650457291461621514656012966309854675609160492017650641589843727464766651886469120000000000000000000000000000000000000) * X
      + (-226239907138147240084922875090303120072408098910993455123839689601527142380177807814261773462624154923581527521702707200000000000000000000000000000000000) * X ^ 2
      + (106132043856350202237805352266621927498436366670446261001087459097380949831746477668395124451202800861895693488986521600000000000000000000000000000000000) * X ^ 3
      + (6802244652813347773877783971615946780847343465677716227511501310639516157684685097145553874324626289407042947949527040000000000000000000000000000000000) * X ^ 4
      + (-26048610961131799240752827798297268082333880420540052236825257069995809934279885036190432792284099979016140750848000000000000000000000000000000000000) * X ^ 5
      + (-9084891645536437300675890949832605437472670066711444952744534147362071822262791478124613970603607734712516617437184000000000000000000000000000000000) * X ^ 6
      + (-141265408199573188232052760369995480328230481648001875785290361931405993420040767825416618574342960513941747269632000000000000000000000000000000000) * X ^ 7) :=
  dvd_sub_add sum₅_2 term₅_3 ⟨0, by ring⟩

lemma sum₅_4 : ker₅ ∣
    (41943040000) * curve₅.Φ (3 : ℤ) ^ 0 * curve₅.ΨSq (3 : ℤ) ^ 8
      + (12615680000) * curve₅.Φ (3 : ℤ) ^ 1 * curve₅.ΨSq (3 : ℤ) ^ 7
      + (339968000) * curve₅.Φ (3 : ℤ) ^ 2 * curve₅.ΨSq (3 : ℤ) ^ 6
      + (-122880000) * curve₅.Φ (3 : ℤ) ^ 3 * curve₅.ΨSq (3 : ℤ) ^ 5
      + (-8729600) * curve₅.Φ (3 : ℤ) ^ 4 * curve₅.ΨSq (3 : ℤ) ^ 4
    -
    ((26510113520585848920029348512482628409273096273214768789164321740715184074455932847503207326422200225862332939585454080000000000000000000000000000000000000)
      + (7813746037264614048433303037615310480969354394914271724233032220186482714341919730306107485605770357656110861471711232000000000000000000000000000000000000) * X
      + (167717841585551947686858196195570382759018275956680244648644176757216436960913902470936314172524525299767861322763468800000000000000000000000000000000000) * X ^ 2
      + (-78678591870977761366244592880112578931271496473837207095342342248654491348659415898432628149223317711840589207148953600000000000000000000000000000000000) * X ^ 3
      + (-5042690326115114247101276072717581802187939892998531529072719158225210992555255449085791799163200716228482770623528960000000000000000000000000000000000) * X ^ 4
      + (19310548974169601840519686367927082452696033913292012439917289962498014462542601557474908683496701629959274611343360000000000000000000000000000000000) * X ^ 5
      + (6734879080805048205532791336446714129028480922448151069685031857906693826589711865452984512672804478796276120420352000000000000000000000000000000000) * X ^ 6
      + (104723917427472364547599380286284356059352025393165701824536249614020609185858511084787207626314551618888645214208000000000000000000000000000000000) * X ^ 7) :=
  dvd_sub_add sum₅_3 term₅_4 ⟨0, by ring⟩

lemma sum₅_5 : ker₅ ∣
    (41943040000) * curve₅.Φ (3 : ℤ) ^ 0 * curve₅.ΨSq (3 : ℤ) ^ 8
      + (12615680000) * curve₅.Φ (3 : ℤ) ^ 1 * curve₅.ΨSq (3 : ℤ) ^ 7
      + (339968000) * curve₅.Φ (3 : ℤ) ^ 2 * curve₅.ΨSq (3 : ℤ) ^ 6
      + (-122880000) * curve₅.Φ (3 : ℤ) ^ 3 * curve₅.ΨSq (3 : ℤ) ^ 5
      + (-8729600) * curve₅.Φ (3 : ℤ) ^ 4 * curve₅.ΨSq (3 : ℤ) ^ 4
      + (-17600) * curve₅.Φ (3 : ℤ) ^ 5 * curve₅.ΨSq (3 : ℤ) ^ 3
    -
    ((23562112100279528994667171983266890640723333581269218571275884892437490718584908748391018953903890835916057769043558400000000000000000000000000000000000000)
      + (6944834842377361428764358005857093367685355099280295205828776924139289696456818496225105933818896559571780157386522624000000000000000000000000000000000000) * X
      + (149067131741515375950551812676457208526623571952429636407007066406217611192933759547585710238066776118243424501288140800000000000000000000000000000000000) * X ^ 2
      + (-69929304531893671425802859521054291011954114868661491675753654136215299113893879002407593773093255084126732545110835200000000000000000000000000000000000) * X ^ 3
      + (-4481928553744409788137502325997511776715228659074368709564504447447297158519274134080220791622900489844484121517096960000000000000000000000000000000000) * X ^ 4
      + (17163159987753496522062259283907210852554204512009988024859570130798835808372125532921223410883764047137572588093440000000000000000000000000000000000) * X ^ 5
      + (5985941016832327806767508426435070329852601546399679017145537927791346965750894781432352222459958284534294010396672000000000000000000000000000000000) * X ^ 6
      + (93078314436127356669582240813652252929340793639204128031779477808773594252363324225592029824267800564027694776320000000000000000000000000000000000) * X ^ 7) :=
  dvd_sub_add sum₅_4 term₅_5 ⟨0, by ring⟩

lemma sum₅_6 : ker₅ ∣
    (41943040000) * curve₅.Φ (3 : ℤ) ^ 0 * curve₅.ΨSq (3 : ℤ) ^ 8
      + (12615680000) * curve₅.Φ (3 : ℤ) ^ 1 * curve₅.ΨSq (3 : ℤ) ^ 7
      + (339968000) * curve₅.Φ (3 : ℤ) ^ 2 * curve₅.ΨSq (3 : ℤ) ^ 6
      + (-122880000) * curve₅.Φ (3 : ℤ) ^ 3 * curve₅.ΨSq (3 : ℤ) ^ 5
      + (-8729600) * curve₅.Φ (3 : ℤ) ^ 4 * curve₅.ΨSq (3 : ℤ) ^ 4
      + (-17600) * curve₅.Φ (3 : ℤ) ^ 5 * curve₅.ΨSq (3 : ℤ) ^ 3
      + (10840) * curve₅.Φ (3 : ℤ) ^ 6 * curve₅.ΨSq (3 : ℤ) ^ 2
    -
    ((-19073421033002066245799913374503784554225316766527278082091339858213603863027395401805481023033691854917661582174453760000000000000000000000000000000000000)
      + (-5621811762441894822497586128056469151472439288326363894146557750492484768402996857912136629818016316018843752341700608000000000000000000000000000000000000) * X
      + (-120669155370590855163402151585518876033437302379041015317083263298749867766555896454554575012028904351148663803740160000000000000000000000000000000000000) * X ^ 2
      + (56607449374880278224711702776196941067983749367109267992372476455015271896943058906606180882308184865585528430605107200000000000000000000000000000000000) * X ^ 3
      + (3628100485286588465219930691223791381558696189670199872900670958374184993274849591665701423879039264804703062793912320000000000000000000000000000000000) * X ^ 4
      + (-13893498821750932529192873378090660976783185405073925029414154047652582573403865733185453082957325746633115718123520000000000000000000000000000000000) * X ^ 5
      + (-4845591634860484909210431279424239851251943468811489674951619429858538943436731224922746943538436034599734403399680000000000000000000000000000000000) * X ^ 6
      + (-75346466086176962910204310286048749042679089244521663312612578726398012065441473228703343068420542362575001616384000000000000000000000000000000000) * X ^ 7) :=
  dvd_sub_add sum₅_5 term₅_6 ⟨0, by ring⟩

lemma sum₅_7 : ker₅ ∣
    (41943040000) * curve₅.Φ (3 : ℤ) ^ 0 * curve₅.ΨSq (3 : ℤ) ^ 8
      + (12615680000) * curve₅.Φ (3 : ℤ) ^ 1 * curve₅.ΨSq (3 : ℤ) ^ 7
      + (339968000) * curve₅.Φ (3 : ℤ) ^ 2 * curve₅.ΨSq (3 : ℤ) ^ 6
      + (-122880000) * curve₅.Φ (3 : ℤ) ^ 3 * curve₅.ΨSq (3 : ℤ) ^ 5
      + (-8729600) * curve₅.Φ (3 : ℤ) ^ 4 * curve₅.ΨSq (3 : ℤ) ^ 4
      + (-17600) * curve₅.Φ (3 : ℤ) ^ 5 * curve₅.ΨSq (3 : ℤ) ^ 3
      + (10840) * curve₅.Φ (3 : ℤ) ^ 6 * curve₅.ΨSq (3 : ℤ) ^ 2
      + (230) * curve₅.Φ (3 : ℤ) ^ 7 * curve₅.ΨSq (3 : ℤ) ^ 1
    -
    ((2168688647484219595638089925822170694290031227383133619284742688642641732001066070009565320788244100051915552891863040000000000000000000000000000000000000)
      + (639211986481380209355930372845013745871953518348038709054554246990120597970731595082915589329967175835431028956069888000000000000000000000000000000000000) * X
      + (13720340305019757873181129287658769610942151253193635469048447834099801008151408573676939058497542027226441727344640000000000000000000000000000000000000) * X ^ 2
      + (-6436387715131252482610614184475454278125464403812017978953699624499652206934650693739149098546428322898303816564736000000000000000000000000000000000000) * X ^ 3
      + (-412522762474487862493048137921437889525338825075361595218776576062388635664331791510059106508493961704527393959444480000000000000000000000000000000000) * X ^ 4
      + (1579720445348141250170391394556954147164867282757610070374375486780649428647788956315817604173925597821822440570880000000000000000000000000000000000) * X ^ 5
      + (550954102606124495494352053694038327008909141098283345718693752629776176377813633698624537152385991784417764311040000000000000000000000000000000000) * X ^ 6
      + (8567053878085963646551806629606707139195593827335482826318733149551623447739670494930639781640286516143720497152000000000000000000000000000000000) * X ^ 7) :=
  dvd_sub_add sum₅_6 term₅_7 ⟨0, by ring⟩

lemma sum₅_8 : ker₅ ∣
    (41943040000) * curve₅.Φ (3 : ℤ) ^ 0 * curve₅.ΨSq (3 : ℤ) ^ 8
      + (12615680000) * curve₅.Φ (3 : ℤ) ^ 1 * curve₅.ΨSq (3 : ℤ) ^ 7
      + (339968000) * curve₅.Φ (3 : ℤ) ^ 2 * curve₅.ΨSq (3 : ℤ) ^ 6
      + (-122880000) * curve₅.Φ (3 : ℤ) ^ 3 * curve₅.ΨSq (3 : ℤ) ^ 5
      + (-8729600) * curve₅.Φ (3 : ℤ) ^ 4 * curve₅.ΨSq (3 : ℤ) ^ 4
      + (-17600) * curve₅.Φ (3 : ℤ) ^ 5 * curve₅.ΨSq (3 : ℤ) ^ 3
      + (10840) * curve₅.Φ (3 : ℤ) ^ 6 * curve₅.ΨSq (3 : ℤ) ^ 2
      + (230) * curve₅.Φ (3 : ℤ) ^ 7 * curve₅.ΨSq (3 : ℤ) ^ 1
      + (1) * curve₅.Φ (3 : ℤ) ^ 8 * curve₅.ΨSq (3 : ℤ) ^ 0
    -
    (0) :=
  dvd_sub_add sum₅_7 term₅_8 ⟨0, by ring⟩

/-- **The stability divisibility at row 5**, assembled from the reduced terms. -/
lemma ker₅_dvd_multComp : ker₅ ∣
    ∑ i ∈ Finset.range (ker₅.natDegree + 1), C (ker₅.coeff i) *
      curve₅.Φ (3 : ℤ) ^ i * curve₅.ΨSq (3 : ℤ) ^
        (ker₅.natDegree - i) := by
  rw [ker₅_natDegree]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num only
  rw [ker₅_coeff_0, ker₅_coeff_1, ker₅_coeff_2, ker₅_coeff_3, ker₅_coeff_4, ker₅_coeff_5,
    ker₅_coeff_6, ker₅_coeff_7, ker₅_coeff_8]
  simpa using sum₅_8

/-- **The kernel-polynomial certificate at row 5.** -/
theorem curve₅_isKernelPolynomial : curve₅.IsKernelPolynomial 17 ker₅ 3 where
  monic := ker₅_monic
  natDegree_eq := ker₅_natDegree
  dvd_ΨSq := by
    rw [WeierstrassCurve.ΨSq_ofNat, if_neg (by decide), mul_one]
    exact dvd_pow ker₅_dvd_preΨ' (by norm_num)
  mult_ne_zero := by decide
  generates := by
    intro k hk
    obtain ⟨i, -, hi⟩ := generates_aux_17_3 k hk
    exact ⟨i, hi⟩
  dvd_multComp := ker₅_dvd_multComp


/-! #### Row 6: `p = 19`, `j₀ = -884736`, model `[0, 0, 1, -38, 90]`, multiplier `m = 2` -/

/-- The minimal twist of conductor-level model at row 6 of `genusOneJTable`: `[a₁, a₂, a₃, a₄, a₆] = [0, 0, 1, -38, 90]`. -/
noncomputable def curve₆ : WeierstrassCurve ℚ := ⟨0, 0, 1, -38, 90⟩

lemma curve₆_Δ : curve₆.Δ = -6859 := by
  norm_num [curve₆, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

lemma curve₆_c₄ : curve₆.c₄ = 1824 := by
  norm_num [curve₆, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]

noncomputable instance : curve₆.IsElliptic :=
  ⟨by rw [curve₆_Δ]; exact isUnit_iff_ne_zero.mpr (by norm_num)⟩

lemma curve₆_j : curve₆.j = (-884736 : ℚ) :=
  j_eq_of_Δ_c₄ curve₆ curve₆_Δ curve₆_c₄ (by norm_num) (by norm_num)

/-- The kernel polynomial at row 6, monic of degree `(p-1)/2 = 9`. -/
noncomputable def ker₆ : ℚ[X] :=
  (-130321) + (-130321) * X + (390963) * X ^ 2 + (-274360) * X ^ 3 + (82308) * X ^ 4
    + (-7942) * X ^ 5 + (-1444) * X ^ 6 + (437) * X ^ 7 + (-38) * X ^ 8 + X ^ 9

lemma curve₆_Ψ₂Sq : curve₆.Ψ₂Sq =
    (361) + (-152) * X + (4) * X ^ 3
    := by
  simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, curve₆]
  norm_num [Polynomial.C_eq_natCast, map_ofNat]
  ring

lemma curve₆_Ψ₃ : curve₆.Ψ₃ =
    (-1444) + (1083) * X + (-228) * X ^ 2 + (3) * X ^ 4
    := by
  simp only [WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, curve₆]
  norm_num [Polynomial.C_eq_natCast, map_ofNat]
  ring

lemma curve₆_preΨ₄ : curve₆.preΨ₄ =
    (-20577) + (27436) * X + (-14440) * X ^ 2 + (3610) * X ^ 3 + (-380) * X ^ 4 + (2) * X ^ 6
    := by
  simp only [WeierstrassCurve.preΨ₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, curve₆]
  norm_num [Polynomial.C_eq_natCast, map_ofNat]
  ring

/-! ##### The chain of remainders modulo `ker₆`

`preΨ'ₙ ≡ rₙ (mod ker₆)` for `n = 1, …, 19`, each `rₙ` of degree `< 9`; the chain ends
at `r_19 = 0`, which is exactly `ker₆ ∣ preΨ'_19`.  Every step is one application of a
`step_preΨ'_*` lemma against an explicit cofactor. -/

lemma pre₆_1 : ker₆ ∣ curve₆.preΨ' 1 - 1 := by simp

lemma pre₆_2 : ker₆ ∣ curve₆.preΨ' 2 - 1 := by simp

lemma pre₆_3 : ker₆ ∣ curve₆.preΨ' 3 -
    ((-1444) + (1083) * X + (-228) * X ^ 2 + (3) * X ^ 4) := by
  rw [WeierstrassCurve.preΨ'_three, curve₆_Ψ₃]
  exact ⟨
    0
    , by rw [ker₆]; ring⟩

lemma pre₆_4 : ker₆ ∣ curve₆.preΨ' 4 -
    ((-20577) + (27436) * X + (-14440) * X ^ 2 + (3610) * X ^ 3 + (-380) * X ^ 4 + (2) * X ^ 6) := by
  rw [WeierstrassCurve.preΨ'_four, curve₆_preΨ₄]
  exact ⟨
    0
    , by rw [ker₆]; ring⟩

lemma pre₆_5 : ker₆ ∣ curve₆.preΨ' 5 -
    ((8185983294) + (7264874466) * X + (-22057089892) * X ^ 2 + (14738392853) * X ^ 3
      + (-3967101561) * X ^ 4 + (217766391) * X ^ 5 + (108571111) * X ^ 6 + (-22202583) * X ^ 7
      + (1282633) * X ^ 8) :=
  step_preΨ'_odd_even curve₆ 0 5 (by decide) (by norm_num)
    pre₆_1 pre₆_2 pre₆_3 pre₆_4
    (by rw [curve₆_Ψ₂Sq]; exact ⟨
      (60287) + (2679) * X + (190) * X ^ 2 + (5) * X ^ 3
      , by rw [ker₆]; ring⟩)

lemma pre₆_6 : ker₆ ∣ curve₆.preΨ' 6 -
    ((579937727161027) + (607931108411290) * X + (-1709113156607126) * X ^ 2
      + (1135958739798084) * X ^ 3 + (-309555028281374) * X ^ 4 + (19609277846976) * X ^ 5
      + (7567778132769) * X ^ 6 + (-1607809924905) * X ^ 7 + (93748757128) * X ^ 8) :=
  step_preΨ'_even curve₆ 0 6 (by norm_num)
    pre₆_1 pre₆_2 pre₆_3 pre₆_4 pre₆_5
    (⟨
      (4536083047) + (157290588) * X + (20817065) * X ^ 2 + (938239) * X ^ 3 + (-116964) * X ^ 4
        + (-6612) * X ^ 5 + (-456) * X ^ 6 + (-12) * X ^ 7
      , by rw [ker₆]; ring⟩)

lemma pre₆_7 : ker₆ ∣ curve₆.preΨ' 7 -
    ((25436728793498981763194928) + (26653827446887275938034235) * X
      + (-75034838279672197570657197) * X ^ 2 + (49960743282567452732775762) * X ^ 3
      + (-13674812850314044628283864) * X ^ 4 + (895877011618768071204280) * X ^ 5
      + (324701773102105744290590) * X ^ 6 + (-69757142686251141609779) * X ^ 7
      + (4079030273542207017989) * X ^ 8) :=
  step_preΨ'_odd_odd curve₆ 1 7 (by decide) (by norm_num)
    pre₆_2 pre₆_3 pre₆_4 pre₆_5
    (by rw [curve₆_Ψ₂Sq]; exact ⟨
      (195185367711599565711) + (9338840681658448336) * X + (447331950653974240) * X ^ 2
        + (21185709317903294) * X ^ 3 + (1077516306114308) * X ^ 4 + (42394766734004) * X ^ 5
        + (1871644528763) * X ^ 6 + (347839520458) * X ^ 7 + (-10904609675) * X ^ 8
        + (-1709317672) * X ^ 9 + (234077093) * X ^ 10 + (9771187) * X ^ 11 + (-531392) * X ^ 12
        + (-46208) * X ^ 13 + (-4864) * X ^ 14 + (-128) * X ^ 15
      , by rw [ker₆]; ring⟩)

lemma pre₆_8 : ker₆ ∣ curve₆.preΨ' 8 -
    ((606777062331820276571028648367579) + (635811436767863095088765676794028) * X
      + (-1789907497299659777265906360623634) * X ^ 2
      + (1191778063486321207823322798551844) * X ^ 3
      + (-326200907301804457544419545583786) * X ^ 4 + (21369380870375693491002404705622) * X ^ 5
      + (7745804118104947143888376740768) * X ^ 6 + (-1664039208478484783743224596650) * X ^ 7
      + (97303850052373912825493929082) * X ^ 8) :=
  step_preΨ'_even curve₆ 1 8 (by norm_num)
    pre₆_2 pre₆_3 pre₆_4 pre₆_5 pre₆_6
    (⟨
      (4656019258873598389975735831) + (222790693027389334580253349) * X
        + (10661403671105051990423621) * X ^ 2 + (509576719711666942409264) * X ^ 3
        + (24668283269774227001059) * X ^ 4 + (1085952979774708258233) * X ^ 5
        + (71646335690904261151) * X ^ 6 + (1491011236701592985) * X ^ 7
        + (-91965444371124920) * X ^ 8 + (77845866987976798) * X ^ 9
        + (-7638189632842936) * X ^ 10 + (256163202676254) * X ^ 11 + (24063430427054) * X ^ 12
        + (-1602817197074) * X ^ 13
      , by rw [ker₆]; ring⟩)

lemma pre₆_9 : ker₆ ∣ curve₆.preΨ' 9 -
    ((10383920633658107984735216164318480348818304972)
      + (10880794070031784577290422052190380942873368531) * X
      + (-30631112935152311247388921921360540343746485252) * X ^ 2
      + (20395178430455176651291957147520741948606095164) * X ^ 3
      + (-5582350808782954803995711193804163248356656647) * X ^ 4
      + (365698097863005399424885369178885257577200548) * X ^ 5
      + (132556046220434759536110682428587574196289826) * X ^ 6
      + (-28477127078885538236358462570095505437398293) * X ^ 7
      + (1665185181705830274861033960257730380879202) * X ^ 8) :=
  step_preΨ'_odd_even curve₆ 2 9 (by decide) (by norm_num)
    pre₆_3 pre₆_4 pre₆_5 pre₆_6
    (by rw [curve₆_Ψ₂Sq]; exact ⟨
      (79679565332202594855935852453281357575247)
        + (3812688947827266637624528546881727162586) * X
        + (182438206119908404421811407151412425265) * X ^ 2
        + (8729717947224582299548282270969036611) * X ^ 3
        + (417719394772734815043147831396088123) * X ^ 4
        + (19988033640345843110171759848433288) * X ^ 5
        + (956376384654303979270840144782010) * X ^ 6
        + (45795498433821514046172268691007) * X ^ 7 + (2180637288517626052349588405385) * X ^ 8
        + (105901135598142719433247487374) * X ^ 9 + (5310341275112635579073568101) * X ^ 10
        + (81238723200952660696382006) * X ^ 11 + (39945030487708845545970198) * X ^ 12
        + (-185031032499573863618198) * X ^ 13 + (-632769829314267943816995) * X ^ 14
        + (128584137621722043335047) * X ^ 15 + (-7824561271306688673758) * X ^ 16
        + (-457061615569267728727) * X ^ 17 + (97009911941442039389) * X ^ 18
        + (-4448704937645647115) * X ^ 19 + (14843318939953280) * X ^ 20
        + (-2519769304372864) * X ^ 21 + (250194284282752) * X ^ 22 + (11999840912384) * X ^ 23
      , by rw [ker₆]; ring⟩)

lemma pre₆_10 : ker₆ ∣ curve₆.preΨ' 10 -
    ((141039570547142029840436954527414166892996352637114471369)
      + (147788352485662386640629840057780383805502620354177367494) * X
      + (-416046998645504900760130563950631403089531562452509899965) * X ^ 2
      + (277017449259255122458825632258146911123145784100278156999) * X ^ 3
      + (-75822262961958439211430861807078149996676860224523433068) * X ^ 4
      + (4967093311768189167525244363588178118944868005639177139) * X ^ 5
      + (1800442095055073092537603651049037900228509373706389191) * X ^ 6
      + (-386790492151476966459854918107217558456095086250965034) * X ^ 7
      + (22617372680289862000345299628638626649774743455262235) * X ^ 8) :=
  step_preΨ'_even curve₆ 2 10 (by norm_num)
    pre₆_3 pre₆_4 pre₆_5 pre₆_6 pre₆_7
    (⟨
      (1082247454723719809198059150826941749022513318231457)
        + (51785836040761616121932781139944204368756538847885) * X
        + (2477966387592923430098103982171514633966460580767) * X ^ 2
        + (118571361309714242725208213509426918811609777281) * X ^ 3
        + (5673681690566374738313418812766871891368673330) * X ^ 4
        + (271478600294750556059527353190791832142566245) * X ^ 5
        + (12995560128365336140460512470506837715322615) * X ^ 6
        + (619563352797054713216931952588323516214111) * X ^ 7
        + (30360173185631192402897976038125187844140) * X ^ 8
        + (1298272507913866706106777549029297752699) * X ^ 9
        + (81111667491075368125823046195060285698) * X ^ 10
        + (4380006506373560555751157140110182039) * X ^ 11
        + (-581037641619668781288787258811995542) * X ^ 12
        + (155602099602538438407002258083895626) * X ^ 13
        + (-16194197366801372404914631774131272) * X ^ 14
        + (877902701287559951439785215442235) * X ^ 15
        + (30827994654419392401625895512617) * X ^ 16
        + (-8120941461958868301033342348999) * X ^ 17 + (535386450980585309927879846576) * X ^ 18
        + (-12890932754643310176432845068) * X ^ 19
      , by rw [ker₆]; ring⟩)

lemma pre₆_11 : ker₆ ∣ curve₆.preΨ' 11 -
    ((1726127234007669430279269325475164914804629995191550044779794532164264780)
      + (1808722893191690096357738706336358414597452019256696089281648710415254420) * X
      + (-5091833818007795027030833988718295292627193082368438296442577641108438930) * X ^ 2
      + (3390306433910905352874332344293148541655606122248863511877510479928935875) * X ^ 3
      + (-927958533447163738206487106233756025437290105206382188402401586045752191) * X ^ 4
      + (60790280388142845654421502286429473087721021212169921135747650767341623) * X ^ 5
      + (22034895040128181696880712448929352111552709554855912663834262067816058) * X ^ 6
      + (-4733775065862601429956190310863561792787721767945057571301800577653939) * X ^ 7
      + (276805032755108879637650885493718518627486659546620060534862636309057) * X ^ 8) :=
  step_preΨ'_odd_odd curve₆ 3 11 (by decide) (by norm_num)
    pre₆_4 pre₆_5 pre₆_6 pre₆_7
    (by rw [curve₆_Ψ₂Sq]; exact ⟨
      (13245196353677990621642117958436119331453376857909177840467776908177)
        + (633786259958261740451736376399517389706949166010162139538986974801) * X
        + (30326845490693591872417584204811319160830628904169006195638339358) * X ^ 2
        + (1451147832516087170534178473574509897491864139807087480428108962) * X ^ 3
        + (69437819781951248335137918910328480581160493924309717443203191) * X ^ 4
        + (3322618626216345885551664724679221877723048670006228977885112) * X ^ 5
        + (158988210809492936863575092399120035739361918330977685297364) * X ^ 6
        + (7607624218635367612432455242414297204491031125746482320203) * X ^ 7
        + (364031144467901106143339820742391046473342312342699165613) * X ^ 8
        + (17416769483506967081477825529920254561655679869031694325) * X ^ 9
        + (834135009536689491997935332577780818056116536122516116) * X ^ 10
        + (39783791518951607974492737344176268427697042234751078) * X ^ 11
        + (1896723354199572611018547920248527864796492144504624) * X ^ 12
        + (101761864811203130856537125441877654227085006786863) * X ^ 13
        + (1872581585349621028498858914332454901318713849302) * X ^ 14
        + (405299869767434035323213832198080532935441097154) * X ^ 15
        + (55490209927784750080015570341497882950294327601) * X ^ 16
        + (-15031765889386080702570498955224487752174040188) * X ^ 17
        + (1842786601980169319262826385687976384130369548) * X ^ 18
        + (-2920290464405514648341607958822887753072087) * X ^ 19
        + (-27819972224729249397489437673157101204299316) * X ^ 20
        + (3998272150911118038705520114170581283199928) * X ^ 21
        + (-275436100751041071499977222756243649524630) * X ^ 22
        + (9785614712137979896172620140214796466781) * X ^ 23
        + (-181040988659562395098617889478294375648) * X ^ 24
        + (2361420156066905054703690256906917120) * X ^ 25
        + (354640378997361209047964464354777088) * X ^ 26
        + (-26366138840652515838570583109156864) * X ^ 27
      , by rw [ker₆]; ring⟩)

lemma pre₆_19 : ker₆ ∣ curve₆.preΨ' 19 -
    (0) :=
  step_preΨ'_odd_odd curve₆ 7 19 (by decide) (by norm_num)
    pre₆_8 pre₆_9 pre₆_10 pre₆_11
    (by rw [curve₆_Ψ₂Sq]; exact ⟨
      (-14828343055858681140432092585150064013737540441666505714738401056136172041101070032577435054182079297102421510426189808746714473709790061940630820154508613433444084658107597336224133182336866783448861980829)
        + (-47324623784856075542625060672009838923642550757677437793675593802768930598175673660478453120737150678157884415495357111870510337930702977926606657633452071176291839310889132019316768376885661035744667052385) * X
        + (80111784949313247057963851680952825122003311738570041327949265207379877891461407501311126641663330002766163539740447752556281655841007589047581372693854322401230905544451869884387953897776905060191940338615) * X ^ 2
        + (174415808776689262593799088453147481772075308408546964633097560052508083291194374673649050608997182404082699263792650160756209897526077450597015251921811256710983984424788918390849987219884167535877449087489) * X ^ 3
        + (-393844002750671186307489297957308421609580576525102248044060680621162292202698593840306695876675999339241893978119594413205776927404836551142138470014499934703407191817787242612880149149270221100993030700695) * X ^ 4
        + (43591203229894942012412502993173359178073606697914345313257912045353891506538712246389550347223756610320365529485908486812770557095927792140804732411403077178858952740326969034905553373379876796277831832837) * X ^ 5
        + (632574016168655324655275228549901049300668843224803721390359560647246895585531171738757763897805614571420850651833970769646307734045870292078466997656708646538717549869316658849750043483255792568000029228824) * X ^ 6
        + (-957234569171299455667720010739503258564779413065681377752186069003977557811853894156464185233630355162721806383793770981284777768731755550557463054867948769471173349614223079567017348110955267706724772158798) * X ^ 7
        + (760505209934051207519651774319744617499307470526281728053053372770517245792875531404154487452763152994558976870725849864092091576681600492683675742150498975431182029167087801687294071515786872922305556930624) * X ^ 8
        + (-384176762725674290327157754027158252062303886945207786769906380652588540178091376065060542132983939748161062882565629226062558655869996456315130296009484737267767089133211926128796966229911148214061049326917) * X ^ 9
        + (124700657533816524349623038029112068321800624818692041102829619871109900881608335336377716110234222129339371850538312618892063327012984868070205586801536913565137718459001241702600203558774591798525145589699) * X ^ 10
        + (-21707209834918823081377530349316520680796496994287746648450445602882846221578493399184476407253967040200246896030124010417245196037080028739966271708966683097017713689957008913552727577264508415307785172321) * X ^ 11
        + (-934516499484889966471684558301252921353147642463641051435435788829809841884205474253958893926743817944690726700655934750069680080013946536902532811870197188634798889858626351921554372042351131867653911564) * X ^ 12
        + (1663417650111115827089966374380490320930797570964872343138247428642008055974758510450382274184424423627889604341092928054687122376235451082801041156573163807443067252970937487822921467232520057491046422054) * X ^ 13
        + (-442571739623557266396695270404037207884780347217182671220172321600554650895541609721355560155314538316985070240581787803759237697224218880583055733867707038253834639838785320982111108593772921953121665728) * X ^ 14
        + (44323102500634732418481047987552894833634552117423402401038326782612939131945009613385424483038117356497771926789731690072341575899863086759319323980077204997699508223909671293591697263247903431101298099) * X ^ 15
        + (5337972147243474320820506713041513962301895634049981042572266784650261921646836127758217256451277072288983643107870200188994874402285092597729303299823283018234261296949748806998791456405923206794211879) * X ^ 16
        + (-2381841049626983650403412421010563006223645608066941581953414246138201324777215111865848325719306805486835908154160667596491157268308915790404251011620557000427089442473996088494686117522397877143321969) * X ^ 17
        + (312977548135857899221439620304622590452147146243368887415009626281662583288968025846013687709245244141593965674076294182638109576159104073453015393867081354904506930791031686344708285319890111208981733) * X ^ 18
        + (-6488881226064977141017681139474014026259709841269838218810958704972665486737013503994685324192140655799630908450232772923333646825154109667830315809621230609923909510262063146867815859058092903975193) * X ^ 19
        + (-3744226140716856417536736775470831271072228001341413676289760762037431013534343065533914049534435265445167195370861575783762285625571614554008120026916722899633925804644490899726228915128118243824119) * X ^ 20
        + (581137006183833829456883413418564230047862327934575892564572664945739892673353201357062788231504836611890539148737356677054719013329721131250287005249829292226957375018062987211437623689635263794454) * X ^ 21
        + (-39835477556326028004285762682017087447781135020754739078704231769665046463518848663926450808743170398177304474155956013769324414879195566376687985158512459227903735239855510694208910051051424217566) * X ^ 22
        + (1231780229816206514733667956811698478580118520109539165711015764086644287001011676476271874375038178796418971664295752361333649286157570294482713114651126814293743449362680044068853540855171814490) * X ^ 23
        + (-12180877138949977774532942908132508811526490650379611220821971380377450249704375994427144466066180407206785693142499151098837356601718490715094603331210794582839634023396304633404049049330266528) * X ^ 24
        + (644971813719885592032645317364369541574369946457694354760214146669407289596474301507559842587509281096483401123619520474904936527577918593867609233001959929121691755833933163029759496913679568) * X ^ 25
        + (-498307455305898440079447424383073202376366343255119582956844211119255100033716134846554207793478070996730036490421899490201932510571500131483990621524231810484067446386048809010524605312752) * X ^ 26
        + (-7290709380684121945606294281268863110912002566797062113565012335169508086713790123654490376648299576175989176669949964139693535771885676823910369102845051169892900514568172313900646136740160) * X ^ 27
        + (547689508570584987814658885639067084657163118376399952630809457692804645944826756565277709531597935559213964355875706703077974296915183182701105347037239063660562386435887835671787101954400) * X ^ 28
        + (-18012602692773615838744800902137854118806110408798696898845024698126516523137024913773050957215265219297026695594604934399947244568828174868262024621495986664014880149561514174284588172000) * X ^ 29
      , by rw [ker₆]; ring⟩)

lemma ker₆_dvd_preΨ' : ker₆ ∣ curve₆.preΨ' 19 := by
  simpa using pre₆_19

lemma ker₆_coeff_0 : C (ker₆.coeff 0) = (-130321 : ℚ[X]) := by
  rw [ker₆]; simp [Polynomial.coeff_X, map_ofNat]

lemma ker₆_coeff_1 : C (ker₆.coeff 1) = (-130321 : ℚ[X]) := by
  rw [ker₆]; simp [Polynomial.coeff_X, map_ofNat]

lemma ker₆_coeff_2 : C (ker₆.coeff 2) = (390963 : ℚ[X]) := by
  rw [ker₆]; simp [Polynomial.coeff_X, map_ofNat]

lemma ker₆_coeff_3 : C (ker₆.coeff 3) = (-274360 : ℚ[X]) := by
  rw [ker₆]; simp [Polynomial.coeff_X, map_ofNat]

lemma ker₆_coeff_4 : C (ker₆.coeff 4) = (82308 : ℚ[X]) := by
  rw [ker₆]; simp [Polynomial.coeff_X, map_ofNat]

lemma ker₆_coeff_5 : C (ker₆.coeff 5) = (-7942 : ℚ[X]) := by
  rw [ker₆]; simp [Polynomial.coeff_X, map_ofNat]

lemma ker₆_coeff_6 : C (ker₆.coeff 6) = (-1444 : ℚ[X]) := by
  rw [ker₆]; simp [Polynomial.coeff_X, map_ofNat]

lemma ker₆_coeff_7 : C (ker₆.coeff 7) = (437 : ℚ[X]) := by
  rw [ker₆]; simp [Polynomial.coeff_X, map_ofNat]

lemma ker₆_coeff_8 : C (ker₆.coeff 8) = (-38 : ℚ[X]) := by
  rw [ker₆]; simp [Polynomial.coeff_X, map_ofNat]

lemma ker₆_coeff_9 : C (ker₆.coeff 9) = (1 : ℚ[X]) := by
  rw [ker₆]; simp [Polynomial.coeff_X]

lemma ker₆_natDegree : ker₆.natDegree = 9 := by
  rw [ker₆]; compute_degree!

lemma ker₆_monic : ker₆.Monic := by
  rw [ker₆]; monicity!

lemma curve₆_Φ : curve₆.Φ (2 : ℤ) =
    (1444) + (-722) * X + (76) * X ^ 2 + X ^ 4
    := by
  rw [WeierstrassCurve.Φ_two, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, curve₆]
  norm_num [Polynomial.C_eq_natCast, map_ofNat]
  ring

lemma curve₆_ΨSq : curve₆.ΨSq (2 : ℤ) =
    (361) + (-152) * X + (4) * X ^ 3
    := by
  rw [WeierstrassCurve.ΨSq_two, curve₆_Ψ₂Sq]

/-! ##### The stability divisibility at row 6

The root set of `ker₆` is carried into itself by `x(P) ↦ x(2 ⬝ P)`, written
multiplied-out as a divisibility so that no rational function appears.  Every power
`Φ^i` and `ΨSq^j` is reduced modulo `ker₆` BEFORE being multiplied, so each `ring`
call below is an identity in degree `≤ 18` rather than the degree-`36` identity the
unreduced sum would need — which is what keeps this inside the default heartbeat
budget. -/

lemma phi₆_red : ker₆ ∣ curve₆.Φ (2 : ℤ) -
    ((1444) + (-722) * X + (76) * X ^ 2 + X ^ 4) := by
  rw [curve₆_Φ]
  exact ⟨
    0
    , by rw [ker₆]; ring⟩

lemma psi₆_red : ker₆ ∣ curve₆.ΨSq (2 : ℤ) -
    ((361) + (-152) * X + (4) * X ^ 3) := by
  rw [curve₆_ΨSq]
  exact ⟨
    0
    , by rw [ker₆]; ring⟩

lemma phi₆_pow_0 : ker₆ ∣ curve₆.Φ (2 : ℤ) ^ 0 - 1 := by simp

lemma phi₆_pow_1 : ker₆ ∣ curve₆.Φ (2 : ℤ) ^ 1 -
    ((1444) + (-722) * X + (76) * X ^ 2 + X ^ 4) := by
  rw [pow_one]; exact phi₆_red

lemma phi₆_pow_2 : ker₆ ∣ curve₆.Φ (2 : ℤ) ^ 2 -
    ((2085136) + (-2085136) * X + (740772) * X ^ 2 + (-109744) * X ^ 3 + (8664) * X ^ 4
      + (-1444) * X ^ 5 + (152) * X ^ 6 + X ^ 8) :=
  dvd_sub_pow_succ 1 phi₆_pow_1 phi₆_red ⟨
    0
    , by rw [ker₆]; ring⟩

lemma phi₆_pow_3 : ker₆ ∣ curve₆.Φ (2 : ℤ) ^ 3 -
    ((6868698626) + (-497695899) * X + (-8673774797) * X ^ 2 + (6792069878) * X ^ 3
      + (-1962243297) * X ^ 4 + (124717197) * X ^ 5 + (52361606) * X ^ 6 + (-11262478) * X ^ 7
      + (669655) * X ^ 8) :=
  dvd_sub_pow_succ 2 phi₆_pow_2 phi₆_red ⟨
    (29602) + (1235) * X + (38) * X ^ 2 + X ^ 3
    , by rw [ker₆]; ring⟩

lemma phi₆_pow_4 : ker₆ ∣ curve₆.Φ (2 : ℤ) ^ 4 -
    ((901232772770665) + (931199822820640) * X + (-2638174838228078) * X ^ 2
      + (1757729523206668) * X ^ 3 + (-480860607243219) * X ^ 4 + (31283846926472) * X ^ 5
      + (11496767838603) * X ^ 6 + (-2464213594479) * X ^ 7 + (144027120212) * X ^ 8) :=
  dvd_sub_pow_succ 3 phi₆_pow_3 phi₆_red ⟨
    (6839376401) + (349623807) * X + (14184412) * X ^ 2 + (669655) * X ^ 3
    , by rw [ker₆]; ring⟩

lemma phi₆_pow_5 : ker₆ ∣ curve₆.Φ (2 : ℤ) ^ 5 -
    ((188831087541307098209) + (197846314821781049016) * X + (-556987722341070314765) * X ^ 2
      + (370856025916652383546) * X ^ 3 + (-101502225214571623126) * X ^ 4
      + (6647006898137061180) * X ^ 5 + (2411009456662008840) * X ^ 6
      + (-517895728318026349) * X ^ 7 + (30282765548189800) * X ^ 8) :=
  dvd_sub_pow_succ 4 phi₆_pow_4 phi₆_red ⟨
    (1438983029729869) + (73838022437997) * X + (3008816973577) * X ^ 2 + (144027120212) * X ^ 3
    , by rw [ker₆]; ring⟩

lemma phi₆_pow_6 : ker₆ ∣ curve₆.Φ (2 : ℤ) ^ 6 -
    ((39711687374242457678493489) + (41611890443640325831765837) * X
      + (-117143835311025354385919098) * X ^ 2 + (77998060080413031364472207) * X ^ 3
      + (-21348750986317503860648284) * X ^ 4 + (1398527252054477170487426) * X ^ 5
      + (506945492284943074950279) * X ^ 6 + (-108906912155684945603457) * X ^ 7
      + (6368265884026049116804) * X ^ 8) :=
  dvd_sub_pow_succ 5 phi₆_pow_5 phi₆_red ⟨
    (302629777885627107133) + (15527206869266560978) * X + (632849362513186051) * X ^ 2
      + (30282765548189800) * X ^ 3
    , by rw [ker₆]; ring⟩

lemma phi₆_pow_7 : ker₆ ∣ curve₆.Φ (2 : ℤ) ^ 7 -
    ((8351278238461937416502450475933) + (8750889381215200196842898461432) * X
      + (-24635101936849024095285208810573) * X ^ 2 + (16402841129906477058825853368440) * X ^ 3
      + (-4489610360788940683425532960226) * X ^ 4 + (294112788016264818651832182783) * X ^ 5
      + (106608382516815361440895634980) * X ^ 6 + (-22902762808853928077999120874) * X ^ 7
      + (1339227046333894900880522259) * X ^ 8) :=
  dvd_sub_pow_succ 6 phi₆_pow_6 phi₆_red ⟨
    (63642348983613779111691177) + (3265314782769126335517645) * X
      + (133087191437304920835095) * X ^ 2 + (6368265884026049116804) * X ^ 3
    , by rw [ker₆]; ring⟩

lemma phi₆_pow_8 : ker₆ ∣ curve₆.Φ (2 : ℤ) ^ 8 -
    ((1756250313843125148270748544941499183) + (1840287373048002148029168788485479178) * X
      + (-5180692686232983813998394044303108408) * X ^ 2
      + (3449471514860599152949182598991732530) * X ^ 3
      + (-944152564451676663276779220630019872) * X ^ 4
      + (61851144372772364311551572674208301) * X ^ 5
      + (22419432037747064080490171005741255) * X ^ 6
      + (-4816385418088938557573345340150531) * X ^ 7
      + (281635629280221958760481531889861) * X ^ 8) :=
  dvd_sub_pow_succ 7 phi₆_pow_7 phi₆_red ⟨
    (13383806662523968590183615890411) + (686686286959974272130534648265) * X
      + (27987864951834078155460724968) * X ^ 2 + (1339227046333894900880522259) * X ^ 3
    , by rw [ker₆]; ring⟩

lemma phi₆_pow_9 : ker₆ ∣ curve₆.Φ (2 : ℤ) ^ 9 -
    ((369334450282238777641378691980949045682800)
      + (387007204538470227239371889247979534298794) * X
      + (-1089484950480243091819487615154016320730037) * X ^ 2
      + (725414058858510042140071454731892865942492) * X ^ 3
      + (-198552602600428153527121421465342085173457) * X ^ 4
      + (13007120394859415217499216830165009616039) * X ^ 5
      + (4714742745872479585651877880339550921534) * X ^ 6
      + (-1012872155747080824405772930544553831298) * X ^ 7
      + (59227172037320780330693762004293963028) * X ^ 8) :=
  dvd_sub_pow_succ 8 phi₆_pow_8 phi₆_red ⟨
    (2814576505928049239395613378366138388) + (144408172660847780230304547116740540) * X
      + (5885768494559495875324952871664187) * X ^ 2
      + (281635629280221958760481531889861) * X ^ 3
    , by rw [ker₆]; ring⟩

lemma psi₆_pow_0 : ker₆ ∣ curve₆.ΨSq (2 : ℤ) ^ 0 - 1 := by simp

lemma psi₆_pow_1 : ker₆ ∣ curve₆.ΨSq (2 : ℤ) ^ 1 -
    ((361) + (-152) * X + (4) * X ^ 3) := by
  rw [pow_one]; exact psi₆_red

lemma psi₆_pow_2 : ker₆ ∣ curve₆.ΨSq (2 : ℤ) ^ 2 -
    ((130321) + (-109744) * X + (23104) * X ^ 2 + (2888) * X ^ 3 + (-1216) * X ^ 4
      + (16) * X ^ 6) :=
  dvd_sub_pow_succ 1 psi₆_pow_1 psi₆_red ⟨
    0
    , by rw [ker₆]; ring⟩

lemma psi₆_pow_3 : ker₆ ∣ curve₆.ΨSq (2 : ℤ) ^ 3 -
    ((55386425) + (-51085832) * X + (15611084) * X ^ 3 + (-6584640) * X ^ 4 + (785536) * X ^ 5
      + (109744) * X ^ 6 + (-35264) * X ^ 7 + (2432) * X ^ 8) :=
  dvd_sub_pow_succ 2 psi₆_pow_2 psi₆_red ⟨
    (64)
    , by rw [ker₆]; ring⟩

lemma psi₆_pow_4 : ker₆ ∣ curve₆.ΨSq (2 : ℤ) ^ 4 -
    ((607127094305) + (590064296096) * X + (-1722572552320) * X ^ 2 + (1153816261008) * X ^ 3
      + (-316857266560) * X ^ 4 + (20918084352) * X ^ 5 + (7503197280) * X ^ 6
      + (-1617187584) * X ^ 7 + (94726400) * X ^ 8) :=
  dvd_sub_pow_succ 3 psi₆_pow_3 psi₆_red ⟨
    (4505280) + (228608) * X + (9728) * X ^ 2
    , by rw [ker₆]; ring⟩

lemma psi₆_pow_5 : ker₆ ∣ curve₆.ΨSq (2 : ℤ) ^ 5 -
    ((19944533735487497) + (20879492288970632) * X + (-58804840129055744) * X ^ 2
      + (39157037420377236) * X ^ 3 + (-10718083809098368) * X ^ 4 + (702204878544384) * X ^ 5
      + (254498342778784) * X ^ 6 + (-54676252700032) * X ^ 7 + (3197230774784) * X ^ 8) :=
  dvd_sub_pow_succ 4 psi₆_pow_4 psi₆_red ⟨
    (151359802752) + (7929662464) * X + (378905600) * X ^ 2
    , by rw [ker₆]; ring⟩

lemma psi₆_pow_6 : ker₆ ∣ curve₆.ΨSq (2 : ℤ) ^ 6 -
    ((671793998260459417393) + (703931372851684349424) * X + (-1981686205931943830080) * X ^ 2
      + (1319471507140457892568) * X ^ 3 + (-361151855280429075008) * X ^ 4
      + (23658975099622686976) * X ^ 5 + (8575749544102742256) * X ^ 6
      + (-1842336377538561792) * X ^ 7 + (107729686788211456) * X ^ 8) :=
  dvd_sub_pow_succ 5 psi₆_pow_5 psi₆_red ⟨
    (5099669443773056) + (267274066967040) * X + (12788923099136) * X ^ 2
    , by rw [ker₆]; ring⟩

lemma psi₆_pow_7 : ker₆ ∣ curve₆.ΨSq (2 : ℤ) ^ 7 -
    ((22635331986252371216969689) + (23718435372328230724729368) * X
      + (-66771057104024200686274048) * X ^ 2 + (44458314069363521134606172) * X ^ 3
      + (-12168655837451372602232768) * X ^ 4 + (797164942199468619469952) * X ^ 5
      + (288951545956992034372816) * X ^ 6 + (-62075704416704816953664) * X ^ 7
      + (3629844512023826948480) * X ^ 8) :=
  dvd_sub_pow_succ 6 psi₆_pow_6 psi₆_red ⟨
    (171828134781657180096) + (9005566881653894144) * X + (430918747152845824) * X ^ 2
    , by rw [ker₆]; ring⟩

lemma psi₆_pow_8 : ker₆ ∣ curve₆.ΨSq (2 : ℤ) ^ 8 -
    ((762674746226742617416214681665) + (799168939517069575539097784640) * X
      + (-2249783784633793399865996967168) * X ^ 2 + (1497978275342138340364657053472) * X ^ 3
      + (-410010643794291837107381248768) * X ^ 4 + (26859672177428731106174419456) * X ^ 5
      + (9735932345202638494220519872) * X ^ 6 + (-2091578548385250763523254784) * X ^ 7
      + (122303966825697761534854656) * X ^ 8) :=
  dvd_sub_pow_succ 7 psi₆_pow_7 psi₆_red ⟨
    (5789576441093189212842816) + (303433548160802428354304) * X
      + (14519378048095307793920) * X ^ 2
    , by rw [ker₆]; ring⟩

lemma psi₆_pow_9 : ker₆ ∣ curve₆.ΨSq (2 : ℤ) ^ 9 -
    ((25697559833840351981528345890632361) + (26927195083800385289660522343306152) * X
      + (-75804205867765430496735829481455616) * X ^ 2
      + (50472874028711816070682247475254564) * X ^ 3
      + (-13814896994004733440285573073294592) * X ^ 4
      + (905009686888588411459828092002304) * X ^ 5 + (328042465563666546203536815618112) * X ^ 6
      + (-70473639252771827795595844729600) * X ^ 7 + (4120909369441814967423971082240) * X ^ 8) :=
  dvd_sub_pow_succ 8 psi₆_pow_8 psi₆_red ⟨
    (195073965442656961630443998976) + (10223888763965056699204888576) * X
      + (489215867302791046139418624) * X ^ 2
    , by rw [ker₆]; ring⟩

lemma term₆_0 : ker₆ ∣
    (-130321) * curve₆.Φ (2 : ℤ) ^ 0 * curve₆.ΨSq (2 : ℤ) ^ 9
    -
    ((-3348931695105908510584755564813099917881)
      + (-3509178990515950011333848932302001034792) * X
      + (9878879912893058667765110033852777332736) * X ^ 2
      + (-6577675416295752582147381173222650035044) * X ^ 3
      + (1800371191155690866671456168484824524032) * X ^ 4
      + (-117941767405007730369856256777832259584) * X ^ 5
      + (-42750822154722587967791121348167973952) * X ^ 6
      + (9184195141060477370149846081006201600) * X ^ 7
      + (-537041029935026768369659335408599040) * X ^ 8) :=
  dvd_sub_const_mul₂ phi₆_pow_0 psi₆_pow_9 ⟨
    0
    , by rw [ker₆]; ring⟩

lemma term₆_1 : ker₆ ∣
    (-130321) * curve₆.Φ (2 : ℤ) ^ 1 * curve₆.ΨSq (2 : ℤ) ^ 8
    -
    ((-20901967648889556168544531617571440633700)
      + (-21902132504426736588309889550978574989518) * X
      + (61657879929035464122055518959835542719540) * X ^ 2
      + (-41053796038210665486696947137413107263040) * X ^ 3
      + (11236807382078953958015053886408640600815) * X ^ 4
      + (-736119823035061782681618677393130280640) * X ^ 5
      + (-266824283979973501606868473725757661824) * X ^ 6
      + (57322085726819096243443732010041823200) * X ^ 7
      + (-3351879123203747096710397326043728448) * X ^ 8) :=
  dvd_sub_const_mul₂ phi₆_pow_1 psi₆_pow_8 ⟨
    (-159287028395107481064127535577805440) + (-8172578942331984883992425570839488) * X
      + (-333096851902172538524270071028224) * X ^ 2
      + (-15938775260691757980983793624576) * X ^ 3
    , by rw [ker₆]; ring⟩

lemma term₆_2 : ker₆ ∣
    (390963) * curve₆.Φ (2 : ℤ) ^ 2 * curve₆.ΨSq (2 : ℤ) ^ 7
    -
    ((391371599696171964003983871110461713524388)
      + (410098837537602636472248578080937348552652) * X
      + (-1154491457795698557454784780608327686055668) * X ^ 2
      + (768697478582334103925280346673384180110332) * X ^ 3
      + (-210399678847672185725648796090459611982228) * X ^ 4
      + (13783218764333655732611742965016102627228) * X ^ 5
      + (4996058199564932639484969693308266459368) * X ^ 6
      + (-1073307392190192724746029143379542079580) * X ^ 7
      + (62761091035788197219587148353264590891) * X ^ 8) :=
  dvd_sub_const_mul₂ phi₆_pow_2 psi₆_pow_7 ⟨
    (3002993739489110158156956380457179316) + (143835663138095312611482933894019464) * X
      + (6832272874582618208790347208151380) * X ^ 2
      + (334378396667411120754496053336144) * X ^ 3 + (15411760014019434570849837630432) * X ^ 4
      + (835513174526109710054297853552) * X ^ 5 + (29657822572397949949170938688) * X ^ 6
      + (1419134899954371455258586240) * X ^ 7
    , by rw [ker₆]; ring⟩

lemma term₆_3 : ker₆ ∣
    (-274360) * curve₆.Φ (2 : ℤ) ^ 3 * curve₆.ΨSq (2 : ℤ) ^ 6
    -
    ((-1714175661536299140870995145521358198780720)
      + (-1796199434704474875996768469330398586184920) * X
      + (5056578351481659012353758542614163794405720) * X ^ 2
      + (-3366832212390995717985954479677048157387920) * X ^ 3
      + (921533419788654964181143150506443360152120) * X ^ 4
      + (-60369373152770701009568024450023449506200) * X ^ 5
      + (-21882327118213246004447132786998982189520) * X ^ 6
      + (4700998770658543659189521712569164101520) * X ^ 7
      + (-274888455955132978641165999935295547720) * X ^ 8) :=
  dvd_sub_const_mul₂ phi₆_pow_3 psi₆_pow_6 ⟨
    (-13153477916399447880500170701158261440) + (-629398211626989312548798357138607360) * X
      + (-30129143449342706880897618123920960) * X ^ 2
      + (-1432081740212748945102248045232000) * X ^ 3
      + (-71300695949925442520829349496320) * X ^ 4 + (-3235370431481355376618468599680) * X ^ 5
      + (-80758550565063678545131448320) * X ^ 6 + (-19792803233713986970868684800) * X ^ 7
    , by rw [ker₆]; ring⟩

lemma term₆_4 : ker₆ ∣
    (82308) * curve₆.Φ (2 : ℤ) ^ 4 * curve₆.ΨSq (2 : ℤ) ^ 5
    -
    ((3209648402894364268272607749832266107728212)
      + (3363230954828379020284760491104864241620864) * X
      + (-9468013689691534941266090015159629926812184) * X ^ 2
      + (6304107493649725447266913774815845528653584) * X ^ 3
      + (-1725493095841035146335380216032962318647468) * X ^ 4
      + (113036526227088424523793775576418805658752) * X ^ 5
      + (40972799849361405033809662214042646803436) * X ^ 6
      + (-8802221111199365412263394827742537985596) * X ^ 7
      + (514705297379538895490679034223479611840) * X ^ 8) :=
  dvd_sub_const_mul₂ phi₆_pow_4 psi₆_pow_5 ⟨
    (24628777583316860770839404299175484432) + (1178482009249144981570439082969976272) * X
      + (56423901390433814351177207837953728) * X ^ 2
      + (2677766940356102196536394623471232) * X ^ 3
      + (134186796811746250035798405655680) * X ^ 4 + (6026916086000734588813054927872) * X ^ 5
      + (143629024118977794846413647872) * X ^ 6 + (37901841459789086327835992064) * X ^ 7
    , by rw [ker₆]; ring⟩

lemma term₆_5 : ker₆ ∣
    (-7942) * curve₆.Φ (2 : ℤ) ^ 5 * curve₆.ΨSq (2 : ℤ) ^ 4
    -
    ((-1932974728000416328727265254478065091057030)
      + (-2025468096213056818586335762429176027510832) * X
      + (5702004982864853061023559914838514020991406) * X ^ 2
      + (-3796577985562324363342138655618308852212828) * X ^ 3
      + (1039158851352252263749390718552144636850052) * X ^ 4
      + (-68074979283965047169111775139994046359496) * X ^ 5
      + (-24675408862016892677464215792990549399728) * X ^ 6
      + (5301038874829916551780186124344579242766) * X ^ 7
      + (-309975488688446342875451353330884077520) * X ^ 8) :=
  dvd_sub_const_mul₂ phi₆_pow_5 psi₆_pow_4 ⟨
    (-14832404735184963375740992299859821440) + (-709727824568788463557873028104264864) * X
      + (-33980491613863475502375948871084608) * X ^ 2
      + (-1612699058034801553434586430064768) * X ^ 3
      + (-80813942589215755018917573443776) * X ^ 4 + (-3626364548060298088682596687872) * X ^ 5
      + (-87160506690460244251477414400) * X ^ 6 + (-22782241412371775482058240000) * X ^ 7
    , by rw [ker₆]; ring⟩

lemma term₆_6 : ker₆ ∣
    (-1444) * curve₆.Φ (2 : ℤ) ^ 6 * curve₆.ΨSq (2 : ℤ) ^ 3
    -
    ((-2193533987933668196180260544191650504115252)
      + (-2298495187841457579349155421773393817683732) * X
      + (6470618341824683577885355800632019807139144) * X ^ 2
      + (-4308345436970218911836349687379820573921980) * X ^ 3
      + (1179234382256661049584436253044533440458016) * X ^ 4
      + (-77251284571524773926246200103962250388744) * X ^ 5
      + (-28001580787371315435231787313202589555148) * X ^ 6
      + (6015603191792058444166349194588693302868) * X ^ 7
      + (-351759265147209052745383851976823591776) * X ^ 8) :=
  dvd_sub_const_mul₂ phi₆_pow_6 psi₆_pow_3 ⟨
    (-16831752456414750622677397282802064112) + (-805426426921064949350003017856260752) * X
      + (-38539874331102903472852666935789696) * X ^ 2
      + (-1837274335706135106930931340905152) * X ^ 3
      + (-90811437285530550458744221213760) * X ^ 4 + (-3999704531112089608911533258752) * X ^ 5
      + (-143096820961137522724667588096) * X ^ 6 + (-22364127077649751496785221632) * X ^ 7
    , by rw [ker₆]; ring⟩

lemma term₆_7 : ker₆ ∣
    (437) * curve₆.Φ (2 : ℤ) ^ 7 * curve₆.ΨSq (2 : ℤ) ^ 2
    -
    ((4143234298662807313146711878183572953987289)
      + (4341489190504980066387998482466212161772096) * X
      + (-12221961453460743309434651537831659982150849) * X ^ 2
      + (8137774332664017439636156011112445538432888) * X ^ 3
      + (-2227384834478737036089809497806157826240274) * X ^ 4
      + (145915300869509405952356274138613485880771) * X ^ 5
      + (52890500252406085028123648532082515183108) * X ^ 6
      + (-11362510728935769253371829691496832375146) * X ^ 7
      + (664416899980810578419110338365059400167) * X ^ 8) :=
  dvd_sub_const_mul₂ phi₆_pow_7 psi₆_pow_2 ⟨
    (31788880464804773089194261855401583688) + (1524179875443132269557792216509997648) * X
      + (72285418765337409779319013181885320) * X ^ 2
      + (3378001441213217952399293292159824) * X ^ 3
      + (195691151743223874462981388976256) * X ^ 4 + (9363875507966593146956611634928) * X ^ 5
    , by rw [ker₆]; ring⟩

lemma term₆_8 : ker₆ ∣
    (-38) * curve₆.Φ (2 : ℤ) ^ 8 * curve₆.ΨSq (2 : ℤ) ^ 1
    -
    ((-2248653474721203192607031959733791486418106)
      + (-2356252157155499989852476048883744278840612) * X
      + (6633213115415095725922519061675247973160192) * X ^ 2
      + (-4416606257376541621735134436347754772318484) * X ^ 3
      + (1208866379797069599338303299236906939458392) * X ^ 4
      + (-79192467657090309808283534882062694988126) * X ^ 5
      + (-28705209173468752080352362831506932587274) * X ^ 6
      + (6166764269924009986037375983569981599666) * X ^ 7
      + (-360598330489531303332989021041642021422) * X ^ 8) :=
  dvd_sub_const_mul₂ phi₆_pow_8 psi₆_pow_1 ⟨
    (-17069860060281176493604667177157050672) + (-894636811173043373049392836492956424) * X
      + (-42808615650593737731593192847258872) * X ^ 2
    , by rw [ker₆]; ring⟩

lemma term₆_9 : ker₆ ∣
    (1) * curve₆.Φ (2 : ℤ) ^ 9 * curve₆.ΨSq (2 : ℤ) ^ 0
    -
    ((369334450282238777641378691980949045682800)
      + (387007204538470227239371889247979534298794) * X
      + (-1089484950480243091819487615154016320730037) * X ^ 2
      + (725414058858510042140071454731892865942492) * X ^ 3
      + (-198552602600428153527121421465342085173457) * X ^ 4
      + (13007120394859415217499216830165009616039) * X ^ 5
      + (4714742745872479585651877880339550921534) * X ^ 6
      + (-1012872155747080824405772930544553831298) * X ^ 7
      + (59227172037320780330693762004293963028) * X ^ 8) :=
  dvd_sub_const_mul₂ phi₆_pow_9 psi₆_pow_0 ⟨
    0
    , by rw [ker₆]; ring⟩

lemma sum₆_1 : ker₆ ∣
    (-130321) * curve₆.Φ (2 : ℤ) ^ 0 * curve₆.ΨSq (2 : ℤ) ^ 9
      + (-130321) * curve₆.Φ (2 : ℤ) ^ 1 * curve₆.ΨSq (2 : ℤ) ^ 8
    -
    ((-24250899343995464679129287182384540551581)
      + (-25411311494942686599643738483280576024310) * X
      + (71536759841928522789820628993688320052276) * X ^ 2
      + (-47631471454506418068844328310635757298084) * X ^ 3
      + (13037178573234644824686510054893465124847) * X ^ 4
      + (-854061590440069513051474934170962540224) * X ^ 5
      + (-309575106134696089574659595073925635776) * X ^ 6
      + (66506280867879573613593578091048024800) * X ^ 7
      + (-3888920153138773865080056661452327488) * X ^ 8) :=
  dvd_sub_add term₆_0 term₆_1 ⟨0, by ring⟩

lemma sum₆_2 : ker₆ ∣
    (-130321) * curve₆.Φ (2 : ℤ) ^ 0 * curve₆.ΨSq (2 : ℤ) ^ 9
      + (-130321) * curve₆.Φ (2 : ℤ) ^ 1 * curve₆.ΨSq (2 : ℤ) ^ 8
      + (390963) * curve₆.Φ (2 : ℤ) ^ 2 * curve₆.ΨSq (2 : ℤ) ^ 7
    -
    ((367120700352176499324854583928077172972807)
      + (384687526042659949872604839597656772528342) * X
      + (-1082954697953770034664964151614639366003392) * X ^ 2
      + (721066007127827685856436018362748422812248) * X ^ 3
      + (-197362500274437540900962286035566146857381) * X ^ 4
      + (12929157173893586219560268030845140087004) * X ^ 5
      + (4686483093430236549910310098234340823592) * X ^ 6
      + (-1006801111322313151132435565288494054780) * X ^ 7
      + (58872170882649423354507091691812263403) * X ^ 8) :=
  dvd_sub_add sum₆_1 term₆_2 ⟨0, by ring⟩

lemma sum₆_3 : ker₆ ∣
    (-130321) * curve₆.Φ (2 : ℤ) ^ 0 * curve₆.ΨSq (2 : ℤ) ^ 9
      + (-130321) * curve₆.Φ (2 : ℤ) ^ 1 * curve₆.ΨSq (2 : ℤ) ^ 8
      + (390963) * curve₆.Φ (2 : ℤ) ^ 2 * curve₆.ΨSq (2 : ℤ) ^ 7
      + (-274360) * curve₆.Φ (2 : ℤ) ^ 3 * curve₆.ΨSq (2 : ℤ) ^ 6
    -
    ((-1347054961184122641546140561593281025807913)
      + (-1411511908661814926124163629732741813656578) * X
      + (3973623653527888977688794390999524428402328) * X ^ 2
      + (-2645766205263168032129518461314299734575672) * X ^ 3
      + (724170919514217423280180864470877213294739) * X ^ 4
      + (-47440215978877114790007756419178309419196) * X ^ 5
      + (-17195844024783009454536822688764641365928) * X ^ 6
      + (3694197659336230508057086147280670046740) * X ^ 7
      + (-216016285072483555286658908243483284317) * X ^ 8) :=
  dvd_sub_add sum₆_2 term₆_3 ⟨0, by ring⟩

lemma sum₆_4 : ker₆ ∣
    (-130321) * curve₆.Φ (2 : ℤ) ^ 0 * curve₆.ΨSq (2 : ℤ) ^ 9
      + (-130321) * curve₆.Φ (2 : ℤ) ^ 1 * curve₆.ΨSq (2 : ℤ) ^ 8
      + (390963) * curve₆.Φ (2 : ℤ) ^ 2 * curve₆.ΨSq (2 : ℤ) ^ 7
      + (-274360) * curve₆.Φ (2 : ℤ) ^ 3 * curve₆.ΨSq (2 : ℤ) ^ 6
      + (82308) * curve₆.Φ (2 : ℤ) ^ 4 * curve₆.ΨSq (2 : ℤ) ^ 5
    -
    ((1862593441710241626726467188238985081920299)
      + (1951719046166564094160596861372122427964286) * X
      + (-5494390036163645963577295624160105498409856) * X ^ 2
      + (3658341288386557415137395313501545794077912) * X ^ 3
      + (-1001322176326817723055199351562085105352729) * X ^ 4
      + (65596310248211309733786019157240496239556) * X ^ 5
      + (23776955824578395579272839525278005437508) * X ^ 6
      + (-5108023451863134904206308680461867938856) * X ^ 7
      + (298689012307055340204020125979996327523) * X ^ 8) :=
  dvd_sub_add sum₆_3 term₆_4 ⟨0, by ring⟩

lemma sum₆_5 : ker₆ ∣
    (-130321) * curve₆.Φ (2 : ℤ) ^ 0 * curve₆.ΨSq (2 : ℤ) ^ 9
      + (-130321) * curve₆.Φ (2 : ℤ) ^ 1 * curve₆.ΨSq (2 : ℤ) ^ 8
      + (390963) * curve₆.Φ (2 : ℤ) ^ 2 * curve₆.ΨSq (2 : ℤ) ^ 7
      + (-274360) * curve₆.Φ (2 : ℤ) ^ 3 * curve₆.ΨSq (2 : ℤ) ^ 6
      + (82308) * curve₆.Φ (2 : ℤ) ^ 4 * curve₆.ΨSq (2 : ℤ) ^ 5
      + (-7942) * curve₆.Φ (2 : ℤ) ^ 5 * curve₆.ΨSq (2 : ℤ) ^ 4
    -
    ((-70381286290174702000798066239080009136731)
      + (-73749050046492724425738901057053599546546) * X
      + (207614946701207097446264290678408522581550) * X ^ 2
      + (-138236697175766948204743342116763058134916) * X ^ 3
      + (37836675025434540694191366990059531497323) * X ^ 4
      + (-2478669035753737435325755982753550119940) * X ^ 5
      + (-898453037438497098191376267712543962220) * X ^ 6
      + (193015422966781647573877443882711303910) * X ^ 7
      + (-11286476381391002671431227350887749997) * X ^ 8) :=
  dvd_sub_add sum₆_4 term₆_5 ⟨0, by ring⟩

lemma sum₆_6 : ker₆ ∣
    (-130321) * curve₆.Φ (2 : ℤ) ^ 0 * curve₆.ΨSq (2 : ℤ) ^ 9
      + (-130321) * curve₆.Φ (2 : ℤ) ^ 1 * curve₆.ΨSq (2 : ℤ) ^ 8
      + (390963) * curve₆.Φ (2 : ℤ) ^ 2 * curve₆.ΨSq (2 : ℤ) ^ 7
      + (-274360) * curve₆.Φ (2 : ℤ) ^ 3 * curve₆.ΨSq (2 : ℤ) ^ 6
      + (82308) * curve₆.Φ (2 : ℤ) ^ 4 * curve₆.ΨSq (2 : ℤ) ^ 5
      + (-7942) * curve₆.Φ (2 : ℤ) ^ 5 * curve₆.ΨSq (2 : ℤ) ^ 4
      + (-1444) * curve₆.Φ (2 : ℤ) ^ 6 * curve₆.ΨSq (2 : ℤ) ^ 3
    -
    ((-2263915274223842898181058610430730513251983)
      + (-2372244237887950303774894322830447417230278) * X
      + (6678233288525890675331620091310428329720694) * X ^ 2
      + (-4446582134145985860041093029496583632056896) * X ^ 3
      + (1217071057282095590278627620034592971955339) * X ^ 4
      + (-79729953607278511361571956086715800508684) * X ^ 5
      + (-28900033824809812533423163580915133517368) * X ^ 6
      + (6208618614758840091740226638471404606778) * X ^ 7
      + (-363045741528600055416815079327711341773) * X ^ 8) :=
  dvd_sub_add sum₆_5 term₆_6 ⟨0, by ring⟩

lemma sum₆_7 : ker₆ ∣
    (-130321) * curve₆.Φ (2 : ℤ) ^ 0 * curve₆.ΨSq (2 : ℤ) ^ 9
      + (-130321) * curve₆.Φ (2 : ℤ) ^ 1 * curve₆.ΨSq (2 : ℤ) ^ 8
      + (390963) * curve₆.Φ (2 : ℤ) ^ 2 * curve₆.ΨSq (2 : ℤ) ^ 7
      + (-274360) * curve₆.Φ (2 : ℤ) ^ 3 * curve₆.ΨSq (2 : ℤ) ^ 6
      + (82308) * curve₆.Φ (2 : ℤ) ^ 4 * curve₆.ΨSq (2 : ℤ) ^ 5
      + (-7942) * curve₆.Φ (2 : ℤ) ^ 5 * curve₆.ΨSq (2 : ℤ) ^ 4
      + (-1444) * curve₆.Φ (2 : ℤ) ^ 6 * curve₆.ΨSq (2 : ℤ) ^ 3
      + (437) * curve₆.Φ (2 : ℤ) ^ 7 * curve₆.ΨSq (2 : ℤ) ^ 2
    -
    ((1879319024438964414965653267752842440735306)
      + (1969244952617029762613104159635764744541818) * X
      + (-5543728164934852634103031446521231652430155) * X ^ 2
      + (3691192198518031579595062981615861906375992) * X ^ 3
      + (-1010313777196641445811181877771564854284935) * X ^ 4
      + (66185347262230894590784318051897685372087) * X ^ 5
      + (23990466427596272494700484951167381665740) * X ^ 6
      + (-5153892114176929161631603053025427768368) * X ^ 7
      + (301371158452210523002295259037348058394) * X ^ 8) :=
  dvd_sub_add sum₆_6 term₆_7 ⟨0, by ring⟩

lemma sum₆_8 : ker₆ ∣
    (-130321) * curve₆.Φ (2 : ℤ) ^ 0 * curve₆.ΨSq (2 : ℤ) ^ 9
      + (-130321) * curve₆.Φ (2 : ℤ) ^ 1 * curve₆.ΨSq (2 : ℤ) ^ 8
      + (390963) * curve₆.Φ (2 : ℤ) ^ 2 * curve₆.ΨSq (2 : ℤ) ^ 7
      + (-274360) * curve₆.Φ (2 : ℤ) ^ 3 * curve₆.ΨSq (2 : ℤ) ^ 6
      + (82308) * curve₆.Φ (2 : ℤ) ^ 4 * curve₆.ΨSq (2 : ℤ) ^ 5
      + (-7942) * curve₆.Φ (2 : ℤ) ^ 5 * curve₆.ΨSq (2 : ℤ) ^ 4
      + (-1444) * curve₆.Φ (2 : ℤ) ^ 6 * curve₆.ΨSq (2 : ℤ) ^ 3
      + (437) * curve₆.Φ (2 : ℤ) ^ 7 * curve₆.ΨSq (2 : ℤ) ^ 2
      + (-38) * curve₆.Φ (2 : ℤ) ^ 8 * curve₆.ΨSq (2 : ℤ) ^ 1
    -
    ((-369334450282238777641378691980949045682800)
      + (-387007204538470227239371889247979534298794) * X
      + (1089484950480243091819487615154016320730037) * X ^ 2
      + (-725414058858510042140071454731892865942492) * X ^ 3
      + (198552602600428153527121421465342085173457) * X ^ 4
      + (-13007120394859415217499216830165009616039) * X ^ 5
      + (-4714742745872479585651877880339550921534) * X ^ 6
      + (1012872155747080824405772930544553831298) * X ^ 7
      + (-59227172037320780330693762004293963028) * X ^ 8) :=
  dvd_sub_add sum₆_7 term₆_8 ⟨0, by ring⟩

lemma sum₆_9 : ker₆ ∣
    (-130321) * curve₆.Φ (2 : ℤ) ^ 0 * curve₆.ΨSq (2 : ℤ) ^ 9
      + (-130321) * curve₆.Φ (2 : ℤ) ^ 1 * curve₆.ΨSq (2 : ℤ) ^ 8
      + (390963) * curve₆.Φ (2 : ℤ) ^ 2 * curve₆.ΨSq (2 : ℤ) ^ 7
      + (-274360) * curve₆.Φ (2 : ℤ) ^ 3 * curve₆.ΨSq (2 : ℤ) ^ 6
      + (82308) * curve₆.Φ (2 : ℤ) ^ 4 * curve₆.ΨSq (2 : ℤ) ^ 5
      + (-7942) * curve₆.Φ (2 : ℤ) ^ 5 * curve₆.ΨSq (2 : ℤ) ^ 4
      + (-1444) * curve₆.Φ (2 : ℤ) ^ 6 * curve₆.ΨSq (2 : ℤ) ^ 3
      + (437) * curve₆.Φ (2 : ℤ) ^ 7 * curve₆.ΨSq (2 : ℤ) ^ 2
      + (-38) * curve₆.Φ (2 : ℤ) ^ 8 * curve₆.ΨSq (2 : ℤ) ^ 1
      + (1) * curve₆.Φ (2 : ℤ) ^ 9 * curve₆.ΨSq (2 : ℤ) ^ 0
    -
    (0) :=
  dvd_sub_add sum₆_8 term₆_9 ⟨0, by ring⟩

/-- **The stability divisibility at row 6**, assembled from the reduced terms. -/
lemma ker₆_dvd_multComp : ker₆ ∣
    ∑ i ∈ Finset.range (ker₆.natDegree + 1), C (ker₆.coeff i) *
      curve₆.Φ (2 : ℤ) ^ i * curve₆.ΨSq (2 : ℤ) ^
        (ker₆.natDegree - i) := by
  rw [ker₆_natDegree]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num only
  rw [ker₆_coeff_0, ker₆_coeff_1, ker₆_coeff_2, ker₆_coeff_3, ker₆_coeff_4, ker₆_coeff_5,
    ker₆_coeff_6, ker₆_coeff_7, ker₆_coeff_8, ker₆_coeff_9]
  simpa using sum₆_9

/-- **The kernel-polynomial certificate at row 6.** -/
theorem curve₆_isKernelPolynomial : curve₆.IsKernelPolynomial 19 ker₆ 2 where
  monic := ker₆_monic
  natDegree_eq := ker₆_natDegree
  dvd_ΨSq := by
    rw [WeierstrassCurve.ΨSq_ofNat, if_neg (by decide), mul_one]
    exact dvd_pow ker₆_dvd_preΨ' (by norm_num)
  mult_ne_zero := by decide
  generates := by
    intro k hk
    obtain ⟨i, -, hi⟩ := generates_aux_19_2 k hk
    exact ⟨i, hi⟩
  dvd_multComp := ker₆_dvd_multComp


end GenusOneKernel
