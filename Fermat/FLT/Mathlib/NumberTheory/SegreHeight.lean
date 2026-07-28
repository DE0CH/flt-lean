module

/-
SegreHeight.lean — own work for the Fermat project.

# Segre coordinates: the geometric half of the theory of heights on an abelian variety

This module is the INTERFACE between the geometry of an abelian variety
over `ℚ` and the elementary theory of heights.  It exists to cut

  `Fermat.exists_integralCoordinates_of_abelianScheme`

(in `Fermat/FLT/ModularCurve/X0.lean`) into a purely geometric leaf and a
purely elementary one.

## The classical argument this transcribes

Let `A` be an abelian variety over `ℚ` and `L` a symmetric very ample
line bundle, giving a closed immersion `φ_L : A ↪ ℙ^{n-1}_ℚ`.  The
theorem of the cube says

  `m^* L ⊗ d^* L ≅ p₁^* L² ⊗ p₂^* L²`   on `A × A`,

where `m` and `d` are addition and subtraction.  Read through the Segre
embedding `ℙ^{n-1} × ℙ^{n-1} ↪ ℙ^{n²-1}`, `z_{ij} = x_i y_j`, this says
exactly that the map

  `Segre(P, Q) ↦ Segre(P + Q, P − Q)`

is given by a family of forms of degree **2** in the Segre coordinates
`z`.  (A bidegree-`(2,2)` monomial `x_a x_b y_c y_d` is the degree-2
monomial `z_{ac} z_{bd}`, which is why the Segre picture is the one where
the degree is uniform and mathlib's height machine applies verbatim.)

The height then follows formally: heights multiply along Segre, so
`h(Segre(P,Q)) = h(P) + h(Q)`, and a degree-`2` morphism multiplies
heights by `2` up to `O(1)`, which is the quasi-parallelogram law.

## What is here, and what is a leaf

* `Fermat.segreVec`, the Segre coordinate vector of a pair of points;
* `Fermat.SegreCoordinates A`, the interface: primitive integral
  projective coordinates, the degree-2 forms, and the Nullstellensatz
  certificate for them;
* `Fermat.nonempty_integralCoordinates_of_segreCoordinates` (**PROVEN**,
  2026-07-28), the elementary half: such a system yields a
  `Fermat.IntegralCoordinates`.  Its supporting lemmas, all proven here:
  `Fermat.gcd_segre_eq_one`, `Fermat.one_le_ciSup_abs_of_gcd_eq_one`,
  `Fermat.ciSup_abs_segre_eq`, `Fermat.abs_intHeight_sub_logHeight_le`,
  `Fermat.SegreCoordinates.dim_ne_zero` and `Fermat.logHeight_segreVec`.

This module now contains no `sorry`.

The geometric half — that an abelian scheme over `ℚ` HAS such a system —
is `Fermat.exists_segreCoordinates_of_abelianScheme` in `X0.lean`.

## THE PIN HAS THE HEIGHT MACHINE.  A stale note said otherwise.

`Fermat/FLT/Mathlib/NumberTheory/IntegralHeight.lean` opens with
"neither `Mathlib` nor `~/cs/FLT` contains a height function or
Northcott's theorem; the only thing upstream is `Mathlib/Order/Northcott.lean`",
and the MISSING MACHINERY note of
`exists_integralCoordinates_of_abelianScheme` said the theory of heights
was absent from the pin.  **Both were wrong at this pin**, and the
correction is what makes the cut below cheap.  `Mathlib/NumberTheory/Height/`
contains, at `a3364fa`:

* `Height.mulHeight`, `Height.logHeight` on `ι → K` for a field `K` with
  `Height.AdmissibleAbsValues K`, and that instance for every number
  field (`Height.instAdmissibleAbsValues`), hence for `ℚ`;
* `Height.logHeight_smul_eq_logHeight` — invariance under scaling, which
  is what makes the `∃ c` in `form_eval` harmless;
* `Rat.logHeight_eq_max_abs_of_gcd_eq_one` — for a PRIMITIVE integer
  tuple the logarithmic height is `log (⨆ i, |x i|)`, which is the bridge
  to `Fermat.intHeight`;
* `Height.logHeight_eval_le'` — the UPPER bound `h(p(x)) ≤ C + N h(x)`
  for a family `p` of homogeneous forms of degree `N`;
* `Height.logHeight_eval_ge'` — the LOWER bound, from a Nullstellensatz
  certificate presented as the identity
  `∀ k, ∑ j, (q (k,j)).eval x * (p j).eval x = (x k) ^ (M + N)`;
* `Height.finite_setOf_logHeight₁_le` and the `Northcott` instances.

`Mathlib/NumberTheory/Height/EllipticCurve.lean` runs exactly this
argument for an elliptic curve in the affine model
(`WeierstrassCurve.abs_logHeight_addSubMap_sub_two_mul_logHeight_le`),
which is worth reading before proving the leaf below: it is the same
proof, with `addSubMap` in place of `form` and `addSubMapCoeff_condition`
in place of `cert_eval`.  It does NOT close the abelian-variety case —
the Jacobian of `X_0(N)` has dimension the genus, not `1` — but it is a
model to copy, and it is the reason the certificate is stated in exactly
mathlib's shape rather than as "the forms have no common zero".

**Why the certificate, and not "no common zero".**  The forms define a
morphism only on the Segre image of `A × A`, not on all of `ℙ^{n²-1}`, so
they DO have common zeros elsewhere and the naive Nullstellensatz
hypothesis would be false.  The identity above is the *conclusion* of the
Nullstellensatz applied to the homogeneous ideal of that variety, and it
is required only at the points `segreVec coords P Q` we actually use —
where the ideal's contribution vanishes.  So it is satisfiable by the
genuine geometry, and it removes the Nullstellensatz from the Lean proof
entirely.
-/

public import Fermat.FLT.Mathlib.NumberTheory.IntegralHeight
public import Mathlib.NumberTheory.Height.MvPolynomial
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

@[expose] public noncomputable section

namespace Fermat

/-- **The Segre coordinate vector of a pair of points**, `z_{ij} = x_i y_j`
with `x = coords P` and `y = coords Q`, as a tuple of rationals.

Taking values in `ℚ` rather than `ℤ` is deliberate: it is the type
mathlib's height machine works over, and the forms below are `ℚ`-forms
(no integrality of the coefficients is asked for anywhere, and the
geometry does not supply it). -/
def segreVec {A : Type*} {d : ℕ} (coords : A → (Fin d → ℤ)) (P Q : A) :
    (Fin d × Fin d) → ℚ :=
  fun k => (coords P k.1 : ℚ) * (coords Q k.2 : ℚ)

/-- **The Segre product of two primitive integer tuples is primitive**
(PROVEN).  Bézout on each factor gives `∑ i, x i * f i = 1` and
`∑ j, y j * g j = 1`; multiplying the two identities exhibits `1` as an
integral combination of the products `x i * y j`, so their gcd divides
`1` — and a `Finset.gcd` is normalized, hence equal to `1`. -/
theorem gcd_segre_eq_one {m n : ℕ} {x : Fin m → ℤ} {y : Fin n → ℤ}
    (hx : Finset.univ.gcd x = 1) (hy : Finset.univ.gcd y = 1) :
    (Finset.univ : Finset (Fin m × Fin n)).gcd (fun k => x k.1 * y k.2) = 1 := by
  classical
  obtain ⟨f, hf⟩ := Finset.gcd_eq_sum_mul (Finset.univ : Finset (Fin m)) x
  obtain ⟨g, hg⟩ := Finset.gcd_eq_sum_mul (Finset.univ : Finset (Fin n)) y
  rw [hx] at hf
  rw [hy] at hg
  have key : (1 : ℤ) = ∑ k : Fin m × Fin n, (x k.1 * y k.2) * (f k.1 * g k.2) := by
    rw [Fintype.sum_prod_type]
    calc (1 : ℤ) = (∑ i, x i * f i) * (∑ j, y j * g j) := by rw [← hf, ← hg]; ring
      _ = ∑ i, ∑ j, (x i * y j) * (f i * g j) := by
          rw [Finset.sum_mul_sum]
          exact Finset.sum_congr rfl fun i _ =>
            Finset.sum_congr rfl fun j _ => by ring
  have hdvd : (Finset.univ : Finset (Fin m × Fin n)).gcd (fun k => x k.1 * y k.2) ∣ 1 := by
    rw [key]
    exact Finset.dvd_sum fun k _ =>
      Dvd.dvd.mul_right (Finset.gcd_dvd (Finset.mem_univ k)) _
  rw [← Finset.normalize_gcd]
  exact normalize_eq_one.mpr (isUnit_of_dvd_one hdvd)

/-- **A primitive integer tuple has sup-norm at least `1`** (PROVEN): its
gcd being `1` rules out the zero tuple, and a nonzero integer has
absolute value at least `1`. -/
theorem one_le_ciSup_abs_of_gcd_eq_one {d : ℕ} [NeZero d] {v : Fin d → ℤ}
    (hv : Finset.univ.gcd v = 1) : 1 ≤ ⨆ i, |v i| := by
  have : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  have hne : ¬ (∀ i ∈ (Finset.univ : Finset (Fin d)), v i = 0) := by
    intro h0
    rw [Finset.gcd_eq_zero_iff.mpr h0] at hv
    exact zero_ne_one hv
  push Not at hne
  obtain ⟨i, -, hi⟩ := hne
  exact (Int.one_le_abs hi).trans (Finite.le_ciSup (fun i => |v i|) i)

/-- **The sup-norm is multiplicative along the Segre embedding** (PROVEN):
`⨆_{i,j} |x i * y j| = (⨆ i, |x i|) * (⨆ j, |y j|)`, the elementary
`ℤ`-level statement behind "heights multiply along Segre". -/
theorem ciSup_abs_segre_eq {m n : ℕ} [NeZero m] [NeZero n] (x : Fin m → ℤ) (y : Fin n → ℤ) :
    (⨆ k : Fin m × Fin n, |x k.1 * y k.2|) = (⨆ i, |x i|) * (⨆ j, |y j|) := by
  have : Nonempty (Fin m) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩⟩
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  obtain ⟨i₀, hi₀⟩ := exists_eq_ciSup_of_finite (f := fun i => |x i|)
  obtain ⟨j₀, hj₀⟩ := exists_eq_ciSup_of_finite (f := fun j => |y j|)
  refine le_antisymm (ciSup_le fun k => ?_) ?_
  · rw [abs_mul]
    exact mul_le_mul (Finite.le_ciSup (fun i => |x i|) k.1)
      (Finite.le_ciSup (fun j => |y j|) k.2) (abs_nonneg _)
      (le_trans (abs_nonneg (x i₀)) (le_of_eq hi₀))
  · rw [← hi₀, ← hj₀, ← abs_mul]
    exact Finite.le_ciSup (fun k : Fin m × Fin n => |x k.1 * y k.2|) (i₀, j₀)

/-- **The `ℓ¹` naive height and the projective sup-norm height agree up to
`log (d + 1)` on primitive integer tuples** (PROVEN).

With `M = ⨆ i, |v i| ≥ 1` one has `M ≤ ∑ i, |v i| ≤ d * M`, hence
`M ≤ 1 + ∑ i, |v i| ≤ (d + 1) * M`, and `Height.logHeight` of the
`ℚ`-tuple is `log M` by `Rat.logHeight_eq_max_abs_of_gcd_eq_one`. -/
theorem abs_intHeight_sub_logHeight_le {d : ℕ} [NeZero d] {v : Fin d → ℤ}
    (hv : Finset.univ.gcd v = 1) :
    |intHeight v - Height.logHeight (((↑) : ℤ → ℚ) ∘ v)| ≤ Real.log (d + 1) := by
  have : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  set M : ℤ := ⨆ i, |v i| with hM
  have hM1 : (1 : ℤ) ≤ M := one_le_ciSup_abs_of_gcd_eq_one hv
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  have habs : ∀ i, ((v i).natAbs : ℝ) = ((|v i| : ℤ) : ℝ) := by
    intro i; rw [← Int.natCast_natAbs, Int.cast_natCast]
  have hnn : ∀ i : Fin d, (0 : ℝ) ≤ ((v i).natAbs : ℝ) := fun i => Nat.cast_nonneg _
  have hsum_le : ∑ i, ((v i).natAbs : ℝ) ≤ (d : ℝ) * (M : ℝ) := by
    calc ∑ i, ((v i).natAbs : ℝ) = ∑ i, ((|v i| : ℤ) : ℝ) := Finset.sum_congr rfl fun i _ => habs i
      _ ≤ ∑ _i : Fin d, (M : ℝ) := Finset.sum_le_sum fun i _ => by
            exact_mod_cast (Finite.le_ciSup (fun i => |v i|) i)
      _ = (d : ℝ) * (M : ℝ) := by simp
  have hMle : (M : ℝ) ≤ ∑ i, ((v i).natAbs : ℝ) := by
    obtain ⟨i₀, hi₀⟩ := exists_eq_ciSup_of_finite (f := fun i => |v i|)
    calc (M : ℝ) = ((|v i₀| : ℤ) : ℝ) := by rw [hM, ← hi₀]
      _ = ((v i₀).natAbs : ℝ) := (habs i₀).symm
      _ ≤ ∑ i, ((v i).natAbs : ℝ) :=
          Finset.single_le_sum (f := fun i => ((v i).natAbs : ℝ))
            (fun i _ => hnn i) (Finset.mem_univ i₀)
  have hlog : Height.logHeight (((↑) : ℤ → ℚ) ∘ v) = Real.log (M : ℝ) := by
    rw [Rat.logHeight_eq_max_abs_of_gcd_eq_one hv]
  rw [hlog, intHeight]
  have hpos : (0 : ℝ) < 1 + ∑ i, ((v i).natAbs : ℝ) := by
    have : (0 : ℝ) ≤ ∑ i, ((v i).natAbs : ℝ) := Finset.sum_nonneg fun i _ => hnn i
    linarith
  have hlow : Real.log (M : ℝ) ≤ Real.log (1 + ∑ i, ((v i).natAbs : ℝ)) :=
    Real.log_le_log (by linarith) (by linarith)
  have hhigh : Real.log (1 + ∑ i, ((v i).natAbs : ℝ))
      ≤ Real.log ((d : ℝ) + 1) + Real.log (M : ℝ) := by
    have hprod : 1 + ∑ i, ((v i).natAbs : ℝ) ≤ ((d : ℝ) + 1) * (M : ℝ) := by
      have : (1 : ℝ) ≤ (M : ℝ) := hMR
      nlinarith [hsum_le]
    have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
    calc Real.log (1 + ∑ i, ((v i).natAbs : ℝ)) ≤ Real.log (((d : ℝ) + 1) * (M : ℝ)) :=
          Real.log_le_log hpos hprod
      _ = Real.log ((d : ℝ) + 1) + Real.log (M : ℝ) := Real.log_mul (ne_of_gt hd1) (by linarith)
  rw [abs_le]
  constructor
  · have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have : (0 : ℝ) ≤ Real.log ((d : ℝ) + 1) := Real.log_nonneg (by linarith)
    linarith
  · linarith

/-- **A Segre coordinate system on an additive abelian group**: primitive
integral projective coordinates together with the degree-2 forms that
compute the Segre point of `(P + Q, P − Q)`, and a Nullstellensatz
certificate for them.

This is the elementary transcription of "a symmetric very ample line
bundle on `A/ℚ` and the theorem of the cube" — see the module docstring.
Three remarks on what it does and does not say.

* It is NOT trivially satisfiable.  `form_eval` says the sum-and-
  difference map is computed by ONE fixed family of quadratic forms,
  uniformly in `P` and `Q`; that is the theorem of the cube and nothing
  less.  For `A ≅ ℤ` with a linear parametrisation `n ↦ (n : ℤ)` no such
  forms exist, which is the same non-vacuity witness as for
  `IntegralCoordinates`.
* `primitive` forces `coords P ≠ 0` for every `P` (the `gcd` of the zero
  tuple is `0`), which is what makes the projective height of `coords P`
  well behaved, and it is what
  `Rat.logHeight_eq_max_abs_of_gcd_eq_one` asks for.  Over `ℚ` such a
  representative exists and is unique up to sign, because `ℤ` is a PID
  with unit group `{±1}`; over a general number field this field of the
  structure could not be asked for.
* The scalar `c` in `form_eval` is unavoidable and harmless: the forms
  compute a point of projective space, so they determine `coords (P+Q)`
  and `coords (P−Q)` only up to a common factor, and the height is
  invariant under scaling
  (`Height.logHeight_smul_eq_logHeight`). -/
structure SegreCoordinates (A : Type*) [AddCommGroup A] where
  /-- the number of projective coordinates -/
  dim : ℕ
  /-- the coordinate map, in primitive integral projective coordinates -/
  coords : A → (Fin dim → ℤ)
  /-- the coordinates separate points — injectivity of a closed immersion
  on `ℚ`-points -/
  injective : Function.Injective coords
  /-- the coordinates of each point are primitive; in particular nonzero -/
  primitive : ∀ P : A, Finset.univ.gcd (coords P) = 1
  /-- the common degree of the certificate forms -/
  certDeg : ℕ
  /-- the degree-2 forms computing the sum-and-difference map in Segre
  coordinates -/
  form : (Fin dim × Fin dim) → MvPolynomial (Fin dim × Fin dim) ℚ
  /-- they are homogeneous of degree `2` — this is the theorem of the
  cube, read through the Segre embedding -/
  form_homogeneous : ∀ k, (form k).IsHomogeneous 2
  /-- the Nullstellensatz certificate forms -/
  cert : ((Fin dim × Fin dim) × (Fin dim × Fin dim)) → MvPolynomial (Fin dim × Fin dim) ℚ
  /-- they are homogeneous of one common degree -/
  cert_homogeneous : ∀ a, (cert a).IsHomogeneous certDeg
  /-- the certificate identity, asked for only at the Segre points that
  arise from `A` — which is where the homogeneous ideal of the Segre
  image vanishes, and is exactly the hypothesis of
  `Height.logHeight_eval_ge'` -/
  cert_eval : ∀ P Q : A, ∀ k : Fin dim × Fin dim,
    ∑ j, (cert (k, j)).eval (segreVec coords P Q) * (form j).eval (segreVec coords P Q)
      = (segreVec coords P Q k) ^ (certDeg + 2)
  /-- the forms compute the Segre point of `(P + Q, P − Q)`, up to a
  common nonzero scalar -/
  form_eval : ∀ P Q : A, ∃ c : ℚ, c ≠ 0 ∧ ∀ k : Fin dim × Fin dim,
    (form k).eval (segreVec coords P Q) = c * segreVec coords (P + Q) (P - Q) k

/-- **The dimension of a Segre coordinate system is positive** (PROVEN):
the gcd over the empty index type is `0`, not `1`, so `primitive` at any
point of the (nonempty) group `A` forces `dim ≠ 0`. -/
theorem SegreCoordinates.dim_ne_zero {A : Type*} [AddCommGroup A]
    (sc : SegreCoordinates A) : sc.dim ≠ 0 := by
  intro h0
  haveI : IsEmpty (Fin sc.dim) := by rw [h0]; infer_instance
  have hp := sc.primitive 0
  rw [Finset.univ_eq_empty, Finset.gcd_empty] at hp
  exact zero_ne_one hp

/-- **Heights multiply along the Segre embedding** (PROVEN) — step 1 of
the chain below.

Because the coordinates are primitive, so is their Segre product
(`gcd_segre_eq_one`), so both sides are computed by
`Rat.logHeight_eq_max_abs_of_gcd_eq_one` as logarithms of sup-norms, and
`ciSup_abs_segre_eq` makes the sup-norm multiplicative. -/
theorem logHeight_segreVec {A : Type*} [AddCommGroup A] (sc : SegreCoordinates A)
    [NeZero sc.dim] (P Q : A) :
    Height.logHeight (segreVec sc.coords P Q)
      = Height.logHeight (((↑) : ℤ → ℚ) ∘ sc.coords P)
        + Height.logHeight (((↑) : ℤ → ℚ) ∘ sc.coords Q) := by
  have : Nonempty (Fin sc.dim) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne sc.dim)⟩⟩
  have hz : segreVec sc.coords P Q
      = ((↑) : ℤ → ℚ) ∘
          (fun k : Fin sc.dim × Fin sc.dim => sc.coords P k.1 * sc.coords Q k.2) := by
    funext k
    simp [segreVec]
  have hgcd := gcd_segre_eq_one (sc.primitive P) (sc.primitive Q)
  rw [hz, Rat.logHeight_eq_max_abs_of_gcd_eq_one hgcd,
    Rat.logHeight_eq_max_abs_of_gcd_eq_one (sc.primitive P),
    Rat.logHeight_eq_max_abs_of_gcd_eq_one (sc.primitive Q),
    ciSup_abs_segre_eq]
  have hP : (1 : ℤ) ≤ ⨆ i, |sc.coords P i| := one_le_ciSup_abs_of_gcd_eq_one (sc.primitive P)
  have hQ : (1 : ℤ) ≤ ⨆ i, |sc.coords Q i| := one_le_ciSup_abs_of_gcd_eq_one (sc.primitive Q)
  have hP' : (0 : ℝ) < ((⨆ i, |sc.coords P i| : ℤ) : ℝ) := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one hP
  have hQ' : (0 : ℝ) < ((⨆ i, |sc.coords Q i| : ℤ) : ℝ) := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one hQ
  push_cast
  exact Real.log_mul (ne_of_gt hP') (ne_of_gt hQ')

/-- **A Segre coordinate system is an integral coordinate system**
(PROVEN) — the ELEMENTARY half of the theory of heights on an abelian
variety over `ℚ`, and the whole of what is left of it once the geometry
is granted.

TRUE, and every ingredient of the proof is in the pin — this is the chain
that is now carried out below, with the mathlib name for each step:

1. *heights multiply along Segre*:
   `Height.mulHeight (segreVec coords P Q) = mulHeight (coords P) * mulHeight (coords Q)`,
   because `⨆_{i,j} |x_i y_j|_v = (⨆_i |x_i|_v)(⨆_j |y_j|_v)` at every
   place.  This is the one step with no ready-made lemma — mathlib has
   only the two-variable case (`Height.mulHeight_sym2_le` /
   `mulHeight_sym2_ge`) — and it is elementary from
   `Height.mulHeight`'s definition.
2. *the degree-2 map moves the height by a factor `2`*: combine
   `Height.logHeight_eval_le' form_homogeneous` with
   `Height.logHeight_eval_ge' cert_homogeneous` fed by `cert_eval`, at
   `N = 2` and `M = certDeg`.  Together they give a single `C` with
   `|logHeight (fun k => (form k).eval z) − 2 * logHeight z| ≤ C`.
3. *drop the scalar*: `Height.logHeight_smul_eq_logHeight` and
   `form_eval` turn the left-hand side into
   `logHeight (segreVec coords (P+Q) (P−Q))`.
4. Steps 1–3 give the quasi-parallelogram law for
   `fun P => Height.logHeight ((↑) ∘ coords P)`.
5. *transfer to* `Fermat.intHeight`: by
   `Rat.logHeight_eq_max_abs_of_gcd_eq_one primitive`, the height of step
   4 is `log (⨆ i, |coords P i|)`, and for a nonzero integer tuple
   `⨆ i |v i| ≤ 1 + ∑ i |v i| ≤ (dim + 1) * ⨆ i |v i|`, so
   `intHeight (coords P)` differs from it by at most `log (dim + 1)`.
   The quasi-parallelogram law is stated up to a constant, so it
   survives with `C + 6 * log (dim + 1)`.

`Fermat/FLT/EllipticCurve` is not involved anywhere; the model to copy is
`WeierstrassCurve.abs_logHeight_addSubMap_sub_two_mul_logHeight_le`
(`Mathlib/NumberTheory/Height/EllipticCurve.lean`), whose proof is steps
2 and 3 in four lines.

**FAITHFULNESS AUDIT.**  *Not vacuous.*  The conclusion is
`IntegralCoordinates`, whose own audit records that an arbitrary
injection into `ℤ^d` fails the quasi-parallelogram law; this leaf must
actually derive that law, and it derives it from `form_homogeneous` +
`cert_eval` + `form_eval`, all three of which are used.  *No geometry is
assumed and none is available*: `sc` is a bare structure on an abstract
`AddCommGroup`, so nothing here can accidentally consume properties of an
abelian variety. -/
theorem nonempty_integralCoordinates_of_segreCoordinates {A : Type*} [AddCommGroup A]
    (sc : SegreCoordinates A) : Nonempty (IntegralCoordinates A) := by
  classical
  haveI : NeZero sc.dim := ⟨sc.dim_ne_zero⟩
  haveI : Nonempty (Fin sc.dim) := ⟨⟨0, Nat.pos_of_ne_zero sc.dim_ne_zero⟩⟩
  -- the projective height of the coordinates
  set h : A → ℝ := fun P => Height.logHeight (((↑) : ℤ → ℚ) ∘ sc.coords P)
  obtain ⟨C₁, hC₁⟩ := Height.logHeight_eval_le' sc.form_homogeneous
  obtain ⟨C₂, hC₂⟩ := Height.logHeight_eval_ge' (N := 2) sc.cert_homogeneous
  -- steps 1–4: the quasi-parallelogram law for the projective height `h`
  have hqp : ∀ P Q : A, |h (P + Q) + h (P - Q) - (2 * h P + 2 * h Q)| ≤ max C₁ (-C₂) := by
    intro P Q
    set z : (Fin sc.dim × Fin sc.dim) → ℚ := segreVec sc.coords P Q
    obtain ⟨c, hc0, hc⟩ := sc.form_eval P Q
    have hform : (fun k => (sc.form k).eval z) = c • segreVec sc.coords (P + Q) (P - Q) := by
      funext k
      simpa using hc k
    have hev : Height.logHeight (fun k => (sc.form k).eval z) = h (P + Q) + h (P - Q) := by
      rw [hform, Height.logHeight_smul_eq_logHeight _ hc0]
      exact logHeight_segreVec sc (P + Q) (P - Q)
    have hzz : Height.logHeight z = h P + h Q := logHeight_segreVec sc P Q
    have hup : h (P + Q) + h (P - Q) ≤ C₁ + 2 * (h P + h Q) := by
      have := hC₁ z
      rw [hev, hzz] at this
      simpa using this
    have hlo : C₂ + 2 * (h P + h Q) ≤ h (P + Q) + h (P - Q) := by
      have := hC₂ sc.form (sc.cert_eval P Q)
      rw [hev, hzz] at this
      simpa using this
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have : -C₂ ≤ max C₁ (-C₂) := le_max_right _ _
      linarith
    · have : C₁ ≤ max C₁ (-C₂) := le_max_left _ _
      linarith
  -- step 5: transfer from the projective height to `intHeight`
  refine ⟨{ dim := sc.dim, coords := sc.coords, injective := sc.injective,
            quasiParallelogram := ⟨max C₁ (-C₂) + 6 * Real.log ((sc.dim : ℝ) + 1), fun P Q => ?_⟩ }⟩
  have hd : ∀ R : A, |intHeight (sc.coords R) - h R| ≤ Real.log ((sc.dim : ℝ) + 1) := fun R =>
    abs_intHeight_sub_logHeight_le (sc.primitive R)
  have e1 := abs_le.mp (hd (P + Q))
  have e2 := abs_le.mp (hd (P - Q))
  have e3 := abs_le.mp (hd P)
  have e4 := abs_le.mp (hd Q)
  have e5 := abs_le.mp (hqp P Q)
  rw [abs_le]
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, e5.1, e5.2]

end Fermat
