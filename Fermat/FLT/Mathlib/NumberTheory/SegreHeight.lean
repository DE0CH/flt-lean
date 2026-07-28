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
* `Fermat.nonempty_integralCoordinates_of_segreCoordinates` (SORRY), the
  elementary half: such a system yields a `Fermat.IntegralCoordinates`.

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

/-- **A Segre coordinate system is an integral coordinate system** (sorry
node) — the ELEMENTARY half of the theory of heights on an abelian
variety over `ℚ`, and the whole of what is left of it once the geometry
is granted.

TRUE, and every ingredient of the proof is in the pin.  The chain, with
the mathlib name for each step:

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
    (sc : SegreCoordinates A) : Nonempty (IntegralCoordinates A) :=
  sorry

end Fermat
