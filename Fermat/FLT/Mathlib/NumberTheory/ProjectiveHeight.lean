module

/-
ProjectiveHeight.lean — own work for the Fermat project.

# Northcott's theorem in projective space over `ℚ`, and the height it feeds

`Mathlib` HAS a theory of heights.  This is worth saying loudly, because
several docstrings in this development assert the opposite: the claim
"Weil heights on projective space do not exist in `Mathlib`, in
`~/cs/FLT`, or in this project" was true when it was written and is FALSE
at the current pin.  The relevant modules are

* `Mathlib/NumberTheory/Height/Basic.lean` — `Height.mulHeight` and
  `Height.logHeight` of a tuple `ι → K`, `Height.mulHeight₁` and
  `Height.logHeight₁` of an element of `K`, for any field `K` carrying a
  `Height.AdmissibleAbsValues` instance (a family of absolute values
  satisfying the product formula);
* `Mathlib/NumberTheory/Height/NumberField.lean` — the
  `AdmissibleAbsValues` instance for a number field, **and the Northcott
  property** `NumberField.finite_setOf_mulHeight₁_le`, with the
  instances `Northcott (mulHeight₁ (K := K))` and, through
  `Mathlib/NumberTheory/Height/Northcott.lean`,
  `Northcott (logHeight₁ (K := K))`;
* `Mathlib/NumberTheory/Height/Projectivization.lean` — the height of a
  point of `Projectivization K (ι → K)`;
* `Mathlib/NumberTheory/Height/EllipticCurve.lean` — work in progress
  towards the approximate parallelogram law for the naïve height on a
  Weierstrass curve.

What `Mathlib` does **not** yet have is Northcott's theorem for
PROJECTIVE space — its own `Height/Northcott.lean` lists
"(TODO) for `Projectivization.mulHeight`" and
"(TODO) for `Projectivization.logHeight`".  That is the gap this module
fills, over `ℚ`, in the form the descent argument needs.

## What is proven here

`ProjectiveHeightSource A` packages what a projective embedding of an
abelian variety over `ℚ` gives its group of rational points: a map to
nonzero rational coordinate tuples, injective *up to scaling* (i.e.
injective as a map to `ℙⁿ(ℚ)`), whose naïve logarithmic height satisfies
the approximate parallelogram law.

`ProjectiveHeightSource.toWeilHeight` turns that into a
`Fermat.WeilHeight`, and hence — through
`Fermat.WeilHeight.toDescentHeight` and
`Fermat.fg_of_descentHeight` — into finite generation, given weak
Mordell–Weil.  The only mathematical content added here is the Northcott
half:

`finite_setOf_logHeight_coords_le`: for each `B` there are only finitely
many `P` with `logHeight (coords P) ≤ B`.

`CubeEmbedding A` and `CubeEmbedding.toProjectiveHeightSource` do the
same job one level further down: they carry the **theorem of the cube in
coordinates**, and derive the approximate parallelogram law from it.  See
the docstrings there — the point is that after that reduction the leaf in
`Fermat/FLT/ModularCurve/X0.lean` contains no height, no `ℝ` and no `O(1)`
at all, only algebraic geometry.

`CubeModel A` and `CubeModel.nonempty_cubeEmbedding` go one level further
still.  `CubeEmbedding` asks for a *Nullstellensatz certificate*
(`cert`, `cert_eval`), which is commutative algebra rather than geometry;
`CubeModel` asks instead for the equations of the Segre image and for the
forms of the cube to have no common zero on it over an algebraic closure —
which is exactly "`(P, Q) ↦ (P + Q, P − Q)` is a morphism" — and
`exists_homogeneousCertificate` manufactures the certificate from that.
After this, the leaf in `X0.lean` owes exactly three classical theorems:
projectivity of an abelian variety, a symmetric very ample line bundle,
and the theorem of the cube.

The proof is the classical one.  Cover the bounded-height set by the `n`
subsets on which the `j`-th coordinate is nonzero.  On the `j`-th of
them, send `P` to the tuple of ratios `(xᵢ / x_j)ᵢ`.  Each ratio has
`logHeight₁ (xᵢ / x_j) = logHeight ![xᵢ, x_j] ≤ logHeight x ≤ B` — the
equality is `Height.logHeight₁_div_eq_logHeight` and the inequality is
`Height.logHeight_comp_le`, monotonicity of the height under restriction
to a subfamily of coordinates — so every ratio lies in the finite set
supplied by `Mathlib`'s Northcott property for `ℚ`.  The map is injective
on that subset because the ratios determine `x` up to the scalar
`x_j`, and `coords` is injective up to scaling.  A finite union of sets
injecting into a finite product is finite.

Everything in this module is PROVEN; it contains no `sorry`.
-/

public import Fermat.FLT.Mathlib.GroupTheory.Descent
public import Mathlib.NumberTheory.Height.Basic
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Northcott
-- `Height.logHeight_eval_le'` and `Height.logHeight_eval_ge'`: the two-sided
-- comparison `|logHeight (F x) - N * logHeight x| ≤ C` for a family `F` of
-- homogeneous forms of degree `N`, the lower bound conditional on a
-- Nullstellensatz certificate.  This is the whole height analysis behind
-- `CubeEmbedding.parallelogram`.
public import Mathlib.NumberTheory.Height.MvPolynomial
public import Mathlib.Order.Northcott
-- `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`: Hilbert's Nullstellensatz for
-- an ideal over a base field `k` with zero locus taken in an algebraically closed
-- extension `K`, returning the radical OVER `k`.  That the radical comes back over
-- the small field is what makes `exists_homogeneousCertificate` rational for free.
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

@[expose] public section

namespace Fermat

open Height

/-- **A projective embedding of an abelian group over `ℚ`, together with
the parallelogram law for its naïve height.**

This is what a projective embedding `A ↪ ℙⁿ_ℚ` by a *symmetric ample*
line bundle gives on the group of rational points, written in coordinates
rather than through `Projectivization` so that no lifting API is needed:

* `coords` picks, for each point, a tuple of homogeneous coordinates;
* `coords_ne_zero` says the tuple is a legitimate homogeneous coordinate
  vector;
* `injective_of_smul` says that the induced map to `ℙⁿ(ℚ)` — coordinate
  tuples modulo scaling — is injective, which is what "embedding" means
  on rational points;
* `parallelogram` is the approximate parallelogram law for the naïve
  logarithmic height of those coordinates.  Symmetry of the line bundle
  is what makes it hold; that is why the statement is existential over
  the embedding rather than universal.

The Northcott property is deliberately NOT a field: it is a *theorem*
about any such embedding, `finite_setOf_logHeight_coords_le` below, and
making it a hypothesis would put an already-available finiteness theorem
back onto the geometry. -/
structure ProjectiveHeightSource (A : Type*) [AddCommGroup A] where
  /-- the number of homogeneous coordinates -/
  dim : ℕ
  /-- homogeneous coordinates of a point -/
  coords : A → (Fin dim → ℚ)
  /-- a homogeneous coordinate vector is nonzero -/
  coords_ne_zero : ∀ P : A, coords P ≠ 0
  /-- the induced map to `ℙ^{dim-1}(ℚ)` is injective -/
  injective_of_smul : ∀ P Q : A, ∀ c : ℚ, c ≠ 0 → coords P = c • coords Q → P = Q
  /-- the **approximate parallelogram law** for the naïve height -/
  parallelogram : ∃ C : ℝ, ∀ P Q : A,
    |logHeight (coords (P + Q)) + logHeight (coords (P - Q))
      - 2 * logHeight (coords P) - 2 * logHeight (coords Q)| ≤ C

variable {A : Type*} [AddCommGroup A]

/-- **Northcott's theorem in projective space over `ℚ`** (PROVEN) — for
each bound `B` there are only finitely many points of `A` whose
homogeneous coordinates have logarithmic height at most `B`.

`Mathlib` supplies the Northcott property for `ℚ` itself
(`Northcott (logHeight₁ (K := ℚ))`, from
`NumberField.finite_setOf_mulHeight₁_le`); this is the projective
upgrade, which `Mathlib`'s `Height/Northcott.lean` still lists as a
TODO. -/
theorem finite_setOf_logHeight_coords_le (ps : ProjectiveHeightSource A) (B : ℝ) :
    {P : A | logHeight (ps.coords P) ≤ B}.Finite := by
  classical
  -- `Mathlib`'s Northcott property for `ℚ`: finitely many rationals of bounded height.
  have hF : {q : ℚ | logHeight₁ q ≤ B}.Finite := Northcott.finite_le B
  -- Cover by the index of a nonzero coordinate.
  have hcover : {P : A | logHeight (ps.coords P) ≤ B} =
      ⋃ j : Fin ps.dim, {P : A | logHeight (ps.coords P) ≤ B ∧ ps.coords P j ≠ 0} := by
    ext P
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    refine ⟨fun hP => ?_, fun ⟨_, hP, _⟩ => hP⟩
    obtain ⟨j, hj⟩ := Function.ne_iff.mp (ps.coords_ne_zero P)
    exact ⟨j, hP, hj⟩
  rw [hcover]
  refine Set.finite_iUnion fun j => ?_
  -- On the `j`-th piece, the tuple of ratios `xᵢ / x_j` has all coordinates of height `≤ B`.
  refine Set.Finite.of_finite_image (f := fun P i => ps.coords P i / ps.coords P j)
    (Set.Finite.subset (Set.Finite.pi fun _ : Fin ps.dim => hF) ?_) ?_
  · rintro _ ⟨P, hP, rfl⟩ i -
    show logHeight₁ (ps.coords P i / ps.coords P j) ≤ B
    calc logHeight₁ (ps.coords P i / ps.coords P j)
        = logHeight ![ps.coords P i, ps.coords P j] := logHeight₁_div_eq_logHeight _ _
      _ = logHeight (ps.coords P ∘ ![i, j]) := by
          congr 1
          funext k
          fin_cases k <;> simp
      _ ≤ logHeight (ps.coords P) := logHeight_comp_le _ _
      _ ≤ B := hP.1
  · -- The ratios determine the point: they pin the coordinates up to the scalar `x_j`.
    intro P hP Q hQ hPQ
    have hPj : ps.coords P j ≠ 0 := hP.2
    have hQj : ps.coords Q j ≠ 0 := hQ.2
    refine ps.injective_of_smul P Q (ps.coords P j / ps.coords Q j) (div_ne_zero hPj hQj) ?_
    funext i
    have h := congrFun hPQ i
    rw [div_eq_div_iff hPj hQj] at h
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination h

/-- **A projective embedding with the parallelogram law is a
`WeilHeight`** (PROVEN) — the naïve logarithmic height of the
homogeneous coordinates, with Northcott supplied by
`finite_setOf_logHeight_coords_le`.

Composed with `WeilHeight.toDescentHeight` and `fg_of_descentHeight`,
this is the whole route from "the abelian variety is projectively
embedded and its naïve height satisfies the parallelogram law" to "its
group of rational points is finitely generated", given weak
Mordell–Weil.

**Renamed 2026-07-28** from `toParallelogramHeight`.  It used to target
`Fermat.ParallelogramHeight`, which was a field-for-field duplicate of
`Fermat.WeilHeight` inside the same file and was retired; the only
difference between the two was whether the law was written
`− 2 h P − 2 h Q` or `− (2 h P + 2 h Q)`, which is the `sub_sub` below. -/
noncomputable def ProjectiveHeightSource.toWeilHeight (ps : ProjectiveHeightSource A) :
    WeilHeight A where
  height P := logHeight (ps.coords P)
  quasiParallelogram := by
    obtain ⟨C, hC⟩ := ps.parallelogram
    refine ⟨C, fun P Q => ?_⟩
    have h := hC P Q
    rw [sub_sub] at h
    exact h
  northcott := ⟨fun B => finite_setOf_logHeight_coords_le ps B⟩

/-!
### The theorem of the cube, in coordinates

`ProjectiveHeightSource` still asks for an *analytic* fact — the
approximate parallelogram law, an `∃ C : ℝ` statement about logarithms.
That is not what algebraic geometry produces.  What the geometry produces
is an *algebraic identity*, and the whole of the analysis that turns the
identity into the law is `Mathlib`'s
`Height.logHeight_eval_le'` / `Height.logHeight_eval_ge'`.  Separating the
two is what `CubeEmbedding` is for.
-/

/-- **A projective embedding of `A` over `ℚ` together with the theorem of
the cube, written in coordinates.**

Let `A` be an abelian variety over `ℚ` and `L` a *symmetric* very ample
line bundle on it, giving a closed immersion `φ : A ↪ ℙⁿ_ℚ`.  Write
`x = φ(P)` and `y = φ(Q)` for the homogeneous coordinate vectors of two
rational points, and `z` for their **Segre product** `z (i,j) = xᵢ · y_j`,
the coordinate vector of `(P, Q)` in `ℙⁿ × ℙⁿ ↪ ℙ^{(n+1)²−1}`.

The **theorem of the cube** says that for symmetric `L`

  `σ* L ⊗ δ* L ≅ p₁* L² ⊗ p₂* L²`   on `A × A`,

where `σ (P,Q) = P + Q` and `δ (P,Q) = P − Q`.  Concretely: the Segre
product of the coordinate vectors of `P + Q` and `P − Q` is computed from
`(x, y)` by forms of **bidegree `(2,2)`**.  A monomial of bidegree
`(2,2)` is `x_a x_b y_c y_d = z_{(a,c)} · z_{(b,d)}`, so a bidegree-`(2,2)`
form in `(x, y)` is a form of degree **`2`** in the Segre variables `z`.
That is the field `cube` below, and it is the only geometric input.

The remaining field, `cert`, is the *effective Nullstellensatz
certificate* that `Mathlib`'s lower height bound needs.  Geometrically it
says the forms `cube` have no common zero on the image of `A × A` — i.e.
that `(P, Q) ↦ (P+Q, P−Q)` really is a morphism, defined everywhere.  It
is asked for only **pointwise at Segre points of `A × A`**, not as a
polynomial identity, which is the weakest form that suffices.

**FAITHFULNESS AUDIT.**

*Not vacuous, and not weaker than what it produces.*  Anything satisfying
this structure yields a genuine `ProjectiveHeightSource` — that is
`toProjectiveHeightSource`, proven below — so the leaf that produces a
`CubeEmbedding` is at least as strong as the leaf it replaces.  In the
other direction it is not *too* strong: every symmetric very ample `L` on
an abelian variety over `ℚ` supplies all five data, by the theorem of the
cube and the projective Nullstellensatz.

*It is cheap exactly when `A(ℚ)` is finite.*  That is correct rather than a
defect: a finite group is finitely generated, so the consumer's conclusion
holds for that reason anyway.

**CORRECTED 2026-07-30 (flt-lean-167) — the witness this note used to quote
covers only the TRIVIAL group.**  It read "`dim = 1`, `coords ≡ ![1]`,
`cube = z`, `certDeg = 0`, `cert = 1`", and `dim = 1` is fatal to it *whatever
`coords` is*: `coords_ne_zero` forces the single coordinate to be nonzero, so
`coords P = (coords P i₀ / coords Q i₀) • coords Q` holds for every `P, Q`, and
`injective_of_smul` then hands back `P = Q`.  Machine-checked as
`cm.dim = 1 → Subsingleton A` against `CubeModel` (the same four fields appear
here), so it is a refutation and not a reading.  The correct witness for a
general finite `A` is on `CubeModel` below.

*`dim = 0` is uninhabited*, since `coords_ne_zero` is unsatisfiable when
there are no coordinates.  Nothing has to rule it out by hand.

**WHY THIS IS A CUT AND NOT A RESTATEMENT.**  `parallelogram` mentions
`ℝ`, `logHeight` and an unquantified constant; none of the five fields
here does.  So the leaf built on `CubeEmbedding` is a statement of pure
algebraic geometry — projectivity of an abelian variety, a symmetric very
ample line bundle, the theorem of the cube — with every real-analytic
step discharged in `parallelogram` below. -/
structure CubeEmbedding (A : Type*) [AddCommGroup A] where
  /-- the number of homogeneous coordinates -/
  dim : ℕ
  /-- homogeneous coordinates of a point -/
  coords : A → (Fin dim → ℚ)
  /-- a homogeneous coordinate vector is nonzero -/
  coords_ne_zero : ∀ P : A, coords P ≠ 0
  /-- the induced map to `ℙ^{dim-1}(ℚ)` is injective -/
  injective_of_smul : ∀ P Q : A, ∀ c : ℚ, c ≠ 0 → coords P = c • coords Q → P = Q
  /-- the common degree of the certificate forms -/
  certDeg : ℕ
  /-- the forms of the **theorem of the cube**: bidegree `(2,2)` in `(x, y)`,
  hence degree `2` in the Segre variables `z (i,j) = xᵢ · y_j` -/
  cube : Fin dim × Fin dim → MvPolynomial (Fin dim × Fin dim) ℚ
  /-- `cube` is homogeneous of degree `2` in the Segre variables -/
  cube_homogeneous : ∀ k, (cube k).IsHomogeneous 2
  /-- the Nullstellensatz certificate forms -/
  cert : (Fin dim × Fin dim) × (Fin dim × Fin dim) → MvPolynomial (Fin dim × Fin dim) ℚ
  /-- the certificate forms are homogeneous of degree `certDeg` -/
  cert_homogeneous : ∀ a, (cert a).IsHomogeneous certDeg
  /-- **the theorem of the cube**: evaluated at the Segre point of `(P, Q)`, the
  forms `cube` compute the Segre product of the coordinates of `P + Q` and
  `P − Q`, up to one common nonzero scalar -/
  cube_eval : ∀ P Q : A, ∃ c : ℚ, c ≠ 0 ∧ ∀ k : Fin dim × Fin dim,
    MvPolynomial.eval (fun m : Fin dim × Fin dim => coords P m.1 * coords Q m.2) (cube k)
      = c * (coords (P + Q) k.1 * coords (P - Q) k.2)
  /-- the certificate identity, asked for only at the Segre points of `A × A`:
  the forms `cube` have no common zero there -/
  cert_eval : ∀ P Q : A, ∀ k : Fin dim × Fin dim,
    ∑ j : Fin dim × Fin dim,
        MvPolynomial.eval (fun m : Fin dim × Fin dim => coords P m.1 * coords Q m.2) (cert (k, j))
          * MvPolynomial.eval
              (fun m : Fin dim × Fin dim => coords P m.1 * coords Q m.2) (cube j)
      = (coords P k.1 * coords Q k.2) ^ (certDeg + 2)

namespace CubeEmbedding

variable (ce : CubeEmbedding A)

/-- **The height of a Segre product is the sum of the heights** — this is
`Height.logHeight_fun_mul_eq`, and it is the reason the bidegree-`(2,2)`
packaging works: it converts `logHeight z` into
`logHeight x + logHeight y` on the source, and the height of the Segre
product of `φ(P+Q)` and `φ(P−Q)` into `h(P+Q) + h(P−Q)` on the target. -/
theorem logHeight_segre (P Q : A) :
    logHeight (fun m : Fin ce.dim × Fin ce.dim => ce.coords P m.1 * ce.coords Q m.2)
      = logHeight (ce.coords P) + logHeight (ce.coords Q) :=
  logHeight_fun_mul_eq (ce.coords_ne_zero P) (ce.coords_ne_zero Q)

/-- **The forms of the cube evaluate to something of height
`h(P+Q) + h(P−Q)`** (PROVEN) — the common scalar `c` is invisible to the
height (`Height.logHeight_smul_eq_logHeight`), and what is left is a Segre
product. -/
theorem logHeight_cube_eval (P Q : A) :
    logHeight (fun k => MvPolynomial.eval
        (fun m : Fin ce.dim × Fin ce.dim => ce.coords P m.1 * ce.coords Q m.2) (ce.cube k))
      = logHeight (ce.coords (P + Q)) + logHeight (ce.coords (P - Q)) := by
  obtain ⟨c, hc, hck⟩ := ce.cube_eval P Q
  have hfun : (fun k : Fin ce.dim × Fin ce.dim => MvPolynomial.eval
      (fun m : Fin ce.dim × Fin ce.dim => ce.coords P m.1 * ce.coords Q m.2) (ce.cube k))
      = c • (fun k : Fin ce.dim × Fin ce.dim =>
          ce.coords (P + Q) k.1 * ce.coords (P - Q) k.2) := by
    funext k
    exact hck k
  rw [hfun, logHeight_smul_eq_logHeight _ hc]
  exact logHeight_fun_mul_eq (ce.coords_ne_zero _) (ce.coords_ne_zero _)

/-- **The approximate parallelogram law** (PROVEN, from the theorem of the
cube) — the single analytic step of the theory of heights on an abelian
variety, and the whole of what `CubeEmbedding` buys.

Both directions are `Mathlib`'s height comparison for a family of
homogeneous forms of degree `N = 2`, applied to `cube` at the Segre point
`z` of `(P, Q)`:

* `Height.logHeight_eval_le'` gives
  `logHeight (cube z) ≤ C₁ + 2 · logHeight z`;
* `Height.logHeight_eval_ge'`, fed the certificate `cert_eval`, gives
  `C₂ + 2 · logHeight z ≤ logHeight (cube z)`.

By `logHeight_segre` the right-hand side is `2 h(P) + 2 h(Q)`, and by
`logHeight_cube_eval` the left-hand side is `h(P+Q) + h(P−Q)`.  Note the
cancellation this depends on: *individually* `h(P+Q)` and `h(P−Q)` are
only bounded by `2h(P) + 2h(Q) + O(1)` each, and it is exactly the
theorem of the cube — the statement that their *Segre product* has
bidegree `(2,2)` rather than each factor separately — that makes the sum
come out right. -/
theorem parallelogram : ∃ C : ℝ, ∀ P Q : A,
    |logHeight (ce.coords (P + Q)) + logHeight (ce.coords (P - Q))
      - 2 * logHeight (ce.coords P) - 2 * logHeight (ce.coords Q)| ≤ C := by
  obtain ⟨C₁, hC₁⟩ := logHeight_eval_le' (K := ℚ) ce.cube_homogeneous
  obtain ⟨C₂, hC₂⟩ := logHeight_eval_ge' (K := ℚ) (N := 2) ce.cert_homogeneous
  refine ⟨max C₁ (-C₂), fun P Q => abs_sub_le_iff.mpr ⟨?_, ?_⟩⟩
  · have h1 := hC₁ (fun m : Fin ce.dim × Fin ce.dim => ce.coords P m.1 * ce.coords Q m.2)
    rw [ce.logHeight_cube_eval P Q, ce.logHeight_segre P Q] at h1
    have : C₁ ≤ max C₁ (-C₂) := le_max_left _ _
    push_cast at h1
    linarith
  · have h2 := hC₂ ce.cube (ce.cert_eval P Q)
    rw [ce.logHeight_cube_eval P Q, ce.logHeight_segre P Q] at h2
    have : -C₂ ≤ max C₁ (-C₂) := le_max_right _ _
    push_cast at h2
    linarith

/-- **A cube embedding is a projective height source** (PROVEN) — the four
shared fields are carried over verbatim and the analytic field is
`parallelogram` above.

This is the composite the Mordell–Weil assembly consumes:
`CubeEmbedding → ProjectiveHeightSource → WeilHeight →
DescentHeight → AddGroup.FG`. -/
def toProjectiveHeightSource : ProjectiveHeightSource A where
  dim := ce.dim
  coords := ce.coords
  coords_ne_zero := ce.coords_ne_zero
  injective_of_smul := ce.injective_of_smul
  parallelogram := ce.parallelogram

end CubeEmbedding

/-!
### Shedding the Nullstellensatz certificate

`CubeEmbedding` still asks its producer for `cert` / `cert_homogeneous` /
`cert_eval`, and those are **not geometry either**: they are an *effective
homogeneous Nullstellensatz certificate*, a fact of commutative algebra
about the forms `cube` once one knows they have no common zero on the
Segre image.  `CubeModel` below asks for the geometric statement instead
— the forms of the ideal of the image, and non-vanishing on that image
over an algebraic closure — and `CubeModel.nonempty_cubeEmbedding`
manufactures the certificate.  It is PROVEN, over `Mathlib`'s
`MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`.
-/

/-- **Taking a homogeneous component past multiplication by a homogeneous
factor** (PROVEN).  If `q` is homogeneous of degree `d` then the degree-`n`
part of `p * q` is `(degree-(n − d) part of p) * q`, and is zero when
`n < d`.

`Mathlib` has `MvPolynomial.homogeneousComponent` and
`MvPolynomial.homogeneousComponent_C_mul` but not this; it is what lets an
arbitrary ideal-membership certificate be replaced by a *homogeneous* one,
which is what `Height.logHeight_eval_ge'` requires. -/
theorem homogeneousComponent_mul_right_of_isHomogeneous {σ R : Type*} [CommRing R]
    {q : MvPolynomial σ R} {d : ℕ} (hq : q.IsHomogeneous d) (p : MvPolynomial σ R) (n : ℕ) :
    MvPolynomial.homogeneousComponent n (p * q)
      = (if d ≤ n then MvPolynomial.homogeneousComponent (n - d) p else 0) * q := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial e r =>
      have hm : (MvPolynomial.monomial e r : MvPolynomial σ R).IsHomogeneous e.degree :=
        MvPolynomial.isHomogeneous_monomial _ rfl
      rw [MvPolynomial.homogeneousComponent_of_mem (hm.mul hq),
        MvPolynomial.homogeneousComponent_of_mem hm]
      by_cases hdn : d ≤ n
      · simp only [hdn, if_true]
        by_cases he : n - d = e.degree
        · have : n = e.degree + d := by omega
          simp [this]
        · have : n ≠ e.degree + d := by omega
          simp [he, this]
      · have : n ≠ e.degree + d := by omega
        simp [hdn, this]
  | add p₁ p₂ h₁ h₂ =>
      rw [add_mul, map_add, h₁, h₂, map_add]
      split <;> ring

/-- **THE EFFECTIVE HOMOGENEOUS NULLSTELLENSATZ OVER `ℚ`** (PROVEN) — if a
finite family `f` of forms of a common degree `N` has no common zero on the
projective set cut out by a finite family `g` of forms, *over an algebraic
closure*, then some fixed power of every variable is a **homogeneous**
combination of the `f` modulo the `g`, with `ℚ`-rational coefficients.

This is the whole of `CubeEmbedding.cert`, and it is pure commutative
algebra: no group, no height, no `ℝ`.

**The `ℚ`-rationality is free**, which is the one point worth flagging.
`Mathlib`'s `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical` is already
stated for an ideal over a base field `k` with its zero locus taken in an
algebraically closed extension `K`, and returns the radical **over `k`**.
So the descent from `ℚ̄` to `ℚ` that this statement appears to need is
performed inside that lemma, and no faithful-flatness argument is required
here.

**Homogeneity is the other half**, and is
`homogeneousComponent_mul_right_of_isHomogeneous` above: an arbitrary
certificate `X k ^ n = ∑ aᵢ fᵢ + ∑ b_j g_j` becomes a homogeneous one by
taking degree-`n` components of both sides, because each `fᵢ` and each
`g_j` is homogeneous.

The conclusion is stated with the `g`-part already discharged — it is an
identity at every `ℚ`-point where the `g` vanish, not a polynomial
identity — because that is the form `CubeEmbedding.cert_eval` wants. -/
theorem exists_homogeneousCertificate {σ ι κ : Type*} [Fintype σ] [DecidableEq σ]
    [Fintype ι] [Fintype κ] {N : ℕ}
    (f : ι → MvPolynomial σ ℚ) (hf : ∀ i, (f i).IsHomogeneous N)
    (dg : κ → ℕ) (g : κ → MvPolynomial σ ℚ) (hg : ∀ j, (g j).IsHomogeneous (dg j))
    (hnv : ∀ z : σ → AlgebraicClosure ℚ, z ≠ 0 →
        (∀ j, MvPolynomial.aeval z (g j) = 0) → ∃ i, MvPolynomial.aeval z (f i) ≠ 0) :
    ∃ (m : ℕ) (c : σ → ι → MvPolynomial σ ℚ),
      (∀ k i, (c k i).IsHomogeneous m) ∧
      ∀ z : σ → ℚ, (∀ j, MvPolynomial.eval z (g j) = 0) → ∀ k : σ,
        ∑ i, MvPolynomial.eval z (c k i) * MvPolynomial.eval z (f i) = z k ^ (m + N) := by
  classical
  set K := AlgebraicClosure ℚ with hK
  set F : ι ⊕ κ → MvPolynomial σ ℚ := Sum.elim f g with hF
  set I : Ideal (MvPolynomial σ ℚ) := Ideal.span (Set.range F) with hI
  have hmemI : ∀ t, F t ∈ I := fun t => Ideal.subset_span ⟨t, rfl⟩
  -- 1.  The zero locus of `I` over `K` is contained in `{0}`.
  have hzl : MvPolynomial.zeroLocus K I ⊆ {(0 : σ → K)} := by
    intro z hz
    by_contra hne
    obtain ⟨i, hi⟩ := hnv z (by simpa using hne) fun j => hz _ (hmemI (Sum.inr j))
    exact hi (hz _ (hmemI (Sum.inl i)))
  -- 2.  Hence every variable lies in the radical of `I`, ALREADY OVER `ℚ`.
  have hrad : ∀ k : σ, (MvPolynomial.X k : MvPolynomial σ ℚ) ∈ I.radical := by
    intro k
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K)]
    intro z hz
    have hz0 : z = 0 := hzl hz
    subst hz0
    simp
  choose nk hnk using fun k => (Ideal.mem_radical_iff).mp (hrad k)
  -- 3.  A uniform exponent, chosen `≥ N` so that the certificate degree is `n − N`.
  set n : ℕ := (Finset.univ.sup nk) + N with hn
  have hNn : N ≤ n := Nat.le_add_left _ _
  have hpow : ∀ k : σ, (MvPolynomial.X k : MvPolynomial σ ℚ) ^ n ∈ I := by
    intro k
    have hle : nk k ≤ n := le_trans (Finset.le_sup (Finset.mem_univ k)) (Nat.le_add_right _ _)
    have hsplit : (MvPolynomial.X k : MvPolynomial σ ℚ) ^ n
        = MvPolynomial.X k ^ nk k * MvPolynomial.X k ^ (n - nk k) := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit]
    exact Ideal.mul_mem_right _ _ (hnk k)
  -- 4.  Write each `X k ^ n` as an explicit finite combination.
  have hcomb : ∀ k : σ, ∃ a : ι ⊕ κ → MvPolynomial σ ℚ,
      ∑ t, a t * F t = (MvPolynomial.X k : MvPolynomial σ ℚ) ^ n := by
    intro k
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (MvPolynomial σ ℚ)).mp (hpow k)
    exact ⟨a, by simpa [smul_eq_mul] using ha⟩
  choose a ha using hcomb
  -- 5.  Take homogeneous components of degree `n`; the `f`-coefficients become
  --     homogeneous of degree `n − N` and the `g`-part stays a multiple of `g`.
  have key : ∀ k : σ, (MvPolynomial.X k : MvPolynomial σ ℚ) ^ n
      = (∑ i, MvPolynomial.homogeneousComponent (n - N) (a k (Sum.inl i)) * f i)
        + ∑ j, (if dg j ≤ n then MvPolynomial.homogeneousComponent (n - dg j)
            (a k (Sum.inr j)) else 0) * g j := by
    intro k
    calc (MvPolynomial.X k : MvPolynomial σ ℚ) ^ n
        = MvPolynomial.homogeneousComponent n ((MvPolynomial.X k : MvPolynomial σ ℚ) ^ n) :=
          (MvPolynomial.homogeneousComponent_eq_self
            (MvPolynomial.isHomogeneous_X_pow k n)).symm
      _ = MvPolynomial.homogeneousComponent n (∑ t, a k t * F t) := by rw [ha k]
      _ = ∑ t, MvPolynomial.homogeneousComponent n (a k t * F t) := by rw [map_sum]
      _ = (∑ i, MvPolynomial.homogeneousComponent n (a k (Sum.inl i) * f i))
            + ∑ j, MvPolynomial.homogeneousComponent n (a k (Sum.inr j) * g j) := by
          rw [Fintype.sum_sum_type]; rfl
      _ = _ := by
          congr 1
          · refine Finset.sum_congr rfl fun i _ => ?_
            rw [homogeneousComponent_mul_right_of_isHomogeneous (hf i), if_pos hNn]
          · refine Finset.sum_congr rfl fun j _ => ?_
            rw [homogeneousComponent_mul_right_of_isHomogeneous (hg j)]
  refine ⟨n - N, fun k i => MvPolynomial.homogeneousComponent (n - N) (a k (Sum.inl i)), ?_, ?_⟩
  · intro k i; exact MvPolynomial.homogeneousComponent_isHomogeneous _ _
  · intro z hz k
    have h := congrArg (MvPolynomial.eval z) (key k)
    simp only [map_pow, MvPolynomial.eval_X, map_add, map_sum, map_mul] at h
    have hzero : ∀ j ∈ (Finset.univ : Finset κ),
        MvPolynomial.eval z (if dg j ≤ n then MvPolynomial.homogeneousComponent (n - dg j)
            (a k (Sum.inr j)) else 0) * MvPolynomial.eval z (g j) = 0 := by
      intro j _; rw [hz j, mul_zero]
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, add_zero] at h
    rw [Nat.sub_add_cancel hNn]
    exact h.symm

/-- **A projective embedding of `A` over `ℚ` by a symmetric bundle, with the
theorem of the cube — and NOTHING ELSE.**

This is `CubeEmbedding` with the Nullstellensatz certificate replaced by the
geometry it encodes.  `CubeEmbedding.cert` / `cert_eval` are an *effective*
certificate: polynomials witnessing that the forms `cube` have no common zero
on the Segre image.  A producer coming from algebraic geometry does not have
those polynomials in hand — what it has is

* `rel`, homogeneous forms cutting out the Segre image of `A × A` in
  `ℙ^{dim²−1}` (the abelian variety `A × A` is projective, so its image under
  the Segre embedding is closed, and its homogeneous ideal is finitely
  generated by Hilbert's basis theorem);
* `cube_nonvanishing`, the statement that `(P, Q) ↦ (P + Q, P − Q)` is a
  *morphism defined everywhere* — i.e. the forms `cube` do not all vanish at
  any point of the affine cone over that image other than the origin.  This is
  asked over an ALGEBRAIC CLOSURE, which is where the geometry lives and where
  the Nullstellensatz applies; `ℚ`-points alone would not suffice.

`CubeModel.nonempty_cubeEmbedding` below turns that into a `CubeEmbedding`,
using `exists_homogeneousCertificate` above.  So a producer of a `CubeModel`
owes **only** the three classical theorems: projectivity of an abelian
variety, a symmetric very ample line bundle, and the theorem of the cube.

**FAITHFULNESS AUDIT.**

*Not weaker than what it produces* — `nonempty_cubeEmbedding` is proven, so a
`CubeModel` yields a genuine `CubeEmbedding` and hence, through
`CubeEmbedding.toProjectiveHeightSource`, a `ProjectiveHeightSource`.

*Not stronger than the geometry supplies.*  Every field is something a
symmetric very ample `L` on an abelian variety over `ℚ` gives: `coords` from
the closed immersion `φ_L`, `injective_of_smul` because a closed immersion is
a monomorphism, `cube` / `cube_eval` from the theorem of the cube
`σ*L ⊗ δ*L ≅ p₁*L² ⊗ p₂*L²` (bidegree `(2,2)` in `(x, y)` is degree `2` in the
Segre variables), `rel` from projectivity of `A × A`, and `cube_nonvanishing`
because `(P, Q) ↦ (P + Q, P − Q)` is a morphism on all of `A × A`.

*Symmetry of `L` is NOT a field here*, and that is deliberate: symmetry is
used to *prove* `cube_eval` — for non-symmetric `L` the cube gives
`σ*L ⊗ δ*L ≅ p₁*(L ⊗ [−1]*L) ⊗ p₂*(L ⊗ [−1]*L)` instead — and adding it as a
field would record a hypothesis that no consumer reads.

*It is cheap exactly when `A(ℚ)` is finite.*  That is correct rather than a
defect: a finite group is finitely generated, so the consumer's conclusion
holds anyway.

**THE WITNESS, CORRECTED 2026-07-30 (flt-lean-167).**  This note used to
exhibit `dim = 1`, `coords ≡ ![1]`, `cube = z`, `relDim = 0`, with
`cube_nonvanishing` holding "because `z ≠ 0` forces `z (0,0) ≠ 0`".  That
package exists only for the TRIVIAL group, and the obstruction is `dim = 1`
alone rather than the particular `coords`: `coords_ne_zero` makes the single
coordinate nonzero, so `coords P = (coords P i₀ / coords Q i₀) • coords Q` for
*every* pair, and `injective_of_smul` returns `P = Q`.  Machine-checked as
`cm.dim = 1 → Subsingleton A`, from `coords_ne_zero` and `injective_of_smul`
and nothing else.  `relDim = 0` is wrong for a second, independent reason:
with no relations, `cube_nonvanishing` would have to hold at every nonzero
`z`, not only on the cone over the Segre image.

The construction that DOES work for an arbitrary finite `A`, and which a
successor should use if this non-vacuity is ever wanted as a Lean term rather
than as an audit, is the INDICATOR basis: `dim = Nat.card A` with `coords P`
the indicator of `P`, so that the Segre point of `(P, Q)` is the indicator of
`(P, Q)`.  Then

* `cube k = ∑_{(P,Q) : P+Q = k.1, P−Q = k.2} z (P,Q) ^ 2`, homogeneous of
  degree `2`, and `cube_eval` holds with `c = 1`;
* `relDim` counts the pairs `m ≠ m'`, with `rel = z m * z m'` and
  `relDeg = 2`; these vanish at every Segre point because at most one
  coordinate there is nonzero;
* `cube_nonvanishing`: those relations force a nonzero `z` on the cone to have
  exactly one nonzero coordinate `z (P,Q) = t`, and then
  `cube (P+Q, P−Q) z = t² ≠ 0` — every other summand of that form vanishes, so
  no `2`-torsion coincidence in `P' + Q' = P + Q`, `P' − Q' = P − Q` can
  cancel it.

`coords_ne_zero` and `injective_of_smul` are immediate for the indicator basis.
It is deliberately NOT declared as a lemma here: nothing in the root cone
consumes it, so it would be free-floating code.

**THE RECIPE THIS PARAGRAPH USED TO GIVE WAS FALSE** (found and corrected
2026-07-31).  It read: "`dim = 1`, `coords ≡ ![1]`, `cube = z`, `relDim = 0`".
Constant coordinates satisfy no such thing: `injective_of_smul P Q 1` applied to
`coords P = 1 • coords Q` — which holds for ANY `P, Q` when `coords` is constant
— returns `P = Q`, so that recipe forces `Subsingleton A` and is available only
for the TRIVIAL group, not for every finite one.  (Checked in Lean; the
refutation is three tactic lines and needs no hypothesis on `dim`.)  The claim
was quoted onward into
`Fermat/FLT/ModularCurve/HyperellipticJacobian.lean`'s `exists_cubeModel_pic`
as its "not vacuous" argument, so an agent could have burned a cycle on it.
The correct construction is the INDICATOR embedding, `dim = #A` and
`coords P = e_P`, which is what `nonempty_cubeModel_of_finite` builds.

**A WARNING ABOUT CUTTING THIS FURTHER, and the axis that was searched.**  The
obvious next cut is to split the embedding (`dim`, `coords`,
`coords_ne_zero`, `injective_of_smul`, `rel`) from the cube (`cube`,
`cube_eval`, `cube_nonvanishing`), leaving a leaf "any symmetric projective
embedding of `A(ℚ)` satisfies the theorem of the cube".  **That leaf is
FALSE**, and the counterexample is cheap: take an elliptic curve over `ℚ` with
`E(ℚ) ≅ ℤ` (say `y² + y = x³ − x`), `dim = 3`, `coords n = (1, n³, n⁶)` — this
is injective up to scaling, nonzero, and `[−1]` is induced by the linear map
`diag(1, −1, 1)` — and its height is `6 log|n| + O(1)`, for which
`h(2n) + h(0) − 4h(n) = 6 log 2n − 24 log n` is unbounded.  Nothing about the
*abstract group* `A(ℚ)` plus an injection into `ℙⁿ(ℚ)` constrains the height,
so any faithful further cut must carry the link between `coords` and the
scheme — i.e. must be made at the level of the invertible sheaf and its
global sections, not in coordinates.  The axis searched here is
COORDINATE-LEVEL cuts.

**THE SHEAF-LEVEL AXIS WAS TRIED ON 2026-07-28 AND IT WORKS.**  The producer
`Fermat.exists_cubeModel_of_abelianScheme` (`Fermat/FLT/ModularCurve/X0.lean`)
is now PROVEN over `Fermat.exists_isAmpleSheaf_symmetric_cube`
(`Fermat/FLT/Modularity/AbelianSchemeIsogeny.lean` — a symmetric, normalized,
ample invertible sheaf with `σ^*L ⊗ δ^*L ≅ p₁^*L^{⊗2} ⊗ p₂^*L^{⊗2}`, over any
field) and `Fermat.nonempty_cubeModel_of_isAmpleSheaf_cube` (the coordinate
dictionary).  The counterexample above does not lift to that cut, because
there `coords` is manufactured from `L` rather than chosen: `n ↦ (1 : n³ : n⁶)`
would have to be the restriction to the Zariski-dense set `E(ℚ)` of a morphism
`E ⟶ ℙ²` given by global sections, and a degree-`d` such morphism has height
`≍ d · ĥ(P) ≍ d n²`, never `6 log|n|`.  The blocker the producer's docstring
recorded against this axis — "there is no `Γ(L, ⊤) → Γ(modPullback P L, ⊤)`
pullback-of-sections map" — was already false: it is
`Fermat.modPullbackSection` (`Modularity/AmpleSheaf.lean`), PROVEN. -/
structure CubeModel (A : Type*) [AddCommGroup A] where
  /-- the number of homogeneous coordinates -/
  dim : ℕ
  /-- homogeneous coordinates of a point -/
  coords : A → (Fin dim → ℚ)
  /-- a homogeneous coordinate vector is nonzero -/
  coords_ne_zero : ∀ P : A, coords P ≠ 0
  /-- the induced map to `ℙ^{dim-1}(ℚ)` is injective -/
  injective_of_smul : ∀ P Q : A, ∀ c : ℚ, c ≠ 0 → coords P = c • coords Q → P = Q
  /-- the forms of the **theorem of the cube**: bidegree `(2,2)` in `(x, y)`,
  hence degree `2` in the Segre variables `z (i,j) = xᵢ · y_j` -/
  cube : Fin dim × Fin dim → MvPolynomial (Fin dim × Fin dim) ℚ
  /-- `cube` is homogeneous of degree `2` in the Segre variables -/
  cube_homogeneous : ∀ k, (cube k).IsHomogeneous 2
  /-- **the theorem of the cube**: evaluated at the Segre point of `(P, Q)`, the
  forms `cube` compute the Segre product of the coordinates of `P + Q` and
  `P − Q`, up to one common nonzero scalar -/
  cube_eval : ∀ P Q : A, ∃ c : ℚ, c ≠ 0 ∧ ∀ k : Fin dim × Fin dim,
    MvPolynomial.eval (fun m : Fin dim × Fin dim => coords P m.1 * coords Q m.2) (cube k)
      = c * (coords (P + Q) k.1 * coords (P - Q) k.2)
  /-- the number of generators of the homogeneous ideal of the Segre image -/
  relDim : ℕ
  /-- their degrees -/
  relDeg : Fin relDim → ℕ
  /-- homogeneous generators of the ideal of the Segre image of `A × A` -/
  rel : Fin relDim → MvPolynomial (Fin dim × Fin dim) ℚ
  /-- the generators are homogeneous -/
  rel_homogeneous : ∀ i, (rel i).IsHomogeneous (relDeg i)
  /-- the generators vanish on the image -/
  rel_eval : ∀ P Q : A, ∀ i,
    MvPolynomial.eval (fun m : Fin dim × Fin dim => coords P m.1 * coords Q m.2) (rel i) = 0
  /-- **`(P, Q) ↦ (P + Q, P − Q)` is a morphism defined everywhere**: over an
  algebraic closure, the forms `cube` have no common zero on the affine cone
  over the Segre image apart from the origin -/
  cube_nonvanishing : ∀ z : Fin dim × Fin dim → AlgebraicClosure ℚ, z ≠ 0 →
    (∀ i, MvPolynomial.aeval z (rel i) = 0) → ∃ k, MvPolynomial.aeval z (cube k) ≠ 0

/-- **A cube model is a cube embedding** (PROVEN) — the Nullstellensatz
certificate `cert` / `cert_homogeneous` / `cert_eval` is manufactured from the
geometric non-vanishing by `exists_homogeneousCertificate`.

This is the step that removes commutative algebra from the geometry leaf:
after it, the only thing a producer owes is projectivity of an abelian
variety, a symmetric very ample line bundle, and the theorem of the cube. -/
theorem CubeModel.nonempty_cubeEmbedding (cm : CubeModel A) : Nonempty (CubeEmbedding A) := by
  obtain ⟨m, c, hc, hcert⟩ :=
    exists_homogeneousCertificate (N := 2) cm.cube cm.cube_homogeneous cm.relDeg cm.rel
      cm.rel_homogeneous cm.cube_nonvanishing
  exact ⟨{ dim := cm.dim
           coords := cm.coords
           coords_ne_zero := cm.coords_ne_zero
           injective_of_smul := cm.injective_of_smul
           certDeg := m
           cube := cm.cube
           cube_homogeneous := cm.cube_homogeneous
           cert := fun b => c b.1 b.2
           cert_homogeneous := fun b => hc b.1 b.2
           cube_eval := cm.cube_eval
           cert_eval := fun P Q k =>
             hcert (fun w : Fin cm.dim × Fin cm.dim => cm.coords P w.1 * cm.coords Q w.2)
               (cm.rel_eval P Q) k }⟩

open MvPolynomial in
/-- **A FINITE abelian group carries a `CubeModel`** (PROVEN) — the honest version of the
"cheap when finite" remark on `CubeModel`, whose recorded recipe (`dim = 1`, `coords ≡ ![1]`)
was FALSE; see the audit there.

The construction is the INDICATOR embedding, which is the degenerate `|A|`-dimensional
representation of "every point is its own coordinate hyperplane":

* `dim = #A` and `coords P = e_{P}`, the standard basis vector, through any bijection
  `e : A ≃ Fin #A`.  `injective_of_smul` is immediate: evaluating `coords P = c • coords Q`
  at the index `e Q` gives `[P = Q] = c ≠ 0`.
* The Segre point of `(P, Q)` is then the basis vector `e_{(e P, e Q)}` of the `#A²`
  Segre variables, so **the Segre image is the set of coordinate points**, whose homogeneous
  ideal is generated by the `z_m z_{m'}` with `m ≠ m'` — that is `rel`.
* `cube k = Σ_{m : (m₁ + m₂, m₁ − m₂) = k} z_m²`, a sum of squares of variables, hence
  homogeneous of degree `2`.  At the Segre point of `(P, Q)` exactly the term `m = (P, Q)`
  survives, and it survives precisely when `k = (P + Q, P − Q)`, which is `cube_eval` with
  `c = 1`.  Note the index map `m ↦ (m₁ + m₂, m₁ − m₂)` need NOT be injective — it is not
  when `A` has `2`-torsion — and the construction does not need it to be, since the extra
  terms of the sum vanish at every Segre point anyway.
* `cube_nonvanishing`: `rel` forces a point of the cone to have at most one nonzero
  coordinate, say at `m₀`, and then `cube (m₀₁ + m₀₂, m₀₁ − m₀₂)` evaluates to `z_{m₀}² ≠ 0`.

This carries no arithmetic: the height it produces through
`CubeModel.nonempty_cubeEmbedding` is bounded on all of `A`, and Northcott is vacuous
because `A` is finite. -/
theorem nonempty_cubeModel_of_finite (A : Type*) [AddCommGroup A] [Finite A] :
    Nonempty (CubeModel A) := by
  classical
  obtain ⟨n, ⟨e⟩⟩ : ∃ n : ℕ, Nonempty (A ≃ Fin n) := ⟨Nat.card A, ⟨Finite.equivFin A⟩⟩
  obtain ⟨N, ⟨ε⟩⟩ : ∃ N : ℕ, Nonempty (Fin N ≃ (Fin n × Fin n) × (Fin n × Fin n)) :=
    ⟨Fintype.card ((Fin n × Fin n) × (Fin n × Fin n)), ⟨(Fintype.equivFin _).symm⟩⟩
  refine ⟨
    { dim := n
      coords := fun P i => if i = e P then 1 else 0
      coords_ne_zero := ?_
      injective_of_smul := ?_
      cube := fun k => ∑ m ∈ Finset.univ.filter
        (fun m : Fin n × Fin n =>
          (e (e.symm m.1 + e.symm m.2), e (e.symm m.1 - e.symm m.2)) = k), (X m) ^ 2
      cube_homogeneous := ?_
      cube_eval := ?_
      relDim := N
      relDeg := fun _ => 2
      rel := fun i => if (ε i).1 = (ε i).2 then 0 else X (ε i).1 * X (ε i).2
      rel_homogeneous := ?_
      rel_eval := ?_
      cube_nonvanishing := ?_ }⟩
  · intro P hP
    have := congrFun hP (e P)
    simp at this
  · intro P Q c hc hPQ
    by_cases hEq : e Q = e P
    · exact e.injective hEq.symm
    · exfalso
      have h := congrFun hPQ (e Q)
      simp only [Pi.smul_apply, smul_eq_mul] at h
      rw [if_neg hEq] at h
      exact hc (by simpa using h.symm)
  · intro k
    refine MvPolynomial.IsHomogeneous.sum _ _ _ ?_
    intro m _
    simpa using (isHomogeneous_X ℚ m).pow 2
  · intro P Q
    refine ⟨1, one_ne_zero, ?_⟩
    intro k
    have hsq : ∀ m : Fin n × Fin n,
        ((if m.1 = e P then (1 : ℚ) else 0) * (if m.2 = e Q then (1 : ℚ) else 0)) ^ 2
          = if m = (e P, e Q) then 1 else 0 := by
      intro m
      by_cases h1 : m.1 = e P <;> by_cases h2 : m.2 = e Q <;>
        simp [h1, h2, Prod.ext_iff]
    rw [map_sum]
    simp only [map_pow, eval_X, hsq]
    rw [Finset.sum_ite_eq' _ (e P, e Q) (fun _ => (1 : ℚ))]
    obtain ⟨k1, k2⟩ := k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.symm_apply_apply, Prod.mk.injEq, one_mul]
    by_cases h1 : k1 = e (P + Q)
    · subst h1
      by_cases h2 : k2 = e (P - Q)
      · subst h2; simp
      · simp [h2, Ne.symm h2]
    · by_cases h2 : k2 = e (P - Q)
      · subst h2; simp [h1, Ne.symm h1]
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  · intro i
    by_cases h : (ε i).1 = (ε i).2
    · rw [if_pos h]; exact isHomogeneous_zero _ _ _
    · rw [if_neg h]
      simpa using (isHomogeneous_X ℚ (ε i).1).mul (isHomogeneous_X ℚ (ε i).2)
  · intro P Q i
    by_cases h : (ε i).1 = (ε i).2
    · simp [h]
    · simp only [h, if_false, map_mul, eval_X]
      have hz : ∀ m : Fin n × Fin n,
          (if m.1 = e P then (1 : ℚ) else 0) * (if m.2 = e Q then (1 : ℚ) else 0)
            = if m = (e P, e Q) then 1 else 0 := by
        intro m
        by_cases h1 : m.1 = e P <;> by_cases h2 : m.2 = e Q <;>
          simp [h1, h2, Prod.ext_iff]
      rw [hz, hz]
      by_cases h1 : (ε i).1 = (e P, e Q) <;> by_cases h2 : (ε i).2 = (e P, e Q) <;>
        simp_all
  · intro z hz hrel
    obtain ⟨m₀, hm₀⟩ : ∃ m₀, z m₀ ≠ 0 := by
      by_contra hcon
      exact hz (funext fun m => not_not.mp fun h => hcon ⟨m, h⟩)
    have hvanish : ∀ m, m ≠ m₀ → z m = 0 := by
      intro m hm
      have hi := hrel (ε.symm (m, m₀))
      simp only [Equiv.apply_symm_apply, hm, if_false, map_mul, aeval_X] at hi
      exact (mul_eq_zero.mp hi).resolve_right hm₀
    refine ⟨(e (e.symm m₀.1 + e.symm m₀.2), e (e.symm m₀.1 - e.symm m₀.2)), ?_⟩
    rw [map_sum]
    simp only [map_pow, aeval_X]
    have hmem : m₀ ∈ Finset.univ.filter
        (fun m : Fin n × Fin n =>
          (e (e.symm m.1 + e.symm m.2), e (e.symm m.1 - e.symm m.2))
            = (e (e.symm m₀.1 + e.symm m₀.2), e (e.symm m₀.1 - e.symm m₀.2))) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    rw [Finset.sum_eq_single_of_mem m₀ hmem (fun m _ hm => by rw [hvanish m hm]; ring)]
    exact pow_ne_zero 2 hm₀

end Fermat
