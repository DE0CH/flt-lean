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

`ProjectiveHeightSource.toParallelogramHeight` turns that into a
`Fermat.ParallelogramHeight`, and hence — through
`Fermat.ParallelogramHeight.toDescentHeight` and
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
`ParallelogramHeight`** (PROVEN) — the naïve logarithmic height of the
homogeneous coordinates, with Northcott supplied by
`finite_setOf_logHeight_coords_le`.

Composed with `ParallelogramHeight.toDescentHeight` and
`fg_of_descentHeight`, this is the whole route from "the abelian variety
is projectively embedded and its naïve height satisfies the
parallelogram law" to "its group of rational points is finitely
generated", given weak Mordell–Weil. -/
noncomputable def ProjectiveHeightSource.toParallelogramHeight (ps : ProjectiveHeightSource A) :
    ParallelogramHeight A where
  height P := logHeight (ps.coords P)
  parallelogram := ps.parallelogram
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

*It is cheap exactly when `A(ℚ) `is finite* — with `dim = 1`,
`coords ≡ ![1]`, `cube = z`, `certDeg = 0`, `cert = 1` the whole package
holds for the trivial group.  That is correct rather than a defect: a
finite group is finitely generated, so the consumer's conclusion holds for
that reason anyway.

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
`CubeEmbedding → ProjectiveHeightSource → ParallelogramHeight →
DescentHeight → AddGroup.FG`. -/
def toProjectiveHeightSource : ProjectiveHeightSource A where
  dim := ce.dim
  coords := ce.coords
  coords_ne_zero := ce.coords_ne_zero
  injective_of_smul := ce.injective_of_smul
  parallelogram := ce.parallelogram

end CubeEmbedding

end Fermat
