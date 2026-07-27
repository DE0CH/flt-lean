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

end Fermat
