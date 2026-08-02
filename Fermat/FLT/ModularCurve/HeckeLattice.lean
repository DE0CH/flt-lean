/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.Data.Complex.Basic

/-!
# The integral Hecke lattice, and the eigenvalue argument for Shimura's
algebraicity theorem

This module is the **shape-free half of Shimura's algebraicity theorem**: the
step that turns *"the Hecke operators preserve a lattice"* into *"the Hecke
eigenvalues are algebraic integers"*.  It knows nothing about modular curves,
modular forms, `Γ₀(N)` or `Γ₁(N)` — it is linear algebra over `ℤ` — and that is
exactly why it lives here rather than in `X0.lean` or `X1.lean`: **one copy,
consumed by both sides.**

## The mathematics, in one paragraph

Let `f` be a normalised weight-two Hecke eigenform of level `N ≥ 1`, with
`T_n f = a_n f`.  Classically (Shimura, *Introduction to the arithmetic theory
of automorphic functions*, §3.5 and §7.5; Diamond–Shurman §6.5) the Hecke
correspondence `T_n` acts on the **integral homology** `H₁(X₀(N), ℤ)` resp.
`H₁(X₁(N), ℤ)`, a free `ℤ`-module of rank `2g`, and the period map

  `φ : H₁(X, ℤ) → ℂ,   γ ↦ ∫_γ ω_f`

is a nonzero `ℤ`-linear functional satisfying `φ ∘ T_n = a_n · φ`, because the
Hecke action on cycles is adjoint to the Hecke action on differentials.  Reading
`T_n` as an integer matrix in a `ℤ`-basis of the lattice, `a_n` is therefore a
root of the *monic integer* characteristic polynomial of that matrix — hence an
algebraic integer.  That last sentence is the whole content of this module, and
it is now Lean code rather than prose.

## What is here

* `isIntegral_of_intMatrix_mulVec` / `isIntegral_of_intMatrix_vecMul` (PROVEN):
  an eigenvalue of a matrix with **integer entries**, read on `ℂ`, is integral
  over `ℤ`.  Witness: `Matrix.charpoly`, which is monic
  (`Matrix.charpoly_monic`) and commutes with entrywise `ℤ → ℂ`
  (`Matrix.charpoly_map`).
* `IntegralHeckeEigensystem` — the packaging of the classical input: a rank, a
  family of integer matrices indexed by `n`, and a nonzero **period row vector**
  that is a simultaneous eigenvector with eigenvalue `a n`.
* `IntegralHeckeEigensystem.isIntegral_coeff` (PROVEN): from that packaging,
  `IsIntegral ℤ (a n)` for EVERY `n` at once.
* `IsIntegralHeckeStructure` — the SPACE-side packaging of the same input: a
  `ℂ`-module `V`, a family of `ℂ`-linear operators `T n` on it, and a finite
  `ℂ`-basis of `V` in which every `T n` has INTEGER matrix.  Nothing about
  eigenvectors, nothing about `a`.
* `IntegralHeckeEigensystem.ofIsIntegralHeckeStructure` (PROVEN): an
  `IsIntegralHeckeStructure` plus a NONZERO simultaneous eigenvector with
  eigenvalues `a n` is an `IntegralHeckeEigensystem a`.  This is the bridge the
  two modular-curve leaves consume, and it is why the residue on each side is a
  statement about `S₂(Γ)` rather than about matrices.

## Why the ROW (`ᵥ*`) convention, and not the column one

`period` is the period map, and the natural datum is its value on each element
of a `ℤ`-basis `b` of the lattice.  With `T n := LinearMap.toMatrix b b (T_n)`
the identity `φ (T_n x) = a n * φ x` reads, on basis vectors,

  `∑ i, φ (b i) * (T n) i j = a n * φ (b j)`,

which is literally `period ᵥ* T n = a n • period` — **no transpose anywhere**.
Had the structure been written with `*ᵥ`, every future construction would have
had to transpose the matrix of the Hecke operator, which is exactly the sort of
bookkeeping that turns into a sign error.  `Matrix.charpoly_transpose` makes the
two conventions equivalent for the conclusion, which is why
`isIntegral_of_intMatrix_vecMul` is a three-line consequence of the column form.

## The bridge from an abstract lattice — VERIFIED, and deliberately not committed

A future prover of the geometry will hold an abstract finite free `ℤ`-module
`L` (the homology), abstract `ℤ`-linear `T n : L →ₗ[ℤ] L`, and the period
functional `φ : L →ₗ[ℤ] ℂ` — not matrices.  The conversion is mechanical, and
the following was **written and COMPILED against this module on 2026-07-31**
(`lake env lean`, `EXIT=0`, zero errors):

```
noncomputable def IntegralHeckeEigensystem.ofPeriodMap {L : Type*} [AddCommGroup L]
    [Module ℤ L] [Module.Free ℤ L] [Module.Finite ℤ L] {a : ℕ → ℂ} (T : ℕ → L →ₗ[ℤ] L)
    (φ : L →ₗ[ℤ] ℂ) (hφ : φ ≠ 0) (h : ∀ n x, φ (T n x) = a n * φ x) :
    IntegralHeckeEigensystem a := by
  classical
  set b := Module.finBasis ℤ L with hb
  refine { rank := Module.finrank ℤ L
           T := fun n => LinearMap.toMatrix b b (T n)
           period := fun i => φ (b i)
           period_ne := ?_
           period_hecke := ?_ }
  · intro hv
    exact hφ (b.ext fun i => by simpa using congrFun hv i)
  · intro n
    ext j
    have hrep := b.sum_repr (T n (b j))
    have hφT : φ (T n (b j)) = ∑ i, ((b.repr (T n (b j)) i : ℤ) : ℂ) * φ (b i) := by
      conv_lhs => rw [← hrep]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [LinearMap.map_smul]; simp [zsmul_eq_mul]
    rw [h n (b j)] at hφT
    simp only [Matrix.vecMul, Matrix.map_apply, dotProduct, Pi.smul_apply, smul_eq_mul,
      algebraMap_int_eq, eq_intCast, LinearMap.toMatrix_apply]
    rw [hφT]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
```

It is NOT committed as a declaration only because it would be **free-floating**:
its sole consumer would be a HOMOLOGY-route proof of one of the two lattice
leaves, and the route both leaves now take is the `q`-expansion one, which
consumes `ofIsIntegralHeckeStructure` below instead.  Paste it back the moment
the homology route is started.  (The same idiom, for the same reason, is used in
`X1.lean` for the mechanized level-`0` falsity witness.)

**WHICH BRIDGE GOES WITH WHICH ROUTE, since there are now two.**  A period map
`φ : H₁(X, ℤ) → ℂ` is a functional on a lattice that is not sitting inside the
space the operators act on, so it produces the ROW eigenvector directly — that is
`ofPeriodMap`.  The `q`-expansion lattice `S₂(Γ, ℤ)` instead sits INSIDE
`S₂(Γ)`, with `f` itself the eigenvector, so what one holds is a `ℂ`-basis in
which the Hecke matrices are integral together with `f`'s coordinate vector —
that is `ofIsIntegralHeckeStructure`, and the transpose in its proof is exactly
the passage from the column convention (an eigenvector of the operator) to the
row convention the structure stores.  Neither bridge subsumes the other cheaply;
each is a few lines, and committing the one with a consumer is the rule.

Note also what the bridge shows about the strength of the packaging: `Fin r → ℤ`
is itself a finite free `ℤ`-module, so `IntegralHeckeEigensystem` is *equivalent*
to the abstract-lattice datum, not a weakening of it.  Nothing is lost by
storing matrices.

## Faithfulness

`IntegralHeckeEigensystem a` is **not junk-satisfiable**: `isIntegral_coeff`
proves that its mere existence forces every `a n` to be an algebraic integer, so
no instance exists for a system with a transcendental coefficient.  In
particular there is no degenerate `rank := 0` instance — `period : Fin 0 → ℂ` is
always `0`, so `period_ne` is unsatisfiable there.

It is, deliberately, **stronger than the per-`n` conclusion**: it demands ONE
lattice and ONE simultaneous eigenvector serving every `n`.  That is the point.
A per-`n` version ("for each `n` some integer matrix has `a n` as an
eigenvalue") is *logically equivalent* to `∀ n, IsIntegral ℤ (a n)` and would
therefore be a pure restatement with no content; the simultaneity is what makes
the geometric input (a single `H₁`) the thing being asked for.
-/

@[expose] public section

namespace Fermat

open Matrix Polynomial

/-- **An eigenvalue of an INTEGER matrix, read on `ℂ`, is an algebraic integer**
(PROVEN 2026-07-31).

This is the whole of "so it is a root of a monic integer characteristic
polynomial" from the classical statement of Shimura's algebraicity theorem.  The
witness is `A.charpoly`: it is monic over `ℤ` (`Matrix.charpoly_monic`), and
`Matrix.charpoly_map` says that forming it commutes with pushing the entries
along `ℤ → ℂ`, so evaluating it at `μ` is evaluating the charpoly of the
COMPLEX matrix, which vanishes because `μ • 1 - A` kills the nonzero vector `v`
and a square matrix over a field with nontrivial kernel has zero determinant
(`Matrix.exists_mulVec_eq_zero_iff`, `Matrix.eval_charpoly`).

`hv : v ≠ 0` is load-bearing and is the only hypothesis: with `v = 0` the
displayed equation holds for EVERY `μ`, so the statement would assert that every
complex number is an algebraic integer, refuted by `μ = 1/2` at `r = 1`,
`A = 0`. -/
theorem isIntegral_of_intMatrix_mulVec {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    {μ : ℂ} {v : Fin r → ℂ} (hv : v ≠ 0)
    (heig : A.map (algebraMap ℤ ℂ) *ᵥ v = μ • v) : IsIntegral ℤ μ := by
  refine ⟨A.charpoly, A.charpoly_monic, ?_⟩
  have hker : (Matrix.scalar (Fin r) μ - A.map (algebraMap ℤ ℂ)) *ᵥ v = 0 := by
    rw [sub_mulVec, heig]
    ext i
    simp [Matrix.scalar, Matrix.mulVec_diagonal]
  have hdet : (Matrix.scalar (Fin r) μ - A.map (algebraMap ℤ ℂ)).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, hker⟩
  have h1 : (A.map (algebraMap ℤ ℂ)).charpoly.eval μ = 0 := by
    rw [Matrix.eval_charpoly]; exact hdet
  rw [Matrix.charpoly_map] at h1
  rw [← Polynomial.eval_map]
  exact h1

/-- **The ROW form of the previous lemma** (PROVEN 2026-07-31): a nonzero LEFT
eigenvector of an integer matrix has algebraic-integer eigenvalue.

This is the form the period map produces — see the module docstring — and it is
what `IntegralHeckeEigensystem.isIntegral_coeff` consumes.  A left eigenvector
of `A` is a right eigenvector of `Aᵀ` (`Matrix.mulVec_transpose`), and
`(Aᵀ).map g = (A.map g)ᵀ` holds by `rfl`, so nothing is needed beyond the column
form; note in particular that no relation between `A.charpoly` and `Aᵀ.charpoly`
has to be invoked, since the column lemma is applied to `Aᵀ` outright. -/
theorem isIntegral_of_intMatrix_vecMul {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    {μ : ℂ} {w : Fin r → ℂ} (hw : w ≠ 0)
    (heig : w ᵥ* A.map (algebraMap ℤ ℂ) = μ • w) : IsIntegral ℤ μ := by
  refine isIntegral_of_intMatrix_mulVec Aᵀ hw ?_
  have hmt : (Aᵀ).map (algebraMap ℤ ℂ) = (A.map (algebraMap ℤ ℂ))ᵀ := rfl
  rw [hmt, Matrix.mulVec_transpose]
  exact heig

/-- **AN INTEGRAL HECKE EIGENSYSTEM FOR `a`** — the classical geometric input to
Shimura's algebraicity theorem, packaged so that both the `Γ₀` and the `Γ₁` side
can ask for it.

Concretely, for a weight-two eigenform of level `N ≥ 1` this is meant to be
instantiated by

* `rank` := `2g`, the rank of the integral homology `H₁(X, ℤ)` of the
  compactified modular curve (`X = X₀(N)` resp. `X₁(N)`);
* `T n` := the matrix of the Hecke correspondence `T_n` on `H₁(X, ℤ)` in a
  chosen `ℤ`-basis — INTEGER entries, which is the whole point: `T_n` is induced
  by a correspondence of curves and therefore preserves the lattice;
* `period` := the values `∫_{b i} ω_f` of the period map of `ω_f = 2πi f dq/q`
  on that basis;
* `period_hecke` := adjointness of the Hecke action on cycles and on
  differentials, `∫_{T_n γ} ω_f = ∫_γ T_n^* ω_f = a_n ∫_γ ω_f`;
* `period_ne` := nonvanishing of the periods of a nonzero holomorphic
  differential on a compact Riemann surface.

Nothing in the structure refers to a curve, a form, or a level: it is a
statement about the sequence `a` alone, which is why the two leaves that produce
it (one per level shape) can share this one consumer.  See the module docstring
for the equivalence with the abstract-lattice datum, and for the faithfulness
audit (not junk-satisfiable; no degenerate `rank = 0` instance). -/
structure IntegralHeckeEigensystem (a : ℕ → ℂ) where
  /-- the rank of the integral homology lattice -/
  rank : ℕ
  /-- the Hecke operators as INTEGER matrices in a `ℤ`-basis of the lattice -/
  T : ℕ → Matrix (Fin rank) (Fin rank) ℤ
  /-- the period map, recorded by its values on that basis -/
  period : Fin rank → ℂ
  /-- the period map is not identically zero -/
  period_ne : period ≠ 0
  /-- it is a simultaneous left eigenvector, with eigenvalue `a n` at `T n` -/
  period_hecke : ∀ n, period ᵥ* (T n).map (algebraMap ℤ ℂ) = a n • period

/-- **SHIMURA'S EIGENVALUE ARGUMENT** (PROVEN 2026-07-31): a system carrying an
integral Hecke eigensystem has algebraic-integer coefficients — every one of
them, at once.

Note the quantifier: this gives `IsIntegral ℤ (a n)` for EVERY `n`, primes and
prime powers and composites alike, with no multiplicativity and no Hecke
recursion.  The `Γ₀` and `Γ₁` files nevertheless keep their recursion lemmas and
consume this only at primes, because those lemmas are what makes the *prime*
leaf the honest residue: this theorem's own hypothesis is the geometric input,
and it is the geometry, not the arithmetic, that is missing. -/
theorem IntegralHeckeEigensystem.isIntegral_coeff {a : ℕ → ℂ}
    (H : IntegralHeckeEigensystem a) (n : ℕ) : IsIntegral ℤ (a n) :=
  isIntegral_of_intMatrix_vecMul (H.T n) H.period_ne (H.period_hecke n)

/-- **A `ℂ`-SPACE WITH A HECKE-STABLE INTEGRAL LATTICE** (NEW 2026-07-31) — the
space-side packaging of the classical input, and the thing the two modular-curve
leaves now produce.

`V` is meant to be `S₂(Γ)` for `Γ = Γ₀(N)` or `Γ₁(N)`, `T n` the Hecke operators
on it, `basis` a `ℤ`-basis of the lattice `S₂(Γ, ℤ)` of forms with integral
`q`-expansion, and `mat n` the matrix of `T n` in it.  The three facts being
asked for are exactly the three the classical proof supplies:

* `indep` + `spanning` — `S₂(Γ)` is FINITE-DIMENSIONAL and the integral forms
  span it (the `q`-expansion principle: `S₂(Γ, ℤ) ⊗ ℂ = S₂(Γ)`);
* `hecke_mat` — `T n` PRESERVES the lattice, because the `q`-expansion formula
  `a_m(T_n g) = ∑_{d ∣ (m,n)} d · a_{mn/d²}(⟨d⟩ g)` has integer coefficients.

**Deliberately free of `a` and of `f`.**  An eigenvector is not part of the
datum; it is supplied separately by `ofIsIntegralHeckeStructure`.  That split is
what lets the SAME structure serve the `Γ₀` and the `Γ₁` sides, whose eigenforms
and whose coefficient conventions differ (a nebentypus on one side, none on the
other) while their lattices do not.

**Not junk-satisfiable in the way that matters.**  `rank := 0` is a legal
inhabitant when `V = 0` — and it is then USELESS, because
`ofIsIntegralHeckeStructure` also demands a nonzero eigenvector, which `V = 0`
cannot supply.  So the degenerate instance is harmless: it can never be fed to
the only consumer.  Conversely `T n := a n • id` forces `a n ∈ ℤ` by `indep`, so
a structure does not exist for a system with a non-integral coefficient — which
is `isIntegral_coeff` seen from the other side. -/
structure IsIntegralHeckeStructure {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : ℕ → V →ₗ[ℂ] V) where
  /-- the rank of the lattice, classically `dim_ℂ S₂(Γ) = g` -/
  rank : ℕ
  /-- a `ℤ`-basis of the lattice -/
  basis : Fin rank → V
  /-- it is `ℂ`-linearly independent -/
  indep : LinearIndependent ℂ basis
  /-- and it spans `V` over `ℂ` — together with `indep`, it is a `ℂ`-basis -/
  spanning : Submodule.span ℂ (Set.range basis) = ⊤
  /-- the matrix of `T n` in that basis, with INTEGER entries -/
  mat : ℕ → Matrix (Fin rank) (Fin rank) ℤ
  /-- and it really is the matrix of `T n`: the lattice is Hecke-stable -/
  hecke_mat : ∀ n j, T n (basis j) = ∑ i, ((mat n i j : ℤ) : ℂ) • basis i

/-- **THE `q`-EXPANSION-LATTICE BRIDGE** (PROVEN 2026-07-31): a Hecke-stable
integral lattice in a `ℂ`-space, together with a NONZERO simultaneous
eigenvector with eigenvalues `a n`, is an `IntegralHeckeEigensystem a`.

This is the whole of the linear algebra between *"the Hecke operators preserve a
lattice and `f` is an eigenform"* and *"the `a n` are algebraic integers"*, and
it is the reason the two modular-curve leaves can be stated about `S₂(Γ)` and
about nothing else.  Read together with `isIntegral_coeff` it says: the
geometric input is a lattice, and everything after it is done.

The proof is three steps and no mathematics: `Module.Basis.mk` turns
`indep`/`spanning` into a genuine `ℂ`-basis `B`; `LinearMap.toMatrix B B (T n)`
is then `mat n` pushed along `ℤ → ℂ` (`hecke_mat` read through
`Module.Basis.repr_self`); and `LinearMap.toMatrix_mulVec_repr` turns
`T n f = a n • f` into `mat n *ᵥ B.repr f = a n • B.repr f`.  The transpose in
the `T` field is the passage from that COLUMN equation to the ROW convention the
structure stores (`Matrix.vecMul_transpose`); see the module docstring for why
the row convention is the right one to store.

`hf0 : f ≠ 0` is load-bearing and is what `period_ne` becomes: with `f = 0` the
eigenvector equation holds for every `a` whatever, so the conclusion would
assert that every complex sequence consists of algebraic integers, refuted at
`a = fun _ => 1/2`. -/
noncomputable def IntegralHeckeEigensystem.ofIsIntegralHeckeStructure {V : Type*}
    [AddCommGroup V] [Module ℂ V] {a : ℕ → ℂ} {T : ℕ → V →ₗ[ℂ] V}
    (H : IsIntegralHeckeStructure T) {f : V} (hf0 : f ≠ 0)
    (hT : ∀ n, T n f = a n • f) : IntegralHeckeEigensystem a := by
  classical
  set B : Module.Basis (Fin H.rank) ℂ V := Module.Basis.mk H.indep H.spanning.ge with hBdef
  have hBcoe : ⇑B = H.basis := Module.Basis.coe_mk _ _
  have hrepr : ∀ x i : Fin H.rank, (B.repr (H.basis x)) i = if x = i then (1 : ℂ) else 0 := by
    intro x i
    have hx : H.basis x = B x := (congrFun hBcoe x).symm
    rw [hx, Module.Basis.repr_self, Finsupp.single_apply]
  have hmat : ∀ n, LinearMap.toMatrix B B (T n) = (H.mat n).map (algebraMap ℤ ℂ) := by
    intro n
    ext i j
    rw [LinearMap.toMatrix_apply, hBcoe, H.hecke_mat n j, map_sum]
    simp [hrepr]
  refine { rank := H.rank
           T := fun n => (H.mat n)ᵀ
           period := fun i => B.repr f i
           period_ne := ?_
           period_hecke := ?_ }
  · intro hzero
    refine hf0 ?_
    have hr : B.repr f = 0 := by
      ext i
      exact congrFun hzero i
    have := congrArg B.repr.symm hr
    simpa using this
  · intro n
    have htr : ((H.mat n)ᵀ).map (algebraMap ℤ ℂ) = ((H.mat n).map (algebraMap ℤ ℂ))ᵀ := rfl
    rw [htr, Matrix.vecMul_transpose, ← hmat n]
    have h2 := LinearMap.toMatrix_mulVec_repr B B (T n) f
    rw [h2, hT n]
    funext i
    simp

end Fermat
