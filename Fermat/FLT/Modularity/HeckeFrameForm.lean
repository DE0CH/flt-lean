/-
Modularity/HeckeFrameForm.lean — own work for the Fermat project (not
vendored from the FLT project).

# Frobenius forms and the symplectic geometry of the Hecke frame

`Modularity/HeckeFrame.lean` builds, from a linear functional
`θ : F ⊗ₖ T →ₗ[F] F`, the alternating Hecke-self-adjoint form
`frameSymplectic θ` on the frame `(F ⊗ₖ T)²`, and proves it
nondegenerate when `θ` is a *Frobenius form*. Its section note records
two further facts as classical but **unformalized**, and both of them
are load-bearing for the cut of `nonempty_modularTateGaloisData` in
`Modularity/Interface.lean`:

* the CONVERSE — every alternating `A`-self-adjoint form on `A²` is
  `θ (x₀y₁ − x₁y₀)` for a unique `θ` — which is what makes that cut
  *relocate* the four pairing fields rather than weaken them;
* the behaviour of the form under an `A`-linear endomorphism `g`, which
  is what turns the `pair_frob` field into the determinant condition
  `det (τJ Frob_q) = q`.

This module formalizes both, plus the base change of a Frobenius form
along a field extension. Nothing here mentions modular forms, Galois
actions or modular curves; it is stated for an arbitrary field
extension `k ⊆ F` and an arbitrary `k`-algebra `T`, exactly as
`HeckeFrame.lean` is.

## Contents

* `tensorFunctional` / `tensorFunctional_frobenius` — **base change of a
  Frobenius form**: a Frobenius form on `T` over `k` induces one on
  `F ⊗ₖ T` over `F`. This is what lets the Frobenius leaf of
  `Interface.lean` be stated over `ℚ` for the honest rational Hecke
  algebra rather than over `ℚ̄_p` for its base change.
* `forall_frameMul_selfAdjoint` — self-adjointness for a GENERATING set
  of `T` upgrades to self-adjointness for every element of `F ⊗ₖ T`.
* `exists_frameSymplectic_of_alternating` — **the converse direction**:
  an alternating, `A`-self-adjoint `F`-bilinear form on the frame IS
  `frameSymplectic θ` for some `θ`. Needs `char k ≠ 2` (it is false in
  characteristic two, where the squares do not span).
* `commute_frameMul_of_adjoin` — an endomorphism commuting with the
  generators commutes with all of the multiplication algebra.
* `frameSymplectic_map_of_commuting` — **the multiplier formula**:
  `⟨g x, g y⟩ = θ (det g · (x₀y₁ − x₁y₀))` for `A`-linear `g`, with
  `det g` read off the images of the standard frame.
* `exists_frobeniusForm_of_baseChange` — **Frobenius DESCENT**, the
  converse of `tensorFunctional_frobenius`: a finite-dimensional algebra
  over an INFINITE field that becomes Frobenius after base change to a
  field extension was already Frobenius. Proved through the Gram
  determinant `gramDet`, a single polynomial in the coordinates of the
  functional whose non-vanishing is the Frobenius condition over every
  extension at once.
* `frobenius_of_frameSymplectic_nondegenerate` — the converse of
  `frameSymplectic_nondegenerate`, completing the equivalence
  "nondegenerate alternating self-adjoint form on `A²`" ↔ "Frobenius
  form on `A`".
* `frameCayleyHamilton` — **Cayley–Hamilton on the frame**:
  `g² − tr(g)·g + det(g) = 0` for `A`-linear `g`, with trace and
  determinant read off the images of the standard frame exactly as in
  `frameSymplectic_map_of_commuting`. This is what turns the
  Eichler–Shimura *congruence relation* — a quadratic operator identity —
  into the classical *trace* condition `tr (τJ Frob_q) = T_q`, and is
  used for exactly that in `Interface.lean`.
* `traceDet_of_congruence_of_multiplier` — the CONVERSE arrow, and the
  one the CUT-OBSTRUCTION AUDIT in `Interface.lean` records as
  "elementary, not formalized": from the quadratic operator identity
  `g² − t·g + c = 0` together with `⟨gx, gy⟩ = c⟨x, y⟩` for a
  nondegenerate alternating self-adjoint form, `det g = c` and
  `tr g = t`. Needs `c ≠ 0` and `char k ≠ 2`.
* `exists_freeElement_of_frobenius` — a faithful module over a commutative
  Frobenius algebra contains a free rank-one submodule. Pure commutative
  algebra (Gorenstein socle); PROVEN, over the `FrobeniusSocle` namespace,
  which carries the duality `ann (ann I) = I` and the minimality of `ann 𝔪`.
  It was FALSE as first stated — commutativity was omitted, and `M₂(F)` on
  `F²` refutes it — so it now takes `hcomm`, which its consumer already held;
  see the FALSITY AUDIT in its docstring.
* `exists_frameEquiv_of_symplectic` — **the symplectic rigidity of the
  frame**: a faithful `A`-module of dimension `2·dim A` carrying a
  nondegenerate alternating `A`-self-adjoint form IS `A²`, for `A` a
  commutative Frobenius algebra in characteristic `≠ 2`. This is
  multiplicity one in its linear-algebra form; it is what lets
  `exists_galoisRep_modularTateFrame_traceDet` in `Interface.lean` be
  cut along its FREENESS content rather than along its geometry, and it
  is FALSE in characteristic two (counterexample in its docstring).
-/
module

public import Fermat.FLT.Modularity.HeckeFrame
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Operations

@[expose] public section

namespace GaloisRepresentation.Modularity

open scoped TensorProduct

section BaseChange

variable {k : Type*} [Field k] {F : Type*} [Field F] [Algebra k F]
variable {T : Type*} [Ring T] [Algebra k T]

/-- **Base change of a linear functional**: `θ : T →ₗ[k] k` extends to
`F ⊗ₖ T →ₗ[F] F`, sending `c ⊗ t` to `θ t • c`. -/
noncomputable def tensorFunctional (θ : T →ₗ[k] k) : (F ⊗[k] T) →ₗ[F] F :=
  (TensorProduct.AlgebraTensorModule.rid k F F).toLinearMap.comp
    (LinearMap.baseChange F θ)

@[simp] theorem tensorFunctional_tmul (θ : T →ₗ[k] k) (c : F) (t : T) :
    tensorFunctional (F := F) θ (c ⊗ₜ[k] t) = θ t • c := by
  simp [tensorFunctional]

/-- **Base change of a FROBENIUS form.** If the trace form of `θ` on the
finite-dimensional commutative `k`-algebra `T` is nondegenerate, so is
the trace form of `tensorFunctional θ` on `F ⊗ₖ T`.

This is the reduction that lets `exists_frobeniusForm_modularTateFrame`
in `Interface.lean` be glue over a leaf stated for the honest rational
Hecke algebra `𝕋_ℚ` over `ℚ`, with no tensor product and no `ℚ̄_p` in
sight. -/
theorem tensorFunctional_frobenius [FiniteDimensional k T]
    (hT : ∀ x y : T, x * y = y * x) (θ : T →ₗ[k] k)
    (hθ : ∀ a : T, (∀ b : T, θ (a * b) = 0) → a = 0) :
    ∀ a : F ⊗[k] T,
      (∀ b : F ⊗[k] T, tensorFunctional (F := F) θ (a * b) = 0) → a = 0 := by
  classical
  -- `ψ x` is the functional `t ↦ θ (x * t)`; `hθ` says it is injective.
  set ψ : T →ₗ[k] Module.Dual k T :=
    { toFun := fun x => θ.comp (LinearMap.mulLeft k x)
      map_add' := by intro x y; ext t; simp [add_mul]
      map_smul' := by intro c x; ext t; simp } with hψdef
  have hψapply : ∀ (x t : T), ψ x t = θ (x * t) := fun x t => rfl
  have hψinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    refine hθ x fun b => ?_
    have := congrArg (fun (f : Module.Dual k T) => f b) hx
    simpa [hψapply] using this
  have hψsurj : Function.Surjective ψ := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hψinj
    exact (Subspace.dual_finrank_eq (K := k) (V := T)).symm
  -- a `k`-basis of `T`, and the family dual to it under `ψ`
  set b : Module.Basis (Fin (Module.finrank k T)) k T := Module.finBasis k T with hbdef
  choose t ht using fun j => hψsurj (b.dualBasis j)
  have hdual : ∀ i j, θ (b i * t j) = if i = j then 1 else 0 := by
    intro i j
    have h1 : θ (t j * b i) = b.dualBasis j (b i) := by
      have := congrArg (fun (f : Module.Dual k T) => f (b i)) (ht j)
      simpa [hψapply] using this
    rw [hT (b i) (t j), h1, b.dualBasis_apply_self]
  -- the `F`-basis of the base change
  set bF : Module.Basis (Fin (Module.finrank k T)) F (F ⊗[k] T) :=
    b.baseChange F with hbFdef
  intro a ha
  have hzero : ∀ j, bF.repr a j = 0 := by
    intro j
    -- `L j` is "multiply on the right by `1 ⊗ t j`, then apply the functional"
    set L : (F ⊗[k] T) →ₗ[F] F :=
      (tensorFunctional (F := F) θ).comp
        (LinearMap.mulRight F ((1 : F) ⊗ₜ[k] t j)) with hLdef
    have hLbasis : ∀ i, L (bF i) = if i = j then 1 else 0 := by
      intro i
      have hbFi : bF i = (1 : F) ⊗ₜ[k] b i := by
        simp [hbFdef, Module.Basis.baseChange_apply]
      rw [hbFi]
      simp only [hLdef, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [tensorFunctional_tmul, hdual i j]
      by_cases h : i = j
      · simp [h]
      · simp [h]
    have hLa : L a = bF.repr a j := by
      conv_lhs => rw [← bF.sum_repr a]
      rw [map_sum]
      simp only [map_smul, hLbasis, smul_eq_mul]
      rw [Finset.sum_eq_single j] <;> simp +contextual
    rw [← hLa, hLdef]
    exact ha _
  have : bF.repr a = 0 := by
    ext j; simpa using hzero j
  simpa using congrArg bF.repr.symm this

end BaseChange

section FrameForm

variable {k : Type*} [Field k] {F : Type*} [Field F] [Algebra k F]
variable {T : Type*} [Ring T] [Algebra k T]

/-- Multiplication of a fixed frame vector by a varying scalar, as an
`F`-linear map — the building block of the coefficient functionals
`θᵢⱼ` below. -/
noncomputable def frameMulRight (v : HeckeFrame k F T) :
    (F ⊗[k] T) →ₗ[F] HeckeFrame k F T where
  toFun r := frameMul (k := k) (F := F) (T := T) r v
  map_add' r s := by simp
  map_smul' c r := by simp

@[simp] theorem frameMulRight_apply (v : HeckeFrame k F T) (r : F ⊗[k] T) :
    frameMulRight v r = frameMul (k := k) (F := F) (T := T) r v := rfl

theorem frameMul_apply_coord (r : F ⊗[k] T) (v : HeckeFrame k F T) (i : Fin 2) :
    frameMul (k := k) (F := F) (T := T) r v i = r * v i := rfl

/-- **Self-adjointness propagates from a generating set.** If `S`
generates `T` as a `k`-algebra and the form is self-adjoint for each
`frameAction s`, `s ∈ S`, then it is self-adjoint for multiplication by
every element of `F ⊗ₖ T`. -/
theorem forall_frameMul_selfAdjoint
    (hcomm : ∀ x y : F ⊗[k] T, x * y = y * x)
    (P : HeckeFrame k F T →ₗ[F] HeckeFrame k F T →ₗ[F] F)
    (S : Set T) (hS : Algebra.adjoin k S = ⊤)
    (hgen : ∀ s ∈ S, ∀ x y : HeckeFrame k F T,
      P (frameAction k F T s x) y = P x (frameAction k F T s y)) :
    ∀ (r : F ⊗[k] T) (x y : HeckeFrame k F T),
      P (frameMul (k := k) (F := F) (T := T) r x) y =
        P x (frameMul (k := k) (F := F) (T := T) r y) := by
  intro r
  have hr : r ∈ Algebra.adjoin F
      ((Algebra.TensorProduct.includeRight : T →ₐ[k] F ⊗[k] T) '' S) := by
    rw [adjoin_includeRight_eq_top S hS]; trivial
  induction hr using Algebra.adjoin_induction with
  | mem u hu =>
      obtain ⟨s, hs, rfl⟩ := hu
      intro x y
      have h := hgen s hs x y
      rwa [frameAction_eq_frameMul] at h
  | algebraMap c =>
      intro x y
      have h : frameMul (k := k) (F := F) (T := T)
          (algebraMap F (F ⊗[k] T) c) = algebraMap F (Module.End F (HeckeFrame k F T)) c :=
        AlgHom.commutes _ c
      rw [h]
      show P (c • x) y = P x (c • y)
      rw [map_smul, LinearMap.smul_apply, map_smul]
  | add u v _ _ ihu ihv =>
      intro x y
      have hsplit : ∀ z : HeckeFrame k F T,
          frameMul (k := k) (F := F) (T := T) (u + v) z =
            frameMul (k := k) (F := F) (T := T) u z +
              frameMul (k := k) (F := F) (T := T) v z := by
        intro z; simp
      rw [hsplit x, hsplit y, map_add, LinearMap.add_apply, map_add, ihu, ihv]
  | mul u v _ _ ihu ihv =>
      intro x y
      have hcompu : ∀ (a c : F ⊗[k] T) (z : HeckeFrame k F T),
          frameMul (k := k) (F := F) (T := T) (a * c) z =
            frameMul (k := k) (F := F) (T := T) a
              (frameMul (k := k) (F := F) (T := T) c z) := by
        intro a c z; rw [map_mul]; rfl
      rw [hcompu u v x, ihu, ihv, ← hcompu v u y, hcomm v u, hcompu u v y]

/-- **The converse direction of the section note in `HeckeFrame.lean`**:
an alternating, `A`-self-adjoint `F`-bilinear form on the frame `A²`
(`A := F ⊗ₖ T`, commutative) is `frameSymplectic θ` for a functional
`θ`. Together with `frameSymplectic_self`, `frameSymplectic_frameMul`
and `frameSymplectic_nondegenerate` this says the four pairing fields of
`ModularTateGaloisData` carry exactly one datum, and no geometry.

Characteristic zero is used exactly once, to conclude `θ₀₀ = 0` from
`θ₀₀ (a²) = 0` by `2a = (a+1)² − a² − 1`; the statement is FALSE in
characteristic two.

COMMUTATIVITY OF `A` IS NOT NEEDED HERE, which is slightly stronger than
the section note in `HeckeFrame.lean` claims. The note's polarization
step is run at `b = 1`, where `a·1 = 1·a` holds in any ring, so the
cross-term identity `θ₀₁ + θ₁₀ = 0` comes out with no commutativity at
all. (Commutativity is still needed by `forall_frameMul_selfAdjoint`,
which is what supplies this theorem's `hadj` from self-adjointness for
the Hecke generators alone.) -/
theorem exists_frameSymplectic_of_alternating [CharZero k]
    (P : HeckeFrame k F T →ₗ[F] HeckeFrame k F T →ₗ[F] F)
    (hself : ∀ x : HeckeFrame k F T, P x x = 0)
    (hadj : ∀ (r : F ⊗[k] T) (x y : HeckeFrame k F T),
      P (frameMul (k := k) (F := F) (T := T) r x) y =
        P x (frameMul (k := k) (F := F) (T := T) r y)) :
    ∃ θ : (F ⊗[k] T) →ₗ[F] F,
      ∀ x y : HeckeFrame k F T, P x y = frameSymplectic θ x y := by
  classical
  have h2 : (2 : F) ≠ 0 := by
    have hinj : Function.Injective (algebraMap k F) := (algebraMap k F).injective
    intro h
    have h2k : (2 : k) ≠ 0 := two_ne_zero
    exact h2k (hinj (by rw [map_ofNat, map_zero, h]))
  set θ00 : (F ⊗[k] T) →ₗ[F] F :=
    (P frameBasis₁).comp (frameMulRight (k := k) (F := F) (T := T) frameBasis₁) with hθ00
  set θ01 : (F ⊗[k] T) →ₗ[F] F :=
    (P frameBasis₁).comp (frameMulRight (k := k) (F := F) (T := T) frameBasis₂) with hθ01
  set θ10 : (F ⊗[k] T) →ₗ[F] F :=
    (P frameBasis₂).comp (frameMulRight (k := k) (F := F) (T := T) frameBasis₁) with hθ10
  set θ11 : (F ⊗[k] T) →ₗ[F] F :=
    (P frameBasis₂).comp (frameMulRight (k := k) (F := F) (T := T) frameBasis₂) with hθ11
  -- the general expansion of `P` in the four coefficient functionals
  have hexp : ∀ x y : HeckeFrame k F T,
      P x y = θ00 (x 0 * y 0) + θ01 (x 0 * y 1) + θ10 (x 1 * y 0) + θ11 (x 1 * y 1) := by
    intro x y
    have hmulmul : ∀ (a c : F ⊗[k] T) (z : HeckeFrame k F T),
        frameMul (k := k) (F := F) (T := T) a
            (frameMul (k := k) (F := F) (T := T) c z) =
          frameMul (k := k) (F := F) (T := T) (a * c) z := by
      intro a c z; rw [map_mul]; rfl
    have hy : ∀ a : F ⊗[k] T,
        frameMul (k := k) (F := F) (T := T) a y =
          frameMul (k := k) (F := F) (T := T) (a * y 0) frameBasis₁ +
            frameMul (k := k) (F := F) (T := T) (a * y 1) frameBasis₂ := by
      intro a
      conv_lhs => rw [frame_span y]
      rw [map_add, hmulmul, hmulmul]
    conv_lhs => rw [frame_span x]
    rw [map_add, LinearMap.add_apply, hadj (x 0), hadj (x 1), hy (x 0), hy (x 1),
      map_add, map_add]
    simp only [hθ00, hθ01, hθ10, hθ11, LinearMap.coe_comp, Function.comp_apply,
      frameMulRight_apply]
    abel
  -- `θ00` and `θ11` vanish
  have hsq : ∀ (φ : (F ⊗[k] T) →ₗ[F] F), (∀ a : F ⊗[k] T, φ (a * a) = 0) →
      ∀ a : F ⊗[k] T, φ a = 0 := by
    intro φ hφ a
    have h1 : (a + 1) * (a + 1) = a * a + (a + a) + 1 * 1 := by
      rw [add_mul, mul_add, mul_add]; simp [mul_one, one_mul]; abel
    have h2' : φ (a * a) + φ (a + a) + φ (1 * 1) = 0 := by
      have := hφ (a + 1)
      rw [h1, map_add, map_add] at this
      exact this
    rw [hφ a, hφ 1, zero_add, add_zero, map_add] at h2'
    have : (2 : F) * φ a = 0 := by rw [two_mul]; exact h2'
    exact (mul_eq_zero.mp this).resolve_left h2
  have h00 : ∀ a : F ⊗[k] T, θ00 a = 0 := by
    refine hsq θ00 fun a => ?_
    have := hself (Pi.single 0 a)
    rw [hexp] at this
    simpa using this
  have h11 : ∀ a : F ⊗[k] T, θ11 a = 0 := by
    refine hsq θ11 fun a => ?_
    have := hself (Pi.single 1 a)
    rw [hexp] at this
    simpa using this
  -- and the cross terms are opposite
  have hcross : ∀ a : F ⊗[k] T, θ01 a + θ10 a = 0 := by
    intro a
    have := hself (![a, 1] : HeckeFrame k F T)
    rw [hexp] at this
    simpa [h00, h11, mul_one, one_mul] using this
  refine ⟨θ01, fun x y => ?_⟩
  rw [hexp, frameSymplectic_apply, h00, h11, map_sub]
  have hθ10' : θ10 (x 1 * y 0) = -θ01 (x 1 * y 0) := by
    have h := hcross (x 1 * y 0)
    rw [add_comm] at h
    exact eq_neg_of_add_eq_zero_left h
  rw [hθ10']
  ring

/-- **Commutation propagates from a generating set**: an `F`-linear
endomorphism commuting with the operators `frameAction s`, `s ∈ S`, for a
generating set `S` of `T`, commutes with multiplication by every element
of `F ⊗ₖ T`. -/
theorem commute_frameMul_of_adjoin
    (g : HeckeFrame k F T →ₗ[F] HeckeFrame k F T)
    (S : Set T) (hS : Algebra.adjoin k S = ⊤)
    (hgen : ∀ s ∈ S, ∀ x : HeckeFrame k F T,
      g (frameAction k F T s x) = frameAction k F T s (g x)) :
    ∀ (r : F ⊗[k] T) (x : HeckeFrame k F T),
      g (frameMul (k := k) (F := F) (T := T) r x) =
        frameMul (k := k) (F := F) (T := T) r (g x) := by
  intro r
  have hr : r ∈ Algebra.adjoin F
      ((Algebra.TensorProduct.includeRight : T →ₐ[k] F ⊗[k] T) '' S) := by
    rw [adjoin_includeRight_eq_top S hS]; trivial
  induction hr using Algebra.adjoin_induction with
  | mem u hu =>
      obtain ⟨s, hs, rfl⟩ := hu
      intro x
      have h := hgen s hs x
      rwa [frameAction_eq_frameMul] at h
  | algebraMap c =>
      intro x
      have h : frameMul (k := k) (F := F) (T := T)
          (algebraMap F (F ⊗[k] T) c) = algebraMap F (Module.End F (HeckeFrame k F T)) c :=
        AlgHom.commutes _ c
      rw [h]
      show g (c • x) = c • g x
      rw [map_smul]
  | add u v _ _ ihu ihv =>
      intro x
      have hsplit : ∀ z : HeckeFrame k F T,
          frameMul (k := k) (F := F) (T := T) (u + v) z =
            frameMul (k := k) (F := F) (T := T) u z +
              frameMul (k := k) (F := F) (T := T) v z := by
        intro z; simp
      rw [hsplit x, map_add, ihu, ihv, hsplit (g x)]
  | mul u v _ _ ihu ihv =>
      intro x
      have hcompu : ∀ (a c : F ⊗[k] T) (z : HeckeFrame k F T),
          frameMul (k := k) (F := F) (T := T) (a * c) z =
            frameMul (k := k) (F := F) (T := T) a
              (frameMul (k := k) (F := F) (T := T) c z) := by
        intro a c z; rw [map_mul]; rfl
      rw [hcompu u v x, ihu, ihv, hcompu u v (g x)]

/-- **The multiplier formula.** For an `A`-linear endomorphism `g` of the
frame, the symplectic form is multiplied by the DETERMINANT of `g`, read
off the images of the standard frame:

  `⟨g x, g y⟩ = θ ((ad − bc) · (x₀y₁ − x₁y₀))`,  `g e₁ = (a, c)`, `g e₂ = (b, d)`.

This is what reduces the `pair_frob` field of `ModularTateGaloisData` to
the determinant condition `det (τJ Frob_q) = q`, with `θ` eliminated. -/
theorem frameSymplectic_map_of_commuting
    (hcomm : ∀ x y : F ⊗[k] T, x * y = y * x)
    (θ : (F ⊗[k] T) →ₗ[F] F)
    (g : HeckeFrame k F T →ₗ[F] HeckeFrame k F T)
    (hg : ∀ (r : F ⊗[k] T) (x : HeckeFrame k F T),
      g (frameMul (k := k) (F := F) (T := T) r x) =
        frameMul (k := k) (F := F) (T := T) r (g x))
    (x y : HeckeFrame k F T) :
    frameSymplectic θ (g x) (g y) =
      θ ((g frameBasis₁ 0 * g frameBasis₂ 1 - g frameBasis₂ 0 * g frameBasis₁ 1) *
        (x 0 * y 1 - x 1 * y 0)) := by
  have hcoord : ∀ (z : HeckeFrame k F T) (i : Fin 2),
      g z i = z 0 * g frameBasis₁ i + z 1 * g frameBasis₂ i := by
    intro z i
    conv_lhs => rw [frame_span z]
    rw [map_add, hg, hg]
    show frameMul (k := k) (F := F) (T := T) (z 0) (g frameBasis₁) i +
      frameMul (k := k) (F := F) (T := T) (z 1) (g frameBasis₂) i = _
    rw [frameMul_apply_coord, frameMul_apply_coord]
  rw [frameSymplectic_apply]
  congr 1
  rw [hcoord x 0, hcoord x 1, hcoord y 0, hcoord y 1]
  letI : CommRing (F ⊗[k] T) :=
    { (inferInstance : Ring (F ⊗[k] T)) with mul_comm := hcomm }
  ring

/-- **Cayley–Hamilton on the Hecke frame.** For an `A`-linear
endomorphism `g` of `A²` (`A := F ⊗ₖ T`, commutative),

  `g² − (a + d)·g + (ad − bc) = 0`,   `g e₁ = (a, c)`, `g e₂ = (b, d)`,

where the scalars act through `frameMul`. The trace and determinant are
read off the images of the standard frame in exactly the same shape as in
`frameSymplectic_map_of_commuting`, so the two lemmas compose without a
translation step.

WHAT IT IS FOR. The Eichler–Shimura clause of
`ModularTateGaloisData.congruence` is the quadratic operator identity
`τJ(Frob_q)² − T_q·τJ(Frob_q) + q = 0`. Given the determinant condition
`det (τJ Frob_q) = q`, this lemma shows that identity is *equivalent* to
the single scalar equation

  `tr (τJ Frob_q) = T_q`,

which is the form the classical statement and the geometry both produce
("`ρ_f(Frob_q)` has trace `a_q` and determinant `q`"). So it is what lets
`exists_galoisRep_modularTateFrame_det` in `Interface.lean` be glue over a
leaf carrying the trace condition instead of the operator identity.

The two directions are not quite symmetric and only one of them is proved
here: Cayley–Hamilton gives congruence from trace-and-determinant with no
side condition. The converse needs `τJ(Frob_q)` invertible to cancel it
from `(tr − T_q)·τJ(Frob_q) = 0`, which holds in the application because
`det = q` is a unit of `A`, but is not part of this statement.

No commutativity instance is installed on `F ⊗ₖ T`; as everywhere in this
file it is supplied as the hypothesis `hcomm`, so no instance diamond
enters any type. -/
theorem frameCayleyHamilton
    (hcomm : ∀ x y : F ⊗[k] T, x * y = y * x)
    (g : Module.End F (HeckeFrame k F T))
    (hg : ∀ (r : F ⊗[k] T) (x : HeckeFrame k F T),
      g (frameMul (k := k) (F := F) (T := T) r x) =
        frameMul (k := k) (F := F) (T := T) r (g x)) :
    g * g
        - frameMul (k := k) (F := F) (T := T)
            (g frameBasis₁ 0 + g frameBasis₂ 1) * g
        + frameMul (k := k) (F := F) (T := T)
            (g frameBasis₁ 0 * g frameBasis₂ 1 - g frameBasis₂ 0 * g frameBasis₁ 1) = 0 := by
  classical
  letI : CommRing (F ⊗[k] T) :=
    { (inferInstance : Ring (F ⊗[k] T)) with mul_comm := hcomm }
  have hcoord : ∀ (z : HeckeFrame k F T) (i : Fin 2),
      g z i = z 0 * g frameBasis₁ i + z 1 * g frameBasis₂ i := by
    intro z i
    conv_lhs => rw [frame_span z]
    rw [map_add, hg, hg]
    show frameMul (k := k) (F := F) (T := T) (z 0) (g frameBasis₁) i +
      frameMul (k := k) (F := F) (T := T) (z 1) (g frameBasis₂) i = _
    rw [frameMul_apply_coord, frameMul_apply_coord]
  refine LinearMap.ext fun x => ?_
  funext i
  simp only [LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.zero_apply, Pi.add_apply, Pi.sub_apply, Pi.zero_apply,
    Module.End.mul_apply, frameMul_apply_coord]
  rw [hcoord (g x) i, hcoord x 0, hcoord x 1, hcoord x i]
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] <;> ring

/-- **The converse of `frameSymplectic_nondegenerate`**: if the form
attached to `θ` is nondegenerate then `θ` is a Frobenius form. With
`frameSymplectic_nondegenerate` this closes the equivalence recorded in
the section note of `HeckeFrame.lean`. -/
theorem frobenius_of_frameSymplectic_nondegenerate (θ : (F ⊗[k] T) →ₗ[F] F)
    (h : ∀ x : HeckeFrame k F T, (∀ y, frameSymplectic θ x y = 0) → x = 0) :
    ∀ a : F ⊗[k] T, (∀ b : F ⊗[k] T, θ (a * b) = 0) → a = 0 := by
  classical
  intro a ha
  have hx : (Pi.single 0 a : HeckeFrame k F T) = 0 := by
    refine h _ fun y => ?_
    rw [frameSymplectic_apply]
    have h0 : (Pi.single 0 a : HeckeFrame k F T) 0 = a := by simp
    have h1 : (Pi.single 0 a : HeckeFrame k F T) 1 = 0 := by simp
    rw [h0, h1, zero_mul, sub_zero]
    exact ha (y 1)
  have := congrFun hx 0
  simpa using this

end FrameForm

section FrobeniusDescent

open MvPolynomial

/-! ### Frobenius descent along a field extension

`tensorFunctional_frobenius` above pushes a Frobenius form UP a field
extension `k ⊆ F`. This section proves the converse — the direction that
is *not* formal — so that a Frobenius form may be produced over a large
field where the mathematics is available and then descended to the small
field where the statement is wanted.

The argument is the one recorded in the docstring of
`exists_frobeniusForm_modularHeckeAlgebraQ` (`Modularity/Interface.lean`).
Fix a `k`-basis `e` of `T`. For a functional `θ` the Gram matrix of the
trace form is `(θ (eᵢ eⱼ))`, whose entries are `k`-LINEAR in `θ`; so its
determinant is the evaluation, at the coordinate vector of `θ`, of one
fixed polynomial `gramDet e ∈ k[X₀, …, X_{n-1}]` built from the structure
constants of `T`. Base change to `F` replaces that polynomial by its
image under `k → F` and nothing else, because `1 ⊗ eᵢ` is an `F`-basis of
`F ⊗ₖ T` with the SAME structure constants. A Frobenius form over `F` is
therefore an `F`-point where `gramDet e` does not vanish, so `gramDet e`
is not the zero polynomial; and over an INFINITE field a nonzero
polynomial has a `k`-point where it does not vanish
(`MvPolynomial.funext`). That point is the required `θ`.

Infiniteness of `k` is essential and not a technicality: over `𝔽_q` a
nonzero polynomial can vanish at every point. -/

/-- **The trace form of a linear functional** on a `k`-algebra:
`(a, b) ↦ θ (a * b)`. The *Frobenius* condition on `θ` — the one used
throughout this development — is exactly left-nondegeneracy of this
form. -/
noncomputable def frobeniusTraceForm {k : Type*} [CommRing k] {T : Type*} [Ring T]
    [Algebra k T] (θ : T →ₗ[k] k) : LinearMap.BilinForm k T :=
  LinearMap.mk₂ k (fun a b => θ (a * b))
    (fun a₁ a₂ b => by simp [add_mul])
    (fun c a b => by simp)
    (fun a b₁ b₂ => by simp [mul_add])
    (fun c a b => by simp)

@[simp] theorem frobeniusTraceForm_apply {k : Type*} [CommRing k] {T : Type*} [Ring T]
    [Algebra k T] (θ : T →ₗ[k] k) (a b : T) :
    frobeniusTraceForm θ a b = θ (a * b) := rfl

section GramDet

variable {k : Type*} [Field k] {T : Type*} [Ring T] [Algebra k T] {n : ℕ}

/-- **The Gram determinant as a polynomial in the functional.** Given a
`k`-basis `b` of `T`, this is the determinant of the matrix whose `(i, j)`
entry is the linear form `∑ₗ cᵢⱼₗ Xₗ`, where `bᵢ bⱼ = ∑ₗ cᵢⱼₗ bₗ`. Its
value at the coordinate vector `(θ (bₗ))ₗ` is the determinant of the Gram
matrix of `frobeniusTraceForm θ` — see `eval_map_gramDet`. -/
noncomputable def gramDet (b : Module.Basis (Fin n) k T) : MvPolynomial (Fin n) k :=
  (Matrix.of fun i j => ∑ l, C (b.repr (b i * b j) l) * X l).det

/-- Evaluating `gramDet`, after transporting its coefficients along any
ring map `ψ`, reproduces the Gram determinant. Stated for a general `ψ`
because it is used twice: at `ψ = id` over the small field, and at
`ψ = algebraMap k F` over the big one. -/
theorem eval_map_gramDet {R : Type*} [CommRing R] (b : Module.Basis (Fin n) k T)
    (ψ : k →+* R) (y : Fin n → R) :
    eval y (MvPolynomial.map ψ (gramDet b))
      = (Matrix.of fun i j => ∑ l, ψ (b.repr (b i * b j) l) * y l).det := by
  classical
  rw [gramDet, RingHom.map_det (MvPolynomial.map ψ), RingHom.map_det (eval y)]
  congr 1
  ext i j
  simp [Matrix.map_apply]

/-- **A functional whose Gram determinant is nonzero is a Frobenius
form.** -/
theorem frobenius_of_gramDet_ne_zero (b : Module.Basis (Fin n) k T)
    (θ : T →ₗ[k] k) (h : eval (fun l => θ (b l)) (gramDet b) ≠ 0) :
    ∀ a : T, (∀ c : T, θ (a * c) = 0) → a = 0 := by
  classical
  have hmat : LinearMap.BilinForm.toMatrix b (frobeniusTraceForm θ)
      = Matrix.of fun i j => ∑ l, (RingHom.id k) (b.repr (b i * b j) l) * θ (b l) := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, frobeniusTraceForm_apply]
    conv_lhs => rw [show b i * b j = ∑ l, b.repr (b i * b j) l • b l from (b.sum_repr _).symm]
    rw [map_sum]
    simp
  have hdet : (LinearMap.BilinForm.toMatrix b (frobeniusTraceForm θ)).det ≠ 0 := by
    rw [hmat, ← eval_map_gramDet b (RingHom.id k) (fun l => θ (b l))]
    simpa using h
  exact ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mpr hdet).1

end GramDet

variable {k : Type*} [Field k] [Infinite k] {F : Type*} [Field F] [Algebra k F]
variable {T : Type*} [Ring T] [Algebra k T] [FiniteDimensional k T]

/-- **FROBENIUS DESCENT ALONG A FIELD EXTENSION** — the converse of
`tensorFunctional_frobenius`, and the check named in the docstring of
`exists_frobeniusForm_modularHeckeAlgebraQ` as the one that justifies
attacking the Frobenius property of a `k`-algebra over a LARGER field.

If the finite-dimensional `k`-algebra `T` becomes a Frobenius algebra
after base change to a field extension `F`, it already was one over `k`.

`Infinite k` is genuinely needed (see the section note); it holds for
every field of characteristic zero, in particular for `k = ℚ`, which is
the only instance used here. NO commutativity of `T` is required. -/
theorem exists_frobeniusForm_of_baseChange
    (Θ : (F ⊗[k] T) →ₗ[F] F)
    (hΘ : ∀ a : F ⊗[k] T, (∀ c : F ⊗[k] T, Θ (a * c) = 0) → a = 0) :
    ∃ θ : T →ₗ[k] k, ∀ a : T, (∀ c : T, θ (a * c) = 0) → a = 0 := by
  classical
  set n := Module.finrank k T with hn
  set b : Module.Basis (Fin n) k T := Module.finBasis k T with hb
  set bF : Module.Basis (Fin n) F (F ⊗[k] T) := b.baseChange F with hbF
  haveI : Module.Free F (F ⊗[k] T) := Module.Free.of_basis bF
  haveI : Module.Finite F (F ⊗[k] T) := Module.Finite.of_basis bF
  -- the base-changed basis has the SAME structure constants
  have hstruct : ∀ i j, bF i * bF j
      = ∑ l, (algebraMap k F) (b.repr (b i * b j) l) • bF l := by
    intro i j
    have hbFi : ∀ i, bF i = (1 : F) ⊗ₜ[k] b i := by
      intro i; simp [hbF, Module.Basis.baseChange_apply]
    rw [hbFi, hbFi, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    conv_lhs => rw [show b i * b j = ∑ l, b.repr (b i * b j) l • b l from (b.sum_repr _).symm]
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hbFi, TensorProduct.tmul_smul, algebraMap_smul]
  have hmatF : LinearMap.BilinForm.toMatrix bF (frobeniusTraceForm Θ)
      = Matrix.of fun i j =>
          ∑ l, (algebraMap k F) (b.repr (b i * b j) l) * Θ (bF l) := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, frobeniusTraceForm_apply, hstruct i j, map_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [map_smul, smul_eq_mul]
  have hdetF : (LinearMap.BilinForm.toMatrix bF (frobeniusTraceForm Θ)).det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero bF).mp
      (LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft hΘ)
  have hmapne : MvPolynomial.map (algebraMap k F) (gramDet b) ≠ 0 := by
    intro hzero
    apply hdetF
    rw [hmatF, ← eval_map_gramDet b (algebraMap k F) (fun l => Θ (bF l)), hzero]
    simp
  have hPne : gramDet b ≠ 0 := fun hz => hmapne (by rw [hz]; simp)
  -- a nonzero polynomial over an infinite field has a nonvanishing point
  have hx : ∃ x : Fin n → k, eval x (gramDet b) ≠ 0 := by
    by_contra hcon
    refine hPne (MvPolynomial.funext fun x => ?_)
    simpa using not_not.mp (not_exists.mp hcon x)
  obtain ⟨x, hxne⟩ := hx
  refine ⟨b.constr k x, frobenius_of_gramDet_ne_zero b _ ?_⟩
  have hval : (fun l => (b.constr k x) (b l)) = x := by
    funext l; simp
  rw [hval]
  exact hxne

end FrobeniusDescent

namespace FrobeniusSocle

/-! ### Gorenstein duality for a commutative Frobenius algebra

The declarations of this namespace are the commutative-algebra content of
`exists_freeElement_of_frobenius` below. For a finite-dimensional commutative
`F`-algebra `A` carrying a Frobenius form `θ`, the trace form identifies `A`
with its `F`-dual in a way that turns the ideal-theoretic annihilator into an
orthogonal complement; the consequences are a dimension formula
(`finrank_annihilator_add_finrank`), the duality `ann (ann I) = I`
(`annihilator_annihilator`), and — this is the Gorenstein content — the fact
that for each maximal ideal `m` the ideal `ann m` is a MINIMAL nonzero ideal,
generated by any of its nonzero elements
(`span_singleton_eq_annihilator`, `annihilator_span_singleton_eq`).

Everything here is stated for a bare `CommRing A`; the leaf itself is stated
over `Ring A` together with a commutativity hypothesis, which is the form its
consumer holds (and which is not optional — see the FALSITY AUDIT there). -/

variable {F : Type*} [Field F] {A : Type*} [CommRing A] [Algebra F A]

/-- The **Frobenius comparison map** `A → A^∨`, `a ↦ (b ↦ θ (a * b))`. It is
injective exactly when `θ` is a Frobenius form, and then bijective because `A`
and `A^∨` have the same dimension. -/
noncomputable def frobeniusDualMap (θ : A →ₗ[F] F) : A →ₗ[F] Module.Dual F A where
  toFun a := θ.comp (LinearMap.mulLeft F a)
  map_add' x y := by ext t; simp [add_mul]
  map_smul' c x := by ext t; simp

@[simp] theorem frobeniusDualMap_apply (θ : A →ₗ[F] F) (a b : A) :
    frobeniusDualMap (F := F) θ a b = θ (a * b) := rfl

theorem frobeniusDualMap_injective (θ : A →ₗ[F] F)
    (hθ : ∀ a : A, (∀ b : A, θ (a * b) = 0) → a = 0) :
    Function.Injective (frobeniusDualMap (F := F) θ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  refine hθ x fun b => ?_
  have h := congrArg (fun (f : Module.Dual F A) => f b) hx
  simpa using h

/-- Antitonicity of the ideal annihilator. -/
theorem annihilator_le_annihilator_of_le {I J : Ideal A} (h : I ≤ J) :
    J.annihilator ≤ I.annihilator := by
  intro x hx
  rw [Submodule.mem_annihilator] at hx ⊢
  exact fun n hn => hx n (h hn)

/-- **The unique minimal ideal attached to a maximal ideal, half one**: for a
maximal ideal `m` and a nonzero `a ∈ ann m`, the annihilator of `a` is `m`
itself. (No Frobenius hypothesis: `ann a` contains `m`, is proper because
`1 * a = a ≠ 0`, and `m` is maximal.) -/
theorem annihilator_span_singleton_eq {m : Ideal A} (hm : m.IsMaximal)
    {a : A} (ha : a ∈ m.annihilator) (ha0 : a ≠ 0) :
    (Ideal.span ({a} : Set A)).annihilator = m := by
  have hle : m ≤ (Ideal.span ({a} : Set A)).annihilator := by
    intro x hx
    rw [Submodule.mem_annihilator_span_singleton]
    have hxa := Submodule.mem_annihilator.mp ha x hx
    simp only [smul_eq_mul] at hxa ⊢
    rw [mul_comm]
    exact hxa
  have hne : (Ideal.span ({a} : Set A)).annihilator ≠ ⊤ := by
    intro htop
    apply ha0
    have h1 : (1 : A) ∈ (Ideal.span ({a} : Set A)).annihilator := by
      rw [htop]; trivial
    rw [Submodule.mem_annihilator_span_singleton] at h1
    simpa using h1
  exact (hm.eq_of_le hne hle).symm

variable [FiniteDimensional F A]

theorem frobeniusDualMap_surjective (θ : A →ₗ[F] F)
    (hθ : ∀ a : A, (∀ b : A, θ (a * b) = 0) → a = 0) :
    Function.Surjective (frobeniusDualMap (F := F) θ) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq (K := F) (V := A)).symm).mp (frobeniusDualMap_injective θ hθ)

/-- **Step 1 — Gorenstein duality from the form**: `ann I` is the orthogonal
complement of `I` for the trace form, so `dim ann I = dim A − dim I` for EVERY
ideal `I`. This is the only place the Frobenius hypothesis enters, and
everything else in this namespace is a consequence of it. -/
theorem finrank_annihilator_add_finrank (θ : A →ₗ[F] F)
    (hθ : ∀ a : A, (∀ b : A, θ (a * b) = 0) → a = 0) (I : Ideal A) :
    Module.finrank F (Submodule.restrictScalars F I.annihilator)
      + Module.finrank F (Submodule.restrictScalars F I) = Module.finrank F A := by
  have hmap : Submodule.map (frobeniusDualMap (F := F) θ)
        (Submodule.restrictScalars F I.annihilator)
      = (Submodule.restrictScalars F I).dualAnnihilator := by
    ext f
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [Submodule.mem_dualAnnihilator]
      intro w hw
      have ha' : a * w = 0 := by
        have h := Submodule.mem_annihilator.mp ha w hw
        simpa using h
      simp [ha']
    · intro hf
      obtain ⟨a, rfl⟩ := frobeniusDualMap_surjective θ hθ f
      refine ⟨a, ?_, rfl⟩
      simp only [SetLike.mem_coe, Submodule.restrictScalars_mem, Submodule.mem_annihilator]
      intro n hn
      have han : a * n = 0 := by
        refine hθ (a * n) fun b => ?_
        rw [mul_assoc]
        exact ((Submodule.mem_dualAnnihilator _).mp hf) (n * b)
          (by exact Ideal.mul_mem_right b I hn)
      simpa using han
  have h1 : Module.finrank F (Submodule.restrictScalars F I.annihilator)
      = Module.finrank F ((Submodule.restrictScalars F I).dualAnnihilator) := by
    rw [← hmap]
    exact (Submodule.equivMapOfInjective _ (frobeniusDualMap_injective θ hθ) _).finrank_eq
  rw [h1, add_comm]
  exact Subspace.finrank_add_finrank_dualAnnihilator_eq _

/-- **The duality `ann (ann I) = I`**, immediate from step 1 and
`I ≤ ann (ann I)`. -/
theorem annihilator_annihilator (θ : A →ₗ[F] F)
    (hθ : ∀ a : A, (∀ b : A, θ (a * b) = 0) → a = 0) (I : Ideal A) :
    I.annihilator.annihilator = I := by
  have hle : Submodule.restrictScalars F I
      ≤ Submodule.restrictScalars F I.annihilator.annihilator := by
    intro x hx
    simp only [Submodule.restrictScalars_mem, Submodule.mem_annihilator] at hx ⊢
    intro n hn
    have h := hn x hx
    simp only [smul_eq_mul] at h ⊢
    rw [mul_comm]
    exact h
  have h1 := finrank_annihilator_add_finrank θ hθ I
  have h2 := finrank_annihilator_add_finrank θ hθ I.annihilator
  have hfr : Module.finrank F (Submodule.restrictScalars F I.annihilator.annihilator)
      ≤ Module.finrank F (Submodule.restrictScalars F I) := by omega
  exact (Submodule.restrictScalars_injective F A A
    (Submodule.eq_of_le_of_finrank_le hle hfr)).symm

/-- **Step 2 — the minimal ideal at a maximal ideal is nonzero**:
`dim ann m = dim A − dim m > 0`. -/
theorem annihilator_maximal_ne_bot (θ : A →ₗ[F] F)
    (hθ : ∀ a : A, (∀ b : A, θ (a * b) = 0) → a = 0) {m : Ideal A} (hm : m.IsMaximal) :
    m.annihilator ≠ ⊥ := by
  intro hbot
  have h1 := finrank_annihilator_add_finrank θ hθ m
  rw [hbot] at h1
  have h2 : Module.finrank F (Submodule.restrictScalars F (⊥ : Ideal A)) = 0 := by
    have hb : Submodule.restrictScalars F (⊥ : Ideal A) = ⊥ := by ext x; simp
    rw [hb]
    exact finrank_bot F A
  rw [h2, zero_add] at h1
  have h3 : Submodule.restrictScalars F m ≠ ⊤ := by
    intro htop
    refine hm.ne_top ((Ideal.eq_top_iff_one m).mpr ?_)
    have h4 : (1 : A) ∈ Submodule.restrictScalars F m := by rw [htop]; trivial
    exact h4
  exact absurd h1 (Nat.ne_of_lt (Submodule.finrank_lt h3))

/-- **The unique minimal ideal attached to a maximal ideal, half two**: `ann m`
is generated by ANY of its nonzero elements, i.e. it is a minimal nonzero
ideal. Both dimensions equal `dim A − dim m`: the left one by step 1, the right
one by rank–nullity for `x ↦ x * a` together with
`annihilator_span_singleton_eq`. -/
theorem span_singleton_eq_annihilator (θ : A →ₗ[F] F)
    (hθ : ∀ a : A, (∀ b : A, θ (a * b) = 0) → a = 0) {m : Ideal A} (hm : m.IsMaximal)
    {a : A} (ha : a ∈ m.annihilator) (ha0 : a ≠ 0) :
    Ideal.span ({a} : Set A) = m.annihilator := by
  have hle : Submodule.restrictScalars F (Ideal.span ({a} : Set A))
      ≤ Submodule.restrictScalars F m.annihilator := by
    intro x hx
    simp only [Submodule.restrictScalars_mem] at hx ⊢
    exact (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ha)) hx
  have h1 := finrank_annihilator_add_finrank θ hθ (Ideal.span ({a} : Set A))
  have h2 := finrank_annihilator_add_finrank θ hθ m
  rw [annihilator_span_singleton_eq hm ha ha0] at h1
  have hfr : Module.finrank F (Submodule.restrictScalars F m.annihilator)
      ≤ Module.finrank F (Submodule.restrictScalars F (Ideal.span ({a} : Set A))) := by omega
  exact Submodule.restrictScalars_injective F A A (Submodule.eq_of_le_of_finrank_le hle hfr)

/-- **Every nonzero ideal contains the minimal ideal of some maximal ideal.**
Take `0 ≠ b ∈ I` and a maximal `m ⊇ ann b`; then
`ann m ≤ ann (ann b) = (b) ≤ I` by the duality. -/
theorem exists_maximal_annihilator_le (θ : A →ₗ[F] F)
    (hθ : ∀ a : A, (∀ b : A, θ (a * b) = 0) → a = 0) {b : A} (hb : b ≠ 0) :
    ∃ m : Ideal A, m.IsMaximal ∧ m.annihilator ≤ Ideal.span ({b} : Set A) := by
  have hne : (Ideal.span ({b} : Set A)).annihilator ≠ ⊤ := by
    intro htop
    apply hb
    have h1 : (1 : A) ∈ (Ideal.span ({b} : Set A)).annihilator := by rw [htop]; trivial
    rw [Submodule.mem_annihilator_span_singleton] at h1
    simpa using h1
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  refine ⟨m, hm, ?_⟩
  calc m.annihilator ≤ (Ideal.span ({b} : Set A)).annihilator.annihilator :=
        annihilator_le_annihilator_of_le hle
    _ = Ideal.span ({b} : Set A) := annihilator_annihilator θ hθ _

/-- **Step 3, the separator**: a finite-dimensional algebra has finitely many
maximal ideals, and for each one there is an element lying in all the OTHERS
and not in it (prime avoidance). This is what lets the finitely many witnesses
of the main proof be merged into a single vector, and it is why no
infinite-field hypothesis is needed. -/
theorem exists_separator [IsArtinianRing A] [Fintype (MaximalSpectrum A)]
    (i : MaximalSpectrum A) :
    ∃ y : A, (∀ j : MaximalSpectrum A, j ≠ i → y ∈ j.asIdeal) ∧ y ∉ i.asIdeal := by
  classical
  have hprime : i.asIdeal.IsPrime := i.isMaximal.isPrime
  have hprod : ¬ (∏ j ∈ Finset.univ.erase i, j.asIdeal) ≤ i.asIdeal := by
    intro hle
    obtain ⟨j, hj, hji⟩ := hprime.prod_le.mp hle
    exact (Finset.mem_erase.mp hj).1
      (MaximalSpectrum.ext (j.isMaximal.eq_of_le i.isMaximal.ne_top hji))
  obtain ⟨y, hy, hyi⟩ := SetLike.not_le_iff_exists.mp hprod
  refine ⟨y, fun j hj => ?_, hyi⟩
  have hsub : (∏ k ∈ Finset.univ.erase i, k.asIdeal) ≤ j.asIdeal :=
    le_trans Ideal.prod_le_inf (Finset.inf_le (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩))
  exact hsub hy

/-- **The commutative case of `exists_freeElement_of_frobenius`**, and the whole
mathematical content of it. -/
theorem exists_freeElement {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V]
    (θ : A →ₗ[F] F) (hθ : ∀ a : A, (∀ b : A, θ (a * b) = 0) → a = 0)
    (act : A →ₐ[F] Module.End F V) (hact : Function.Injective act) :
    ∃ v : V, ∀ a : A, act a v = 0 → a = 0 := by
  classical
  haveI : IsArtinianRing A := isArtinian_of_tower F inferInstance
  haveI : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  have hact0 : ∀ a : A, a ≠ 0 → ∃ w : V, act a w ≠ 0 := by
    intro a ha
    by_contra hcon
    refine ha (hact ?_)
    have hz : ∀ w : V, act a w = 0 := by
      intro w
      by_contra hw
      exact hcon ⟨w, hw⟩
    ext w
    simpa using hz w
  have hA : ∀ i : MaximalSpectrum A, ∃ a : A, a ∈ i.asIdeal.annihilator ∧ a ≠ 0 := by
    intro i
    exact (Submodule.ne_bot_iff _).mp (annihilator_maximal_ne_bot θ hθ i.isMaximal)
  choose a ha ha0 using hA
  have hW : ∀ i : MaximalSpectrum A, ∃ w : V, act (a i) w ≠ 0 := fun i => hact0 _ (ha0 i)
  choose w hw using hW
  choose y hy hyi using fun i : MaximalSpectrum A => exists_separator (A := A) i
  refine ⟨∑ i : MaximalSpectrum A, act (y i) (w i), ?_⟩
  intro b hb
  by_contra hb0
  obtain ⟨m, hm, hmle⟩ := exists_maximal_annihilator_le θ hθ hb0
  set i : MaximalSpectrum A := ⟨m, hm⟩ with hi
  have him : i.asIdeal = m := rfl
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hmle (him ▸ ha i))
  have key : act (a i) (∑ j : MaximalSpectrum A, act (y j) (w j)) = 0 := by
    rw [← hc, map_mul, Module.End.mul_apply, hb, map_zero]
  have expand : act (a i) (∑ j : MaximalSpectrum A, act (y j) (w j))
      = act (a i * y i) (w i) := by
    rw [map_sum]
    refine Finset.sum_eq_single i ?_ (fun h => absurd (Finset.mem_univ i) h) |>.trans ?_
    · intro j _ hji
      have hzero : a i * y j = 0 := by
        have h := Submodule.mem_annihilator.mp (ha i) (y j) (hy j i (Ne.symm hji))
        simpa using h
      have hstep : act (a i) (act (y j) (w j)) = act (a i * y j) (w j) := by
        rw [map_mul]; rfl
      rw [hstep, hzero]
      simp
    · rw [map_mul]; rfl
  rw [expand] at key
  have ham : a i ∈ m.annihilator := him ▸ ha i
  have hyne : a i * y i ≠ 0 := by
    intro h0
    refine hyi i ?_
    rw [him, ← annihilator_span_singleton_eq hm ham (ha0 i),
      Submodule.mem_annihilator_span_singleton]
    simpa [mul_comm] using h0
  have hspan : Ideal.span ({a i * y i} : Set A) = m.annihilator :=
    span_singleton_eq_annihilator θ hθ hm (Ideal.mul_mem_right _ _ ham) hyne
  obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.mp (by rw [hspan]; exact ham)
  refine hw i ?_
  rw [← hc', map_mul, Module.End.mul_apply, key, map_zero]

end FrobeniusSocle

section FrobeniusFree

variable {F : Type*} [Field F] {A : Type*} [Ring A] [Algebra F A]
variable {V : Type*} [AddCommGroup V] [Module F V]

/-- **A FAITHFUL MODULE OVER A COMMUTATIVE FROBENIUS ALGEBRA CONTAINS A
FREE RANK-ONE SUBMODULE** (opened by the SIXTEENTH decomposition of the
modularity subtree, 2026-07-27; **PROVEN 2026-07-28**, after the missing
commutativity hypothesis was supplied — see the FALSITY AUDIT below): if `A` is
a finite-dimensional commutative `F`-algebra carrying a Frobenius form `θ`
(nondegenerate trace form) and `V` is a faithful `A`-module, then some
`v ∈ V` has `ann_A(v) = 0`.

**FALSITY AUDIT (2026-07-28): the leaf was FALSE as originally stated**, which
omitted `hcomm` although its docstring, its title and its consumer all
described `A` as commutative. Counterexample without it: `A = M₂(F)` with
`θ = trace` — the trace form is nondegenerate, so `hθ` holds — acting on
`V = F²`, which is faithful. Every `v ∈ V` has a nonzero annihilator: for
`v = 0` take `a = 1`, and for `v ≠ 0` take any nonzero rank-one `a = u ⊗ f`
with `f v = 0`. So no free element exists, and the leaf fails. The repair is
the one hypothesis the caller already held: `exists_frameEquiv_of_symplectic`
takes `hcomm` for its own use and was discarding it here.

THE PROOF, as executed (it is the docstring's three steps, with step 3 done by
separators rather than by avoiding a union of subspaces, so that NO
infinite-field hypothesis is needed; the machinery is in the `FrobeniusSocle`
namespace above).

This is the ONE deep input of `exists_frameEquiv_of_symplectic` below,
and hence of the sixteenth cut of `exists_galoisRep_modularTateFrame_traceDet`
in `Modularity/Interface.lean`. It is pure commutative algebra: no Galois
theory, no modular curve, no `p`-adics.

WHY IT IS TRUE, in a form a successor can execute.

*Step 1 — Gorenstein duality from the form.* For an ideal `I ⊆ A` one has
`ann_A(I) = I^⊥` for the trace form `(a,b) ↦ θ(ab)`: `a ∈ ann(I)` gives
`θ(a·I) = 0`; conversely `θ(a·i·b) = 0` for all `b` forces `a·i = 0` by
nondegeneracy. Hence `dim_F ann(I) = dim_F A − dim_F I` for EVERY ideal —
this is the only place the Frobenius hypothesis is used, and it is a
one-line consequence of it.

*Step 2 — one minimal ideal per maximal ideal.* Fix a maximal ideal `𝔪` and put
`m := ann(𝔪)`. It is nonzero, since `dim m = dim A − dim 𝔪 > 0` by step 1
(`FrobeniusSocle.annihilator_maximal_ne_bot`), and it is a MINIMAL nonzero
ideal: for `0 ≠ a ∈ m` the ideal `ann(a)` contains `𝔪` and is proper, hence
equals `𝔪` by maximality (`annihilator_span_singleton_eq`), so rank–nullity for
`x ↦ x·a` gives `dim (a) = dim A − dim 𝔪 = dim m`, whence `(a) = m`
(`span_singleton_eq_annihilator`). Conversely EVERY nonzero ideal `I` contains
such an `m`: take `0 ≠ b ∈ I` and a maximal `𝔪 ⊇ ann(b)`, and use the duality
`ann(ann(I)) = I` — itself immediate from step 1 — to get
`ann(𝔪) ⊆ ann(ann(b)) = (b) ⊆ I` (`exists_maximal_annihilator_le`). So
`ann(v) = 0` **iff** `ann(𝔪)·v ≠ 0` for every maximal `𝔪`.

*Step 3 — merge the witnesses.* `A` is artinian, so it has finitely many
maximal ideals `𝔪₁, …, 𝔪_s`; faithfulness gives, for each `i`, a nonzero
`aᵢ ∈ ann(𝔪ᵢ)` and a `wᵢ ∈ V` with `aᵢ·wᵢ ≠ 0`. Prime avoidance supplies a
separator `yᵢ ∈ ⋂_{j≠i} 𝔪_j \ 𝔪ᵢ` (`exists_separator`). Then
`v := Σ_i yᵢ·wᵢ` works: for `b ≠ 0`, step 2 gives an `i` with `aᵢ ∈ (b)`, and
`aᵢ·v = (aᵢyᵢ)·wᵢ` because `aᵢy_j = 0` for `j ≠ i`; since `yᵢ ∉ 𝔪ᵢ = ann(aᵢ)`
the element `aᵢyᵢ` is a nonzero member of the minimal ideal `ann(𝔪ᵢ)`, hence
generates it, hence `aᵢ ∈ (aᵢyᵢ)` and `aᵢ·wᵢ = 0` — contradiction. So
`b·v ≠ 0`.

NOTE this replaces the original step 3 ("`{v : ann(v) ≠ 0}` is a finite union
of proper subspaces, avoid it"), which needs `F` infinite. The separator
argument needs nothing of the kind, so the theorem holds over EVERY field, and
the leaf carries no `Infinite F` hypothesis. (`F = ℚ̄_p` in the application, so
either route would have sufficed there.)

CLASSICAL NAME: this is the standard first step of "an abelian variety
whose Tate module carries a nondegenerate alternating self-adjoint
pairing over a Gorenstein Hecke algebra is free of rank two", i.e. of
multiplicity one (Mazur, *Eisenstein ideal* II §15; Ribet, *Invent.
Math.* 100 (1990) §2).

REFUTING CHECK (discharged): no commutative artinian Frobenius `F`-algebra `A`
carries a faithful `V` in which every element has nonzero annihilator. Drop
commutativity and `M₂(F)` on `F²` is such a pair — see the FALSITY AUDIT
above. -/
theorem exists_freeElement_of_frobenius [FiniteDimensional F A] [FiniteDimensional F V]
    (hcomm : ∀ x y : A, x * y = y * x)
    (θ : A →ₗ[F] F) (hθ : ∀ a : A, (∀ b : A, θ (a * b) = 0) → a = 0)
    (act : A →ₐ[F] Module.End F V) (hact : Function.Injective act) :
    ∃ v : V, ∀ a : A, act a v = 0 → a = 0 := by
  letI : CommRing A := { (inferInstance : Ring A) with mul_comm := hcomm }
  exact FrobeniusSocle.exists_freeElement θ hθ act hact

/-- **THE SYMPLECTIC RIGIDITY OF THE FRAME**: over a commutative
Frobenius algebra `A`, a FAITHFUL module `V` of dimension `2·dim A`
carrying a NONDEGENERATE ALTERNATING `A`-self-adjoint form IS `A²`.

This is the algebra question the CUT-OBSTRUCTION AUDIT of
`exists_galoisRep_modularTateFrame_traceDet` (`Modularity/Interface.lean`)
asked a successor to settle before attempting any geometry. **The answer
is YES away from characteristic two**, and this is the proof; it is what
makes the sixteenth cut of that leaf possible, because it removes item 7
(freeness of the Tate module of rank two over `𝕋`) from the geometry and
turns it into commutative algebra.

PROOF, and it is short once the free element is in hand. Let `v` be an
element with `ann_A(v) = 0` (`exists_freeElement_of_frobenius` above; the
only deep input) and put `L := A·v`, a free rank-one submodule.

1. *`L` is isotropic.* `⟨a·v, b·v⟩ = ⟨v, (ab)·v⟩ =: g(ab)` with `g`
   `F`-linear, and `g(a²) = ⟨a·v, a·v⟩ = 0` by alternation; polarizing,
   `2g(a) = g((a+1)²) − g(a²) − g(1) = 0`, so `g ≡ 0` since `2 ≠ 0`.
   **This is the only use of `char F ≠ 2`, and the statement is FALSE in
   characteristic two — see the counterexample below.**
2. *The Frobenius functional identifies `A ≅ A^∨`*, so the `A`-linear map
   `Φ : V → A^∨`, `w ↦ (a ↦ ⟨a·v, w⟩)`, becomes `φ : V → A`. `Φ` is the
   composite of the isomorphism `V ≅ V^∨` (nondegeneracy, finite
   dimension) with `A^∨ ← V^∨` dual to the injection `a ↦ a·v`, hence is
   SURJECTIVE.
3. *`ker φ = L`.* Step 1 gives `L ⊆ ker φ`; rank–nullity and `φ`
   surjective give `dim ker φ = 2·dim A − dim A = dim A = dim L`.
4. *Split.* Pick `u` with `φ(u) = 1`. Then `(a, b) ↦ a·v + b·u` is an
   `A`-linear bijection `A² → V`: injective because `φ` kills `a·v` and
   sends `b·u` to `b`; surjective because `w − φ(w)·u ∈ ker φ = L`.

**FALSE IN CHARACTERISTIC TWO** (counterexample found 2026-07-27, and
recorded so that nobody drops `h2`). Take `char k = 2`,
`A = k × k[x]/x²` (`dim A = 3`, commutative artinian Frobenius as a
product of Frobenius algebras) and
`V = k⁴ ⊕ k[x]/x²` (`dim V = 6 = 2·dim A`), faithful. Give `k⁴` the
standard symplectic form and `k[x]/x²` the trace form of `θ(α + βx) := β`
— which in characteristic two IS alternating, since
`(α + βx)² = α²` and `θ(α²) = 0` — with the two blocks orthogonal. Every
hypothesis but `h2` holds, and `V ≇ A²` because the first idempotent cuts
out `k⁴` on one side and `k²` on the other.

The application has `F = ℚ̄_p`, of characteristic zero, so the
restriction costs nothing there. -/
theorem exists_frameEquiv_of_symplectic [FiniteDimensional F A] [FiniteDimensional F V]
    (h2 : (2 : F) ≠ 0) (hcomm : ∀ x y : A, x * y = y * x)
    (θ : A →ₗ[F] F) (hθ : ∀ a : A, (∀ b : A, θ (a * b) = 0) → a = 0)
    (act : A →ₐ[F] Module.End F V) (hact : Function.Injective act)
    (hdim : Module.finrank F V = 2 * Module.finrank F A)
    (P : V →ₗ[F] V →ₗ[F] F)
    (hself : ∀ x : V, P x x = 0)
    (hnondeg : ∀ x : V, (∀ y : V, P x y = 0) → x = 0)
    (hadj : ∀ (a : A) (x y : V), P (act a x) y = P x (act a y)) :
    ∃ e : V ≃ₗ[F] (Fin 2 → A), ∀ (a : A) (x : V), e (act a x) = a • e x := by
  classical
  -- alternating implies skew
  have hskew : ∀ x y : V, P x y + P y x = 0 := by
    intro x y
    have h := hself (x + y)
    simp only [map_add, LinearMap.add_apply] at h
    rw [hself x, hself y, zero_add, add_zero] at h
    rw [add_comm]
    exact h
  have hnondeg' : ∀ x : V, (∀ y : V, P y x = 0) → x = 0 := by
    intro x hx
    refine hnondeg x fun y => ?_
    have h := hskew x y
    rw [hx y, add_zero] at h
    exact h
  -- the Frobenius identification `A ≅ A^∨`
  set Θ : A →ₗ[F] Module.Dual F A :=
    { toFun := fun a => θ.comp (LinearMap.mulLeft F a)
      map_add' := by intro x y; ext t; simp [add_mul]
      map_smul' := by intro c x; ext t; simp }
  have hΘapply : ∀ a b : A, Θ a b = θ (a * b) := fun _ _ => rfl
  have hΘinj : Function.Injective Θ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    refine hθ x fun b => ?_
    have h := congrArg (fun (f : Module.Dual F A) => f b) hx
    simpa [hΘapply] using h
  have hΘsurj : Function.Surjective Θ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := F) (V := A)).symm).mp hΘinj
  set Θe : A ≃ₗ[F] Module.Dual F A := LinearEquiv.ofBijective Θ ⟨hΘinj, hΘsurj⟩
  -- a free element
  obtain ⟨v, hv⟩ := exists_freeElement_of_frobenius hcomm θ hθ act hact
  set Lv : A →ₗ[F] V :=
    { toFun := fun a => act a v
      map_add' := by intro x y; simp
      map_smul' := by intro c x; simp }
  have hLvapply : ∀ a : A, Lv a = act a v := fun _ => rfl
  have hLvinj : Function.Injective Lv := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    exact hv a ha
  -- the functional `w ↦ (a ↦ ⟨a·v, w⟩)`, surjective onto `A^∨`
  set Φ : V →ₗ[F] Module.Dual F A := Lv.dualMap.comp P.flip
  have hΦapply : ∀ (w : V) (a : A), Φ w a = P (act a v) w := fun _ _ => rfl
  have hPflipinj : Function.Injective P.flip := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    refine hnondeg' x fun y => ?_
    have h := congrArg (fun (f : Module.Dual F V) => f y) hx
    simpa using h
  have hPflipsurj : Function.Surjective P.flip :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := F) (V := V)).symm).mp hPflipinj
  have hΦsurj : Function.Surjective Φ := by
    have h := (LinearMap.dualMap_surjective_of_injective hLvinj).comp hPflipsurj
    exact h
  -- `φ : V → A`, `A`-linear and surjective
  set φ : V →ₗ[F] A := Θe.symm.toLinearMap.comp Φ
  have hφspec : ∀ (w : V) (a : A), θ (φ w * a) = P (act a v) w := by
    intro w a
    have hΘφ : Θ (φ w) = Φ w := Θe.apply_symm_apply (Φ w)
    calc θ (φ w * a) = Θ (φ w) a := (hΘapply _ _).symm
      _ = Φ w a := by rw [hΘφ]
      _ = P (act a v) w := hΦapply w a
  have hφsurj : Function.Surjective φ := Θe.symm.surjective.comp hΦsurj
  have hactmul : ∀ (a b : A) (x : V), act a (act b x) = act (a * b) x := by
    intro a b x
    rw [map_mul]
    rfl
  have hφlin : ∀ (b : A) (w : V), φ (act b w) = b * φ w := by
    intro b w
    refine hΘinj (LinearMap.ext fun a => ?_)
    rw [hΘapply, hΘapply, hφspec (act b w) a, ← hadj b (act a v) w, hactmul,
      ← hφspec w (b * a)]
    congr 1
    rw [← mul_assoc, hcomm (φ w) b]
  -- the free line `A·v` is isotropic
  set g : A →ₗ[F] F :=
    { toFun := fun a => P v (act a v)
      map_add' := by intro x y; simp
      map_smul' := by intro c x; simp }
  have hgapply : ∀ a : A, g a = P v (act a v) := fun _ => rfl
  have hgsq : ∀ a : A, g (a * a) = 0 := by
    intro a
    rw [hgapply, ← hactmul, ← hadj a v (act a v), hself]
  have hg : ∀ a : A, g a = 0 := by
    intro a
    have h1 : (a + 1) * (a + 1) = a * a + (a + a) + 1 * 1 := by
      rw [add_mul, mul_add, mul_add]; simp [mul_one, one_mul]; abel
    have h2' := hgsq (a + 1)
    rw [h1, map_add, map_add, hgsq a, hgsq 1, map_add, zero_add, add_zero] at h2'
    have h3 : (2 : F) * g a = 0 := by rw [two_mul]; exact h2'
    exact (mul_eq_zero.mp h3).resolve_left h2
  have hLker : ∀ c : A, φ (act c v) = 0 := by
    intro c
    have hz : Θ (φ (act c v)) = Θ 0 := by
      refine LinearMap.ext fun a => ?_
      rw [hΘapply, hΘapply, hφspec (act c v) a, hadj a v (act c v), hactmul,
        zero_mul, map_zero]
      exact hg (a * c)
    exact hΘinj hz
  -- the kernel of `φ` is exactly that line, by dimension count
  have hkerdim : Module.finrank F (LinearMap.ker φ) = Module.finrank F A := by
    have h := LinearMap.finrank_range_add_finrank_ker φ
    rw [LinearMap.range_eq_top.mpr hφsurj, finrank_top, hdim] at h
    omega
  have hrangedim : Module.finrank F (LinearMap.range Lv) = Module.finrank F A :=
    LinearMap.finrank_range_of_inj hLvinj
  have hle : LinearMap.range Lv ≤ LinearMap.ker φ := by
    rintro x ⟨c, rfl⟩
    exact hLker c
  have hEq : LinearMap.range Lv = LinearMap.ker φ :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hrangedim, hkerdim])
  -- a second generator
  obtain ⟨u, hu⟩ := hφsurj 1
  set ψ : (Fin 2 → A) →ₗ[F] V :=
    { toFun := fun z => act (z 0) v + act (z 1) u
      map_add' := by intro x y; simp; abel
      map_smul' := by intro c x; simp }
  have hψapply : ∀ z : Fin 2 → A, ψ z = act (z 0) v + act (z 1) u := fun _ => rfl
  have hψinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    rw [hψapply] at hz
    have h1 : φ (act (z 0) v) + φ (act (z 1) u) = 0 := by
      rw [← map_add, hz, map_zero]
    rw [hLker (z 0), hφlin (z 1) u, hu, mul_one, zero_add] at h1
    rw [h1, map_zero, LinearMap.zero_apply, add_zero] at hz
    have h0 : z 0 = 0 := hv (z 0) hz
    funext i
    fin_cases i
    · exact h0
    · exact h1
  have hψsurj : Function.Surjective ψ := by
    intro w
    have hkey : w - act (φ w) u ∈ LinearMap.ker φ := by
      simp only [LinearMap.mem_ker, map_sub, hφlin (φ w) u, hu, mul_one, sub_self]
    rw [← hEq] at hkey
    obtain ⟨c, hc⟩ := hkey
    refine ⟨![c, φ w], ?_⟩
    rw [hψapply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hLvapply] at hc
    rw [hc]
    abel
  have hψequiv : ∀ (a : A) (z : Fin 2 → A), ψ (a • z) = act a (ψ z) := by
    intro a z
    rw [hψapply, hψapply, map_add]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hactmul, hactmul]
  set E : (Fin 2 → A) ≃ₗ[F] V := LinearEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  have hEapply : ∀ z : Fin 2 → A, E z = ψ z := fun _ => rfl
  refine ⟨E.symm, fun a x => ?_⟩
  refine E.injective ?_
  rw [E.apply_symm_apply, hEapply, hψequiv, ← hEapply, E.apply_symm_apply]

end FrobeniusFree

section TraceDet

variable {k : Type*} [Field k] [CharZero k] {F : Type*} [Field F] [Algebra k F]
variable {T : Type*} [Ring T] [Algebra k T]

/-- **TRACE AND DETERMINANT FROM THE CONGRUENCE RELATION AND THE PAIRING
MULTIPLIER** — the arrow the CUT-OBSTRUCTION AUDIT of
`exists_galoisRep_modularTateFrame_traceDet` records as "elementary but
not formalized, because nothing consumes it". The sixteenth cut consumes
it, so here it is.

Given an `A`-linear `g` on the frame `A²` which
* satisfies the quadratic OPERATOR identity `g² − t·g + c = 0`, and
* multiplies an alternating nondegenerate `A`-self-adjoint form by the
  scalar `c ≠ 0`,

its determinant is `c` and its trace is `t`. Both directions of the
dictionary between "congruence + pairing" and "trace + determinant" are
now formalized: this theorem is `(c) ⟹ (a)`, and `frameCayleyHamilton`
is `(a) ⟹ (b)`.

The determinant half is `frameSymplectic_map_of_commuting` plus
nondegeneracy: `⟨gx, gy⟩ = θ(det g · (x₀y₁ − x₁y₀))` and
`⟨gx, gy⟩ = c⟨x, y⟩ = θ(c · (x₀y₁ − x₁y₀))`, and `(x, y) ↦ x₀y₁ − x₁y₀`
is onto `A` (take `x = (z, 0)`, `y = (0, 1)`), so `θ((det g − c)·z) = 0`
for every `z`. The trace half subtracts Cayley–Hamilton from the
congruence, leaving `(t − tr g)·g = 0`, and cancels `g`: `g` commutes with
`frameMul (tr g)`, so `g·(frameMul (tr g) − g) = c` and multiplying by
that factor turns `(t − tr g)·g = 0` into `c·frameMul (t − tr g) = 0`.
No inverse of `g` is constructed; only `c ≠ 0` is used. -/
theorem traceDet_of_congruence_of_multiplier
    (hcomm : ∀ x y : F ⊗[k] T, x * y = y * x)
    (g : Module.End F (HeckeFrame k F T))
    (hglin : ∀ (r : F ⊗[k] T) (x : HeckeFrame k F T),
      g (frameMul (k := k) (F := F) (T := T) r x) =
        frameMul (k := k) (F := F) (T := T) r (g x))
    (P : HeckeFrame k F T →ₗ[F] HeckeFrame k F T →ₗ[F] F)
    (hself : ∀ x : HeckeFrame k F T, P x x = 0)
    (hnondeg : ∀ x : HeckeFrame k F T, (∀ y, P x y = 0) → x = 0)
    (hadj : ∀ (r : F ⊗[k] T) (x y : HeckeFrame k F T),
      P (frameMul (k := k) (F := F) (T := T) r x) y =
        P x (frameMul (k := k) (F := F) (T := T) r y))
    (c : F) (hc : c ≠ 0)
    (hmult : ∀ x y : HeckeFrame k F T, P (g x) (g y) = c * P x y)
    (t : F ⊗[k] T)
    (hcong : g * g - frameMul (k := k) (F := F) (T := T) t * g + c • 1 = 0) :
    (g frameBasis₁ 0 * g frameBasis₂ 1 - g frameBasis₂ 0 * g frameBasis₁ 1
        = c • (1 : F ⊗[k] T)) ∧
      (g frameBasis₁ 0 + g frameBasis₂ 1 = t) := by
  classical
  obtain ⟨θ, hθ⟩ := exists_frameSymplectic_of_alternating P hself hadj
  have hθfrob : ∀ a : F ⊗[k] T, (∀ b : F ⊗[k] T, θ (a * b) = 0) → a = 0 := by
    refine frobenius_of_frameSymplectic_nondegenerate θ ?_
    intro x hx
    refine hnondeg x fun y => ?_
    rw [hθ]
    exact hx y
  -- the determinant
  have hdet : g frameBasis₁ 0 * g frameBasis₂ 1 - g frameBasis₂ 0 * g frameBasis₁ 1
      = c • (1 : F ⊗[k] T) := by
    have hkey : ∀ z : F ⊗[k] T,
        θ ((g frameBasis₁ 0 * g frameBasis₂ 1 - g frameBasis₂ 0 * g frameBasis₁ 1
          - c • 1) * z) = 0 := by
      intro z
      have hmul := frameSymplectic_map_of_commuting hcomm θ g hglin
        (![z, 0] : HeckeFrame k F T) (![0, 1] : HeckeFrame k F T)
      have hfr := hmult (![z, 0] : HeckeFrame k F T) (![0, 1] : HeckeFrame k F T)
      rw [hθ, hθ, hmul, frameSymplectic_apply] at hfr
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, mul_zero, sub_zero] at hfr
      rw [sub_mul, map_sub, hfr, smul_mul_assoc, one_mul, map_smul, smul_eq_mul, sub_self]
    exact sub_eq_zero.mp (hθfrob _ hkey)
  refine ⟨hdet, ?_⟩
  -- the trace
  set tr := g frameBasis₁ 0 + g frameBasis₂ 1
  have hCH := frameCayleyHamilton hcomm g hglin
  rw [hdet] at hCH
  have hc1 : frameMul (k := k) (F := F) (T := T) (c • (1 : F ⊗[k] T)) = c • 1 := by
    rw [map_smul, map_one]
  rw [hc1] at hCH
  have heq : g * g - frameMul (k := k) (F := F) (T := T) tr * g + c • 1 =
      g * g - frameMul (k := k) (F := F) (T := T) t * g + c • 1 := hCH.trans hcong.symm
  have heq2 := sub_right_injective (add_right_cancel heq)
  have hzero : frameMul (k := k) (F := F) (T := T) (t - tr) * g = 0 := by
    rw [map_sub, sub_mul, ← heq2, sub_self]
  have hcommg : g * frameMul (k := k) (F := F) (T := T) tr =
      frameMul (k := k) (F := F) (T := T) tr * g := by
    refine LinearMap.ext fun z => ?_
    exact hglin tr z
  have hgh : g * (frameMul (k := k) (F := F) (T := T) tr - g) = c • 1 := by
    rw [mul_sub, hcommg]
    have h2' : g * g - frameMul (k := k) (F := F) (T := T) tr * g = -(c • 1) :=
      eq_neg_of_add_eq_zero_left hCH
    have h3' := congrArg Neg.neg h2'
    rw [neg_sub, neg_neg] at h3'
    exact h3'
  have hfin : frameMul (k := k) (F := F) (T := T) (t - tr) = 0 := by
    have h := congrArg (fun f => f * (frameMul (k := k) (F := F) (T := T) tr - g)) hzero
    simp only [mul_assoc, hgh] at h
    rw [mul_smul_comm, mul_one] at h
    exact (smul_eq_zero.mp h).resolve_left hc
  have hfin2 : t - tr = 0 := by
    refine frameMul_injective ?_
    rw [hfin, map_zero]
  exact (sub_eq_zero.mp hfin2).symm

end TraceDet

end GaloisRepresentation.Modularity
