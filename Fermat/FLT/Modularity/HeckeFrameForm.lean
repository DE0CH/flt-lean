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

end GaloisRepresentation.Modularity
