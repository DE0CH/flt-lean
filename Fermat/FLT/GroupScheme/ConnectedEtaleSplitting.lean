module

public import Mathlib.RingTheory.HopfAlgebra.Quotient
public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.Noetherian.Nilpotent

/-!
# The connected–étale splitting of a finite commutative Hopf algebra

Let `A` be a finite commutative Hopf algebra over a field `k` — dually, `G = Spec A` a finite
commutative group scheme.  Write `E` for the étale quotient (`A ⧸ nil A`, the coordinate ring of
`G_red`, a Hopf quotient as soon as `k` is perfect) and `A₀` for the local factor at the identity
(the coordinate ring of `G⁰`).  The main theorem of this file,
`Fermat.ConnectedEtaleSplitting.nonempty_algEquiv_tensor`, is that the canonical map

    φ = (π₀ ⊗ π) ∘ Δ : A ⟶ A₀ ⊗[k] E,      dually    G⁰ × G_red ⟶ G,

is an isomorphism of `k`-algebras.

## The route, and why it needs no base change

The classical proof passes to a field `K` splitting `E`, where the local factors of `A ⊗ K` are
permuted simply transitively by the translation automorphisms `τ_g` attached to the `K`-points of
`G`, and then descends by faithful flatness.  **None of that is needed.**  The whole proof here is
convolution algebra over `k` plus one formal-étaleness argument, and it turns on the following
observation, which is the reason the file is short.

`E` is étale over `k`, hence formally étale, and `π : A ↠ E` has nilpotent kernel.  So `π` admits
an algebra section `s : E →ₐ[k] A` — but more importantly the lift is **UNIQUE**, and uniqueness
forces `s` to be a *coalgebra* map as well: both `Δ_A ∘ s` and `(s ⊗ s) ∘ Δ_E` are algebra maps
`E → A ⊗ A` lifting `Δ_E` along the nilpotent surjection `π ⊗ π`, so they agree.  Dually, `s` is
the retraction `r : G ↠ G_red` of the closed immersion `G_red ↪ G`, and it is a homomorphism of
group schemes.

With `s` in hand everything is convolution bookkeeping in the group `WithConv (A →ₐ[k] A)`:

* `c := id * (s ∘ π)⁻¹` is the algebra map dual to `g ↦ g · r(g)⁻¹`;
* `π ∘ c = 1`, because `π ∘ s = id` — so `c(x) ≡ ε(x)` modulo `nil A` for every `x`;
* hence `c(1 − e₀)` is an idempotent **and** a nilpotent, hence `0`.  That is the one step where
  the identity component enters, and it is two lines: it says `g · r(g)⁻¹` lands in `G⁰`;
* so `c` factors as `j ∘ π₀`, and `θ := (x ⊗ y ↦ j x · s y)` is a two-sided inverse of `φ`, by
  `θ ∘ φ = c * (s ∘ π) = id` and by `φ ∘ j = includeLeft`, `φ ∘ s = includeRight`.

**A route note recorded on the leaf this file closes said the section route "does not close",
because "`s` is only an ALGEBRA section and nothing in formal smoothness supplies" that it is a
coalgebra map.**  That is true of *smoothness* and false of *étaleness*: smoothness gives
existence of the lift, unramifiedness gives uniqueness, and uniqueness is what promotes `s` to a
bialgebra map.  The étale quotient is étale, so both halves are available.

## Main statements

* `Fermat.ConnectedEtaleSplitting.exists_section` — the algebra section of a formally étale
  quotient with nilpotent kernel, together with the automatic compatibility with `Δ`.
* `Fermat.ConnectedEtaleSplitting.comp_section_eq_counit` — `π₀ ∘ s` is trivial (`G⁰ ∩ G_red = 1`).
* `Fermat.ConnectedEtaleSplitting.nonempty_algEquiv_tensor` — the splitting.

Nothing in this file mentions a group scheme, a perfect field or a nilradical: the two Hopf
quotients enter abstractly, through `π` and `π₀`, so the statements are reusable at any pair of
Hopf quotients with the stated properties.
-/

@[expose] public section

open TensorProduct Coalgebra Bialgebra HopfAlgebra WithConv

namespace Fermat.ConnectedEtaleSplitting

/-! ### Generalities -/

/-- An ideal contained in a nilpotent ideal is nilpotent. -/
theorem isNilpotent_of_le {R : Type*} [CommRing R] {I J : Ideal R} (hJ : IsNilpotent J)
    (h : I ≤ J) : IsNilpotent I := by
  obtain ⟨n, hn⟩ := hJ
  refine ⟨n, ?_⟩
  have hle : I ^ n ≤ J ^ n := Ideal.pow_right_mono h n
  rw [hn] at hle
  simpa using hle

/-- An element that is both idempotent and nilpotent is zero. -/
theorem eq_zero_of_isIdempotentElem_of_isNilpotent {R : Type*} [MonoidWithZero R] {x : R}
    (hi : IsIdempotentElem x) (hn : IsNilpotent x) : x = 0 := by
  obtain ⟨n, hnx⟩ := hn
  have key : ∀ m : ℕ, x ^ (m + 1) = x := by
    intro m
    induction m with
    | zero => simp
    | succ p ih => rw [pow_succ, ih]; exact hi
  cases n with
  | zero =>
    have h1 : (1 : R) = 0 := by simpa using hnx
    rw [← mul_one x, h1, mul_zero]
  | succ m => rw [← key m]; exact hnx

section Nilpotent

variable {k A E : Type} [Field k] [CommRing A] [Algebra k A] [Module.Finite k A]
  [CommRing E] [Algebra k E]

/-- The kernel of `π ⊗ π` is nilpotent as soon as the kernel of `π` consists of nilpotents:
`Algebra.TensorProduct.map_ker` writes it as the join of two ideals generated by nilpotents, and
`A ⊗[k] A` is noetherian. -/
theorem isNilpotent_ker_map_self (π : A →ₐ[k] E) (hπ : Function.Surjective π)
    (hker : RingHom.ker (π : A →+* E) ≤ nilradical A) :
    IsNilpotent (RingHom.ker (Algebra.TensorProduct.map π π)) := by
  haveI : IsNoetherianRing (A ⊗[k] A) := isNoetherian_of_tower k inferInstance
  refine isNilpotent_of_le (IsNoetherianRing.isNilpotent_nilradical (A ⊗[k] A)) ?_
  rw [Algebra.TensorProduct.map_ker _ _ hπ hπ]
  refine sup_le ?_ ?_ <;> rw [Ideal.map_le_iff_le_comap] <;> intro x hx <;>
    simp only [Ideal.mem_comap, mem_nilradical]
  · exact (mem_nilradical.mp (hker hx)).map _
  · exact (mem_nilradical.mp (hker hx)).map _

end Nilpotent

/-! ### Post-composition is a homomorphism for the convolution product -/

section ConvComp

variable {k A : Type} [Field k] [CommRing A] [Bialgebra k A]

/-- Post-composition with an algebra map is a monoid homomorphism for the convolution product.
Since `WithConv (A →ₐ[k] C)` is a *group* whenever `A` is a Hopf algebra and `C` is commutative,
this is automatically compatible with convolution inverses — which is the only thing it is used
for below. -/
noncomputable def convCompHom {C D : Type} [CommRing C] [Algebra k C] [CommRing D] [Algebra k D]
    (h : C →ₐ[k] D) :
    WithConv (A →ₐ[k] C) →* WithConv (A →ₐ[k] D) where
  toFun f := toConv (h.comp f.ofConv)
  map_one' := by
    refine congrArg toConv (AlgHom.ext fun x => ?_)
    simp [AlgHom.convOne_apply, AlgHom.commutes]
  map_mul' f g := congrArg toConv (AlgHom.comp_convMul_distrib h f g)

@[simp]
theorem convCompHom_apply {C D : Type} [CommRing C] [Algebra k C] [CommRing D] [Algebra k D]
    (h : C →ₐ[k] D) (f : WithConv (A →ₐ[k] C)) :
    (convCompHom h f).ofConv = h.comp f.ofConv := rfl

@[simp]
theorem convCompHom_toConv {C D : Type} [CommRing C] [Algebra k C] [CommRing D] [Algebra k D]
    (h : C →ₐ[k] D) (g : A →ₐ[k] C) :
    convCompHom h (toConv g) = toConv (h.comp g) := rfl

end ConvComp

/-! ### The section of the étale quotient, and its automatic coalgebra property -/

section Section

variable {k A E : Type} [Field k] [CommRing A] [HopfAlgebra k A] [Module.Finite k A]
    [CommRing E] [Bialgebra k E] [Algebra.FormallyEtale k E]

/-- **The algebra section of a formally étale Hopf quotient is automatically a coalgebra map.**

`Algebra.FormallySmooth.liftOfSurjective` produces an algebra section `s` of `π` because the
kernel is nilpotent.  `Algebra.FormallyUnramified.lift_unique'` then says the lift is UNIQUE, and
both `Δ_A ∘ s` and `(s ⊗ s) ∘ Δ_E` lift `Δ_E` along the nilpotent surjection `π ⊗ π`, so they
agree.  Dually: the retraction `G ↠ G_red` is a homomorphism of group schemes. -/
theorem exists_section (π : A →ₐc[k] E) (hπ : Function.Surjective (π : A →ₐ[k] E))
    (hker : RingHom.ker ((π : A →ₐ[k] E) : A →+* E) ≤ nilradical A) :
    ∃ s : E →ₐ[k] A, (π : A →ₐ[k] E).comp s = AlgHom.id k E ∧
      (Algebra.TensorProduct.map s s).comp (Bialgebra.comulAlgHom k E)
        = (Bialgebra.comulAlgHom k A).comp s := by
  haveI : IsNoetherianRing A := isNoetherian_of_tower k inferInstance
  have hnil : IsNilpotent (RingHom.ker ((π : A →ₐ[k] E) : A →+* E)) :=
    isNilpotent_of_le (IsNoetherianRing.isNilpotent_nilradical A) hker
  refine ⟨Algebra.FormallySmooth.liftOfSurjective (AlgHom.id k E) (π : A →ₐ[k] E) hπ hnil, ?_, ?_⟩
  · exact Algebra.FormallySmooth.comp_liftOfSurjective _ _ _ _
  · set s := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id k E) (π : A →ₐ[k] E) hπ hnil
    have hs : (π : A →ₐ[k] E).comp s = AlgHom.id k E :=
      Algebra.FormallySmooth.comp_liftOfSurjective _ _ _ _
    refine Algebra.FormallyUnramified.lift_unique' (R := k)
      (Algebra.TensorProduct.map (π : A →ₐ[k] E) (π : A →ₐ[k] E))
      (isNilpotent_ker_map_self _ hπ hker) _ _ ?_
    rw [← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp, hs,
      Algebra.TensorProduct.map_id, AlgHom.id_comp]
    refine AlgHom.ext fun y => ?_
    simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]
    have hsy : π (s y) = y := AlgHom.congr_fun hs y
    have hmc := CoalgHomClass.map_comp_comul_apply π (s y)
    rw [hsy] at hmc
    exact hmc.symm

end Section

/-! ### Two coalgebra identities -/

section Aux

/-- In a local bialgebra over a field, the kernel of the counit is the maximal ideal: the counit
is a surjective algebra map onto `k`, so its kernel is maximal. -/
theorem ker_counit_eq_maximalIdeal {k A₀ : Type} [Field k] [CommRing A₀] [Bialgebra k A₀]
    [IsLocalRing A₀] :
    RingHom.ker ((Bialgebra.counitAlgHom k A₀ : A₀ →ₐ[k] k) : A₀ →+* k)
      = IsLocalRing.maximalIdeal A₀ := by
  have hsurj : Function.Surjective ((Bialgebra.counitAlgHom k A₀ : A₀ →ₐ[k] k) : A₀ →+* k) :=
    fun r => ⟨algebraMap k A₀ r, by simp⟩
  exact IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hsurj)

/-- `(ε ⊗ id) ∘ Δ = includeRight`, with the counit pushed into an arbitrary algebra `A₀`. -/
theorem map_counit_comp_comul {k A₀ E : Type} [Field k] [CommRing A₀] [Algebra k A₀]
    [CommRing E] [Bialgebra k E] :
    (Algebra.TensorProduct.map ((Algebra.ofId k A₀).comp (Bialgebra.counitAlgHom k E))
      (AlgHom.id k E)).comp (Bialgebra.comulAlgHom k E)
      = (Algebra.TensorProduct.includeRight : E →ₐ[k] A₀ ⊗[k] E) := by
  refine AlgHom.ext fun y => ?_
  have h := Coalgebra.rTensor_counit_comul (R := k) (A := E) y
  have hcomp : TensorProduct.map
      (((Algebra.ofId k A₀).comp (Bialgebra.counitAlgHom k E)) : E →ₗ[k] A₀)
      (LinearMap.id : E →ₗ[k] E)
      = (TensorProduct.map (Algebra.linearMap k A₀) (LinearMap.id : E →ₗ[k] E)).comp
        (LinearMap.rTensor E (Coalgebra.counit : E →ₗ[k] k)) := by
    rw [LinearMap.rTensor, ← TensorProduct.map_comp]
    rfl
  have hrw : (Algebra.TensorProduct.map ((Algebra.ofId k A₀).comp (Bialgebra.counitAlgHom k E))
      (AlgHom.id k E)) (comul y)
      = TensorProduct.map (((Algebra.ofId k A₀).comp (Bialgebra.counitAlgHom k E)) : E →ₗ[k] A₀)
        (LinearMap.id : E →ₗ[k] E) (comul y) := rfl
  simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, hrw, hcomp,
    LinearMap.comp_apply, h, TensorProduct.map_tmul, LinearMap.id_coe, id_eq]
  simp [Algebra.linearMap_apply]

/-- Multiplying `includeLeft ∘ f` against `includeRight ∘ g` inside `A₀ ⊗[k] E` recovers
`map f g`.  Precomposed with `Δ` this says the convolution of the two is `φ`. -/
theorem lmul_map_include {k A A₀ E : Type} [CommRing k] [CommRing A] [Algebra k A]
    [CommRing A₀] [Algebra k A₀] [CommRing E] [Algebra k E]
    (f : A →ₐ[k] A₀) (g : A →ₐ[k] E) :
    (Algebra.TensorProduct.lmul' k).comp (Algebra.TensorProduct.map
      ((Algebra.TensorProduct.includeLeft : A₀ →ₐ[k] A₀ ⊗[k] E).comp f)
      ((Algebra.TensorProduct.includeRight : E →ₐ[k] A₀ ⊗[k] E).comp g))
      = Algebra.TensorProduct.map f g := by
  refine Algebra.TensorProduct.ext' fun a b => ?_
  simp [Algebra.TensorProduct.tmul_mul_tmul]

end Aux

/-! ### The splitting -/

section Main

variable {k A A₀ E : Type} [Field k] [CommRing A] [HopfAlgebra k A] [Module.Finite k A]
    [CommRing A₀] [Bialgebra k A₀] [IsLocalRing A₀] [Module.Finite k A₀]
    [CommRing E] [Bialgebra k E] [Algebra.FormallyEtale k E]

omit [Module.Finite k A] in
/-- **`G⁰ ∩ G_red = 1`.**  The composite `π₀ ∘ s : E → A₀` and the trivial map `1 ∘ ε` are two
algebra maps out of the formally unramified `E` agreeing modulo the (nilpotent) maximal ideal of
`A₀`, since `ε_{A₀} ∘ π₀ = ε_A` and `ε_A ∘ s = ε_E`.  Hence they are equal. -/
theorem comp_section_eq_counit (π : A →ₐc[k] E) (π₀ : A →ₐc[k] A₀) (s : E →ₐ[k] A)
    (hs : (π : A →ₐ[k] E).comp s = AlgHom.id k E) :
    (π₀ : A →ₐ[k] A₀).comp s = (Algebra.ofId k A₀).comp (Bialgebra.counitAlgHom k E) := by
  haveI : IsArtinianRing A₀ := isArtinian_of_tower k inferInstance
  have hmnil : IsNilpotent (IsLocalRing.maximalIdeal A₀) := by
    rw [← IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal A₀) bot_ne_top]
    exact IsArtinianRing.isNilpotent_jacobson_bot
  refine Algebra.FormallyUnramified.lift_unique' (R := k) (Bialgebra.counitAlgHom k A₀)
    (by rw [ker_counit_eq_maximalIdeal]; exact hmnil) _ _ ?_
  refine AlgHom.ext fun y => ?_
  have h1 : counit (R := k) ((π₀ : A →ₐ[k] A₀) (s y)) = counit (R := k) (s y) :=
    LinearMap.congr_fun (CoalgHomClass.counit_comp (R := k) π₀) (s y)
  have h2 : counit (R := k) (π (s y)) = counit (R := k) (s y) :=
    LinearMap.congr_fun (CoalgHomClass.counit_comp (R := k) π) (s y)
  have h3 : π (s y) = y := AlgHom.congr_fun hs y
  simp only [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, Algebra.ofId_apply]
  rw [h1, ← h2, h3]
  simp

/-- **THE CONNECTED–ÉTALE SPLITTING.**  `φ = (π₀ ⊗ π) ∘ Δ` is an isomorphism of `k`-algebras.

`π` is the étale Hopf quotient (`G_red ↪ G`, whose kernel consists of nilpotents), `π₀` is the
Hopf quotient cutting out the identity component (`G⁰ ↪ G`), presented through a counit-one
idempotent `e₀` whose span-complement is the kernel; `A₀` is local, which is what says `G⁰` is
connected.  Dually the statement is that multiplication `G⁰ × G_red ⟶ G` is an isomorphism.

The proof is described in the module docstring: a section `s` of `π` is automatically a coalgebra
map, `c := id * (s ∘ π)⁻¹` kills `1 - e₀` because `c(1 - e₀)` is idempotent and nilpotent, and the
resulting `j` with `j ∘ π₀ = c` provides the inverse `θ = (x ⊗ y ↦ j x · s y)`. -/
theorem nonempty_algEquiv_tensor
    (π : A →ₐc[k] E) (hπ : Function.Surjective (π : A →ₐ[k] E))
    (hker : RingHom.ker ((π : A →ₐ[k] E) : A →+* E) ≤ nilradical A)
    (π₀ : A →ₐc[k] A₀) (hπ₀ : Function.Surjective (π₀ : A →ₐ[k] A₀))
    {e₀ : A} (he₀ : IsIdempotentElem e₀) (hcε : counit (R := k) e₀ = 1)
    (hker₀ : RingHom.ker ((π₀ : A →ₐ[k] A₀) : A →+* A₀) ≤ Ideal.span {1 - e₀}) :
    Nonempty (A ≃ₐ[k] A₀ ⊗[k] E) := by
  obtain ⟨s, hs, hscomul⟩ := exists_section π hπ hker
  set φ : A →ₐ[k] A₀ ⊗[k] E :=
    (Algebra.TensorProduct.map (π₀ : A →ₐ[k] A₀) (π : A →ₐ[k] E)).comp
      (Bialgebra.comulAlgHom k A) with hφdef
  -- `φ ∘ s = includeRight`: the identity component meets `G_red` trivially
  have hφs : φ.comp s = Algebra.TensorProduct.includeRight := by
    rw [hφdef, AlgHom.comp_assoc, ← hscomul, ← AlgHom.comp_assoc,
      ← Algebra.TensorProduct.map_comp, comp_section_eq_counit π π₀ s hs, hs]
    exact map_counit_comp_comul
  set c : WithConv (A →ₐ[k] A) :=
    toConv (AlgHom.id k A) * (toConv (s.comp (π : A →ₐ[k] E)))⁻¹ with hcdef
  -- `π ∘ c = 1`, i.e. `c(x) ≡ ε(x)` modulo the nilradical
  have hπc : convCompHom (π : A →ₐ[k] E) c = 1 := by
    rw [hcdef, map_mul, map_inv, convCompHom_toConv, convCompHom_toConv, AlgHom.comp_id,
      ← AlgHom.comp_assoc, hs, AlgHom.id_comp, mul_inv_cancel]
  -- `c` kills `1 - e₀`: its value there is idempotent AND nilpotent
  have hce : c.ofConv (1 - e₀) = 0 := by
    have hidem : IsIdempotentElem (c.ofConv (1 - e₀)) := by
      have h1 : IsIdempotentElem (1 - e₀) := he₀.one_sub
      show c.ofConv (1 - e₀) * c.ofConv (1 - e₀) = c.ofConv (1 - e₀)
      rw [← map_mul, h1]
    have hz : (π : A →ₐ[k] E) (c.ofConv (1 - e₀)) = 0 := by
      have h2 := congrArg (fun f : WithConv (A →ₐ[k] E) => f.ofConv (1 - e₀)) hπc
      simpa [AlgHom.convOne_apply, hcε] using h2
    exact eq_zero_of_isIdempotentElem_of_isNilpotent hidem
      (mem_nilradical.mp (hker (RingHom.mem_ker.mpr hz)))
  -- the convolution identity `w * v = φ`
  have hw : toConv ((Algebra.TensorProduct.includeLeft : A₀ →ₐ[k] A₀ ⊗[k] E).comp
        (π₀ : A →ₐ[k] A₀))
      * toConv ((Algebra.TensorProduct.includeRight : E →ₐ[k] A₀ ⊗[k] E).comp
        (π : A →ₐ[k] E)) = toConv φ := by
    rw [AlgHom.convMul_def]
    refine congrArg toConv ?_
    rw [hφdef, ← AlgHom.comp_assoc, lmul_map_include]
  have h1 : convCompHom φ (toConv (AlgHom.id k A)) = toConv φ := by
    rw [convCompHom_toConv, AlgHom.comp_id]
  have h2 : convCompHom φ (toConv (s.comp (π : A →ₐ[k] E)))
      = toConv ((Algebra.TensorProduct.includeRight : E →ₐ[k] A₀ ⊗[k] E).comp
        (π : A →ₐ[k] E)) := by
    rw [convCompHom_toConv, ← AlgHom.comp_assoc, hφs]
  -- `φ ∘ c = includeLeft ∘ π₀`
  have hφc : convCompHom φ c = toConv ((Algebra.TensorProduct.includeLeft :
      A₀ →ₐ[k] A₀ ⊗[k] E).comp (π₀ : A →ₐ[k] A₀)) := by
    rw [hcdef, map_mul, map_inv, h1, h2, mul_inv_eq_iff_eq_mul]
    exact hw.symm
  -- `c` factors through `π₀`
  have hcker : RingHom.ker ((π₀ : A →ₐ[k] A₀) : A →+* A₀)
      ≤ RingHom.ker ((c.ofConv : A →ₐ[k] A) : A →+* A) := by
    intro a ha
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.mp (hker₀ ha)
    refine RingHom.mem_ker.mpr ?_
    show c.ofConv ((1 - e₀) * d) = 0
    rw [map_mul, hce, zero_mul]
  obtain ⟨j, hj⟩ : ∃ j : A₀ →ₐ[k] A, j.comp (π₀ : A →ₐ[k] A₀) = c.ofConv :=
    ⟨AlgHom.liftOfSurjective (π₀ : A →ₐ[k] A₀) hπ₀ c.ofConv hcker,
      AlgHom.liftOfSurjective_comp _ _ _ _⟩
  have hφj : φ.comp j = Algebra.TensorProduct.includeLeft := by
    have hcomp : (φ.comp j).comp (π₀ : A →ₐ[k] A₀)
        = (Algebra.TensorProduct.includeLeft : A₀ →ₐ[k] A₀ ⊗[k] E).comp
          (π₀ : A →ₐ[k] A₀) := by
      rw [AlgHom.comp_assoc, hj]
      exact congrArg WithConv.ofConv hφc
    refine AlgHom.ext fun x => ?_
    obtain ⟨a, rfl⟩ := hπ₀ x
    exact AlgHom.congr_fun hcomp a
  -- the inverse
  set θ : A₀ ⊗[k] E →ₐ[k] A := Algebra.TensorProduct.lift j s (fun x y => Commute.all _ _)
    with hθdef
  have hθφ : θ.comp φ = AlgHom.id k A := by
    have key : θ.comp φ = (c * toConv (s.comp (π : A →ₐ[k] E))).ofConv := by
      rw [AlgHom.convMul_def, ofConv_toConv, hφdef, ← AlgHom.comp_assoc, ← AlgHom.comp_assoc]
      refine congrArg (fun f : A ⊗[k] A →ₐ[k] A => f.comp (Bialgebra.comulAlgHom k A)) ?_
      rw [← hj]
      refine Algebra.TensorProduct.ext' fun a b => ?_
      simp [hθdef]
    rw [key, hcdef, inv_mul_cancel_right, ofConv_toConv]
  have hφθ : φ.comp θ = AlgHom.id k (A₀ ⊗[k] E) := by
    refine Algebra.TensorProduct.ext' fun x y => ?_
    have hjx : φ (j x) = Algebra.TensorProduct.includeLeft x := AlgHom.congr_fun hφj x
    have hsy : φ (s y) = Algebra.TensorProduct.includeRight y := AlgHom.congr_fun hφs y
    simp only [AlgHom.comp_apply, hθdef, Algebra.TensorProduct.lift_tmul, map_mul, hjx, hsy,
      AlgHom.coe_id, id_eq]
    simp [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul]
  exact ⟨AlgEquiv.ofAlgHom φ θ hφθ hθφ⟩

end Main

end Fermat.ConnectedEtaleSplitting
