/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Fermat.FLT.Mathlib.RingTheory.HopfAlgebra.CartierDual
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Artinian.Algebra
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Short exact sequences of finite flat commutative group schemes, and exactness of Cartier duality

This file supplies the piece `(R3)` of
`Fermat/FLT/GaloisRepresentation/HardlyRamified/Family.lean`'s citation
`exists_unramified_grouplike_family_generating_corner` actually consumes: *an iterated extension
of `μ`-types is of multiplicative type*. The Cartier-duality construction itself lives in
`Fermat/FLT/Mathlib/RingTheory/HopfAlgebra/CartierDual.lean` and is complete and sorry-free; what
was missing, and is supplied here, is

1. a **definition of a short exact sequence** of finite flat commutative group schemes
   (`HopfAlgebra.IsShortExact`), which this tree did not have;
2. the **functoriality** of Cartier duality (`CartierDual.map`);
3. the statement that Cartier duality is **exact** (`HopfAlgebra.IsShortExact.cartierDual`);
4. the definition of **multiplicative type** as "the Cartier dual is étale"
   (`HopfAlgebra.IsMultiplicativeType`), and `(R3)` itself
   (`HopfAlgebra.isMultiplicativeType_of_isShortExact`) *proven* from 3 together with the étale
   side `HopfAlgebra.etale_of_isShortExact` (now proven).

## The definition, and why it is what it is

`CartierDual.lean`'s "What remains" section recorded that a definition of a short exact sequence
was blocked at the *design* level rather than the proof level — the fppf sheaf quotient `G / G'`
is not constructible in this pin, which carries the fppf/fpqc sites but no descent statement —
and that the Hopf-side formulation
`A'' ↪ A ↠ A'`, `A` faithfully flat over `A''`, `ker(A → A') = A · ker(ε_{A''})`
"should be written by whoever also writes `(R3)`, so that the definition is pinned by its
consumer rather than guessed at in advance".

**It is pinned by its consumer here, and the pinning is real rather than nominal**: the
definition below is exactly what makes `isMultiplicativeType_of_isShortExact` a *two-line
assembly* out of `IsShortExact.cartierDual` and `etale_of_isShortExact`, with the `A''`/`A'`
roles exchanged by duality and nothing left over. Concretely, the consumer forced three choices:

* **The sequence is recorded contravariantly**, as the pair of coordinate-ring maps
  `i : A'' →ₐc[R] A` and `π : A →ₐc[R] A'`, standing for `1 → Spec A' → Spec A → Spec A'' → 1`.
  This is what lets the dual sequence be written down at all — `CartierDual.map` is
  contravariant, so `(i, π) ↦ (map π, map i)` lands in the same shape with no reindexing.
* **`Module.FaithfullyFlat` is taken through `RingHom.FaithfullyFlat`** rather than through an
  `[Algebra A'' A]` instance plus an `IsScalarTower`. A bialgebra map is not an algebra
  *instance*, and demanding one would force every user to install a scalar tower before it could
  even state the hypothesis; `RingHom.FaithfullyFlat (i : A'' →+* A)` unfolds to exactly the same
  proposition through `i.toAlgebra` and needs nothing installed.
* **Exactness at the middle is `Ideal.map`, not `Ideal.span (i '' _)`.** They are equal
  (`Ideal.map` *is* that span), but `Ideal.map` is the form the surjectivity/quotient API in
  mathlib is stated against, and the dual statement has to be manipulated through
  `RingHom.ker`/`Ideal.map` lemmas.

Both `i` and `π` are `BialgHom`s: over a Hopf algebra a bialgebra map automatically commutes with
the antipode, so this is the same thing as a homomorphism of group schemes.

## Faithfulness notes

* `i` is **not** separately required to be injective: a faithfully flat ring map is injective, so
  `A'' ↪ A` is a consequence rather than a hypothesis.
* `IsShortExact` deliberately carries **no** finiteness or flatness hypothesis over `R`. It is the
  correct definition for affine group schemes in general; the finite flat hypotheses are imposed
  where they are used, namely wherever a Cartier dual is formed (which needs `Module.Finite R` and
  `Module.Free R` — see the "Why finite free" design note in `CartierDual.lean`).
* `etale_of_isShortExact` is stated over an **arbitrary** base `R`, and is now PROVEN there — but
  by neither of the two routes this docstring used to record. No torsor, no fppf descent, and no
  henselian local hypothesis: étaleness of a finite free group scheme is equivalent to idempotence
  of its augmentation ideal, and *that* property is extension-closed by pure ideal theory. See
  `IsShortExact.augmentationIdeal_sq_eq` and `derivation_eq_zero`. The faithful-flatness field of
  `IsShortExact` turns out not to be needed for this half at all.

## Main definitions

* `Bialgebra.augmentationIdeal R A` — the kernel of the counit, cutting out the identity section.
* `CartierDual.map f` — functoriality of Cartier duality: a bialgebra map `f : A →ₐc[R] B`
  transposes to `CartierDual R B →ₐc[R] CartierDual R A`.
* `HopfAlgebra.IsShortExact i π` — a short exact sequence of group schemes, on coordinate rings.
* `HopfAlgebra.IsMultiplicativeType R A` — the Cartier dual of `Spec A` is étale.
* `HopfAlgebra.invariantAux d` — the invariant derivative `a ↦ ∑ S(a₍₁₎) · d a₍₂₎` of a derivation.

## Main statements

* `Bialgebra.augmentationIdeal_sq_eq_of_formallyUnramified` and
  `HopfAlgebra.formallyUnramified_of_augmentationIdeal_sq_eq` — a group scheme is unramified iff
  its augmentation ideal is idempotent. **PROVEN**, over an arbitrary base.
* `HopfAlgebra.IsShortExact.augmentationIdeal_sq_eq` — idempotence of the augmentation ideal is
  extension-closed. **PROVEN**.
* `HopfAlgebra.etale_of_isShortExact` — étale-by-étale is étale. **PROVEN**, unconditionally.
* `HopfAlgebra.IsShortExact.cartierDual` — **Cartier duality is exact**. **PROVEN** as an
  assembly of the statements below; as of 2026-07-28 the only one of them still open is the
  *generation* half of the dual normal basis, `exists_spanning_cartierDual`. Its sibling, the
  rank count, was closed the same day over two new leaves — one Hopf-theoretic
  (`IsShortExact.nonempty_linearEquiv_baseChange`, still open) and one not
  (`Module.finrank_eq_finrank_mul_of_rankAtStalk_eq`, **PROVEN 2026-07-30**).
* `HopfAlgebra.IsShortExact.apply_comp` — `π ∘ i` is `ε` followed by the unit. **PROVEN.**
* `AlgHom.flat_quotient_range_of_faithfullyFlat` — the cokernel of a faithfully flat algebra map
  is a flat `R`-module. **PROVEN** (2026-07-28) by the diagram chase in the `FaithfullyFlatSplit`
  section. This is the general-module-theory content that this file used to assume as a sorried
  root-namespace leaf `Module.Flat.quotient_range_of_rTensor_injective` ("a flat module modulo a
  pure submodule is flat"). **That leaf no longer exists**: it was introduced on one branch while
  a second branch proved the same conclusion outright, and the merge kept the proven route. Do not
  re-create it — nothing in this file needs it, and a general restatement with no consumer would
  be free-floating.
* `HopfAlgebra.IsShortExact.rTensor_injective` — `i` is a **pure** map of `R`-modules.
  **PROVEN** (2026-07-28) from the `faithfullyFlat` field alone.
  Note there is no longer a separate `HopfAlgebra.IsShortExact.flat_quotient` wrapper either: the
  branch that introduced it also introduced the leaf, and both went when the merge kept the proven
  route. `AlgHom.flat_quotient_range_of_faithfullyFlat` applied to `i.toAlgHom` is that statement.
  It is **not** gated on Takeuchi's theorem, contrary to what this file used to record.
* `HopfAlgebra.IsShortExact.exists_linearRetraction` — `i(A'')` is an `R`-module direct summand
  of `A`. **PROVEN** (2026-07-27) from faithful flatness alone, via purity of a faithfully flat
  algebra map; the fppf-descent route the docstring used to record is not needed. See the
  `FaithfullyFlatSplit` section.
* `HopfAlgebra.IsShortExact.surjective_cartierDual_map` — **PROVEN** from the retraction.
* `HopfAlgebra.IsShortExact.le_ker_cartierDual` — the easy half of the dual kernel condition.
  **PROVEN**, from `apply_comp` alone.
* `HopfAlgebra.IsShortExact.ker_cartierDual_le` — the hard half. **PROVEN** (2026-07-28) from
  `exists_basis_cartierDual`. (Its "gated on fppf descent" note is **withdrawn**: the sibling
  field carrying the identical note turned out to need no descent at all.)
* `HopfAlgebra.IsShortExact.faithfullyFlat_cartierDual` — classically `Ext¹(G'', 𝔾ₘ) = 0`.
  **PROVEN** (2026-07-28) from `exists_basis_cartierDual` plus the pin's
  `[Nontrivial M] [Module.Free R M] → Module.FaithfullyFlat R M`.
* `HopfAlgebra.IsShortExact.exists_basis_cartierDual` — the dual normal basis. **PROVEN**
  (2026-07-28) by Orzech's property from two strictly weaker statements,
  `IsShortExact.exists_spanning_cartierDual` (generation by `rk_R A''` elements) and
  `IsShortExact.nonempty_linearEquiv_cartierDual` (the rank count `rk_R A = rk_R A'' · rk_R A'`).
  Of those, only the generation half is still open.
* `HopfAlgebra.IsShortExact.nonempty_linearEquiv_cartierDual` and its unpackaged form
  `HopfAlgebra.IsShortExact.finrank_eq_mul` — the rank count. **PROVEN** (2026-07-28) from the
  two leaves below, which share nothing with each other.
* `HopfAlgebra.IsShortExact.nonempty_linearEquiv_baseChange` — the torsor identity
  `A ⊗_{A''} A ≅ A ⊗_R A'`. OPEN. Pure Hopf algebra; needs no flatness over `A''` and no descent.
* `Module.finrank_eq_finrank_mul_of_rankAtStalk_eq` — the degree of a tower. **PROVEN**
  (2026-07-30), and stated at the root namespace because it mentions no Hopf algebra and belongs
  in mathlib, which has `rankAtStalk` and `finrank_mul_finrank` but no multiplicativity of the
  degree along a composite of finite *locally* free maps. It is an **upstream candidate**: nothing
  in its statement or proof mentions this project.
* `HopfAlgebra.etale_of_isShortExact` — étale-by-étale is étale. **PROVEN** (2026-07-27),
  with no non-Hopf leaf left under it.
* `HopfAlgebra.isMultiplicativeType_of_isShortExact` — `(R3)`: an extension of multiplicative type
  by multiplicative type is of multiplicative type. **PROVEN** from the two above.

This file assumes **no** non-Hopf leaf. Two branches closed flatness of `A ⧸ i(A'')` concurrently
and by different routes: one over a new sorried general statement
`Module.Flat.quotient_range_of_rTensor_injective` wrapped as `IsShortExact.flat_quotient`, the
other — kept here — over the PROVEN `AlgHom.flat_quotient_range_of_faithfullyFlat` in the
`FaithfullyFlatSplit` section below, which needs no leaf at all. The merge kept the second, so
**neither the leaf nor the `flat_quotient` wrapper exists any more**; a task prompt naming either
of them by line number is describing the losing branch. It used to carry a different sorried shim
`Algebra.FormallyEtale.of_formallyUnramified_of_flat_of_finitePresentation` (flat + unramified +
finitely presented is étale, Stacks 00UU); that statement **is in the pin**, as
`Algebra.Etale.of_formallyUnramified_of_flat` in `Mathlib/RingTheory/Smooth/Fiber.lean`, so the
shim was deleted on 2026-07-27 and the mathlib lemma is used directly. See the note above
`namespace CartierDual` for why the earlier "absent from the pin" survey missed it.

## References

* Tate, *Finite flat group schemes*, in Cornell–Silverman–Stevens, §2 (exactness of duality).
* Waterhouse, *Introduction to Affine Group Schemes*, ch. 14–16 (faithful flatness and quotients).
* Demazure–Gabriel, *Groupes algébriques*, II §1, III §3.
* Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras* (the faithfully flat
  formulation used here).
-/

@[expose] public section

open TensorProduct Coalgebra

universe u v w x

namespace Bialgebra

section AugmentationIdeal

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]

/-- The **augmentation ideal** of a bialgebra `A`: the kernel of the counit `ε : A →ₐ[R] R`.

Geometrically this is the ideal cutting out the identity section of the group scheme `Spec A`,
and `A · i(augmentationIdeal R A'')` is the ideal cutting out the kernel of a homomorphism
`Spec A → Spec A''`. -/
def augmentationIdeal : Ideal A := RingHom.ker (counitAlgHom R A : A →+* R)

variable {R A}

lemma mem_augmentationIdeal_iff {a : A} :
    a ∈ augmentationIdeal R A ↔ Coalgebra.counit (R := R) a = 0 :=
  RingHom.mem_ker

/-- The counit splits `A` as `R · 1 ⊕ I`: every `a` differs from `ε(a) · 1` by an element of the
augmentation ideal. This is the identity section of `Spec A`, written on rings. -/
lemma sub_algebraMap_counit_mem_augmentationIdeal (a : A) :
    a - algebraMap R A (Coalgebra.counit (R := R) a) ∈ augmentationIdeal R A := by
  rw [mem_augmentationIdeal_iff, map_sub]
  simp

/-- **A formally unramified bialgebra has idempotent augmentation ideal**: `I = I²`.

Geometrically, `I/I²` is the cotangent space at the identity, which is a quotient of `Ω[A⁄R]`
because the identity section `Spec R → Spec A` is a retraction of `Spec A → Spec R`; so `Ω = 0`
forces it to vanish. The proof below avoids the Kähler machinery: the two `R`-algebra maps
`A → A ⧸ I²` given by the quotient map and by `a ↦ ε(a) · 1` agree modulo the square-zero ideal
`I/I²`, so formal unramifiedness identifies them, and evaluating at `a ∈ I` gives `a ∈ I²`. -/
theorem augmentationIdeal_sq_eq_of_formallyUnramified [Algebra.FormallyUnramified R A] :
    augmentationIdeal R A ^ 2 = augmentationIdeal R A := by
  refine le_antisymm (Ideal.pow_le_self two_ne_zero) fun a ha => ?_
  have hJ2 : (Ideal.map (Ideal.Quotient.mk (augmentationIdeal R A ^ 2))
      (augmentationIdeal R A)) ^ 2 = ⊥ := by
    rw [← Ideal.map_pow, Ideal.map_quotient_self]
  have heq : (Ideal.Quotient.mkₐ R (Ideal.map (Ideal.Quotient.mk
        (augmentationIdeal R A ^ 2)) (augmentationIdeal R A))).comp
        (Ideal.Quotient.mkₐ R (augmentationIdeal R A ^ 2)) =
      (Ideal.Quotient.mkₐ R (Ideal.map (Ideal.Quotient.mk
        (augmentationIdeal R A ^ 2)) (augmentationIdeal R A))).comp
        ((Ideal.Quotient.mkₐ R (augmentationIdeal R A ^ 2)).comp
          ((Algebra.ofId R A).comp (counitAlgHom R A))) := by
    ext b
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Algebra.ofId_apply,
      counitAlgHom_apply]
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← map_sub]
    exact Ideal.mem_map_of_mem _ (sub_algebraMap_counit_mem_augmentationIdeal b)
  have := Algebra.FormallyUnramified.comp_injective (R := R) (A := A) _ hJ2 heq
  have h2 := AlgHom.congr_fun this a
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Algebra.ofId_apply,
    counitAlgHom_apply] at h2
  rw [mem_augmentationIdeal_iff] at ha
  rw [ha, map_zero] at h2
  rw [← Ideal.Quotient.eq_zero_iff_mem, h2, map_zero]

end AugmentationIdeal

end Bialgebra

/-! ### The commutative-algebra input: flat + unramified + finitely presented is étale

This is not about Hopf algebras at all; it is the standard equivalence between the "formally
étale + finitely presented" definition of étaleness used by mathlib and the "flat + unramified"
definition used by the Stacks project. It used to be the one thing this file assumed, as a sorried
shim `Algebra.FormallyEtale.of_formallyUnramified_of_flat_of_finitePresentation`.

**It is in the pin after all, and the shim has been deleted** (2026-07-27). The statement is
`Algebra.Etale.of_formallyUnramified_of_flat` in `Mathlib/RingTheory/Smooth/Fiber.lean`, tagged
`@[stacks 08WD "(3) => (1)"]`, with exactly the hypotheses
`[Algebra.FinitePresentation R S] [Module.Flat R S] [FormallyUnramified R S]`; mathlib proves it
through the fibrewise criterion (`Algebra.Smooth.of_formallySmooth_fiber` and
`Algebra.FormallySmooth.of_formallySmooth_residueField_tensor`), not through the local structure
theorem for unramified algebras. The stale survey that this file used to carry — "mathlib has no
lemma deriving `FormallySmooth`/`FormallyEtale`/`Etale` from a flatness hypothesis" — was reading
only `Mathlib/RingTheory/Etale/` and `Mathlib/RingTheory/Smooth/Flat.lean`; the relevant file is
`Mathlib/RingTheory/Smooth/Fiber.lean`, whose module docstring advertises the result by name.
`Mathlib/RingTheory/Etale/Weakly.lean`'s TODO is a *different*, genuinely open statement (weakly
étale of finite presentation is étale, Olivier's theorem).

So there is nothing to restate here: `Algebra.Etale.of_formallyUnramified_of_flat` is used
directly at the one place this file needed it, `HopfAlgebra.etale_of_augmentationIdeal_sq_eq`. -/

namespace CartierDual

/-! ### Functoriality

Cartier duality is a contravariant functor. On coordinate rings it is the transpose: a bialgebra
map `f : A →ₐc[R] B` sends a functional `φ` on `B` to `φ ∘ f` on `A`. That this is again a
bialgebra map is four calculations, each of which trades a property of `f` for the dual property
of the transpose:

| identity for `map f`      | comes from        |
| ------------------------- | ----------------- |
| preserves `1` (`= ε`)     | `f` preserves `ε` |
| preserves `*` (convolution) | `f` preserves `Δ` |
| preserves `ε` (`= eval at 1`) | `f` preserves `1` |
| preserves `Δ`             | `f` preserves `*` |

-/

section Map

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B]
variable [HopfAlgebra R A] [HopfAlgebra R B]

/-- The linear map underlying `CartierDual.map`: precomposition with `f`. -/
noncomputable def mapLinear (f : A →ₐc[R] B) : CartierDual R B →ₗ[R] CartierDual R A :=
  (toDual R A).symm.toLinearMap ∘ₗ (f.toCoalgHom.toLinearMap).dualMap ∘ₗ (toDual R B).toLinearMap

@[simp] lemma mapLinear_apply (f : A →ₐc[R] B) (φ : CartierDual R B) (a : A) :
    mapLinear f φ a = φ (f a) := rfl

/-- A representation of `comul a` pushes forward along a coalgebra map to one of `comul (f a)`.
This is what turns "`f` preserves `Δ`" into "the transpose preserves convolution". -/
noncomputable def reprMap {ι : Type*} {a : A} (f : A →ₐc[R] B) (𝓡 : Coalgebra.Repr R a ι) :
    Coalgebra.Repr R (f a) ι where
  index := 𝓡.index
  left i := f (𝓡.left i)
  right i := f (𝓡.right i)
  eq := by
    rw [← CoalgHomClass.map_comp_comul_apply f a, ← 𝓡.eq, map_sum]
    simp

@[simp] lemma reprMap_index {ι : Type*} {a : A} (f : A →ₐc[R] B) (𝓡 : Coalgebra.Repr R a ι) :
    (reprMap f 𝓡).index = 𝓡.index := rfl

@[simp] lemma reprMap_left {ι : Type*} {a : A} (f : A →ₐc[R] B) (𝓡 : Coalgebra.Repr R a ι)
    (i : ι) : (reprMap f 𝓡).left i = f (𝓡.left i) := rfl

@[simp] lemma reprMap_right {ι : Type*} {a : A} (f : A →ₐc[R] B) (𝓡 : Coalgebra.Repr R a ι)
    (i : ι) : (reprMap f 𝓡).right i = f (𝓡.right i) := rfl

/-- The pairing sees `mapLinear` as a change of the points it is evaluated at. This is the
tensor-square form of `mapLinear_apply`, and it is what lets `mapLinear_comul` be proven by
`pairMap_injective`. -/
lemma pairMap_map (f : A →ₐc[R] B) (a b : A) (x : CartierDual R B ⊗[R] CartierDual R B) :
    pairMap a b (TensorProduct.map (mapLinear f) (mapLinear f) x) = pairMap (f a) (f b) x := by
  induction x with
  | zero => simp
  | tmul φ ψ => simp
  | add x y hx hy => simp [hx, hy]

section FiniteFree

variable [Module.Finite R A] [Module.Free R A] [Module.Finite R B] [Module.Free R B]

/-- The transpose preserves the counit, because the counit of a Cartier dual is evaluation at `1`
and `f` preserves `1`. -/
lemma mapLinear_counit (f : A →ₐc[R] B) (φ : CartierDual R B) :
    counit (R := R) (mapLinear f φ) = counit (R := R) φ := by
  rw [counit_apply, counit_apply, mapLinear_apply, map_one]

/-- The transpose preserves comultiplication, because `f` preserves multiplication:
`⟨Δ (map f φ), a ⊗ b⟩ = φ (f (a * b)) = φ (f a * f b) = ⟨Δ φ, f a ⊗ f b⟩`. -/
lemma mapLinear_comul (f : A →ₐc[R] B) (φ : CartierDual R B) :
    comul (R := R) (mapLinear f φ) =
      TensorProduct.map (mapLinear f) (mapLinear f) (comul (R := R) φ) := by
  refine pairMap_injective fun a b => ?_
  rw [pairMap_comul, pairMap_map, pairMap_comul, mapLinear_apply, map_mul]

end FiniteFree

section Cocomm

variable [IsCocomm R A] [IsCocomm R B]

/-- The transpose preserves the unit, because the unit of a Cartier dual is the counit and `f`
preserves the counit. -/
lemma mapLinear_one (f : A →ₐc[R] B) : mapLinear f 1 = 1 := by
  ext a
  rw [mapLinear_apply, one_apply, one_apply, CoalgHomClass.counit_comp_apply]

/-- The transpose preserves the convolution product, because `f` preserves comultiplication:
both sides evaluate at `a` to `∑ᵢ φ (f a₍₁₎ᵢ) * ψ (f a₍₂₎ᵢ)`. -/
lemma mapLinear_mul (f : A →ₐc[R] B) (φ ψ : CartierDual R B) :
    mapLinear f (φ * ψ) = mapLinear f φ * mapLinear f ψ := by
  ext a
  rw [mapLinear_apply, mul_apply_repr (reprMap f (Coalgebra.Repr.arbitrary R a)),
    mul_apply_repr (Coalgebra.Repr.arbitrary R a)]
  simp

variable [Module.Finite R A] [Module.Free R A] [Module.Finite R B] [Module.Free R B]

/-- **Functoriality of Cartier duality.** A bialgebra map `f : A →ₐc[R] B` — i.e. a homomorphism
of group schemes `Spec B → Spec A` — transposes to a bialgebra map
`CartierDual R B →ₐc[R] CartierDual R A`, i.e. a homomorphism of the Cartier duals in the
opposite direction. -/
noncomputable def map (f : A →ₐc[R] B) : CartierDual R B →ₐc[R] CartierDual R A where
  toFun := mapLinear f
  map_add' := (mapLinear f).map_add
  map_smul' := (mapLinear f).map_smul'
  map_one' := mapLinear_one f
  map_mul' := mapLinear_mul f
  counit_comp := LinearMap.ext fun φ => mapLinear_counit f φ
  map_comp_comul := LinearMap.ext fun φ => (mapLinear_comul f φ).symm

@[simp] lemma map_apply (f : A →ₐc[R] B) (φ : CartierDual R B) (a : A) :
    map f φ a = φ (f a) := rfl

@[simp] lemma coe_map (f : A →ₐc[R] B) : ⇑(map f) = ⇑(mapLinear f) := rfl

end Cocomm

end Map

end CartierDual

/-! ### Faithfully flat algebra maps are split as maps of modules

This section is pure commutative algebra — no Hopf structure, no group schemes. It supplies the
module-theoretic input to `HopfAlgebra.IsShortExact.exists_linearRetraction`, and it says
something strictly more general than the normal-basis argument the docstring there used to
appeal to: **the faithful flatness hypothesis alone splits `i`, with no descent, no torsor and
no local triviality.**

The chain is three steps, each of which is a standard fact whose mathlib form was the only thing
missing:

1. `AlgHom.rTensor_injective_of_faithfullyFlat` — a faithfully flat algebra map `f : B → A` is a
   **pure** monomorphism of `R`-modules: `B ⊗[R] Z → A ⊗[R] Z` is injective for *every* `R`-module
   `Z`. This is `Module.FaithfullyFlat.tensorProduct_mk_injective` applied to the `B`-module
   `B ⊗[R] Z`, transported along `cancelBaseChange : A ⊗[B] (B ⊗[R] Z) ≃ A ⊗[R] Z`; the point is
   that an *induced* `B`-module already computes the `R`-linear base change.
2. `AlgHom.flat_quotient_range_of_faithfullyFlat` — hence the cokernel `A ⧸ f(B)` is `R`-flat.
   With `A` and `B` flat, the long exact sequence collapses to exactly the purity of step 1; the
   proof below is that collapse written as a diagram chase, since the pin has no `Tor`-free
   statement of it.
3. `AlgHom.exists_linearRetraction_of_faithfullyFlat` — the cokernel is finitely presented
   (both sides are finite free), so flat makes it projective
   (`Module.Flat.projective_of_finitePresentation`), so the sequence splits.

The reason this is worth isolating: it removes "fppf descent" from the dependency list of the
surjectivity half of exactness of Cartier duality. -/

section FaithfullyFlatSplit

variable {R : Type u} {B : Type v} {A : Type w}
variable [CommRing R] [CommRing B] [CommRing A] [Algebra R B] [Algebra R A]

/-- **A faithfully flat algebra map is a pure monomorphism of `R`-modules**: tensoring it with an
arbitrary `R`-module `Z` keeps it injective.

Proof: `B ⊗[R] Z` is a `B`-module, and faithful flatness of `A` over `B` makes
`M →ₗ[B] A ⊗[B] M` injective for every `B`-module `M`
(`Module.FaithfullyFlat.tensorProduct_mk_injective`). For the induced module `M = B ⊗[R] Z` the
target is `A ⊗[B] (B ⊗[R] Z) ≅ A ⊗[R] Z` and the map becomes `f ⊗ id`. -/
theorem AlgHom.rTensor_injective_of_faithfullyFlat (f : B →ₐ[R] A)
    (hf : RingHom.FaithfullyFlat (f : B →+* A)) (Z : Type*) [AddCommGroup Z] [Module R Z] :
    Function.Injective ((f.toLinearMap).rTensor Z) := by
  algebraize [(f : B →+* A)]
  haveI : IsScalarTower R B A :=
    IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  set e := TensorProduct.AlgebraTensorModule.cancelBaseChange R B A A Z with he
  have key : ∀ x : B ⊗[R] Z,
      (f.toLinearMap).rTensor Z x = e (TensorProduct.mk B A (B ⊗[R] Z) 1 x) := by
    intro x
    induction x with
    | zero => simp
    | tmul b z =>
        simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, TensorProduct.mk_apply, he,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
        rw [Algebra.smul_def, mul_one]
        rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  have hmk : Function.Injective (TensorProduct.mk B A (B ⊗[R] Z) 1) :=
    Module.FaithfullyFlat.tensorProduct_mk_injective (B ⊗[R] Z)
  intro x y hxy
  exact hmk (e.injective (by rw [← key, ← key]; exact hxy))

/-- **The cokernel of a faithfully flat algebra map is a flat `R`-module.**

Given `g : X ↪ Y` and `x ∈ X ⊗ (A ⧸ f(B))` killed by `g ⊗ id`, lift `x` to `y ∈ X ⊗ A`. Then
`(g ⊗ id) y` dies in `Y ⊗ (A ⧸ f(B))`, so by right exactness it is `(id ⊗ f) u` for some
`u ∈ Y ⊗ B`. Purity (step 1 above), applied to `Z = Y ⧸ g(X)`, forces `u` into the image of
`X ⊗ B`; flatness of `A` then forces `y` into the image of `X ⊗ B`, and `x = 0`.

Flatness of `A` and of `B` is all that is used besides purity — in the application both are
finite free. -/
theorem AlgHom.flat_quotient_range_of_faithfullyFlat (f : B →ₐ[R] A)
    (hf : RingHom.FaithfullyFlat (f : B →+* A)) [Module.Flat R A] [Module.Flat R B] :
    Module.Flat R (A ⧸ LinearMap.range f.toLinearMap) := by
  set K : Submodule R A := LinearMap.range f.toLinearMap with hK
  have hex : Function.Exact f.toLinearMap K.mkQ :=
    LinearMap.exact_iff.mpr (Submodule.ker_mkQ K)
  refine Module.Flat.iff_rTensor_preserves_injective_linearMap'.mpr ?_
  show ∀ ⦃X Y : Type u⦄ [AddCommGroup X] [AddCommGroup Y] [Module R X] [Module R Y]
      (g : X →ₗ[R] Y), Function.Injective g → Function.Injective (g.rTensor (A ⧸ K))
  intro X Y _ _ _ _ g hg
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective X (Submodule.mkQ_surjective K) x
  have hsq : ∀ z : X ⊗[R] A, LinearMap.rTensor _ g (LinearMap.lTensor X K.mkQ z) =
      LinearMap.lTensor Y K.mkQ (LinearMap.rTensor A g z) := fun z => by
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
      LinearMap.lTensor_comp_rTensor]
  rw [hsq] at hx
  -- `rTensor A g y` is killed by `lTensor Y mkQ`, hence comes from `Y ⊗ B`
  obtain ⟨u, hu⟩ := (_root_.lTensor_exact Y hex (Submodule.mkQ_surjective K) _).mp hx
  -- its image in `C ⊗ B` dies, where `C = Y ⧸ range g`; purity makes that mean `u ∈ X ⊗ B`
  set C := Y ⧸ LinearMap.range g with hC
  set p : Y →ₗ[R] C := (LinearMap.range g).mkQ with hp
  have hpg : p ∘ₗ g = 0 := by
    ext b
    simp only [hp, LinearMap.coe_comp, Function.comp_apply, LinearMap.zero_apply]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self g b)
  have hu0 : LinearMap.rTensor B p u = 0 := by
    refine (f.toLinearMap.lTensor_inj_iff_rTensor_inj C).mpr
      (f.rTensor_injective_of_faithfullyFlat hf C) ?_
    rw [map_zero]
    have h1 : ∀ z : Y ⊗[R] B, LinearMap.lTensor C f.toLinearMap (LinearMap.rTensor B p z) =
        LinearMap.rTensor A p (LinearMap.lTensor Y f.toLinearMap z) := fun z => by
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
        LinearMap.rTensor_comp_lTensor]
    rw [h1, hu, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hpg, LinearMap.rTensor_zero,
      LinearMap.zero_apply]
  obtain ⟨w, hw⟩ := (Module.Flat.rTensor_exact B
    (LinearMap.exact_iff.mpr (Submodule.ker_mkQ (LinearMap.range g))) _).mp hu0
  -- and then `y` comes from `X ⊗ B`, so `x = 0`
  have hy : LinearMap.lTensor X f.toLinearMap w = y := by
    refine Module.Flat.rTensor_preserves_injective_linearMap (M := A) g hg ?_
    have h2 : ∀ z : X ⊗[R] B, LinearMap.rTensor A g (LinearMap.lTensor X f.toLinearMap z) =
        LinearMap.lTensor Y f.toLinearMap (LinearMap.rTensor B g z) := fun z => by
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
        LinearMap.lTensor_comp_rTensor]
    rw [h2, hw, hu]
  rw [← hy, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
  have hzero : K.mkQ ∘ₗ f.toLinearMap = 0 := by
    ext b
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.zero_apply,
      Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self _ b)
  rw [hzero, LinearMap.lTensor_zero, LinearMap.zero_apply]

/-- **A faithfully flat map of finite free `R`-algebras admits an `R`-linear retraction.**

The cokernel is finitely presented because both sides are finite free, and flat by the previous
theorem; a finitely presented flat module is projective, so the quotient map splits and the
splitting exhibits `f(B)` as a direct summand. -/
theorem AlgHom.exists_linearRetraction_of_faithfullyFlat (f : B →ₐ[R] A)
    (hf : RingHom.FaithfullyFlat (f : B →+* A))
    [Module.Finite R A] [Module.Free R A] [Module.Finite R B] [Module.Free R B] :
    ∃ r : A →ₗ[R] B, ∀ b : B, r (f b) = b := by
  set K : Submodule R A := LinearMap.range f.toLinearMap with hK
  haveI : Module.Flat R (A ⧸ K) := f.flat_quotient_range_of_faithfullyFlat hf
  haveI : Module.FinitePresentation R A := Module.finitePresentation_of_projective R A
  haveI : Module.FinitePresentation R (A ⧸ K) :=
    Module.finitePresentation_of_surjective K.mkQ (Submodule.mkQ_surjective K)
      (by rw [Submodule.ker_mkQ]; exact Module.Finite.iff_fg.mp inferInstance)
  haveI : Module.Projective R (A ⧸ K) := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property K.mkQ (LinearMap.id (R := R) (M := A ⧸ K))
    (Submodule.mkQ_surjective K)
  have hinj : Function.Injective f.toLinearMap := hf.injective
  set t : A →ₗ[R] A := LinearMap.id - s ∘ₗ K.mkQ with ht
  have htK : ∀ a : A, t a ∈ K := by
    intro a
    rw [← Submodule.ker_mkQ K, LinearMap.mem_ker, ht]
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub]
    rw [← LinearMap.comp_apply, hs]
    simp
  set eB : B ≃ₗ[R] K := LinearEquiv.ofInjective f.toLinearMap hinj with heB
  refine ⟨eB.symm ∘ₗ t.codRestrict K htK, fun b => ?_⟩
  have hb : t (f b) = f b := by
    have hker : K.mkQ (f b) = 0 := by
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ, hK]; exact LinearMap.mem_range_self _ b
    simp [ht, hker]
  have hcod : (t.codRestrict K htK) (f b) = eB b := by
    apply Subtype.ext
    show t (f b) = f.toLinearMap b
    exact hb
  simp [hcod]

end FaithfullyFlatSplit

/-! ### The degree of a tower

The one piece of pure commutative algebra that the rank count below needs, stated at the root
namespace because it belongs in mathlib. -/

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **The degree of a tower**: if `S` is a finite free `R`-algebra and `M` is a finite flat
`S`-module whose rank is the constant `n` at every stalk of `S`, then `M` has `R`-rank
`rk_R S · n`.

**PROVEN 2026-07-30.** Cut on 2026-07-28 out of
`HopfAlgebra.IsShortExact.nonempty_linearEquiv_cartierDual`, alongside
`HopfAlgebra.IsShortExact.nonempty_linearEquiv_baseChange`; the two are independent —
this one mentions no Hopf algebra at all. It remains an **upstream candidate**: it is stated in
full generality, its proof uses nothing from this project, and the composition lemma it supplies
is exactly what `Mathlib/AlgebraicGeometry/Morphisms/FlatRank.lean` is missing.

## PROOF (2026-07-30): the fibre over one prime, then SEMILOCAL freeness

The route recorded below — reduce to a field base, then decompose the Artinian fibre algebra into
local factors — was right about the reduction and **wrong about the second step being a gap**.
The Artinian decomposition never has to be performed, because the pin already carries the
consequence one wants from it:

`Module.free_of_flat_of_finrank_eq` (`Mathlib/RingTheory/LocalRing/Module.lean`, stacks `02M9`)
says a finite flat module over a **semilocal** ring — `[Finite (MaximalSpectrum B)]` — whose
fibre dimension is the constant `n` at every maximal ideal is FREE of rank `n`. An Artinian ring
is semilocal (`IsArtinianRing.primeSpectrumEquivMaximalSpectrum` plus `Finite (PrimeSpectrum B)`),
so over the fibre the tower formula is just `Module.finrank_mul_finrank` for free modules.

So the proof is four steps, and no step needs the non-reduced `IsArtinianRing.equivPi` that this
docstring used to name as "the concrete gap to fill":

1. Pick any prime `p` of `R` — `[Nontrivial R]` is what supplies one — and let `κ = κ(p)`. Both
   sides of the conclusion are computed there, because `M` and `S` are `R`-FREE:
   `Module.finrank_baseChange` gives `finrank κ (κ ⊗[R] S) = finrank R S`, and the same for `M`
   after `Algebra.IsPushout.cancelBaseChange R κ S B M : B ⊗[S] M ≃ₗ[κ] κ ⊗[R] M`, where
   `B := κ ⊗[R] S`. (That is the *left*-handed cancellation, which is what a tower needs;
   `AlgebraTensorModule.cancelBaseChange` cancels on the right and does not apply here.)
2. `B` is a finite-dimensional `κ`-algebra, hence `IsArtinianRing` (`isArtinian_of_tower`),
   hence semilocal.
3. `N := B ⊗[S] M` has fibre dimension `n` at every maximal ideal `P` of `B`: cancel the base
   change the other way, `(B ⧸ P) ⊗[B] (B ⊗[S] M) ≃ₗ[B ⧸ P] (B ⧸ P) ⊗[S] M`
   (`AlgebraTensorModule.cancelBaseChange`), then read that dimension as a rank at a stalk of the
   FIELD `B ⧸ P` (`rankAtStalk_eq_finrank_of_free`) and pull it back along `S → B ⧸ P` with
   `Module.rankAtStalk_baseChange`. What comes out is `hn` at one prime of `S`.
4. `Module.free_of_flat_of_finrank_eq` makes `N` free of rank `n` over `B`, and
   `Module.finrank_mul_finrank κ B N` finishes. The `Subsingleton B` corner (which happens exactly
   when `finrank R S = 0`) is discharged first, since `StrongRankCondition B` is unavailable there.

## Why it is not in the pin (checked, not assumed)

This pin has `Module.rankAtStalk` with a rich API in
`Mathlib/RingTheory/Spectrum/Prime/FreeLocus.lean`: base change (`rankAtStalk_baseChange`),
tensor products (`rankAtStalk_tensorProduct`, `rankAtStalk_tensorProduct_of_isScalarTower`),
constancy under specialisation, and `rankAtStalk_eq` computing it as the dimension of the fibre.
`Mathlib/RingTheory/Flat/LocallyFree.lean` turns constant rank into Zariski-local freeness
(`Module.Free.away_of_finite_of_flat_of_rankAtStalk_constant`), and this project already carries
`Module.finitePresentation_of_rankAtStalk_const`
(`Fermat/FLT/Mathlib/AlgebraicGeometry/FinitePresentationOfFinrank.lean`), whose hypothesis has
exactly the shape used here.

What is missing everywhere is **multiplicativity of the degree along a composite of finite
locally free maps**. `Module.finrank_mul_finrank` is the tower formula for *free* modules, and
freeness over `S` is precisely what fails here. On the scheme side
`Mathlib/AlgebraicGeometry/Morphisms/FlatRank.lean` defines `Scheme.Hom.finrank` for finite flat
morphisms and proves its pullback compatibility (`finrank_pullback_snd`, `finrank_of_isPullback`)
but has **no composition lemma**. Checked by grep over `Mathlib/` for `rankAtStalk` together with
`comp`/`tower`/`trans`/`finrank_mul`, and over `Fermat/` and `~/cs/FLT`.

## The route as first planned (kept because its first half IS what was used)

Fix a prime `q` of `R` with residue field `κ`. Both sides are computed at `q`:
`finrank R M = rankAtStalk M q = dim_κ (κ ⊗[R] M)` and likewise for `S`
(`Module.rankAtStalk_eq_finrank_of_free`, `Module.rankAtStalk_eq`). Base change to `κ` turns the
tower into `κ → B := κ ⊗[R] S → N := κ ⊗[R] M`, with `B` a finite-dimensional `κ`-algebra and `N`
finite flat over `B` of constant rank `n` (`Module.rankAtStalk_baseChange`). So it is enough to
prove the statement over a **field** base, where `B` is Artinian: `B` is a finite product of
local rings, `N` is free of rank `n` over each factor (`Module.free_of_flat_of_isLocalRing`), and
`dim_κ N = ∑ᵢ n · dim_κ Bᵢ = n · dim_κ B`.

The last step was recorded here as needing the decomposition of a **non-reduced** Artinian ring
into local factors, since this pin has `IsArtinianRing.equivPi` only for *reduced* `B`
(`Mathlib/RingTheory/Artinian/Module.lean`). **That diagnosis was correct about the pin and wrong
about the requirement**: the decomposition is not needed at all, because
`Module.free_of_flat_of_finrank_eq` already gives freeness over any semilocal ring, and Artinian
implies semilocal. See the PROOF section above. (The nilradical-filtration workaround also
recorded here — filter `N` by powers of `nil B` and telescope — is therefore unnecessary too;
it is left on record only because it is a correct argument.)

## FALSITY AUDIT

`[Nontrivial R]` is **load-bearing and was added after the statement was refuted without it.**
Over the zero ring `S` is zero too, so `PrimeSpectrum S` is EMPTY and `hn` holds vacuously for
*every* `n`; meanwhile `rank_subsingleton` makes `finrank R M = finrank R S = 1`, so the
conclusion reads `1 = n`. Witness: `R = S = M = 0`, `n = 5`, giving `1 = 5`. Freeness offers no
protection — over the zero ring every module is free. The consumer discharges the subsingleton
base separately, so the hypothesis costs it nothing.

With `[Nontrivial R]` the remaining corner is harmless: if `S` is the zero ring then `M` is zero,
`finrank R S = 0` and the conclusion reads `0 = 0 · n`.

The constancy hypothesis `hn` is load-bearing too, and cannot be weakened to constancy on the
image of `Spec R`. Refuting check: `R = κ` a field, `S = κ × κ`, `M = κ × 0` (a direct summand
of `S`, hence flat). Then `rankAtStalk M` is `1` at one prime and `0` at the other,
`finrank R M = 1` and `finrank R S = 2`, and no `n` satisfies `1 = 2 · n`. -/
theorem Module.finrank_eq_finrank_mul_of_rankAtStalk_eq
    {R : Type*} {S : Type*} {M : Type*} [CommRing R] [Nontrivial R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Module.Free R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite S M] [Module.Flat S M] [Module.Free R M] [Module.Finite R M]
    {n : ℕ} (hn : ∀ p : PrimeSpectrum S, Module.rankAtStalk (R := S) M p = n) :
    Module.finrank R M = Module.finrank R S * n := by
  classical
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum R) := inferInstance
  set κ := p.asIdeal.ResidueField with hκ
  set B := κ ⊗[R] S with hBdef
  set N := B ⊗[S] M with hNdef
  -- Both `R`-ranks are computed in the fibre over `p`, because `S` and `M` are `R`-free.
  have hM : Module.finrank κ N = Module.finrank R M := by
    rw [(Algebra.IsPushout.cancelBaseChange R κ S B M).finrank_eq]
    exact Module.finrank_baseChange
  have hS : Module.finrank κ B = Module.finrank R S := Module.finrank_baseChange
  -- `B` is a finite-dimensional `κ`-algebra, hence artinian, hence semilocal.
  haveI : IsArtinianRing B := isArtinian_of_tower κ inferInstance
  haveI : Finite (MaximalSpectrum B) :=
    Finite.of_equiv _ (IsArtinianRing.primeSpectrumEquivMaximalSpectrum (R := B))
  -- The fibre dimension of `N` is `n` at every maximal ideal of `B`.
  have hrk : ∀ P : MaximalSpectrum B, Module.finrank (B ⧸ P.1) ((B ⧸ P.1) ⊗[B] N) = n := by
    intro P
    haveI : P.1.IsMaximal := P.2
    letI : Field (B ⧸ P.1) := Ideal.Quotient.field P.1
    have e : ((B ⧸ P.1) ⊗[B] N) ≃ₗ[B ⧸ P.1] ((B ⧸ P.1) ⊗[S] M) :=
      TensorProduct.AlgebraTensorModule.cancelBaseChange S B (B ⧸ P.1) (B ⧸ P.1) M
    rw [e.finrank_eq]
    obtain ⟨q⟩ : Nonempty (PrimeSpectrum (B ⧸ P.1)) := inferInstance
    have h1 : Module.rankAtStalk (R := B ⧸ P.1) ((B ⧸ P.1) ⊗[S] M) q
        = Module.finrank (B ⧸ P.1) ((B ⧸ P.1) ⊗[S] M) :=
      congrFun Module.rankAtStalk_eq_finrank_of_free q
    rw [← h1, Module.rankAtStalk_baseChange]
    exact hn _
  rcases subsingleton_or_nontrivial B with _ | _
  · -- `B = 0`, which happens exactly when `finrank R S = 0`; then `N = 0` too.
    haveI : Subsingleton N := Module.subsingleton B N
    have h1 : Module.finrank κ N = 0 := Module.finrank_zero_of_subsingleton
    have h2 : Module.finrank κ B = 0 := Module.finrank_zero_of_subsingleton
    rw [← hM, ← hS, h1, h2, zero_mul]
  · haveI : Module.Free B N := Module.free_of_flat_of_finrank_eq B N n hrk
    obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq B N n hrk
    have hBN : Module.finrank B N = n := by
      rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
    rw [← hM, ← hS, ← Module.finrank_mul_finrank κ B N, hBN]

namespace HopfAlgebra

/-! ### Short exact sequences -/

section Def

variable {R : Type u} {A'' : Type v} {A : Type w} {A' : Type x}
variable [CommRing R] [CommRing A''] [CommRing A] [CommRing A']
variable [HopfAlgebra R A''] [HopfAlgebra R A] [HopfAlgebra R A']

/-- A **short exact sequence of commutative group schemes**
`1 → Spec A' → Spec A → Spec A'' → 1`, written on coordinate rings, where it becomes
`A'' →[i] A →[π] A'`.

The three conditions say, in the same order:

* `Spec A → Spec A''` is **faithfully flat** — this is what makes `Spec A''` the *fppf quotient*
  `Spec A / Spec A'` and not merely a categorical one, and it is why no fppf-descent statement
  (absent from this pin) is needed to state exactness;
* `Spec A' → Spec A` is a **closed immersion**, i.e. `π` is surjective;
* `Spec A'` is the **kernel** of `Spec A → Spec A''`: its coordinate ring is `A` modulo the ideal
  `A · i(ker ε_{A''})` generated by the augmentation ideal of `A''`.

Injectivity of `i` is not listed because it follows: a faithfully flat ring map is injective.

This is the classical Hopf-algebraic definition (Takeuchi; Waterhouse ch. 14–16), and over a
field it is automatic that a sub-Hopf-algebra is faithfully flat — over a general base it is not,
which is exactly why it appears as a hypothesis. -/
structure IsShortExact (i : A'' →ₐc[R] A) (π : A →ₐc[R] A') : Prop where
  /-- `Spec A → Spec A''` is faithfully flat: `A` is faithfully flat over the sub-bialgebra
  `i(A'')`. -/
  faithfullyFlat : RingHom.FaithfullyFlat (i.toAlgHom.toRingHom : A'' →+* A)
  /-- `Spec A' → Spec A` is a closed immersion. -/
  surjective : Function.Surjective π
  /-- `Spec A'` is the kernel of `Spec A → Spec A''`. -/
  ker_eq : RingHom.ker (π.toAlgHom.toRingHom : A →+* A') =
    Ideal.map (i.toAlgHom.toRingHom : A'' →+* A) (Bialgebra.augmentationIdeal R A'')

variable {i : A'' →ₐc[R] A} {π : A →ₐc[R] A'}

/-- In a short exact sequence the map `A'' → A` is injective, because a faithfully flat ring map
is. Geometrically: `Spec A → Spec A''` is (faithfully flat, hence) an epimorphism. -/
lemma IsShortExact.injective (h : IsShortExact i π) : Function.Injective i := by
  have hff := h.faithfullyFlat
  algebraize [(i.toAlgHom.toRingHom : A'' →+* A)]
  exact FaithfulSMul.algebraMap_injective A'' A

/-- A homomorphism of group schemes carries the augmentation ideal into the augmentation ideal,
because a bialgebra map commutes with the counit. -/
lemma map_augmentationIdeal_le (f : A →ₐc[R] A') :
    Ideal.map (f.toAlgHom.toRingHom : A →+* A') (Bialgebra.augmentationIdeal R A) ≤
      Bialgebra.augmentationIdeal R A' := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Bialgebra.mem_augmentationIdeal_iff] at ha
  rw [Ideal.mem_comap, Bialgebra.mem_augmentationIdeal_iff]
  show Coalgebra.counit (R := R) (f a) = 0
  rw [CoalgHomClass.counit_comp_apply, ha]

/-- A closed immersion of group schemes is surjective on augmentation ideals. -/
lemma IsShortExact.map_augmentationIdeal (h : IsShortExact i π) :
    Ideal.map (π.toAlgHom.toRingHom : A →+* A') (Bialgebra.augmentationIdeal R A) =
      Bialgebra.augmentationIdeal R A' := by
  refine le_antisymm (map_augmentationIdeal_le π) fun b hb => ?_
  obtain ⟨a, rfl⟩ := h.surjective b
  refine Ideal.mem_map_of_mem _ ?_
  rw [Bialgebra.mem_augmentationIdeal_iff] at hb ⊢
  rwa [CoalgHomClass.counit_comp_apply] at hb

/-- **Idempotence of the augmentation ideal is an extension-closed property.**

This is the whole of the reduction of "étale by étale is étale" to a statement about a single
group scheme, and it is pure ideal theory — in particular it uses neither the faithful flatness
nor the Cartier duality. Writing `I`, `I'`, `I''` for the three augmentation ideals and
`J = ker π = i(I'')·A` for the ideal cutting out `Spec A'` inside `Spec A`:

* `J = J²`, because `J = Ideal.map i I''` and `I'' = I''²` (ideal maps commute with powers);
* `I = I² + J`, because `π(I) = I' = I'² = π(I²)` and `π` is surjective with kernel `J`;
* `J ⊆ I`, so `J = J² ⊆ I²`, and the two displayed facts collapse to `I = I²`.

Geometrically: the cotangent space at the identity of an extension is squeezed between those of
the sub and the quotient, so it vanishes when both of them do. -/
theorem IsShortExact.augmentationIdeal_sq_eq (h : IsShortExact i π)
    (h'' : Bialgebra.augmentationIdeal R A'' ^ 2 = Bialgebra.augmentationIdeal R A'')
    (h' : Bialgebra.augmentationIdeal R A' ^ 2 = Bialgebra.augmentationIdeal R A') :
    Bialgebra.augmentationIdeal R A ^ 2 = Bialgebra.augmentationIdeal R A := by
  -- `J = ker π = i(I'')·A` is idempotent because `I''` is.
  have hJ : RingHom.ker (π.toAlgHom.toRingHom : A →+* A') ^ 2 =
      RingHom.ker (π.toAlgHom.toRingHom : A →+* A') := by
    rw [h.ker_eq, ← Ideal.map_pow, h'']
  -- and it sits inside the augmentation ideal of `A`.
  have hJle : RingHom.ker (π.toAlgHom.toRingHom : A →+* A') ≤ Bialgebra.augmentationIdeal R A := by
    rw [h.ker_eq, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Bialgebra.mem_augmentationIdeal_iff] at ha
    rw [Ideal.mem_comap, Bialgebra.mem_augmentationIdeal_iff]
    show Coalgebra.counit (R := R) (i a) = 0
    rw [CoalgHomClass.counit_comp_apply, ha]
  have hJsq : RingHom.ker (π.toAlgHom.toRingHom : A →+* A') ≤
      Bialgebra.augmentationIdeal R A ^ 2 := by
    calc RingHom.ker (π.toAlgHom.toRingHom : A →+* A')
        = RingHom.ker (π.toAlgHom.toRingHom : A →+* A') ^ 2 := hJ.symm
      _ ≤ Bialgebra.augmentationIdeal R A ^ 2 := by
          rw [sq, sq]; exact Ideal.mul_mono hJle hJle
  refine le_antisymm (Ideal.pow_le_self two_ne_zero) fun a ha => ?_
  -- `π a ∈ I' = I'² = π(I²)`, so `a` differs from an element of `I²` by an element of `ker π`.
  have hmem : (π.toAlgHom.toRingHom : A →+* A') a ∈
      Ideal.map (π.toAlgHom.toRingHom : A →+* A') (Bialgebra.augmentationIdeal R A ^ 2) := by
    rw [Ideal.map_pow, h.map_augmentationIdeal, h']
    exact map_augmentationIdeal_le π (Ideal.mem_map_of_mem _ ha)
  obtain ⟨b, hb, hab⟩ := (Ideal.mem_map_iff_of_surjective _ h.surjective).mp hmem
  have hker : a - b ∈ RingHom.ker (π.toAlgHom.toRingHom : A →+* A') := by
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    exact hab.symm
  have hsub := hJsq hker
  simpa using add_mem hsub hb

/-- **The composite `Spec A' → Spec A → Spec A''` is trivial**, written on coordinate rings:
`π ∘ i` is the counit of `A''` followed by the unit of `A'`, i.e. `π (i a) = ε(a) • 1`.

This is the only consequence of the kernel condition `ker π = A · i(ker ε)` that the exactness
proof needs, and it is what makes one half of the dual kernel condition
(`IsShortExact.le_ker_cartierDual`) formal: a functional pulled back along `π` and killing `1`
automatically kills `i(A'')`.

Proof: `a - ε(a) • 1` lies in the augmentation ideal of `A''`, so its image under `i` lies in
`ker π`; expand, and use `i 1 = 1`, `π 1 = 1`. -/
lemma IsShortExact.apply_comp (h : IsShortExact i π) (a : A'') :
    π (i a) = Coalgebra.counit (R := R) a • (1 : A') := by
  have hmem : (a - Coalgebra.counit (R := R) a • (1 : A'')) ∈
      Bialgebra.augmentationIdeal R A'' := by
    rw [Bialgebra.mem_augmentationIdeal_iff]
    simp
  have h0 : (π.toAlgHom.toRingHom : A →+* A')
      (i (a - Coalgebra.counit (R := R) a • (1 : A''))) = 0 := by
    rw [← RingHom.mem_ker, h.ker_eq]
    exact Ideal.mem_map_of_mem _ hmem
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, map_smul, map_one] at h0
  rw [sub_eq_zero] at h0
  exact h0

/-- **`i` is a pure map of `R`-modules**: `N ⊗ A'' → N ⊗ A` is injective for *every* `R`-module
`N`, not merely for `N = R`.

**PROVEN** (2026-07-28), and it uses the `faithfullyFlat` field and nothing else — no
comultiplication, no antipode, no Galois map, and no finiteness or freeness over `R`. The argument
is two mathlib lemmas:

* `Module.FaithfullyFlat.tensorProduct_mk_injective` says that for a faithfully flat algebra
  `A''→ A` the unit `M → A ⊗_{A''} M` is injective for every `A''`-module `M`;
* apply that to the induced `A''`-module `A'' ⊗[R] N` and transport along
  `TensorProduct.AlgebraTensorModule.cancelBaseChange R A'' A A N :
  A ⊗_{A''} (A'' ⊗[R] N) ≃ₗ A ⊗[R] N`, under which `1 ⊗ₜ (a'' ⊗ₜ n) ↦ i a'' ⊗ₜ n`, i.e. the unit
  becomes `LinearMap.rTensor N i`.

This is the Hopf-side statement of purity, i.e. the Hopf specialisation of
`AlgHom.rTensor_injective_of_faithfullyFlat`. **It currently has no consumer.** It was written to
feed a route to flatness of `A ⧸ i(A'')` that went through a sorried general lemma
(`Module.Flat.quotient_range_of_rTensor_injective`); a concurrent branch proved the same conclusion
outright as `AlgHom.flat_quotient_range_of_faithfullyFlat` in the `FaithfullyFlatSplit` section
above, the merge kept that route, and both the leaf and the `IsShortExact.flat_quotient` wrapper
that consumed this lemma went with it. So this is free-floating and is a candidate for the next
free-floating sweep; it is left in place only because deleting a merger-retained declaration is a
sweep decision, not a prover's. -/
theorem IsShortExact.rTensor_injective (h : IsShortExact i π)
    (N : Type*) [AddCommGroup N] [Module R N] :
    Function.Injective
      (LinearMap.rTensor N (i.toAlgHom : A'' →ₐ[R] A).toLinearMap) := by
  have hff := h.faithfullyFlat
  algebraize [(i.toAlgHom.toRingHom : A'' →+* A)]
  haveI : Module.FaithfullyFlat A'' A := hff
  have hmk := Module.FaithfullyFlat.tensorProduct_mk_injective (A := A'') (B := A) (A'' ⊗[R] N)
  have hcomp : ∀ (y : A'' ⊗[R] N),
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R A'' A A N)
        (TensorProduct.mk A'' A (A'' ⊗[R] N) 1 y) =
      LinearMap.rTensor N (i.toAlgHom : A'' →ₐ[R] A).toLinearMap y := by
    intro y
    induction y with
    | zero => simp
    | tmul a n =>
        simp only [TensorProduct.mk_apply,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.rTensor_tmul,
          AlgHom.toLinearMap_apply, Algebra.smul_def, mul_one]
        rfl
    | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  intro y z hyz
  refine hmk ?_
  apply (TensorProduct.AlgebraTensorModule.cancelBaseChange R A'' A A N).injective
  rw [hcomp, hcomp, hyz]

end Def

/-! ### Exactness of Cartier duality -/

section Dual

variable {R : Type u} {A'' : Type v} {A : Type w} {A' : Type x}
variable [CommRing R] [CommRing A''] [CommRing A] [CommRing A']
variable [HopfAlgebra R A''] [HopfAlgebra R A] [HopfAlgebra R A']
variable [IsCocomm R A''] [IsCocomm R A] [IsCocomm R A']
variable [Module.Finite R A''] [Module.Free R A''] [Module.Finite R A] [Module.Free R A]
  [Module.Finite R A'] [Module.Free R A']

variable {i : A'' →ₐc[R] A} {π : A →ₐc[R] A'}

/-! #### The four inputs

`IsShortExact.cartierDual` is assembled below out of the statements tabulated here, all but one of
which are proven. The split is by *where the mathematics is*:

| statement | status | content |
| --------- | ------ | ------- |
| `exists_linearRetraction` | **PROVEN** | `i(A'')` is an `R`-module direct summand of `A` |
| `surjective_cartierDual_map` | **PROVEN** from the above | functionals extend along `i` |
| `le_ker_cartierDual` | **PROVEN** | the easy half of the dual kernel condition |
| `exists_spanning_cartierDual` | **OPEN** | `D(A)` is *generated* over `D(A')` by `rk_R A''` elements |
| `nonempty_linearEquiv_cartierDual` | **PROVEN** from the two below | the rank count `rk_R A = rk_R A'' · rk_R A'` |
| `finrank_eq_mul` | **PROVEN** from the two below | that same rank count, before packaging |
| `nonempty_linearEquiv_baseChange` | **OPEN** | the torsor identity `A ⊗_{A''} A ≅ A ⊗_R A'` |
| `Module.finrank_eq_finrank_mul_of_rankAtStalk_eq` | **PROVEN** (2026-07-30) | the degree of a tower (root namespace, no Hopf content) |
| `exists_basis_cartierDual` | **PROVEN** from those two | `D(A)` is `D(A')`-free of rank `rk_R A''` |
| `ker_cartierDual_le` | **PROVEN** from the cut | the hard half: a character trivial on `Spec A'` descends |
| `faithfullyFlat_cartierDual` | **PROVEN** from the cut | `(Spec A)^D → (Spec A')^D` is faithfully flat |

So exactly **two** statements are open in this file as of 2026-07-30, they are independent of each
other, and both are Hopf-theoretic: `exists_spanning_cartierDual` (generation, the surviving half
of the linear dual of the normal basis) and `IsShortExact.nonempty_linearEquiv_baseChange` (the
torsor identity).  The third, `Module.finrank_eq_finrank_mul_of_rankAtStalk_eq` (the degree of a
tower, root namespace, no Hopf content), was PROVEN on 2026-07-30 — so **this file no longer owes
anything outside Hopf algebra.**  The rank half of the normal basis,
`nonempty_linearEquiv_cartierDual`, was PROVEN on 2026-07-28 over the tower formula and the torsor
identity.

(An older version of this list also named `Module.Flat.quotient_range_of_rTensor_injective` as
what the surjectivity field rests on. **That is stale**: no such declaration is in this file, or
anywhere under `Fermat/` — it belonged to the losing branch of the two that closed
`IsShortExact.flat_quotient` concurrently, and the route kept here goes through the PROVEN
`AlgHom.flat_quotient_range_of_faithfullyFlat` instead. The same correction applies to the bullet
in the module header, which is left alone only because that name has a separate owner.)

The surjectivity field rests on general module theory rather than on anything Hopf-theoretic, but
that input is **no longer a leaf**: it is `AlgHom.flat_quotient_range_of_faithfullyFlat`, PROVEN in
the `FaithfullyFlatSplit` section above. An earlier version of this note listed a second open
statement, a root-namespace `Module.Flat.quotient_range_of_rTensor_injective`; that declaration was
removed when the two concurrent branches were merged and the proven route was kept.

An earlier note claiming that all three fields were gated on *one* missing theorem — Takeuchi's
bijectivity of the Galois map `β : A ⊗_{A''} A → A ⊗[R] A'` — was wrong twice over. The two
`cartierDual` fields do share a gate, and it is the *dual* normal basis rather than `β`; and
flatness of `A ⧸ i(A'')` neither participates in that gate nor needs `β` at all, because the
`faithfullyFlat` field already makes `i` pure.

-/

omit [IsCocomm R A''] [IsCocomm R A] [IsCocomm R A'] [Module.Finite R A'] [Module.Free R A'] in
/-- **`i(A'')` is an `R`-module direct summand of `A`**: the inclusion of the sub-bialgebra
admits an `R`-linear retraction.

**PROVEN** (2026-07-27), and by a route much cheaper than the one this docstring used to
advertise. It is *equivalent* to `surjective_cartierDual_map` — `A''` is finite free over `R`, so
a retraction can be reassembled from extensions of a dual basis — so stating it this way is a
change of formulation, not a weakening.

**The old docstring said this needed the normal-basis isomorphism `A ≅ A'' ⊗[R] A'`, hence fppf
local triviality of the torsor `Spec A → Spec A''`. That is not so, and the correction is worth
recording because the same over-estimate is repeated in the two leaves below.** The faithful
flatness field of `IsShortExact` already does all of the work, through purity:

* a faithfully flat ring map is a **pure** monomorphism of `R`-modules, i.e. stays injective after
  tensoring with an arbitrary `R`-module (`AlgHom.rTensor_injective_of_faithfullyFlat`);
* so `A ⧸ i(A'')` is `R`-**flat** (`AlgHom.flat_quotient_range_of_faithfullyFlat`);
* it is finitely presented because `A''` and `A` are finite free, hence projective, hence the
  sequence `0 → i(A'') → A → A ⧸ i(A'') → 0` splits.

No torsor, no descent, no local triviality, and no Hopf structure: the whole statement is
`AlgHom.exists_linearRetraction_of_faithfullyFlat` applied to `i.toAlgHom`. In particular the
"gated on fppf descent" note that used to sit here — and still sits on `ker_cartierDual_le` —
was an over-estimate for *this* field. -/
theorem IsShortExact.exists_linearRetraction (h : IsShortExact i π) :
    ∃ r : A →ₗ[R] A'', ∀ a : A'', r (i a) = a :=
  i.toAlgHom.exists_linearRetraction_of_faithfullyFlat h.faithfullyFlat

omit [IsCocomm R A'] [Module.Finite R A'] [Module.Free R A'] in
/-- **The transposed inclusion `(Spec A)^D → (Spec A'')^D` is a closed immersion**, i.e.
`CartierDual.map i` is surjective.

PROVEN from `IsShortExact.exists_linearRetraction`: given `ψ : CartierDual R A''`, the functional
`ψ ∘ r` on `A` restricts along `i` to `ψ`. This is the dual of `Spec A → Spec A''` being
faithfully flat. -/
theorem IsShortExact.surjective_cartierDual_map (h : IsShortExact i π) :
    Function.Surjective (CartierDual.map i) := by
  obtain ⟨r, hr⟩ := h.exists_linearRetraction
  intro ψ
  refine ⟨(CartierDual.toDual R A).symm ((CartierDual.toDual R A'' ψ) ∘ₗ r), ?_⟩
  ext a
  rw [CartierDual.map_apply, ← CartierDual.coe_apply, LinearEquiv.apply_symm_apply,
    LinearMap.comp_apply, hr, CartierDual.coe_apply]

/-- **The easy half of the dual kernel condition**: the ideal of `CartierDual R A` generated by
the pullbacks along `π` of the functionals on `A'` killing `1` is contained in the kernel of
restriction along `i`.

PROVEN, and formal: a generator is `ψ ∘ π` with `ψ 1 = 0`, and
`(ψ ∘ π) (i a) = ψ (ε(a) • 1) = ε(a) * ψ 1 = 0` by `IsShortExact.apply_comp`. Only the *kernel*
field of the original sequence is used; neither faithful flatness nor surjectivity enters. -/
theorem IsShortExact.le_ker_cartierDual (h : IsShortExact i π) :
    Ideal.map ((CartierDual.map π).toAlgHom.toRingHom : CartierDual R A' →+* CartierDual R A)
        (Bialgebra.augmentationIdeal R (CartierDual R A'))
      ≤ RingHom.ker ((CartierDual.map i).toAlgHom.toRingHom :
          CartierDual R A →+* CartierDual R A'') := by
  rw [Ideal.map_le_iff_le_comap]
  intro ψ hψ
  rw [Bialgebra.mem_augmentationIdeal_iff, CartierDual.counit_apply] at hψ
  rw [Ideal.mem_comap, RingHom.mem_ker]
  show (CartierDual.map i) ((CartierDual.map π) ψ) = 0
  ext a
  rw [CartierDual.map_apply, CartierDual.map_apply, h.apply_comp, ← CartierDual.coe_apply,
    map_smul, CartierDual.coe_apply, hψ, smul_zero, CartierDual.zero_apply]

/-- A Cartier dual is nontrivial as soon as the base is: `1 = ε` sends `1` to `1`.

Used only to feed the `[Nontrivial M] [Module.Free R M] → Module.FaithfullyFlat R M` instance in
`IsShortExact.faithfullyFlat_cartierDual`. Declared unqualified (rather than as
`CartierDual.nontrivial`) because this section is inside `namespace HopfAlgebra`, where a dotted
name would create a *nested* `HopfAlgebra.CartierDual` namespace and silently shadow the real one
at every `open CartierDual` downstream. -/
lemma nontrivial_cartierDual {R : Type u} {A : Type w} [CommRing R] [CommRing A] [Nontrivial R]
    [HopfAlgebra R A] [IsCocomm R A] [Module.Finite R A] [Module.Free R A] :
    Nontrivial (CartierDual R A) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro hc
  have h1 : (0 : CartierDual R A) (1 : A) = (1 : CartierDual R A) (1 : A) := by rw [hc]
  rw [CartierDual.zero_apply, CartierDual.one_apply] at h1
  simp at h1

/-! #### The one shared cut: the dual normal basis

Both remaining fields of `IsShortExact.cartierDual` — `ker_cartierDual_le` and
`faithfullyFlat_cartierDual` — are consequences of a *single* statement, and it is the dual of the
normal-basis decomposition rather than the decomposition itself:

> `CartierDual R A` is a **free** `CartierDual R A'`-module on an index set of the same size as an
> `R`-basis of `A''`.

That is `IsShortExact.exists_basis_cartierDual` below. The two derivations are written out under
it; neither needs any further Hopf-algebra input, and in particular neither needs fppf descent
(see the gate audit on `ker_cartierDual_le`).

**Since 2026-07-28 the shared cut is itself PROVEN, from two strictly weaker statements**, so
what is left open in this half of the file is those two rather than the freeness:

* `IsShortExact.exists_spanning_cartierDual` — *generation*: some family of `rk_R A''` elements
  spans `CartierDual R A` over `CartierDual R A'`;
* `IsShortExact.nonempty_linearEquiv_cartierDual` — the *rank count*
  `rk_R A = rk_R A'' · rk_R A'`, packaged as an `R`-linear equivalence so that it is also true
  (vacuously) over the zero ring. **This one is PROVEN since 2026-07-28**, over two further
  leaves — the torsor identity `IsShortExact.nonempty_linearEquiv_baseChange` and the tower
  formula `Module.finrank_eq_finrank_mul_of_rankAtStalk_eq` (the latter **PROVEN 2026-07-30**) —
  so the generation half above and the torsor identity are what this half of the file still owes.

The step that makes this a genuine reduction rather than a restatement is **Orzech's property**,
which every commutative ring has (`Mathlib/RingTheory/FiniteType.lean`): a surjective linear map
onto a finitely generated module admitting an injection from its source is injective. So linear
*independence* — the half of "basis" that is usually the expensive one, and the half that fails
for a merely fppf-locally free module — is not something a prover has to supply here at all. -/

/-- **The dual normal basis, generation half**: `CartierDual R A` is *generated* as a
`CartierDual R A'`-module — the module structure being the one given by `CartierDual.map π` — by
a family indexed by `Module.Free.ChooseBasisIndex R A''`, i.e. by `rk_R A''` elements.

OPEN. This is one of the two statements into which `IsShortExact.exists_basis_cartierDual` was
cut on 2026-07-28; the other is the rank count `IsShortExact.nonempty_linearEquiv_cartierDual`,
and the freeness is assembled from the two by Orzech's property.

**Linear independence is deliberately not part of this statement.** Every commutative ring has
Orzech's property, so a surjection onto a finitely generated module that admits an injection from
its source is automatically injective; given the rank count, generation therefore upgrades to a
basis for free. This matters because independence is exactly the half that a *local* argument
cannot give — see the faithfulness audit on `exists_basis_cartierDual`, where the fallback
position is local freeness — whereas generation of a finitely generated module is a condition
that fppf-local and Nakayama-style arguments can reach.

## Where the mathematics is

Tate's argument (*Finite flat group schemes*, in Cornell–Silverman–Stevens, §2) is to dualise an
`R`-basis of `A''` through the normal-basis decomposition `A ≅ A'' ⊗[R] A'`; under it
`CartierDual.map π` becomes `1 ⊗ (regular representation of D(A'))`, so the `rk_R A''`
dual-basis vectors generate.

**Half of that is already available in this file, and a prover should start from it.** The map
`CartierDual.map i : CartierDual R A → CartierDual R A''` is surjective
(`IsShortExact.surjective_cartierDual_map`, PROVEN, via the `R`-linear retraction
`IsShortExact.exists_linearRetraction`), and `CartierDual R A''` is `R`-free on
`Module.Free.ChooseBasisIndex R A''`. So an *explicit* candidate family is available with no new
input: transport the dual basis of `Module.Free.chooseBasis R A''` along a section of
`CartierDual.map i`. For that family, `Submodule.span R (Set.range c) + ker (CartierDual.map i)`
is already all of `CartierDual R A`. What remains open is precisely

> `ker (CartierDual.map i) ≤ Submodule.span (CartierDual R A') (Set.range c)`,

and *that* is where the normal-basis input enters. (Do not try to close it with
`IsShortExact.ker_cartierDual_le`: that lemma is proven *from* this one, through
`exists_basis_cartierDual`, so the route is circular.)

## FAITHFULNESS AUDIT

This statement is implied by the cut it was extracted from — a basis is in particular a spanning
family — so it cannot be stronger than `exists_basis_cartierDual`, whose own audit is below. It
is strictly weaker: it says nothing about independence, and in particular it is satisfied by any
family of `rk_R A''` generators, not only by a dual normal basis.

It is not vacuous: over the zero ring it holds trivially, but over a field it is the assertion
`dim D(A) = dim A'' · dim A'` together with a choice of generators realising it, which is false
for any family of fewer than `rk_R A''` elements.

**This leaf now carries the whole global-versus-local-freeness risk of the cut, alone.** If
`exists_basis_cartierDual` is ever refuted — its audit explains that the only possible shape of a
counterexample is a non-local base on which `D(A)` is fppf-locally but not globally free — then
the sibling `nonempty_linearEquiv_cartierDual` still survives, because local freeness of rank
`rk_R A''` already forces the rank count; so the false statement would have to be *this* one. A
prover who comes to doubt the strong form should therefore attack the generation statement for a
counterexample, and the documented fallback (weaken to local freeness of rank `rk_R A''` and
localise the two consumers' derivations, weakening neither consumer) applies here unchanged. -/
theorem IsShortExact.exists_spanning_cartierDual (h : IsShortExact i π) :
    letI : Algebra (CartierDual R A') (CartierDual R A) :=
      ((CartierDual.map π).toAlgHom.toRingHom :
        CartierDual R A' →+* CartierDual R A).toAlgebra
    ∃ c : Module.Free.ChooseBasisIndex R A'' → CartierDual R A,
      Submodule.span (CartierDual R A') (Set.range c) = ⊤ := sorry

/-! #### The rank count

`IsShortExact.nonempty_linearEquiv_cartierDual` below is the *numerical* half of the dual normal
basis, and it is proven here out of two statements that share nothing with each other: a torsor
identity that is pure Hopf algebra, and the degree of a tower, which is pure commutative algebra
and lives at the root namespace above. -/

/-- **`Spec A` is a `Spec A'`-torsor over `Spec A''`**, in the only form the rank count needs:
`A ⊗[A''] A` and `A ⊗[R] A'` are isomorphic as `A`-modules, where `A` is an `A''`-algebra
through `i`.

OPEN. Cut on 2026-07-28 out of `IsShortExact.nonempty_linearEquiv_cartierDual`, alongside
`Module.finrank_eq_finrank_mul_of_rankAtStalk_eq`.

Geometrically this is the standard trivialisation of a torsor by its own base change,
`G ×_{G''} G ≅ G × G'` via `(x, y) ↦ (x, x⁻¹y)`, which lands in `G'` precisely because `G'` is
the kernel of `G → G''`. On points it is formal; the content is that the ring-level `ker_eq`
field captures "kernel" correctly.

## The route: a finite computation, and it needs NO flatness over `A''`

Only `ker_eq`, surjectivity of `π`, and `R`-flatness of `A` (which is free) are used. The
`faithfullyFlat` field is **not** needed here — it is consumed one level up, in
`IsShortExact.finrank_eq_mul`, where it makes `Spec A → Spec A''` surjective. Worth knowing
before attacking this: it is not a descent statement, and no fppf machinery is involved.

Let `Θ : A ⊗[R] A ≃ₗ[R] A ⊗[R] A`, `a ⊗ b ↦ ∑ a·b₍₁₎ ⊗ b₍₂₎`, the classical translation
isomorphism, whose inverse is `a ⊗ b ↦ ∑ a·S(b₍₁₎) ⊗ b₍₂₎` (the composites collapse by
coassociativity and the antipode axiom). Write

* `K₁ := ker (A ⊗[R] A ↠ A ⊗[A''] A)`, spanned by `a·i(c) ⊗ b - a ⊗ i(c)·b` for `c : A''`;
* `K₂ := ker (A ⊗[R] A ↠ A ⊗[R] A')`, which is `A ⊗[R] RingHom.ker π` because `A` is `R`-flat
  and `π` is surjective; by `ker_eq` it is spanned by `a ⊗ i(c)·b` with `c` in the augmentation
  ideal of `A''`.

Then `Θ K₁ = K₂`, and the map induced on quotients is the required isomorphism.

* `Θ K₁ ⊆ K₂`: apply `id ⊗ π` to `Θ(a·i(c) ⊗ b) - Θ(a ⊗ i(c)·b) =
  ∑ a i(c) b₍₁₎ ⊗ b₍₂₎ - ∑ a i(c₍₁₎) b₍₁₎ ⊗ i(c₍₂₎) b₍₂₎` (using that `i` is a coalgebra map).
  By `IsShortExact.apply_comp`, `π (i c₍₂₎) = ε(c₍₂₎) · 1`, so the second sum contracts along
  the counit axiom to the first and the difference dies.
* `K₂ ⊆ Θ K₁`: for `c` in the augmentation ideal,
  `Θ⁻¹(a ⊗ i(c)·b) = ∑ a S(b₍₁₎) S(i c₍₁₎) ⊗ i(c₍₂₎) b₍₂₎`. Modulo `K₁` move `i(c₍₂₎)` across the
  tensor and use that `i` commutes with the antipode:
  `∑ S(i c₍₁₎) i(c₍₂₎) = i (∑ S(c₍₁₎) c₍₂₎) = ε(c) · 1 = 0`.

## What has to be built (checked, not assumed)

There is **no** Hopf–Galois map in this pin. `Mathlib/RingTheory/HopfAlgebra/` contains exactly
`Basic`, `Convolution`, `GroupLike`, `MonoidAlgebra`, `Quotient`, `TensorProduct`, and a grep
over `Mathlib/` for `hopf.?galois`/`galoisMap` returns nothing. So `Θ` must be built here from
`Coalgebra.comul`, `HopfAlgebra.antipode` and the `Coalgebra.Repr` API
(`sum_antipode_mul_eq_algebraMap_counit` and its siblings). The presentation of `A ⊗[A''] A` as
`A ⊗[R] A` modulo `K₁` has to be written too; the file already carries the analogous
right-exactness plumbing in `AlgHom.flat_quotient_range_of_faithfullyFlat`, which goes through
`lTensor_exact`.

## Faithfulness

`Nonempty` rather than a named equivalence is deliberate and is **not** under-pinning. The sole
consumer, `IsShortExact.finrank_eq_mul`, uses it only through `Module.rankAtStalk_eq_of_equiv`:
it wants some `A`-linear isomorphism and nothing else. An adversary free to choose the
equivalence proves the same rank count, so there is nothing an existential can hide.

Refuting check showing `ker_eq` is load-bearing: drop it and take `A'' := R` with `i` the unit,
`A' := R` with `π := ε_A`. The conclusion would read `A ⊗[R] A ≅ A`, forcing `rk A ^ 2 = rk A`,
which fails for `A = R[ℤ/2]`. With `ker_eq` in force that configuration is excluded, because
`ker ε_A` is the augmentation ideal of `A` while `Ideal.map i (augmentationIdeal R R)` is `0`. -/
theorem IsShortExact.nonempty_linearEquiv_baseChange (h : IsShortExact i π) :
    letI : Algebra A'' A := (i.toAlgHom.toRingHom : A'' →+* A).toAlgebra
    Nonempty ((A ⊗[A''] A) ≃ₗ[A] (A ⊗[R] A')) := sorry

/-- **Multiplicativity of the rank in a short exact sequence**: `rk_R A = rk_R A'' · rk_R A'`.

**PROVEN** (2026-07-28) from `IsShortExact.nonempty_linearEquiv_baseChange` (the torsor identity)
and `Module.finrank_eq_finrank_mul_of_rankAtStalk_eq` (the degree of a tower). It is the whole
mathematical content of `IsShortExact.nonempty_linearEquiv_cartierDual`, which is this identity
repackaged through `CartierDual.finrank_cartierDual`.

The argument is the classical one for `|G| = |G''| · |G'|`, in three steps.

1. `A` is a finite flat `A''`-module: flatness is the `faithfullyFlat` field, finiteness comes
   from `Module.Finite R A` along the tower `R → A'' → A`.
2. Its rank is the **constant** `rk_R A'` at every stalk of `A''`. Faithful flatness makes
   `Spec A → Spec A''` surjective (`PrimeSpectrum.comap_surjective_of_faithfullyFlat`), so it is
   enough to check this after base change along `A'' → A`; there
   `A ⊗[A''] A ≅ A ⊗[R] A'` is `A`-free of rank `rk_R A'`.
3. The tower formula turns a constant relative rank into the product.

Note where the two hypotheses go: faithful flatness is used **only** in step 2, and only for
surjectivity of the map on spectra; the torsor identity itself needs none of it.

The subsingleton base is discharged first and separately: over the zero ring every `finrank` is
`1` by `rank_subsingleton` and the identity reads `1 = 1 · 1`. Afterwards `Nontrivial A` — needed
for the `StrongRankCondition A` that the base-change rank computation uses — follows from
`Nontrivial R`, because the counit is a retraction of `R → A`. -/
theorem IsShortExact.finrank_eq_mul (h : IsShortExact i π) :
    Module.finrank R A = Module.finrank R A'' * Module.finrank R A' := by
  classical
  rcases subsingleton_or_nontrivial R with _ | _
  · have e1 : Module.finrank R A = 1 := by simp [Module.finrank, rank_subsingleton]
    have e2 : Module.finrank R A'' = 1 := by simp [Module.finrank, rank_subsingleton]
    have e3 : Module.finrank R A' = 1 := by simp [Module.finrank, rank_subsingleton]
    rw [e1, e2, e3, one_mul]
  haveI : Nontrivial A := by
    rcases subsingleton_or_nontrivial A with hs | hA
    · exact absurd ((Bialgebra.counit_one (R := R) (A := A)).symm.trans
        (by rw [Subsingleton.elim (1 : A) 0, map_zero])) one_ne_zero
    · exact hA
  letI : Algebra A'' A := (i.toAlgHom.toRingHom : A'' →+* A).toAlgebra
  haveI : IsScalarTower R A'' A :=
    IsScalarTower.of_algebraMap_eq fun r => (i.toAlgHom.commutes r).symm
  haveI hff : Module.FaithfullyFlat A'' A := h.faithfullyFlat
  haveI : Module.Finite A'' A := Module.Finite.of_restrictScalars_finite R A'' A
  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap A'' A)) :=
    PrimeSpectrum.comap_surjective_of_faithfullyFlat
  have hn : ∀ p : PrimeSpectrum A'',
      Module.rankAtStalk (R := A'') A p = Module.finrank R A' := by
    intro p
    obtain ⟨q, rfl⟩ := hsurj p
    rw [← Module.rankAtStalk_baseChange (R := A'') (M := A) (S := A) q]
    obtain ⟨e⟩ := h.nonempty_linearEquiv_baseChange
    rw [Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_eq_finrank_of_free]
    exact Module.finrank_baseChange
  exact Module.finrank_eq_finrank_mul_of_rankAtStalk_eq hn

/-- **The dual normal basis, rank half**: `CartierDual R A` and `rk_R A''` copies of
`CartierDual R A'` have the same `R`-rank.

Since `rk_R (CartierDual R M) = rk_R M` for finite free `M` (`CartierDual.finrank_cartierDual`),
this is exactly the **multiplicativity of ranks in a short exact sequence**,
`rk_R A = rk_R A'' · rk_R A'` — geometrically, that `Spec A → Spec A''` is finite locally free of
rank `rk_R A'`, its fibre over the identity section being `Spec A'`.

**PROVEN** (2026-07-28) — it is `IsShortExact.finrank_eq_mul` above, repackaged. It was the
second of the two statements into which `IsShortExact.exists_basis_cartierDual` was cut earlier
the same day; see `IsShortExact.exists_spanning_cartierDual` for the first, which is still open.

The repackaging is the whole of the proof and is worth reading only for its degenerate case.
`CartierDual.finrank_cartierDual` turns both `Cartier` duals into their originals, so
`rk_R (ChooseBasisIndex R A'' →₀ CartierDual R A') = rk_R A'' · rk_R A' = rk_R A =
rk_R (CartierDual R A)`, and two finite free modules of equal rank are linearly equivalent
through their chosen bases. Over a **subsingleton** base none of that is available —
`finrank_cartierDual` is stated with `[Nontrivial R]`, and `Module.finrank_eq_card_chooseBasisIndex`
needs `StrongRankCondition R` — but there both sides are subsingleton by `Module.subsingleton`
and the zero map is an equivalence, which is exactly the corner the docstring below predicted.

## Why it is phrased as a linear equivalence and not as an equality of `finrank`s

Two reasons, and the second is a correctness matter rather than convenience.

* It is what the assembly consumes: Orzech's property needs an injective `R`-linear map from the
  source of the spanning map into `CartierDual R A`, and an equivalence supplies one directly.
* **The obvious index-set formulation is FALSE over the zero ring.** One might state
  `Nonempty (ChooseBasisIndex R A'' × ChooseBasisIndex R A' ≃ ChooseBasisIndex R A)`; but when
  `R` is subsingleton every module is zero and *every* type indexes a basis of it, so
  `Module.Free.ChooseBasisIndex` is an arbitrary choice and the three chosen types need not match
  — `Empty` against `Unit` refutes it. The linear-equivalence form has no such corner: over the
  zero ring both sides are subsingleton and the equivalence exists trivially.

## FAITHFULNESS AUDIT

Implied by the cut it was extracted from: a `Module.Basis (ChooseBasisIndex R A'')
(CartierDual R A') (CartierDual R A)` gives `CartierDual R A ≃ₗ[CartierDual R A']
(ChooseBasisIndex R A'' →₀ CartierDual R A')`, and restricting scalars to `R` along the tower
`R → CartierDual R A' → CartierDual R A` gives exactly this equivalence. So it is not stronger
than `exists_basis_cartierDual`. It is strictly weaker: it retains only the numerical shadow of
that statement and none of its module structure over `CartierDual R A'`.

Non-vacuity: over a field it says `dim A = dim A'' · dim A'`, which pins a genuine numerical
invariant of the extension and fails for, e.g., a would-be "short exact sequence" whose middle
term had the wrong dimension. -/
theorem IsShortExact.nonempty_linearEquiv_cartierDual (h : IsShortExact i π) :
    Nonempty ((Module.Free.ChooseBasisIndex R A'' →₀ CartierDual R A') ≃ₗ[R]
      CartierDual R A) := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · have h1 : Subsingleton (Module.Free.ChooseBasisIndex R A'' →₀ CartierDual R A') :=
      Module.subsingleton R _
    have h2 : Subsingleton (CartierDual R A) := Module.subsingleton R _
    exact ⟨{ toFun := 0, map_add' := by intros; simp, map_smul' := by intros; simp,
             invFun := 0, left_inv := fun _ => Subsingleton.elim _ _,
             right_inv := fun _ => Subsingleton.elim _ _ }⟩
  · let ι := Module.Free.ChooseBasisIndex R A''
    let D' := CartierDual R A'
    let κ' := Module.Free.ChooseBasisIndex R D'
    let κ := Module.Free.ChooseBasisIndex R (CartierDual R A)
    let c' : Module.Basis κ' R D' := Module.Free.chooseBasis R D'
    let c : Module.Basis κ R (CartierDual R A) := Module.Free.chooseBasis R (CartierDual R A)
    have hcard : Fintype.card (ι × κ') = Fintype.card κ := by
      rw [Fintype.card_prod, ← Module.finrank_eq_card_chooseBasisIndex R A'',
        ← Module.finrank_eq_card_chooseBasisIndex R D',
        ← Module.finrank_eq_card_chooseBasisIndex R (CartierDual R A),
        CartierDual.finrank_cartierDual, CartierDual.finrank_cartierDual, h.finrank_eq_mul]
    let e : ι × κ' ≃ κ := Fintype.equivOfCardEq hcard
    let E1 : (ι →₀ D') ≃ₗ[R] (ι →₀ (κ' →₀ R)) := Finsupp.mapRange.linearEquiv c'.repr
    let E2 : (ι →₀ (κ' →₀ R)) ≃ₗ[R] ((ι × κ') →₀ R) := (Finsupp.curryLinearEquiv R).symm
    let E3 : ((ι × κ') →₀ R) ≃ₗ[R] (κ →₀ R) := Finsupp.domLCongr e
    exact ⟨E1 ≪≫ₗ E2 ≪≫ₗ E3 ≪≫ₗ c.repr.symm⟩

/-- **The dual normal basis.** `CartierDual R A` is a free `CartierDual R A'`-module on
`Module.Free.ChooseBasisIndex R A''`, i.e. free of rank `rk_R A''`, where the module structure is
the one given by `CartierDual.map π`.

**PROVEN** (2026-07-28) from the two statements above, `IsShortExact.exists_spanning_cartierDual`
(generation by `rk_R A''` elements) and `IsShortExact.nonempty_linearEquiv_cartierDual` (the rank
count), by **Orzech's property**: `Finsupp.linearCombination` on the spanning family is a
surjective `CartierDual R A'`-linear map onto `CartierDual R A`, which is a finitely generated
`R`-module; the rank equivalence provides an injective `R`-linear map from its source; so
`OrzechProperty.bijective_of_surjective_of_injective` makes it bijective, and a bijective map
from `ι →₀ S` is a basis. Independence therefore costs nothing once generation and the rank count
are in hand — which is the whole reason for the cut.

Both `IsShortExact.ker_cartierDual_le` and `IsShortExact.faithfullyFlat_cartierDual` are proven
from this statement below, and `IsShortExact.cartierDual` is assembled from those.
(The surjectivity field's former leaf under `IsShortExact.flat_quotient` is no longer open, and
the wrapper no longer exists: that route now goes through the PROVEN
`AlgHom.flat_quotient_range_of_faithfullyFlat` above.  Of the two statements this one is proven
from, `exists_spanning_cartierDual` is still open and `nonempty_linearEquiv_cartierDual` was
PROVEN the same day over two smaller leaves; see the status table above for the current three.)

## Why this is the right cut

This is Tate's own argument (*Finite flat group schemes*, in Cornell–Silverman–Stevens, §2): the
exactness of Cartier duality is proven by exhibiting `D(A)` as a free `D(A')`-module *on the basis
dual to an `R`-basis of `A''`*. The statement below is that sentence, verbatim — the index type is
literally `Module.Free.ChooseBasisIndex R A''`, so a proof may take the chosen `R`-basis of `A''`
and produce the dual family.

Geometrically `Spec D(A) → Spec D(A')` is the quotient map of the dual sequence, a torsor under
`Spec D(A'')`; freeness of the coordinate ring is the assertion that this torsor is *trivial as a
module*, which is what the classical `Ext¹(G'', 𝔾ₘ) = 0` supplies.

## FAITHFULNESS AUDIT

The risk in a statement of this shape is the difference between **free** and **fppf-locally free**:
being a torsor, `Spec D(A) → Spec D(A')` is finite locally free of rank `rk A''` for purely formal
reasons, and global freeness is a genuinely stronger assertion which fppf-local arguments cannot
give. The reasons to believe the strong form here, and the shape a refutation would have to take:

* **The `R`-freeness hypotheses are doing real work.** This section assumes `Module.Free R A''`,
  `Module.Free R A` and `Module.Free R A'` globally — not local freeness. The classical
  counterexamples to "a torsor has free coordinate ring" (Galois module structure: an unramified
  extension whose ring of integers is not free over the group ring) are exactly cases where the
  corresponding global freeness hypothesis fails.
* **Duality preserves the obstruction class.** Worked test case: `R` with `Pic R ≠ 0`,
  `G' = μ_p`, `G'' = ℤ/p`, `G` an extension. Then `A = ∏_{k ∈ ℤ/p} A_k` with `A_k` the coordinate
  ring of the `μ_p`-torsor of class `k·e`, and `D(G)` is an extension of the same shape whose
  class is `±e` under the self-duality of `Ext¹(ℤ/p, μ_p)`. So `Module.Free R A` (all `A_k` free,
  i.e. the `Pic`-components of `e` vanish) forces every component of `D(A)` to be free over
  `D(A') = R^p` — exactly the conclusion below. The hypothesis and the conclusion move together.
* Over a base field, or any local ring, the statement is automatic, so **any counterexample must
  use a non-local base with nontrivial `Pic`** — and by the previous point must decouple the
  freeness of `A` over `R` from the freeness of `D(A)` over `D(A')`.

**If the strong form is ever refuted, the fallback is known and both consumers survive it**, at
the cost of a localisation argument in each: `ker_cartierDual_le` uses only that
`CartierDual R A ⊗_{CartierDual R A'} R` is `R`-free of rank `rk A''`, and
`faithfullyFlat_cartierDual` uses only faithful flatness. Both are fppf-local on `R`. So the
correct repair would be to weaken this leaf to local freeness of rank `rk A''` and to localise the
two proofs below — *not* to weaken either consumer.

## References

* Tate, *Finite flat group schemes*, in Cornell–Silverman–Stevens, §2.
* Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras* (the Hopf–Galois input on
  the `A`-side, whose linear dual this is).
* Waterhouse, *Introduction to Affine Group Schemes*, ch. 14–16. -/
theorem IsShortExact.exists_basis_cartierDual (h : IsShortExact i π) :
    letI : Algebra (CartierDual R A') (CartierDual R A) :=
      ((CartierDual.map π).toAlgHom.toRingHom :
        CartierDual R A' →+* CartierDual R A).toAlgebra
    Nonempty (Module.Basis (Module.Free.ChooseBasisIndex R A'')
      (CartierDual R A') (CartierDual R A)) := by
  letI : Algebra (CartierDual R A') (CartierDual R A) :=
    ((CartierDual.map π).toAlgHom.toRingHom :
      CartierDual R A' →+* CartierDual R A).toAlgebra
  haveI : IsScalarTower R (CartierDual R A') (CartierDual R A) :=
    IsScalarTower.of_algebraMap_eq fun r => ((CartierDual.map π).toAlgHom.commutes r).symm
  obtain ⟨c, hc⟩ := h.exists_spanning_cartierDual
  obtain ⟨e⟩ := h.nonempty_linearEquiv_cartierDual
  -- The spanning family gives a surjection from a free `CartierDual R A'`-module.
  set F : (Module.Free.ChooseBasisIndex R A'' →₀ CartierDual R A') →ₗ[CartierDual R A']
      CartierDual R A := Finsupp.linearCombination (CartierDual R A') c with hF
  have hFsurj : Function.Surjective F := by
    rw [← LinearMap.range_eq_top, hF, Finsupp.range_linearCombination]
    exact hc
  -- Orzech: a surjection onto a finitely generated module whose source injects into it is
  -- injective. The injection is the rank equivalence, read `R`-linearly.
  have hFinj : Function.Injective F :=
    OrzechProperty.injective_of_surjective_of_injective (R := R) e.toLinearMap
      (F.restrictScalars R) e.injective hFsurj
  exact ⟨Module.Basis.ofRepr (LinearEquiv.ofBijective F ⟨hFinj, hFsurj⟩).symm⟩

/-- **The hard half of the dual kernel condition**: a functional on `A` vanishing on the
sub-bialgebra `i(A'')` lies in the ideal of `CartierDual R A` generated by
`(CartierDual.map π) (ker ε_{CartierDual R A'})`.

**PROVEN** (2026-07-28) from `IsShortExact.exists_basis_cartierDual`. In functor-of-points
language this is exactness of
`1 → (Spec A'')^D → (Spec A)^D → (Spec A')^D` at the middle term: a character of `Spec A`
that is trivial on the subgroup `Spec A'` factors through the fppf quotient
`Spec A / Spec A' = Spec A''`.

**ROUTE-AUDIT CORRECTION (2026-07-27). This docstring used to end "so this leaf is gated on
descent, not merely hard". Treat that as a hypothesis, not a fact.** The identical claim sat on
`IsShortExact.exists_linearRetraction` — "locally on `Spec R` the torsor is trivial", hence
fppf descent — and it was simply an over-estimate: that field is now **PROVEN** from the
faithful-flatness field alone, by purity of a faithfully flat ring map, with no descent, no
torsor and no local triviality (see the `FaithfullyFlatSplit` section). One sibling's descent
gate evaporating is a reason to re-derive this one rather than inherit it.

## The derivation from the dual normal basis

* the image of `CartierDual.map π` is exactly `Ann(ker π)` (transpose of a surjection), and
  `(CartierDual.map π) (ker ε) = Ann(ker π) ∩ Ann(1)` as an `R`-submodule — that much is
  elementary;
* the ideal generated by that submodule is taken in the **convolution** ring structure of
  `CartierDual R A`, which is where the elementary description stops.

**The recommended cut, which serves this leaf and `faithfullyFlat_cartierDual` at once.** Both
remaining fields follow from the *single* classical input, the normal-basis decomposition of `A`
as an `A''`-module and right `A'`-comodule,

    e : A ≃ₗ[R] A'' ⊗[R] A',    e (i a'') = a'' ⊗ₜ 1,    e intertwining (id ⊗ π) ∘ Δ ,

so a decomposition of *this file* should state that once and consume it twice, rather than
attacking the two fields separately. Given `e`, dualise: `A^D ≅ (A'')^D ⊗[R] (A')^D` as
`R`-modules, `map π` becomes `1 ⊗ (regular representation of (A')^D)`, and

* `A^D` is **free over `(A')^D` of rank `rk_R A''`** — the `(A')^D`-action is dual to the
  coaction `(id ⊗ π) ∘ Δ`, which `e` intertwines with `id ⊗ Δ_{A'}`, i.e. with the regular
  representation on the second factor. That alone is `faithfullyFlat_cartierDual`, through the
  pin's `[Nontrivial M] [Module.Free R M] → Module.FaithfullyFlat R M` instance;
* **and then a rank count gives this leaf, with no further input.** Write `J` for the ideal on
  the right-hand side. By construction `A^D ⧸ J = A^D ⊗_{(A')^D} R` along the counit, so freeness
  of rank `rk_R A''` makes `A^D ⧸ J` finite free of rank `rk_R A''` over `R`. On the other side
  `map i` is surjective (`surjective_cartierDual_map`, PROVEN), so
  `A^D ⧸ ker (map i) ≅ (A'')^D`, also finite free of rank `rk_R A''`. The inclusion `J ≤ ker`
  (`le_ker_cartierDual`, PROVEN) induces a **surjection between finite free `R`-modules of equal
  rank**, which is therefore injective — i.e. `ker (map i) = J`.

  (Under `e`, `map i` is `α ⊗ β ↦ β 1 • α` and `map π` is `ψ ↦ 1 ⊗ ψ`, so `ker (map i)` is
  `(A'')^D ⊗ ε-kernel`; but note the ideal `J` is generated in the **convolution** ring `A^D`,
  not merely as an `(A')^D`-submodule, and `e` is *not* an algebra isomorphism — the extension
  need not split as group schemes. So the direct "read off the ideal in coordinates" argument
  does **not** work, and the rank count above is what replaces it.)

Refuting check: the reverse inclusion `IsShortExact.le_ker_cartierDual` is proven, so a
counterexample would be a `φ : A →ₗ[R] R` killing `i(A'')` that is not a convolution combination
of pullbacks along `π`; over a field the rank count `rk A = rk A'' * rk A'` makes both sides free
of rank `rk A - rk A''`, so any counterexample must use a non-local base. -/
theorem IsShortExact.ker_cartierDual_le (h : IsShortExact i π) :
    RingHom.ker ((CartierDual.map i).toAlgHom.toRingHom :
        CartierDual R A →+* CartierDual R A'')
      ≤ Ideal.map ((CartierDual.map π).toAlgHom.toRingHom :
          CartierDual R A' →+* CartierDual R A)
          (Bialgebra.augmentationIdeal R (CartierDual R A')) := by
  classical
  letI : Algebra (CartierDual R A') (CartierDual R A) :=
    ((CartierDual.map π).toAlgHom.toRingHom :
      CartierDual R A' →+* CartierDual R A).toAlgebra
  have halg : (algebraMap (CartierDual R A') (CartierDual R A)) =
      ((CartierDual.map π).toAlgHom.toRingHom :
        CartierDual R A' →+* CartierDual R A) := rfl
  haveI : IsScalarTower R (CartierDual R A') (CartierDual R A) :=
    IsScalarTower.of_algebraMap_eq fun r => ((CartierDual.map π).toAlgHom.commutes r).symm
  obtain ⟨b⟩ := h.exists_basis_cartierDual
  set n := Module.Free.ChooseBasisIndex R A'' with hn
  set ε' : CartierDual R A' →ₐ[R] R := Bialgebra.counitAlgHom R (CartierDual R A') with hε'
  -- `Φ` reads off the `b`-coordinates and applies the counit of `CartierDual R A'` to each.
  set Φ : CartierDual R A →ₗ[R] (n →₀ R) :=
    (Finsupp.mapRange.linearMap ε'.toLinearMap) ∘ₗ
      (LinearEquiv.restrictScalars R b.repr).toLinearMap with hΦ
  have hΦ_apply : ∀ (x : CartierDual R A) (k : n), Φ x k = ε' (b.repr x k) := by
    intro x k
    simp [hΦ, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply]
  have hcoord : ∀ x : CartierDual R A, Φ x = 0 ↔ ∀ k, ε' (b.repr x k) = 0 := by
    intro x
    constructor
    · intro hx k
      rw [← hΦ_apply, hx, Finsupp.coe_zero, Pi.zero_apply]
    · intro hx
      ext k
      rw [hΦ_apply, hx k, Finsupp.coe_zero, Pi.zero_apply]
  -- `Φ` is semilinear over the counit, because the counit is a ring map.
  have hsmul : ∀ (c : CartierDual R A') (y : CartierDual R A), Φ (c • y) = ε' c • Φ y := by
    intro c y
    ext k
    rw [hΦ_apply, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finsupp.smul_apply,
      hΦ_apply, smul_eq_mul]
  have hΦsurj : Function.Surjective Φ := by
    intro y
    refine ⟨b.repr.symm (Finsupp.mapRange (algebraMap R (CartierDual R A')) (map_zero _) y), ?_⟩
    ext k
    rw [hΦ_apply, LinearEquiv.apply_symm_apply, Finsupp.mapRange_apply, ε'.commutes]
    simp
  set J : Ideal (CartierDual R A) :=
    Ideal.map ((CartierDual.map π).toAlgHom.toRingHom :
      CartierDual R A' →+* CartierDual R A)
      (Bialgebra.augmentationIdeal R (CartierDual R A')) with hJ
  have hmul : ∀ (a x : CartierDual R A), Φ x = 0 → Φ (a * x) = 0 := by
    intro a x hx
    have hxr := b.sum_repr x
    rw [← hxr, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [mul_smul_comm, hsmul, (hcoord x).1 hx k, zero_smul]
  have hJker : ∀ x ∈ J, Φ x = 0 := by
    have key : ∀ x ∈ Ideal.span ((⇑((CartierDual.map π).toAlgHom.toRingHom :
        CartierDual R A' →+* CartierDual R A)) ''
        (↑(Bialgebra.augmentationIdeal R (CartierDual R A')) : Set (CartierDual R A'))),
        Φ x = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨c, hc, rfl⟩ := hy
          have hc' : c ∈ Bialgebra.augmentationIdeal R (CartierDual R A') := hc
          rw [Bialgebra.mem_augmentationIdeal_iff] at hc'
          have hone : ((CartierDual.map π).toAlgHom.toRingHom :
              CartierDual R A' →+* CartierDual R A) c = c • (1 : CartierDual R A) := by
            rw [Algebra.smul_def, mul_one, halg]
          rw [hone, hsmul, show ε' c = 0 from hc', zero_smul]
      | zero => exact map_zero _
      | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
      | smul a y _ hy => rw [smul_eq_mul]; exact hmul a y hy
    exact key
  have hkerJ : ∀ x : CartierDual R A, Φ x = 0 → x ∈ J := by
    intro x hx
    have hxr := b.sum_repr x
    rw [← hxr]
    refine Ideal.sum_mem _ fun k _ => ?_
    rw [Algebra.smul_def, halg]
    refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    rw [Bialgebra.mem_augmentationIdeal_iff]
    exact (hcoord x).1 hx k
  -- `j` factors through `Φ` because `J ≤ ker j`; the factorisation is surjective, hence bijective.
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property Φ (LinearMap.id) hΦsurj
  set jl : CartierDual R A →ₗ[R] CartierDual R A'' := CartierDual.mapLinear i with hjl
  have hjsurj : Function.Surjective jl := h.surjective_cartierDual_map
  have hJj : ∀ x ∈ J, jl x = 0 := by
    intro x hx
    have hx' := h.le_ker_cartierDual hx
    rw [RingHom.mem_ker] at hx'
    exact hx'
  set g : (n →₀ R) →ₗ[R] CartierDual R A'' := jl ∘ₗ σ with hg_def
  have hg : ∀ x, g (Φ x) = jl x := by
    intro x
    have hker : Φ (σ (Φ x) - x) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact LinearMap.congr_fun hσ (Φ x)
    have hz := hJj _ (hkerJ _ hker)
    rw [map_sub, sub_eq_zero] at hz
    exact hz
  have hgsurj : Function.Surjective g := by
    intro y
    obtain ⟨x, rfl⟩ := hjsurj y
    exact ⟨Φ x, hg x⟩
  have hginj : Function.Injective g := by
    set bd : Module.Basis n R (CartierDual R A'') :=
      ((Module.Free.chooseBasis R A'').dualBasis).map (CartierDual.toDual R A'').symm with hbd
    exact OrzechProperty.injective_of_surjective_of_injective
      bd.repr.symm.toLinearMap g bd.repr.symm.injective hgsurj
  intro x hx
  rw [RingHom.mem_ker] at hx
  have hjx : jl x = 0 := hx
  have hgx : g (Φ x) = g 0 := by rw [hg, hjx, map_zero]
  exact hkerJ x (hginj hgx)

/-- **`(Spec A)^D → (Spec A')^D` is faithfully flat.**

OPEN, and this is the deepest of the two remaining fields: it is the statement that Cartier
duality turns the closed immersion `Spec A' ↪ Spec A` into an fppf quotient, i.e. that every
character of the subgroup `Spec A'` extends fppf-locally to `Spec A`. Classically (Tate, *Finite
flat group schemes*, §2) this is `Ext¹(G'', 𝔾ₘ) = 0` for finite flat `G''`, proven by exhibiting
`CartierDual R A` as a *free* `CartierDual R A'`-module on a basis dual to an
`R`-basis of `A''` — the linear dual of the normal-basis decomposition `A ≅ A'' ⊗[R] A'`.

**The last step of that route is already in the pin, so the leaf really is only the freeness.**
`Mathlib/RingTheory/Flat/FaithfullyFlat/Basic.lean` carries
`instance [Nontrivial M] [Module.Free R M] : Module.FaithfullyFlat R M`; so once
`Module.Free (CartierDual R A') (CartierDual R A)` is available along `(map π).toAlgebra`, this
field is that instance plus `Nontrivial (CartierDual R A)`. Note the corner: `Nontrivial` fails
exactly when `R` is the zero ring, where the whole statement is vacuous because a trivial ring
has no maximal ideals — so any assembly must case-split on `Subsingleton R` rather than assume
nontriviality. See `ker_cartierDual_le` for the shared normal-basis input that supplies the
freeness, and note that the "needs fppf descent" framing that used to sit on the sibling field
`exists_linearRetraction` was refuted there on 2026-07-27.

Refuting check: `RingHom.FaithfullyFlat` unfolds to `Module.FaithfullyFlat` along
`(CartierDual.map π).toAlgebra`, so a refutation would be a maximal ideal `m` of
`CartierDual R A'` with `m • CartierDual R A = ⊤`; over a base field this is impossible because
the module is free of rank `rk A''`, so any counterexample must use a non-local base. -/
theorem IsShortExact.faithfullyFlat_cartierDual (h : IsShortExact i π) :
    RingHom.FaithfullyFlat ((CartierDual.map π).toAlgHom.toRingHom :
      CartierDual R A' →+* CartierDual R A) := by
  letI : Algebra (CartierDual R A') (CartierDual R A) :=
    ((CartierDual.map π).toAlgHom.toRingHom :
      CartierDual R A' →+* CartierDual R A).toAlgebra
  obtain ⟨b⟩ := h.exists_basis_cartierDual
  haveI : Module.Free (CartierDual R A') (CartierDual R A) := Module.Free.of_basis b
  show Module.FaithfullyFlat (CartierDual R A') (CartierDual R A)
  rcases subsingleton_or_nontrivial R with _ | _
  · -- A subsingleton ring has no maximal ideals, so the condition is vacuous.
    refine ⟨fun m hm _ => hm.ne_top ?_⟩
    refine Ideal.eq_top_iff_one _ |>.2 ?_
    haveI : Subsingleton (CartierDual R A') := Module.subsingleton R (CartierDual R A')
    have h1 : (1 : CartierDual R A') = 0 := Subsingleton.elim _ _
    rw [h1]
    exact m.zero_mem
  · haveI := nontrivial_cartierDual (R := R) (A := A)
    infer_instance

/-- **Cartier duality is exact.**

If `1 → Spec A' → Spec A → Spec A'' → 1` is short exact, then so is the dual sequence
`1 → (Spec A'')^D → (Spec A)^D → (Spec A')^D → 1`; on coordinate rings the maps are the
transposes `CartierDual.map π` and `CartierDual.map i`, in that order, which is exactly the
`(i, π)` shape of `IsShortExact` with `A''` and `A'` exchanged.

This is Tate, *Finite flat group schemes*, §2, and Demazure–Gabriel II §1; the essential input is
that a finite locally free Hopf algebra in a short exact sequence is *free* over the sub-Hopf
algebra, so that `A ≅ A'' ⊗[R] A'` as an `A''`-comodule, and the linear dual of that
decomposition supplies all three conditions at once.

PROVEN as an assembly of the statements above; as of 2026-07-28 the remaining mathematics is in
exactly one of them. The kernel condition is fully proven (`le_ker_cartierDual` and
`ker_cartierDual_le`) and so is the faithful-flatness field, both from the single cut
`IsShortExact.exists_basis_cartierDual`; the surjectivity field is reduced to a pure module
statement about `A` (`IsShortExact.exists_linearRetraction`) with no Hopf structure left in it,
and that is PROVEN outright from `AlgHom.exists_linearRetraction_of_faithfullyFlat`. -/
theorem IsShortExact.cartierDual (h : IsShortExact i π) :
    IsShortExact (CartierDual.map π) (CartierDual.map i) :=
  ⟨h.faithfullyFlat_cartierDual, h.surjective_cartierDual_map,
    le_antisymm h.ker_cartierDual_le h.le_ker_cartierDual⟩

end Dual

/-! ### Invariant derivations, and unramifiedness from the augmentation ideal

The converse of `Bialgebra.augmentationIdeal_sq_eq_of_formallyUnramified` is where the group
structure is spent, and it is what makes "the identity is isolated" propagate to the whole
scheme: for a group scheme `Ω[A⁄R] ≅ A ⊗[R] I/I²`, the module of *invariant* differentials being
free on the cotangent space at the identity. Rather than construct that isomorphism we prove the
consequence directly, by translating an arbitrary derivation back to the identity:

given `d : Derivation R A M`, its **invariant derivative** is `D(a) = ∑ S(a₍₁₎) · d a₍₂₎`. Then

* `D` is an `ε`-derivation, `D(xy) = ε(x) D(y) + ε(y) D(x)` (`invariantAux_mul`) — this is where
  the antipode axiom `∑ S(a₍₁₎) a₍₂₎ = ε(a)` enters, and where commutativity of `A` is used to
  regroup the four Sweedler factors;
* hence `D` kills `I²`, so `I = I²` makes `D` vanish on `I`, and `D(1) = 0` makes it vanish on
  `R · 1`, hence everywhere;
* and `d` is recovered from `D` by `d(a) = ∑ a₍₁₎ · D(a₍₂₎)` (`invariantAct_comul`), which is
  coassociativity followed by the other antipode axiom `∑ a₍₁₎ S(a₍₂₎) = ε(a)`.

So every derivation vanishes, i.e. `Ω[A⁄R] = 0`. No finiteness or flatness over `R` is needed. -/

section Invariant

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [HopfAlgebra R A]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
variable (d : Derivation R A M)

/-- `x ⊗ y ↦ x • d y`. -/
noncomputable def actAux : A ⊗[R] A →ₗ[R] M :=
  TensorProduct.lift (LinearMap.mk₂ R (fun x y => x • d y)
    (fun _ _ _ => by rw [add_smul]) (fun _ _ _ => by rw [smul_assoc])
    (fun _ _ _ => by rw [map_add, smul_add]) (fun _ _ _ => by rw [d.map_smul, smul_comm]))

@[simp] lemma actAux_tmul (x y : A) : actAux d (x ⊗ₜ[R] y) = x • d y := rfl

/-- `x ⊗ y ↦ S x • d y`; composed with the comultiplication this is the invariant derivative. -/
noncomputable def antipodeAux : A ⊗[R] A →ₗ[R] M :=
  TensorProduct.lift (LinearMap.mk₂ R (fun x y => antipode R x • d y)
    (fun _ _ _ => by rw [map_add, add_smul]) (fun _ _ _ => by rw [map_smul, smul_assoc])
    (fun _ _ _ => by rw [map_add, smul_add]) (fun _ _ _ => by rw [d.map_smul, smul_comm]))

@[simp] lemma antipodeAux_tmul (x y : A) :
    antipodeAux d (x ⊗ₜ[R] y) = antipode R x • d y := rfl

/-- `x ⊗ (y ⊗ z) ↦ x • (S y • d z)`, the three-fold version needed for coassociativity. -/
noncomputable def antipodeAux3 : A ⊗[R] (A ⊗[R] A) →ₗ[R] M :=
  TensorProduct.lift (LinearMap.mk₂ R (fun x u => x • antipodeAux d u)
    (fun _ _ _ => by rw [add_smul]) (fun _ _ _ => by rw [smul_assoc])
    (fun _ _ _ => by rw [map_add, smul_add]) (fun _ _ _ => by rw [map_smul, smul_comm]))

@[simp] lemma antipodeAux3_tmul (x : A) (u : A ⊗[R] A) :
    antipodeAux3 d (x ⊗ₜ[R] u) = x • antipodeAux d u := rfl

/-- The **invariant derivative** `a ↦ ∑ S(a₍₁₎) · d a₍₂₎` of a derivation. -/
noncomputable def invariantAux : A →ₗ[R] M := antipodeAux d ∘ₗ (Coalgebra.comul (R := R))

@[simp] lemma invariantAux_apply (a : A) :
    invariantAux d a = antipodeAux d (Coalgebra.comul (R := R) a) := rfl

/-- `x ⊗ y ↦ x • D(y)`: composed with the comultiplication this recovers `d`. -/
noncomputable def invariantAct : A ⊗[R] A →ₗ[R] M :=
  TensorProduct.lift (LinearMap.mk₂ R (fun x y => x • invariantAux d y)
    (fun _ _ _ => by rw [add_smul]) (fun _ _ _ => by rw [smul_assoc])
    (fun _ _ _ => by rw [map_add, smul_add]) (fun _ _ _ => by rw [map_smul, smul_comm]))

@[simp] lemma invariantAct_tmul (x y : A) :
    invariantAct d (x ⊗ₜ[R] y) = x • invariantAux d y := rfl

/-- The Leibniz rule for `antipodeAux` on the algebra `A ⊗[R] A`: the correcting factor is
`x ⊗ y ↦ S x * y`, which is exactly what evaluates to `ε` on the image of the comultiplication. -/
lemma antipodeAux_mul (u v : A ⊗[R] A) :
    antipodeAux d (u * v) =
      LinearMap.mul' R A ((antipode R).rTensor A u) • antipodeAux d v +
        LinearMap.mul' R A ((antipode R).rTensor A v) • antipodeAux d u := by
  induction u with
  | zero => simp
  | add u₁ u₂ h₁ h₂ => simp only [add_mul, map_add, h₁, h₂, add_smul, smul_add]; abel
  | tmul x₁ x₂ =>
    induction v with
    | zero => simp
    | add v₁ v₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂, smul_add, add_smul]; abel
    | tmul y₁ y₂ =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, antipodeAux_tmul,
        HopfAlgebra.antipode_mul_distrib, LinearMap.rTensor_tmul, LinearMap.mul'_apply,
        Derivation.leibniz, smul_add, smul_smul]
      simp only [mul_comm, mul_left_comm]

/-- The invariant derivative is an `ε`-derivation: `D(xy) = ε(x) D(y) + ε(y) D(x)`. In particular
it kills every product of two elements of the augmentation ideal. -/
lemma invariantAux_mul (x y : A) :
    invariantAux d (x * y) =
      Coalgebra.counit (R := R) x • invariantAux d y +
        Coalgebra.counit (R := R) y • invariantAux d x := by
  rw [invariantAux_apply, Bialgebra.comul_mul, antipodeAux_mul,
    HopfAlgebra.mul_antipode_rTensor_comul_apply, HopfAlgebra.mul_antipode_rTensor_comul_apply]
  simp [algebraMap_smul]

@[simp] lemma invariantAux_one : invariantAux d 1 = 0 := by
  rw [invariantAux_apply, Bialgebra.comul_one, Algebra.TensorProduct.one_def, antipodeAux_tmul,
    HopfAlgebra.antipode_one, one_smul, Derivation.map_one_eq_zero]

lemma invariantAux_algebraMap (r : R) : invariantAux d (algebraMap R A r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, invariantAux_one, smul_zero]

/-- The derivation is recovered from its invariant derivative: `d a = ∑ a₍₁₎ · D(a₍₂₎)`. This is
coassociativity followed by the antipode axiom `∑ a₍₁₎ S(a₍₂₎) = ε(a) · 1` and counitality. -/
lemma invariantAct_comul (a : A) : invariantAct d (Coalgebra.comul (R := R) a) = d a := by
  have e1 : invariantAct d = antipodeAux3 d ∘ₗ (Coalgebra.comul (R := R)).lTensor A := by
    ext x y
    simp [invariantAux]
  have e2 : antipodeAux3 d ∘ₗ (TensorProduct.assoc R A A A).toLinearMap =
      actAux d ∘ₗ (LinearMap.mul' R A ∘ₗ (antipode R).lTensor A).rTensor A := by
    ext x y z
    simp [smul_smul]
  calc invariantAct d (Coalgebra.comul (R := R) a)
      = antipodeAux3 d ((Coalgebra.comul (R := R)).lTensor A (Coalgebra.comul (R := R) a)) := by
        rw [e1]; rfl
    _ = antipodeAux3 d (TensorProduct.assoc R A A A
          ((Coalgebra.comul (R := R)).rTensor A (Coalgebra.comul (R := R) a))) := by
        rw [Coalgebra.coassoc_apply]
    _ = actAux d ((LinearMap.mul' R A ∘ₗ (antipode R).lTensor A).rTensor A
          ((Coalgebra.comul (R := R)).rTensor A (Coalgebra.comul (R := R) a))) := by
        simpa using LinearMap.congr_fun e2
          ((Coalgebra.comul (R := R)).rTensor A (Coalgebra.comul (R := R) a))
    _ = actAux d ((LinearMap.mul' R A ∘ₗ (antipode R).lTensor A ∘ₗ
          (Coalgebra.comul (R := R))).rTensor A (Coalgebra.comul (R := R) a)) := by
        simp only [LinearMap.rTensor_comp, LinearMap.comp_apply]
    _ = actAux d ((Algebra.linearMap R A ∘ₗ (Coalgebra.counit (R := R) (A := A))).rTensor A
          (Coalgebra.comul (R := R) a)) := by
        rw [HopfAlgebra.mul_antipode_lTensor_comul]
    _ = d a := by
        rw [LinearMap.rTensor_comp, LinearMap.comp_apply, Coalgebra.rTensor_counit_comul]
        simp

/-- **Every derivation of a Hopf algebra with idempotent augmentation ideal vanishes.** -/
theorem derivation_eq_zero
    (h : Bialgebra.augmentationIdeal R A ^ 2 = Bialgebra.augmentationIdeal R A) : d = 0 := by
  have hI : ∀ a ∈ Bialgebra.augmentationIdeal R A, invariantAux d a = 0 := by
    intro a ha
    rw [← h, sq] at ha
    refine Submodule.mul_induction_on ha ?_ ?_
    · intro y hy z hz
      rw [invariantAux_mul, Bialgebra.mem_augmentationIdeal_iff.mp hy,
        Bialgebra.mem_augmentationIdeal_iff.mp hz, zero_smul, zero_smul, add_zero]
    · intro y z hy hz
      rw [map_add, hy, hz, add_zero]
  have hall : invariantAux d = 0 := by
    ext a
    have hsplit : a = algebraMap R A (Coalgebra.counit (R := R) a) +
        (a - algebraMap R A (Coalgebra.counit (R := R) a)) := by ring
    rw [hsplit, map_add, invariantAux_algebraMap,
      hI _ (Bialgebra.sub_algebraMap_counit_mem_augmentationIdeal a), add_zero]
    rfl
  have hact : invariantAct d = 0 := by
    ext x y
    simp [hall]
  ext a
  rw [← invariantAct_comul d a, hact]
  simp

/-- **A Hopf algebra with idempotent augmentation ideal is formally unramified.**

Together with `Bialgebra.augmentationIdeal_sq_eq_of_formallyUnramified` this is the group-scheme
dictionary "unramified ⟺ the cotangent space at the identity vanishes", over an arbitrary base
and with no finiteness hypothesis. -/
theorem formallyUnramified_of_augmentationIdeal_sq_eq
    (h : Bialgebra.augmentationIdeal R A ^ 2 = Bialgebra.augmentationIdeal R A) :
    Algebra.FormallyUnramified R A := by
  have hD : (KaehlerDifferential.D R A) = 0 := derivation_eq_zero _ h
  refine ⟨⟨fun x y => ?_⟩⟩
  suffices h0 : ∀ z : Ω[A⁄R], z = 0 by rw [h0 x, h0 y]
  intro z
  have hz : z ∈ (⊤ : Submodule A Ω[A⁄R]) := Submodule.mem_top
  rw [← KaehlerDifferential.span_range_derivation] at hz
  induction hz using Submodule.span_induction with
  | mem w hw => obtain ⟨a, rfl⟩ := hw; rw [hD]; rfl
  | zero => rfl
  | add u v _ _ hu hv => rw [hu, hv, add_zero]
  | smul c u _ hu => rw [hu, smul_zero]

end Invariant

/-! ### `(R3)`: an extension of multiplicative type by multiplicative type -/

section R3

variable {R : Type u} {A'' : Type v} {A : Type w} {A' : Type x}
variable [CommRing R] [CommRing A''] [CommRing A] [CommRing A']
variable [HopfAlgebra R A''] [HopfAlgebra R A] [HopfAlgebra R A']

/-- A finite flat commutative group scheme is **of multiplicative type** when its Cartier dual is
étale. Over a strictly henselian base this is equivalent to being diagonalizable, i.e. to being a
product of `μ_n`'s — which is the form `Family.lean` uses ("the corner group-likes generate the
corner").

Taking this as the *definition* is what makes `(R3)` an assembly rather than an argument: the
multiplicative statement becomes the étale statement about the dual, and duality being exact
transports the short exact sequence across. -/
def IsMultiplicativeType (R : Type u) (A : Type v) [CommRing R] [CommRing A] [HopfAlgebra R A]
    [IsCocomm R A] [Module.Finite R A] [Module.Free R A] : Prop :=
  Algebra.Etale R (CartierDual R A)

/-- **A finite free Hopf algebra with idempotent augmentation ideal is étale.**

`Module.Finite` and `Module.Free` supply the finite presentation (a finite projective module is
finitely presented, and a module-finitely-presented algebra is algebra-finitely-presented) and the
flatness; `formallyUnramified_of_augmentationIdeal_sq_eq` supplies `Ω[A⁄R] = 0`; the remaining
`H¹` vanishing is mathlib's `Algebra.Etale.of_formallyUnramified_of_flat` (Stacks
[08WD](https://stacks.math.columbia.edu/tag/08WD) `(3) => (1)`, equivalently
[00UU](https://stacks.math.columbia.edu/tag/00UU)). -/
theorem etale_of_augmentationIdeal_sq_eq [Module.Finite R A] [Module.Free R A]
    (h : Bialgebra.augmentationIdeal R A ^ 2 = Bialgebra.augmentationIdeal R A) :
    Algebra.Etale R A := by
  have := formallyUnramified_of_augmentationIdeal_sq_eq (A := A) h
  have : Module.FinitePresentation R A := Module.finitePresentation_of_projective R A
  exact Algebra.Etale.of_formallyUnramified_of_flat

/-- **The étale half of `(R3)`: an extension of étale by étale is étale.**

If `1 → Spec A' → Spec A → Spec A'' → 1` is short exact and both `Spec A'` and `Spec A''` are
étale over the base, then so is `Spec A`.

PROVEN over an **arbitrary** base, and now unconditionally: the single commutative-algebra input
("flat + unramified + finitely presented is étale", Stacks 00UU) is mathlib's
`Algebra.Etale.of_formallyUnramified_of_flat`, not a leaf of this development. The route is *not*
the torsor argument this docstring used to advertise, and no descent statement is needed:

* étale forces the augmentation ideals of `A''` and `A'` to be idempotent
  (`Bialgebra.augmentationIdeal_sq_eq_of_formallyUnramified`);
* idempotence is extension-closed, by three lines of ideal theory
  (`IsShortExact.augmentationIdeal_sq_eq`) — this is where the short exact sequence is consumed,
  through `surjective` and `ker_eq` only;
* an idempotent augmentation ideal makes every derivation of `A` vanish, by translating it back to
  the identity with the antipode (`derivation_eq_zero`), so `A` is formally unramified;
* finite free gives flatness and finite presentation, and the mathlib lemma above converts that
  into étaleness.

Note the faithful flatness field of `IsShortExact` is *not* used: the argument only needs that
`Spec A'` is the scheme-theoretic kernel of a surjection. The **henselian local** route recorded
in `Family.lean` (`Bialgebra.exists_connected_counit_idempotent`, connected component of the
identity) is therefore not needed either, and specialising to that base is not required. -/
theorem etale_of_isShortExact [IsCocomm R A''] [IsCocomm R A] [IsCocomm R A']
    [Module.Finite R A''] [Module.Free R A''] [Module.Finite R A] [Module.Free R A]
    [Module.Finite R A'] [Module.Free R A']
    {i : A'' →ₐc[R] A} {π : A →ₐc[R] A'} (h : IsShortExact i π)
    (h'' : Algebra.Etale R A'') (h' : Algebra.Etale R A') :
    Algebra.Etale R A := by
  haveI := h''
  haveI := h'
  refine etale_of_augmentationIdeal_sq_eq (h.augmentationIdeal_sq_eq ?_ ?_)
  · exact Bialgebra.augmentationIdeal_sq_eq_of_formallyUnramified
  · exact Bialgebra.augmentationIdeal_sq_eq_of_formallyUnramified

/-- **`(R3)`: an extension of multiplicative type by multiplicative type is of multiplicative
type.** This is the requirement that
`exists_unramified_grouplike_family_generating_corner` consumes, and — with the definition of a
short exact sequence pinned as above and multiplicative type *defined* as "the dual is étale" —
it is a two-line assembly: dualise the sequence with `IsShortExact.cartierDual`, which exchanges
the roles of `A''` and `A'`, and apply the étale half to the dual sequence.

PROVEN, modulo its two inputs. That this proof is three symbols long is the evidence that the
definition of `IsShortExact` above really is pinned by its consumer: any other placement of the
faithful-flatness and kernel conditions would leave a mismatch here. -/
theorem isMultiplicativeType_of_isShortExact
    [IsCocomm R A''] [IsCocomm R A] [IsCocomm R A']
    [Module.Finite R A''] [Module.Free R A''] [Module.Finite R A] [Module.Free R A]
    [Module.Finite R A'] [Module.Free R A']
    {i : A'' →ₐc[R] A} {π : A →ₐc[R] A'} (h : IsShortExact i π)
    (h'' : IsMultiplicativeType R A'') (h' : IsMultiplicativeType R A') :
    IsMultiplicativeType R A :=
  etale_of_isShortExact h.cartierDual h' h''

end R3

end HopfAlgebra
