/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Fermat.FLT.Mathlib.RingTheory.HopfAlgebra.CartierDual
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Etale.Basic

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
   side `HopfAlgebra.etale_of_isShortExact`.

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
* `etale_of_isShortExact` is stated over an **arbitrary** base `R`, and it is true there: `G → G''`
  is an fppf torsor under the étale `G'`, hence étale after the faithfully flat base change
  `G → G''` trivialising it, hence étale by fppf descent of étaleness; and `G'' → S` is étale by
  hypothesis. The *elementary* route recorded in `Family.lean` — `H°` maps trivially to an étale
  quotient, so `H° ⊆ H'`, and `H'` étale gives `H'° = 0` — proves the same statement but needs
  `R` henselian local for the connected component to exist
  (`Bialgebra.exists_connected_counit_idempotent`, already in this cone). Specialising the
  statement to a henselian local `R` is therefore a legitimate weakening if the general form
  resists; it is *not* a correction, and the general form is not false.

## Main definitions

* `Bialgebra.augmentationIdeal R A` — the kernel of the counit, cutting out the identity section.
* `CartierDual.map f` — functoriality of Cartier duality: a bialgebra map `f : A →ₐc[R] B`
  transposes to `CartierDual R B →ₐc[R] CartierDual R A`.
* `HopfAlgebra.IsShortExact i π` — a short exact sequence of group schemes, on coordinate rings.
* `HopfAlgebra.IsMultiplicativeType R A` — the Cartier dual of `Spec A` is étale.

## Main statements

* `HopfAlgebra.IsShortExact.cartierDual` — **Cartier duality is exact**. **PROVEN** as an
  assembly of the four statements below, three of which are open.
* `HopfAlgebra.IsShortExact.apply_comp` — `π ∘ i` is `ε` followed by the unit. **PROVEN.**
* `HopfAlgebra.IsShortExact.exists_linearRetraction` — `i(A'')` is an `R`-module direct summand
  of `A`. OPEN; equivalent to the surjectivity field, and free of Hopf structure.
* `HopfAlgebra.IsShortExact.surjective_cartierDual_map` — **PROVEN** from the retraction.
* `HopfAlgebra.IsShortExact.le_ker_cartierDual` — the easy half of the dual kernel condition.
  **PROVEN**, from `apply_comp` alone.
* `HopfAlgebra.IsShortExact.ker_cartierDual_le` — the hard half. OPEN, and *gated on fppf
  descent*, which this pin does not carry.
* `HopfAlgebra.IsShortExact.faithfullyFlat_cartierDual` — OPEN; the deepest field, classically
  `Ext¹(G'', 𝔾ₘ) = 0`.
* `HopfAlgebra.etale_of_isShortExact` — étale-by-étale is étale. OPEN.
* `HopfAlgebra.isMultiplicativeType_of_isShortExact` — `(R3)`: an extension of multiplicative type
  by multiplicative type is of multiplicative type. **PROVEN** from the two above.

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

end AugmentationIdeal

end Bialgebra

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

`IsShortExact.cartierDual` is assembled below out of four statements, of which two are proven
here. The split is by *where the mathematics is*:

| statement | status | content |
| --------- | ------ | ------- |
| `exists_linearRetraction` | OPEN | `i(A'')` is an `R`-module direct summand of `A` |
| `surjective_cartierDual_map` | **PROVEN** from the above | functionals extend along `i` |
| `le_ker_cartierDual` | **PROVEN** | the easy half of the dual kernel condition |
| `ker_cartierDual_le` | OPEN | the hard half: a character trivial on `Spec A'` descends |
| `faithfullyFlat_cartierDual` | OPEN | `(Spec A)^D → (Spec A')^D` is faithfully flat |

-/

/-- **`i(A'')` is an `R`-module direct summand of `A`**: the inclusion of the sub-bialgebra
admits an `R`-linear retraction.

OPEN, and this is the module-theoretic heart of the surjectivity half of exactness of duality.
It is *equivalent* to `surjective_cartierDual_map` — `A''` is finite free over `R`, so a
retraction can be reassembled from extensions of a dual basis — so stating it this way is a
change of formulation, not a weakening.

Why it is true. `A` is faithfully flat over `i(A'')`, so `Spec A → Spec A''` is an fppf
`Spec A'`-torsor; locally on `Spec R` the torsor is trivial and the normal-basis isomorphism
`A ≅ A'' ⊗[R] A'` of `A''`-modules carries `i(A'')` to `A'' ⊗ R·1`. Since `ε_{A'} : A' → R`
splits `R·1 ⊆ A'`, the quotient `A / i(A'')` is *locally free*, hence — being finitely presented
over `R` — projective, hence the sequence `0 → i(A'') → A → A/i(A'') → 0` splits globally.
Locality is not an obstruction here precisely because it is used to establish projectivity of the
quotient, which is a local property, rather than to produce the splitting directly.

Refuting check, if this is ever doubted: exhibit a short exact sequence of finite free
commutative Hopf algebras in which `A / i(A'')` has `R`-torsion. Equivalently, exhibit a
functional on `A''` that does not extend to `A`.

Note this needs *no* finiteness or freeness over `R` to state, and the freeness enters only
through the proof; it is stated in the `Dual` section only because that is where it is used. -/
theorem IsShortExact.exists_linearRetraction (h : IsShortExact i π) :
    ∃ r : A →ₗ[R] A'', ∀ a : A'', r (i a) = a := sorry

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

/-- **The hard half of the dual kernel condition**: a functional on `A` vanishing on the
sub-bialgebra `i(A'')` lies in the ideal of `CartierDual R A` generated by
`(CartierDual.map π) (ker ε_{CartierDual R A'})`.

OPEN. In functor-of-points language this is exactness of
`1 → (Spec A'')^D → (Spec A)^D → (Spec A')^D` at the middle term: a character of `Spec A`
that is trivial on the subgroup `Spec A'` factors through the fppf quotient
`Spec A / Spec A' = Spec A''`. That factorisation is **fppf descent along the faithfully flat
`Spec A → Spec A''`**, and the descent statement for modules is *not in this pin* — the same gap
`CartierDual.lean`'s "What remains" section records as the reason a definition of the quotient
could not be written there. So this leaf is gated on descent, not merely hard.

What is available, and what is not:

* the image of `CartierDual.map π` is exactly `Ann(ker π)` (transpose of a surjection), and
  `(CartierDual.map π) (ker ε) = Ann(ker π) ∩ Ann(1)` as an `R`-submodule — that much is
  elementary;
* the ideal generated by that submodule is taken in the **convolution** ring structure of
  `CartierDual R A`, which is where the elementary description stops, and where the comodule
  decomposition `A ≅ A'' ⊗[R] A'` is spent.

Refuting check: the reverse inclusion `IsShortExact.le_ker_cartierDual` is proven, so a
counterexample would be a `φ : A →ₗ[R] R` killing `i(A'')` that is not a convolution combination
of pullbacks along `π`; over a field the rank count `rk A = rk A'' * rk A'` makes both sides free
of rank `rk A - rk A''`, so any counterexample must use a non-local base. -/
theorem IsShortExact.ker_cartierDual_le (h : IsShortExact i π) :
    RingHom.ker ((CartierDual.map i).toAlgHom.toRingHom :
        CartierDual R A →+* CartierDual R A'')
      ≤ Ideal.map ((CartierDual.map π).toAlgHom.toRingHom :
          CartierDual R A' →+* CartierDual R A)
          (Bialgebra.augmentationIdeal R (CartierDual R A')) := sorry

/-- **`(Spec A)^D → (Spec A')^D` is faithfully flat.**

OPEN, and this is the deepest of the three fields: it is the statement that Cartier duality turns
the closed immersion `Spec A' ↪ Spec A` into an fppf quotient, i.e. that every character of the
subgroup `Spec A'` extends fppf-locally to `Spec A`. Classically (Tate, *Finite flat group
schemes*, §2) this is `Ext¹(G'', 𝔾ₘ) = 0` for finite flat `G''`, proven by exhibiting
`CartierDual R A` as a *free* `CartierDual R A'`-module on a basis dual to an
`R`-basis of `A''` — the linear dual of the normal-basis decomposition `A ≅ A'' ⊗[R] A'`.

Refuting check: `RingHom.FaithfullyFlat` unfolds to `Module.FaithfullyFlat` along
`(CartierDual.map π).toAlgebra`, so a refutation would be a maximal ideal `m` of
`CartierDual R A'` with `m • CartierDual R A = ⊤`; over a base field this is impossible because
the module is free of rank `rk A''`, so any counterexample must use a non-local base. -/
theorem IsShortExact.faithfullyFlat_cartierDual (h : IsShortExact i π) :
    RingHom.FaithfullyFlat ((CartierDual.map π).toAlgHom.toRingHom :
      CartierDual R A' →+* CartierDual R A) := sorry

/-- **Cartier duality is exact.**

If `1 → Spec A' → Spec A → Spec A'' → 1` is short exact, then so is the dual sequence
`1 → (Spec A'')^D → (Spec A)^D → (Spec A')^D → 1`; on coordinate rings the maps are the
transposes `CartierDual.map π` and `CartierDual.map i`, in that order, which is exactly the
`(i, π)` shape of `IsShortExact` with `A''` and `A'` exchanged.

This is Tate, *Finite flat group schemes*, §2, and Demazure–Gabriel II §1; the essential input is
that a finite locally free Hopf algebra in a short exact sequence is *free* over the sub-Hopf
algebra, so that `A ≅ A'' ⊗[R] A'` as an `A''`-comodule, and the linear dual of that
decomposition supplies all three conditions at once.

PROVEN as an assembly of the four statements above; the remaining mathematics is in the three of
them that are open. Note that the kernel condition is now half proven
(`IsShortExact.le_ker_cartierDual`), and that the surjectivity field is reduced to a pure module
statement about `A` (`IsShortExact.exists_linearRetraction`) with no Hopf structure left in
it. -/
theorem IsShortExact.cartierDual (h : IsShortExact i π) :
    IsShortExact (CartierDual.map π) (CartierDual.map i) :=
  ⟨h.faithfullyFlat_cartierDual, h.surjective_cartierDual_map,
    le_antisymm h.ker_cartierDual_le h.le_ker_cartierDual⟩

end Dual

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

/-- **The étale half of `(R3)`: an extension of étale by étale is étale.**

If `1 → Spec A' → Spec A → Spec A'' → 1` is short exact and both `Spec A'` and `Spec A''` are
étale over the base, then so is `Spec A`.

OPEN, and elementary in the sense recorded in `Family.lean`: `Spec A → Spec A''` is an fppf torsor
under `Spec A'`, and a torsor under an étale group scheme is étale (trivialise it along the
faithfully flat `Spec A → Spec A''` itself, where it becomes `Spec A' × Spec A → Spec A`, then
descend); `Spec A'' → Spec R` is étale by hypothesis; compose.

Over a **henselian local** `R` there is the shorter route `Family.lean` names, and both halves of
its machinery are already in this cone: the connected component `H°` of `Spec A` maps to the étale
`Spec A''` by a homomorphism out of a connected scheme, hence trivially, so `H° ⊆ Spec A'`; and
`Spec A'` étale forces `(Spec A')° = 0`, whence `H° = 0` and `Spec A` is étale. The connected
idempotent is `Bialgebra.exists_connected_counit_idempotent`, and the splitting of a finite algebra
over a henselian local ring is recorded in the supply survey under
`exists_unramified_grouplike_family_generating_corner`. Specialising this statement by adding
`[IsLocalRing R] [HenselianLocalRing R]` is a legitimate weakening for `(R3)`'s purposes, since
that is the base `(R3)` runs over; the general statement above is nevertheless true. -/
theorem etale_of_isShortExact [IsCocomm R A''] [IsCocomm R A] [IsCocomm R A']
    [Module.Finite R A''] [Module.Free R A''] [Module.Finite R A] [Module.Free R A]
    [Module.Finite R A'] [Module.Free R A']
    {i : A'' →ₐc[R] A} {π : A →ₐc[R] A'} (_h : IsShortExact i π)
    (_h'' : Algebra.Etale R A'') (_h' : Algebra.Etale R A') :
    Algebra.Etale R A :=
  sorry

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
