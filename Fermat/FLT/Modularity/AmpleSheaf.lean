/-
Modularity/AmpleSheaf.lean — own work for the Fermat project (not vendored
from the FLT project).

# Tensor powers, non-vanishing loci and AMPLE sheaves of modules

This module exists for exactly one consumer: the leaf
`isQuasiAffine_ker_mulByNat_of_isAlgClosed` in
`Modularity/AbelianSchemeIsogeny.lean` — "`ker[p]` is a quasi-affine scheme
over an algebraically closed field of characteristic `p`", the residue of
"`[p]` is an isogeny", classically proved by Mumford *Abelian Varieties* §6,
Application 2 of the THEOREM OF THE CUBE.

## Why this module exists now, and did not before

That leaf's docstring carried, until 2026-07-27, a recorded verdict that the
cut below was **not available**:

> the operative fact is stronger and it is what decides feasibility: **there
> is no monoidal structure on sheaves of modules over a scheme, so `L^{⊗n}`
> cannot even be WRITTEN.** … stating the interface faithfully means defining
> tensor powers of invertible sheaves — a mathlib-scale build (monoidal
> `SheafOfModules`, then invertibility, then ampleness), not a task-scale one.

The first clause of that verdict is now **FALSE**, and the refuting check is
one grep: `Fermat.modTensor` in `ModularCurve/RelativePicard.lean` supplies the
object part of the tensor product of two `𝒪_Z`-modules, by SHEAFIFYING the
presheaf tensor product (`PresheafOfModules.Monoidal.tensorObj` — the pin does
have a monoidal structure on *presheaves* of modules).  Together with
`Fermat.modPullback` (a wrapper on `Scheme.Modules.pullback`) and
`Fermat.IsInvertibleSheaf`, that is enough to WRITE `L^{⊗n}`, `[n]^* L`, and
hence the cube's output `[n]^* L ≅ L^{⊗ n²}`.  The remaining
statement-level gap was **ampleness**, and this module closes it: see
`IsAmpleSheaf` below, whose plumbing was verified to elaborate on 2026-07-27.

The verdict's *conclusion* — that this is a theory build and not a task — is
unchanged and is not disputed here.  What changed is that the theory is now a
list of NAMED LEAVES with honest statements, instead of a wall.

## What is proven here and what is left open

**Update 2026-07-27 (second pass).  All six of the original sheaf-theoretic
leaves are now PROVEN**, on top of four smaller named ones.  The route that
closed them is worth recording, because it refutes a second recorded verdict:

> `modTensor` is deliberately object-only … the ASSOCIATOR is the genuinely
> missing piece, and it is the statement that sheafification is monoidal.

Only the last clause survives.  `PresheafOfModules (R ⋙ forget₂ CommRingCat
RingCat)` is a **full symmetric monoidal category at this pin**
(`Mathlib/Algebra/Category/ModuleCat/Presheaf/Monoidal.lean` — `tensorHom`,
associator, both unitors, braiding), and `PresheafOfModules.sheafification` is
a **left adjoint whose counit is an iso** (`sheafificationAdjunction`, plus the
`IsIso` instance in `Presheaf/Sheafification.lean`).  Consequently:

* FUNCTORIALITY of `modTensor` is free — `modTensorMapIso` below;
* both UNITORS are free — `a(𝟙 ⊗ M) ≅ a(M) ≅ M`; only the left one is kept
  (`modTensorUnitLeftIso`), since nothing here consumes the right one and this
  project does not allow free-floating declarations;
* the ASSOCIATOR is *not*, and is the only one of the three that is a real
  theorem.

**Update 2026-07-28.  `nonempty_modTensor_assoc` is now PROVEN**, by the route
its own docstring named and called untried: `PresheafOfModules.sheafification`
is a LOCALIZATION functor (`ModuleCat/Sheaf/Localization.lean`), so
`CategoryTheory.LocalizedMonoidal` transports the presheaf-level monoidal
structure to `Z.Modules` as soon as the inverted class `modLocW Z` is
compatible with `⊗`.  That compatibility is `MorphismProperty.IsMonoidal`, its
right-whiskering half follows from its left-whiskering half by the braiding,
and what was left was ONE leaf, `modLocW_whiskerLeft` — TENSORING PRESERVES
LOCAL ISOMORPHISMS.

**Update 2026-07-28 (fourth pass).  `modLocW_whiskerLeft` is now PROVEN**, so
`MorphismProperty.IsMonoidal (modLocW Z)` and with it the whole localized
monoidal structure are unconditional.  The proof is elementary and lives in
`Fermat/FLT/Mathlib/Algebra/Category/ModuleCat/Presheaf/MonoidalW.lean`, stated
for an arbitrary site: neither of the two theories the old docstring named as
prerequisites (`MonoidalClosed (PresheafOfModules R)`; a monoidal stalk functor)
is needed.  What is needed is the EQUATIONAL CRITERION FOR VANISHING without
mathlib's "the `mᵢ` generate `M`" hypothesis, which that file supplies as
`Fermat.SheafificationMonoidal.exists_relations`.

Similarly, `nonempty_modPullback_modUnit` turned out to be **free from the
pin**, contradicting the recorded note that finality of `Opens.map f` "is not
automatic".  It *is* automatic: `StructuredArrow U (Opens.map g)` has `⊤` as a
TERMINAL object (`U ≤ f ⁻¹ᵁ ⊤` always), hence is connected, hence
`(Opens.map g).Final`, hence `SheafOfModules.pullbackObjUnitToUnit` is an
isomorphism by mathlib's own instance.  See `opensMapFinal` below.

PROVEN (free from the pin): `modPullbackCompIso`, `modPullbackCongrIso`,
`modPullbackMapIso` — pseudo-functoriality of `modPullback`, straight off
`Scheme.Modules.pullbackComp` / `pullbackCongr` / `Functor.mapIso`.

PROVEN here, in the tensor/ampleness API: `modTensorMapIso`,
`modTensorUnitLeftIso`, `modTensorPowMapIso`,
`modTensorPowUnitIso`, `modPullbackUnitIso`, `trivializedSection_of_iso`,
`nonvanishingAt_of_iso`, `nonvanishingLocus_of_iso`, `unitEndoApply_eq`,
`trivializedSection_restrictUnitIso`, `trivializedSection_trans`,
`nonvanishingLocus_modUnit` (the transition-function computation, which was the
only remaining obligation of `isQuasiAffine_of_isAmpleSheaf_modUnit`), and —
derived from the four leaves below — all six original statements
(`isAmpleSheaf_of_iso`, `isAmpleSheaf_modTensorPow`, `isAmpleSheaf_modPullback`,
`isQuasiAffine_of_isAmpleSheaf_modUnit`, `nonempty_modPullback_modTensorPow`,
`nonempty_modPullback_modUnit`).

**Update 2026-07-28 (third pass).**  Two of those four are now PROVEN, over a
TRIVIALIZATION CALCULUS (`§ Restriction of a trivialization` and
`§ Well-definedness` below) and four smaller named leaves.  The headline is a
FAITHFULNESS VERDICT that had been recorded as an open risk:

> **`nonvanishingLocus_modPullback_of_isAmpleSheaf` and `exists_tensorPowSection`
> are BOTH FAITHFUL AS STATED.  The numerical-semigroup worry is real, and it
> does not make either statement false; it is bridged by the classical theorem
> that an INVERTIBLE sheaf of modules is LOCALLY FREE OF RANK ONE (Stacks 01CV,
> Hartshorne II.6.12), isolated here as the single leaf
> `exists_trivialization_of_modTensorPow`.**

The reasoning is written out at `isInvertibleSheaf_of_isAmpleSheaf`.  Two
consequences of the verdict are worth pulling forward, because they change what
a prover should do:

* `exists_tensorPowSection`'s `V` and `hloc` turn out to be **inert** — the
  statement `nonvanishingLocus (A^{⊗k}) (s^{⊗k}) = nonvanishingLocus A s` is
  true with no hypothesis on `A` at all (`nonvanishingLocus_tensorPowSection`),
  and `exists_tensorPowSection` is a one-line corollary.  The FAITHFULNESS note
  that used to stand on it — "a version stated without `V` and `hloc` should be
  treated as unproven-and-suspect" — was right that `hloc` is not what saves the
  `⊆` direction, and wrong that anything is lost by dropping it: Stacks 01CV is
  what saves it, and it needs no `V`.
* `nonvanishingLocus_modPullback_of_isAmpleSheaf` needs **neither**
  `[IsClosedImmersion f]` **nor** `hn` **nor** `hV`.  Basic opens pull back along
  ANY morphism of schemes (`Scheme.preimage_basicOpen`), so the residue-field
  argument the closed immersion was there to supply is not needed.  The three
  hypotheses are kept (they cost the consumer nothing and removing them would
  churn the call site) but the unused ones are underscore-prefixed.

OPEN.  `modLocW_whiskerLeft` — SHEAFIFICATION IS MONOIDAL — used to head this
list; it is PROVEN as of 2026-07-28, and with it every associativity statement
in the module (`nonempty_modTensor_assoc`, `nonempty_modTensorPow_add`,
`nonempty_modTensorPow_mul`, `isAmpleSheaf_modTensorPow`).  What remains is
listed below, with the entries that have since been PROVEN kept in place for
the notes they carry — read the `PROVEN` marks, not a count.  One is an
original leaf:

* `exists_modPushforwardTensorPre` and `isIso_modPullbackTensorComparison` —
  monoidality of `f^*` on objects, which used to be the single leaf
  `exists_modPullback_modTensor`.

  **PROVEN 2026-07-29** (`flt-lean-346`): the comparison map is now WRITTEN
  (`modPullbackTensorComparison`, the transpose of `(η ⊗ η) ≫ ν`), its section
  identity `f^*(a ⊗ b) = f^*a ⊗ f^*b` is a THEOREM about it
  (`modPullbackTensorComparison_tensorSection`), and
  `exists_modPullback_modTensor` — statement unchanged, so no consumer moved —
  is three lines over the two.  Net sorry count is unchanged (1 → 2) but both
  successors are canonical and fully pinned, and they split PLUMBING from
  MATHEMATICS:
  - `exists_modPushforwardTensorPre` is the lax monoidal structure map of `f_*`
    at presheaf level, pinned on pure tensors over EVERY open (hence unique).
    It contains no mathematics; it is mathlib's missing
    `(PresheafOfModules.restrictScalars α).LaxMonoidal`, objectwise.
    **PROVEN 2026-07-30** — and objectwise is all it needed: the instance itself
    was never built.  See its docstring for the one real obstacle, which is a
    `CommRing` re-keying and not any part of the bilinearity the route audit
    warned about.
  - `isIso_modPullbackTensorComparison` is all of the mathematics.  The
    open-immersion case — which is what everything below actually consumes — is
    strictly easier and should be done first; see its docstring.

  Historical note: the leaf was `nonempty_modPullback_modTensor`, a bare
  `Nonempty`, which pins no isomorphism at all — post-composing a witness with
  multiplication by a unit of `Γ(X, ⊤)` satisfies every clause while scaling
  every trivialized section.  That defect is now structurally impossible: an
  `IsIso` on a named map has nothing to choose.

The rest came out of the trivialization calculus, each strictly smaller than the
leaf it came out of:

* `exists_trivialization_of_modTensorPow` — **the mathematical one**: Stacks
  01CV, the semigroup bridge.  It is the only entry in this list that is not
  bookkeeping.  **PROVEN 2026-07-29** by reduction (one line, since
  `modTensorPow A (j+1)` IS `modTensor A (modTensorPow A j)`) to the classical
  TWO-FACTOR statement `exists_trivialization_of_modTensor_trivial`, which is
  where the mathematics and the corrected route audit now live.
* `exists_trivialization_tensorPow` — `s^{⊗k}` read through the `k`-th power of
  a trivialization is the `k`-th power of the trivialized section.  **PROVEN
  2026-07-28**, by induction, over ONE new leaf `exists_trivialization_modTensor`
  ("a trivialization of a tensor product multiplies sections").  That cut is a
  CORRECTION: the route recorded here relied on reading `trivializedSection`
  through the anonymous iso supplied by `nonempty_restrict_modTensor`, which pins
  nothing — see that leaf's docstring for the unit-scaling counterexample.
* `exists_trivialization_modTensor` — the new leaf just described.  **PROVEN
  2026-07-29**, in the `§ The CANONICAL trivialization of a tensor product`
  block: the anonymous iso is used there for EXISTENCE only, and the value comes
  from a canonical morphism built out of the sheafification adjunction, so the
  unit-scaling ambiguity never arises.
* `exists_trivialization_modPullback` — the same for `f^*`.  **PROVEN 2026-07-28**
  over a five-lemma calculus for the pullback of a global section through the
  canonical comparison isomorphisms, and a `trivializationOfPullback` that is now
  real code rather than an `∃`.  See `trivializedSection_trivializationOfPullback`.
* `trivializedSection_trivializationOfLE` — **PROVEN 2026-07-28.**  It was never
  mathematics; it was blocked by `modRestrictLEIso` being routed through
  `modPullback`.  Rerouting that through mathlib's `restrictFunctorCongr` +
  `restrictFunctorComp` (both `app`s are `rfl`) closed it.  Two owners found
  exactly this reroute independently and wrote the SAME definition; the proof
  kept here is the one that was already on `main`.

**Update 2026-07-29 (Picard block).**  The Picard-group block at the end of
this file added one leaf on 2026-07-28 — `exists_modDual`, the dual sheaf `L^∨`
together with its evaluation pairing `L ⊗ L^∨ ⟶ 𝒪_Z`, asked for only up to
LOCAL isomorphy of that one global map — and that leaf, its consumer, and
`isIso_of_locally_isIso` have since been HOISTED to
`ModularCurve/RelativePicard.lean`, which is UPSTREAM of this module and states
the same inverse theorem (`exists_modTensor_inv`) for its own calculus.  So this
module's warning set is back to six.  Read `exists_modDual`'s docstring, now
upstream, before attacking it: it records that mathlib has
no internal `Hom` on (pre)sheaves of modules at this pin, that the "just glue
the inverse cocycle" route is NOT cheap (mathlib's `Sites/Descent/IsStack.lean`
has no instances, so `Scheme.Modules` is not known to be a stack), and which
construction does avoid both obstructions.

## A note on the definition of ampleness

`NonvanishingAt L s z` is stated through the LOCAL TRIVIALIZATIONS of `L`
rather than through stalks, because `Scheme.Modules` has no `Module` structure
on stalks at this pin (`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean` has
`stalkFunctor` only through the underlying `Ab`-presheaf).  The `∃`
formulation is FAITHFUL without any well-definedness lemma: if `s` generates
`L` at `z` then every trivialization near `z` witnesses it, and conversely a
trivialization sending `s` to a unit at `z` exhibits `s` as a generator.  The
well-definedness IS needed to *prove* things about the locus, which is why it
is named above as an obligation of
`isQuasiAffine_of_isAmpleSheaf_modUnit` rather than smuggled into the
definition.
-/
module

public import Fermat.FLT.ModularCurve.RelativePicard
public import Fermat.FLT.Mathlib.Algebra.Category.ModuleCat.Presheaf.MonoidalW
public import Mathlib.CategoryTheory.Localization.Monoidal.Basic
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open TopologicalSpace MonoidalCategory Opposite

namespace Fermat

/-! ### Tensor powers -/

/-- **Tensor powers of an `𝒪_Z`-module**, `L^{⊗n}`, right-nested onto the
unit: `L^{⊗0} = 𝒪_Z` and `L^{⊗(n+1)} = L ⊗ L^{⊗n}`.

This is the object that the verdict quoted in the module docstring said could
not be written.  It can, because `modTensor` exists. -/
noncomputable def modTensorPow {Z : Scheme.{u}} (L : Z.Modules) : ℕ → Z.Modules
  | 0 => modUnit Z
  | (n + 1) => modTensor L (modTensorPow L n)

/-! ### Non-vanishing loci -/

/-- **A global section of `L`, read through a trivialization of `L` over `U`,
as an element of `Γ(U, 𝒪)`.**

The three steps are: restrict `s` from `⊤` to `U.ι ''ᵁ ⊤`, transport across
`Scheme.Modules.restrictAppIso` into the sections of `L|_U`, and apply the
trivialization.  The last identification — sections of `modUnit U` ARE
sections of `𝒪_U` — is definitional at this pin, which is why no coercion
appears. -/
noncomputable def trivializedSection {Z : Scheme.{u}} {L : Z.Modules} {U : Z.Opens}
    (φ : L.restrict U.ι ≅ modUnit (U : Scheme.{u})) (s : Γ(L, ⊤)) : Γ((U : Scheme.{u}), ⊤) :=
  φ.hom.val.app (.op ⊤)
    ((Scheme.Modules.restrictAppIso (f := U.ι) L ⊤).inv
      (L.presheaf.map (homOfLE le_top).op s))

/-- **`s` does not vanish at `z`**: some neighbourhood of `z` trivializes `L`
in such a way that `s` becomes a unit at `z`.

See the module docstring for why this `∃` form is faithful with no
well-definedness lemma, and why stalks are not used. -/
def NonvanishingAt {Z : Scheme.{u}} (L : Z.Modules) (s : Γ(L, ⊤)) (z : Z) : Prop :=
  ∃ (U : Z.Opens) (hz : z ∈ U) (φ : L.restrict U.ι ≅ modUnit (U : Scheme.{u})),
    (⟨z, hz⟩ : (U : Scheme.{u})) ∈ (U : Scheme.{u}).basicOpen (trivializedSection φ s)

/-- **The non-vanishing locus `Z_s` of a global section**, as a bare set.

It is open — a union of images of basic opens — but the openness proof is not
needed anywhere below, because `IsAmpleSheaf` names the affine open
separately and only asks that the locus EQUAL it. -/
def nonvanishingLocus {Z : Scheme.{u}} (L : Z.Modules) (s : Γ(L, ⊤)) : Set Z :=
  {z | NonvanishingAt L s z}

/-! ### Ampleness -/

/-- **`L` is AMPLE**: every point lies in the non-vanishing locus of a global
section of some positive tensor power of `L`, and that locus is affine.

This is the classical definition (EGA II 4.5.3 / Hartshorne II.7.4 for a
quasi-compact separated scheme), and it is the hypothesis under which
EGA II 5.1.2 says that a scheme with ample structure sheaf is quasi-affine.

**Not vacuous.**  `IsAmpleSheaf` is satisfiable: on an affine `Z` the unit
section of `modTensorPow (modUnit Z) 1` has non-vanishing locus `⊤`.  It is
also not trivially satisfiable — for `Z` proper over a field and of positive
dimension, `IsAmpleSheaf (modUnit Z)` is FALSE, which is precisely why the
consumer's leaf carries content. -/
def IsAmpleSheaf {Z : Scheme.{u}} (L : Z.Modules) : Prop :=
  ∀ z : Z, ∃ (n : ℕ) (_ : 0 < n) (s : Γ(modTensorPow L n, ⊤)) (V : Z.Opens),
    z ∈ V ∧ IsAffineOpen V ∧ nonvanishingLocus (modTensorPow L n) s = (V : Set Z)

/-! ### HOISTED to `ModularCurve/RelativePicard.lean` (2026-07-28)

The pseudo-functoriality of `modPullback`, the presheaf monoidal structure,
`modSheafifyValIso`, `modTensorMapIso`, `modTensorUnitLeftIso`, `opensMapFinal`,
`modPullbackUnitIso`, `modRestrictPullbackIso`, `modRestrictLEIso`,
`trivializationOfLE` and `isInvertibleSheaf_modUnit`
were declared HERE and are now declared in `RelativePicard.lean`, unchanged, and
inherited by import.  They had to move because `RelativePicard.lean`'s two
representability leaves consume them and it is UPSTREAM of this module; the
collision that revealed it was `Fermat.isInvertibleSheaf_modUnit` being declared
twice.  Nothing about them changed, so every use below still resolves. -/

/-- **Tensor powers transport along an isomorphism**: `L ≅ M` gives
`L^{⊗n} ≅ M^{⊗n}`. -/
noncomputable def modTensorPowMapIso {Z : Scheme.{u}} {L M : Z.Modules} (e : L ≅ M) :
    ∀ n : ℕ, modTensorPow L n ≅ modTensorPow M n
  | 0 => Iso.refl _
  | (n + 1) => modTensorMapIso e (modTensorPowMapIso e n)

/-- **`𝒪_Z^{⊗n} ≅ 𝒪_Z`** — iterated left unitor.  This is the "UNITOR"
obligation recorded against `isQuasiAffine_of_isAmpleSheaf_modUnit`. -/
noncomputable def modTensorPowUnitIso {Z : Scheme.{u}} :
    ∀ n : ℕ, modTensorPow (modUnit Z) n ≅ modUnit Z
  | 0 => Iso.refl _
  | (n + 1) => modTensorUnitLeftIso _ ≪≫ modTensorPowUnitIso n

/-! ### Tensor products of global sections

HOISTED 2026-07-28 from `§ Tensor powers of a global section`, which is a
thousand lines below.  The reason is `exists_modPullback_modTensor`: that leaf
states its PINNING clause in terms of `tensorSection`, so both definitions have
to precede it.  `tensorPowSection` stays where it was — it needs `unitOne`,
which needs the non-vanishing-locus material. -/

/-- The unit of the sheafification adjunction at the presheaf tensor product:
this is what turns a tensor of sections into a section of `modTensor`. -/
noncomputable def modTensorMk {Z : Scheme.{u}} (L M : Z.Modules) :
    PresheafOfModules.Monoidal.tensorObj (R := Z.presheaf) L.val M.val ⟶ (modTensor L M).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 Z.ringCatSheaf.obj)).unit.app _

/-- **`a ⊗ b` as a global section of `L ⊗ M`.**  The presheaf tensor product is
OBJECTWISE (`PresheafOfModules.Monoidal.tensorObj` sends `X` to
`M₁.obj X ⊗ M₂.obj X`), so `a ⊗ₜ b` is literally an element of it; the only step
is pushing it through the sheafification unit. -/
noncomputable def tensorSection {Z : Scheme.{u}} {L M : Z.Modules} (a : Γ(L, ⊤)) (b : Γ(M, ⊤)) :
    Γ(modTensor L M, ⊤) :=
  (modTensorMk L M).app (op ⊤) (a ⊗ₜ b)

/-! ### Pullback of a global section, and `f^* 𝒪_Y ≅ 𝒪_X` -/

/-- **The pullback of a global section**, `f^* s ∈ Γ(f^*A, ⊤)`.

Obtained from the unit `A ⟶ f_* f^* A` of the pullback/pushforward adjunction
evaluated on global sections; `Γ(f_*N, ⊤) = Γ(N, f ⁻¹ᵁ ⊤) = Γ(N, ⊤)` is
definitional. -/
noncomputable def modPullbackSection {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Y.Modules)
    (s : Γ(A, ⊤)) : Γ(modPullback f A, ⊤) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app A).val.app (op ⊤) s

/-! ### Transport of the non-vanishing locus along an isomorphism

The second obligation recorded against `isAmpleSheaf_of_iso`.  It is a
computation with `trivializedSection`: `Scheme.Modules.restrictAppIso` is
`Iso.refl` and `restrictFunctor` is a pushforward, so only the naturality of
`α` survives. -/

/-- Transporting a trivialization of `A` to one of `B` along `α : A ≅ B` leaves
the trivialized section unchanged. -/
lemma trivializedSection_of_iso {Z : Scheme.{u}} {A B : Z.Modules} (α : A ≅ B) {U : Z.Opens}
    (φ : A.restrict U.ι ≅ modUnit (U : Scheme.{u})) (s : Γ(A, ⊤)) :
    trivializedSection ((Scheme.Modules.restrictFunctor U.ι).mapIso α.symm ≪≫ φ)
      (α.hom.val.app (op ⊤) s) = trivializedSection φ s := by
  unfold trivializedSection
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  have hcomp : ∀ (x : Γ(B.restrict U.ι, ⊤)),
      ((Scheme.Modules.restrictFunctor U.ι).map α.inv ≫ φ.hom).val.app (op ⊤) x
        = φ.hom.val.app (op ⊤) (α.inv.val.app (op (U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens))) x) :=
    fun _ => rfl
  rw [hcomp]
  refine congrArg _ ?_
  have hnat := PresheafOfModules.naturality_apply α.hom.val
    (X := op (⊤ : Z.Opens)) (Y := op (U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens)))
    (homOfLE le_top).op s
  have hinv : ∀ (V : Z.Opensᵒᵖ) (y : A.val.obj V), α.inv.val.app V (α.hom.val.app V y) = y := by
    intro V y
    have : (α.hom ≫ α.inv).val.app V = 𝟙 _ := by rw [α.hom_inv_id]; rfl
    exact ConcreteCategory.congr_hom this y
  exact (congrArg _ hnat.symm).trans (hinv _ _)

/-- Non-vanishing transports along an isomorphism of sheaves. -/
lemma nonvanishingAt_of_iso {Z : Scheme.{u}} {A B : Z.Modules} (α : A ≅ B) (s : Γ(A, ⊤)) (z : Z)
    (h : NonvanishingAt A s z) : NonvanishingAt B (α.hom.val.app (op ⊤) s) z := by
  obtain ⟨U, hz, φ, hmem⟩ := h
  exact ⟨U, hz, (Scheme.Modules.restrictFunctor U.ι).mapIso α.symm ≪≫ φ,
    by rw [trivializedSection_of_iso]; exact hmem⟩

/-- **The non-vanishing locus is an invariant of the pair `(sheaf, section)` up
to isomorphism.** -/
lemma nonvanishingLocus_of_iso {Z : Scheme.{u}} {A B : Z.Modules} (α : A ≅ B) (s : Γ(A, ⊤)) :
    nonvanishingLocus B (α.hom.val.app (op ⊤) s) = nonvanishingLocus A s := by
  ext z
  constructor
  · intro h
    have h2 := nonvanishingAt_of_iso α.symm _ z h
    have e0 : (α.symm.hom.val.app (op ⊤)) ((α.hom.val.app (op ⊤)) s) = s := by
      have hh : (α.hom ≫ α.inv).val.app (op ⊤) = 𝟙 _ := by rw [α.hom_inv_id]; rfl
      exact ConcreteCategory.congr_hom hh s
    rw [e0] at h2
    exact h2
  · exact fun h => nonvanishingAt_of_iso α s z h

/-! ### SHEAFIFICATION IS MONOIDAL, via `CategoryTheory.LocalizedMonoidal`

The route recorded (and untried) in the old docstring of `nonempty_modTensor_assoc`:
pair `Mathlib/CategoryTheory/Localization/Monoidal/Basic.lean` with
`Mathlib/Algebra/Category/ModuleCat/Sheaf/Localization.lean`.  It works, and it
reduces the WHOLE associativity question to a single statement about local
isomorphisms, `modLocW_whiskerLeft` below.

The chain is:

* `PresheafOfModules.sheafification` is a LOCALIZATION functor, for the class
  `modLocW Z` of morphisms it inverts (mathlib:
  `PresheafOfModules.instIsLocalization`, or directly
  `Adjunction.isLocalization` applied to `sheafificationAdjunction`, which is
  what is used here since it avoids naming the Grothendieck topology);
* `PresheafOfModules Z.ringCatSheaf.obj` is symmetric monoidal at this pin;
* IF `modLocW Z` is compatible with `⊗` (`MorphismProperty.IsMonoidal`), then
  `CategoryTheory.LocalizedMonoidal` puts a monoidal structure on the localized
  category — which IS `Z.Modules`, as a type synonym — and makes sheafification
  a monoidal functor, with comparison isomorphism
  `Localization.Monoidal.μ : a(P) ⊗ a(Q) ≅ a(P ⊗ Q)`;
* `modTensor L M` is `a(L.val ⊗ M.val)`, and `a(M.val) ≅ M`
  (`modSheafifyValIso`), so `μ` identifies `modTensor` with the localized
  tensor product (`modTensorLocIso`), and the associator transports.

`MorphismProperty.IsMonoidal` asks for stability under BOTH whiskerings; the
right one follows from the left one by the braiding, so exactly one genuine
statement is left. -/

/-- **Local isomorphisms of presheaves of `𝒪_Z`-modules**: the morphisms that
become isomorphisms after sheafification.

Equal to `J.W.inverseImage (PresheafOfModules.toPresheaf _)` — mathlib's
`PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms` —
i.e. to the locally bijective morphisms of underlying abelian presheaves; this
formulation is used because it names no Grothendieck topology. -/
def modLocW (Z : Scheme.{u}) : MorphismProperty (PresheafOfModules.{u} Z.ringCatSheaf.obj) :=
  (MorphismProperty.isomorphisms _).inverseImage
    (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj))

/-- Sheafification is the localization of presheaves of modules at `modLocW`. -/
instance modLocW_isLocalization (Z : Scheme.{u}) :
    (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).IsLocalization (modLocW Z) :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 Z.ringCatSheaf.obj)).isLocalization

instance modLocW_isMultiplicative (Z : Scheme.{u}) : (modLocW Z).IsMultiplicative := by
  unfold modLocW; infer_instance

instance modLocW_respectsIso (Z : Scheme.{u}) : (modLocW Z).RespectsIso := by
  unfold modLocW; infer_instance

/-- Presheaves of modules over a presheaf of COMMUTATIVE rings form a symmetric
monoidal category; as with `presheafOfModulesMonoidal`, typeclass search cannot
invert the composition `Z.presheaf ⋙ forget₂ _ _` against `Z.ringCatSheaf.obj`
on its own. -/
noncomputable instance presheafOfModulesSymmetric (Z : Scheme.{u}) :
    SymmetricCategory (PresheafOfModules.{u} Z.ringCatSheaf.obj) :=
  inferInstanceAs (SymmetricCategory
    (PresheafOfModules.{u} (Z.presheaf ⋙ forget₂ CommRingCat RingCat)))

/-- **TENSORING PRESERVES LOCAL ISOMORPHISMS** — PROVEN (2026-07-28).  This is
the entire mathematical content of "sheafification is monoidal" for
`𝒪_Z`-modules: with it, `MorphismProperty.IsMonoidal (modLocW Z)` holds, and
every associativity and unit statement about `modTensor` follows formally.

Concretely: if `g` becomes an isomorphism after sheafification, so does
`X ◁ g : X ⊗ Y₁ ⟶ X ⊗ Y₂`.  Unfolded through
`PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms` and
`GrothendieckTopology.WEqualsLocallyBijective`, it says that `X ⊗ -` preserves
LOCAL BIJECTIVITY of maps of abelian presheaves.

TRUE, and standard (Stacks 01LA; Mac Lane VII).  It is NOT a formal consequence
of right exactness alone: local surjectivity of `X ◁ g` is the easy half (a
section of `X ⊗ Y₂` is a finite sum of tensors, each of whose right factors
lifts locally, and finitely many covering sieves may be intersected), while
local INJECTIVITY has to rule out a `Tor`-type contribution.

The proof lives in
`Fermat/FLT/Mathlib/Algebra/Category/ModuleCat/Presheaf/MonoidalW.lean`
(`Fermat.SheafificationMonoidal.W_whiskerLeft`), stated for an ARBITRARY site
and an arbitrary presheaf of commutative rings, so nothing here is special to
`Z.Opens`.

ROUTE ACTUALLY TAKEN, and a correction to the three routes this docstring used
to record as the only candidates.  Routes 1 and 3 were both real but both cost
a missing theory:

* the *internal hom* route (mathlib's own proof of
  `CategoryTheory.GrothendieckTopology.W.whiskerLeft` in
  `Mathlib/CategoryTheory/Sites/Monoidal.lean`) needs `MonoidalClosed
  (PresheafOfModules R)`, which is still absent from this pin — re-checked
  2026-07-28 by `grep -rn MonoidalClosed
  Mathlib/Algebra/Category/ModuleCat/{Presheaf,Sheaf}/`, which is EMPTY;
* the *stalk* route (`Mathlib/CategoryTheory/Sites/Point/IsMonoidalW.lean`
  plus `Mathlib/Topology/Sheaves/Points.lean`) needs a MONOIDAL stalk functor
  for presheaves of modules, i.e.
  `colim_{U ∋ z} (X(U) ⊗_{𝒪(U)} Y(U)) ≅ X_z ⊗_{𝒪_{Z,z}} Y_z` — a filtered
  colimit of tensor products over a filtered system of base rings, which the pin
  does not have either.

Neither is needed.  The statement is ELEMENTARY, and the one non-formal input is
the EQUATIONAL CRITERION FOR VANISHING (Stacks 00HK; Altman–Kleiman Lemma 8.16):
if `∑ᵢ xᵢ ⊗ g(yᵢ) = 0` in `X(U) ⊗_{𝒪(U)} Y₂(U)`, the vanishing is witnessed by a
finite system of relations `g(qₛ) = ∑ⱼ aₛⱼ wⱼ`, `∑ₛ aₛⱼ pₛ = 0`.  Cover `U` so
that every `wⱼ` lifts to some `vⱼ` (local surjectivity of `g`), refine so that
`qₛ − ∑ⱼ aₛⱼ vⱼ` dies (local injectivity of `g`), and on that cover
`∑ₛ pₛ ⊗ qₛ = ∑ⱼ (∑ₛ aₛⱼ pₛ) ⊗ vⱼ = 0`.

Mathlib's `TensorProduct.vanishesTrivially_of_sum_tmul_eq_zero` states the
criterion only when the `xᵢ` GENERATE the module, which is exactly what is
unavailable here (and the hypothesis is not removable: `2 ⊗ 1 = 0` in
`ℤ ⊗ ℤ/2` while `2 ⊗ 1 ≠ 0` in `2ℤ ⊗ ℤ/2`).  `SheafificationMonoidal
.exists_relations` is the general form, obtained by the same argument over a
free presentation indexed by `Fin k ⊕ M` — the `⊕` is what keeps the original
family from being identified when two `xᵢ` coincide. -/
theorem modLocW_whiskerLeft {Z : Scheme.{u}} (X : PresheafOfModules.{u} Z.ringCatSheaf.obj)
    {Y₁ Y₂ : PresheafOfModules.{u} Z.ringCatSheaf.obj} {g : Y₁ ⟶ Y₂}
    (hg : modLocW Z g) : modLocW Z (X ◁ g) := by
  have key : modLocW Z = _ :=
    (PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (𝟙 Z.ringCatSheaf.obj)).symm
  rw [key] at hg ⊢
  exact SheafificationMonoidal.W_whiskerLeft (R := Z.presheaf) X hg

/-- The right-hand whiskering, from the left-hand one by the braiding. -/
theorem modLocW_whiskerRight {Z : Scheme.{u}}
    {X₁ X₂ : PresheafOfModules.{u} Z.ringCatSheaf.obj} {f : X₁ ⟶ X₂}
    (hf : modLocW Z f) (Y : PresheafOfModules.{u} Z.ringCatSheaf.obj) :
    modLocW Z (f ▷ Y) :=
  ((modLocW Z).arrow_mk_iso_iff (Arrow.isoMk (β_ X₁ Y) (β_ X₂ Y)
    (BraidedCategory.braiding_naturality_left f Y).symm)).2 (modLocW_whiskerLeft Y hf)

instance modLocW_isMonoidal (Z : Scheme.{u}) : (modLocW Z).IsMonoidal where
  whiskerLeft X _ _ _ hg := modLocW_whiskerLeft X hg
  whiskerRight _ hf Y := modLocW_whiskerRight hf Y

/-- The unit isomorphism required by `LocalizedMonoidal`.  Nothing here consumes
the monoidal unit of the localized structure, so the tautological choice is
taken and no identification with `modUnit Z` is needed. -/
noncomputable abbrev modLocEps (Z : Scheme.{u}) :
    (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).obj
        (𝟙_ (PresheafOfModules.{u} Z.ringCatSheaf.obj)) ≅
      (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).obj
        (𝟙_ (PresheafOfModules.{u} Z.ringCatSheaf.obj)) := Iso.refl _

/-- `Z.Modules`, carrying the localized monoidal structure.  This is a TYPE
SYNONYM for `Z.Modules`, which is why `toModLM` below is the identity. -/
noncomputable abbrev ModLM (Z : Scheme.{u}) : Type (u + 1) :=
  LocalizedMonoidal (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj))
    (modLocW Z) (modLocEps Z)

/-- Sheafification, seen as a monoidal functor into `ModLM Z`. -/
noncomputable abbrev modLocA (Z : Scheme.{u}) :
    PresheafOfModules.{u} Z.ringCatSheaf.obj ⥤ ModLM Z :=
  Localization.Monoidal.toMonoidalCategory
    (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)) (modLocW Z) (modLocEps Z)

/-- An `𝒪_Z`-module, seen as an object of `ModLM Z`.  The identity; it exists
only to stop the elaborator from immediately unfolding the type synonym and
losing the monoidal instance. -/
def toModLM {Z : Scheme.{u}} (M : Z.Modules) : ModLM Z := M

/-- `modSheafifyValIso`, read in `ModLM Z`. -/
noncomputable def modSheafifyValIsoLM {Z : Scheme.{u}} (M : Z.Modules) :
    (modLocA Z).obj M.val ≅ toModLM M where
  hom := (modSheafifyValIso M).hom
  inv := (modSheafifyValIso M).inv
  hom_inv_id := (modSheafifyValIso M).hom_inv_id
  inv_hom_id := (modSheafifyValIso M).inv_hom_id

/-- **`modTensor` IS the localized monoidal product**: `a(L.val ⊗ M.val)` is
identified with `L ⊗ M` in `ModLM Z` by the monoidal-functor comparison `μ`
together with `a(M.val) ≅ M`. -/
noncomputable def modTensorLocIso {Z : Scheme.{u}} (L M : Z.Modules) :
    toModLM (modTensor L M) ≅ toModLM L ⊗ toModLM M :=
  (Localization.Monoidal.μ _ (modLocW Z) (modLocEps Z) L.val M.val).symm ≪≫
    MonoidalCategory.tensorIso (modSheafifyValIsoLM L) (modSheafifyValIsoLM M)

/-! ### The two CATEGORICAL leaves

The first of the two (the ASSOCIATOR) is PROVEN; only
`nonempty_modPullback_modTensor` remains.  Each is strictly smaller than one of
the six statements it replaced, and each
names in its docstring what it needs.  Between them they are the residue of the
ampleness theory that `Mathlib/AlgebraicGeometry/` does not have
(`grep -rl Ample Mathlib/AlgebraicGeometry/` is EMPTY at this pin — re-run it
before believing this sentence).

The other three open leaves are further down, in the trivialization calculus
that begins after `nonvanishingLocus_modUnit`; only one of them
(`exists_trivialization_of_modTensorPow`) is mathematics.
(`trivializedSection_trivializationOfLE`, the fourth, was PROVEN 2026-07-28 by
rerouting `modRestrictLEIso` through `Scheme.Modules.restrictFunctorCongr`.) -/

/-- **THE ASSOCIATOR** — PROVEN (2026-07-28): `(L ⊗ M) ⊗ N ≅ L ⊗ (M ⊗ N)` for
`𝒪_Z`-modules.

The route recorded in the previous version of this docstring — pair
`Mathlib/CategoryTheory/Localization/Monoidal/Basic.lean` with
`Mathlib/Algebra/Category/ModuleCat/Sheaf/Localization.lean` — is the one that
works; see the section above.  The whole associativity question reduces to
`modLocW_whiskerLeft` ("tensoring preserves local isomorphisms") — itself PROVEN
since 2026-07-28 — from which the localized monoidal structure, and with it this
associator, both unitors and the braiding, are formal.

Everything else about tensor powers in this file (`nonempty_modTensorPow_add`,
`nonempty_modTensorPow_mul`, and hence `isAmpleSheaf_modTensorPow`) is DERIVED
from this statement, so the module now carries NO open associativity
obligation. -/
theorem nonempty_modTensor_assoc {Z : Scheme.{u}} (L M N : Z.Modules) :
    Nonempty (modTensor (modTensor L M) N ≅ modTensor L (modTensor M N)) := by
  have e : toModLM (modTensor (modTensor L M) N) ≅ toModLM (modTensor L (modTensor M N)) :=
    modTensorLocIso (modTensor L M) N ≪≫
      MonoidalCategory.tensorIso (modTensorLocIso L M) (Iso.refl (toModLM N)) ≪≫
      α_ (toModLM L) (toModLM M) (toModLM N) ≪≫
      MonoidalCategory.tensorIso (Iso.refl (toModLM L)) (modTensorLocIso M N).symm ≪≫
      (modTensorLocIso L (modTensor M N)).symm
  exact ⟨{ hom := e.hom, inv := e.inv, hom_inv_id := e.hom_inv_id, inv_hom_id := e.inv_hom_id }⟩

/-! ### The CANONICAL comparison map `f^*(L ⊗ M) ⟶ f^*L ⊗ f^*M`

ADDED 2026-07-28/29 (`flt-lean-346`), replacing the single leaf
`exists_modPullback_modTensor` by a WRITTEN map plus two strictly smaller
obligations.  `exists_modPullback_modTensor` is now PROVEN; see its docstring.

The construction is the standard adjunction transpose and nothing more:

    f^*(L ⊗ M) ⟶ f^*L ⊗ f^*M   is the transpose of
    L ⊗ M --(η ⊗ η)--> f_*f^*L ⊗ f_*f^*M --ν--> f_*(f^*L ⊗ f^*M)

where `η` is the unit of `pullbackPushforwardAdjunction` and `ν` is the LAX
MONOIDAL structure map of `f_*`.  Writing it this way buys three things:

* the map is CANONICAL — the old `Nonempty`/`∃` form quantified over a larger
  set of isomorphisms (post-compose any witness by a unit of `Γ(X, ⊤)`), which
  is exactly the defect that forced the leaf to be restated on 2026-07-28.
  Here there is nothing to post-compose: `modPullbackTensorComparison` is a
  definition;
* the SECTION IDENTITY `f^*(a ⊗ b) = f^*a ⊗ f^*b` becomes a THEOREM about it
  (`modPullbackTensorComparison_tensorSection`) rather than a clause an
  existential is asked to carry;
* the two residues separate cleanly into PLUMBING and MATHEMATICS —
  `exists_modPushforwardTensorPre` and `isIso_modPullbackTensorComparison`.

WHY `ν` IS CUT AS A LEAF RATHER THAN WRITTEN (measured, not assumed).  The
previous route audit said "exactly ONE missing instance —
`(PresheafOfModules.restrictScalars α).LaxMonoidal` — stands between here and a
written comparison map".  That is CORRECT, and an attempt to dodge it by writing
`ν` by hand was made and FAILED for an instructive reason, recorded here so the
next owner does not repeat it.

The presheaf tensor IS objectwise (`PresheafOfModules.Monoidal.tensorObj` sends
`V` to `M₁.obj V ⊗ M₂.obj V`), so `ν` "obviously" ought to be
`ModuleCat.MonoidalCategory.tensorLift (fun a b ↦ modTensorMk (a ⊗ₜ b))`.  Its
four bilinearity obligations are where it dies: the elements `a b` are typed at
`((pushforward f).obj A).val.obj V`, whose module structure is
`ModuleCat.restrictScalars`-wrapped, while the tensor `a ⊗ₜ b` being fed to
`modTensorMk` is over `Γ(X, f ⁻¹ᵁ V)`.  Same carriers, DIFFERENT instance terms.
Consequences actually observed:

* the two ADDITIVITY obligations do go through, after a `show` that retypes the
  element (`(a : ↑(A.val.obj (op (f ⁻¹ᵁ V.unop)))) + a'`) — `rw` alone cannot,
  because the `+` it must match sits at the wrapped type;
* the two SEMILINEARITY obligations do not.  `rw`/`erw [TensorProduct.smul_tmul']`
  cannot fire: the scalar `c` lives in `Γ(Y, V)` and the pattern wants one in
  `Γ(X, f ⁻¹ᵁ V)`, and unification may not invert `Module.compHom`.  Supplying
  the scalar explicitly as `(f.app V.unop).hom c` gets the smul to elaborate but
  then `SMulCommClass` search fails — `Γ(X, f ⁻¹ᵁ V)` and
  `(X.presheaf ⋙ forget₂ CommRingCat RingCat).obj (op (f ⁻¹ᵁ V))` are the SAME
  ring in two spellings and the instance is not found across them.
  `erw [← map_smul]; rfl` does reduce the goal to a syntactic identity but
  spawns `SMulCommClass`/`SMul` side goals between the `X`- and `Y`-rings for
  which no instance exists (and should not).

That plumbing is precisely what the missing `LaxMonoidal` instance packages —
mathlib's `ModuleCat.restrictScalars` already has it
(`Mathlib/Algebra/Category/ModuleCat/Monoidal/Adjunction.lean`, with
`restrictScalars_μ_tmul : μ (restrictScalars f) M₁ M₂ (m₁ ⊗ₜ m₂) = m₁ ⊗ₜ m₂`),
and lifting it objectwise to `PresheafOfModules.restrictScalars` is the honest
way in.  Note also that mathlib needs
`set_option backward.isDefEq.respectTransparency false` throughout
`Presheaf/Monoidal.lean` for the very same reason; expect to need it.

So: `exists_modPushforwardTensorPre` is bounded, mechanical, and contains NO
mathematics.  `isIso_modPullbackTensorComparison` contains all of it.

**CLOSED 2026-07-30 — and the prediction above was right about the input and
wrong about the packaging.**  `restrictScalars_μ_tmul` is indeed exactly what
was needed, and `set_option backward.isDefEq.respectTransparency false` is
indeed needed throughout (on the def, on the pinning lemma, and on the theorem
— omitting it on the last one makes `rw [ConcreteCategory.comp_apply]` fail to
match a goal it does match with it).  But **`(PresheafOfModules.restrictScalars
α).LaxMonoidal` was never built**, because `ν₀` consumes only its object part
and the presheaf tensor is objectwise: `modPushforwardTensorPreApp` is mathlib's
`μ` at each open, and naturality is one application of
`PresheafOfModules.naturality_apply` to `modTensorMk` after
`ModuleCat.MonoidalCategory.tensor_ext` reduces to pure tensors.  Both steps
that make this work — `(tensorObj P Q).map g` on a pure tensor, and
`(f_*M).val.map g = M.val.map (f⁻¹ᵁ g)` — are `rfl`, which is why the naturality
proof is four lines and mentions no bilinearity at all.  Anyone who still wants
the general instance should note the residue is bookkeeping, not content. -/

/-- **`modTensor` is functorial on arbitrary morphisms.**  The file already had
`modTensorMapIso` for isomorphisms; this is the same construction without the
inverse, needed because the comparison map below is transposed from
`η ⊗ η`, and `η` is not invertible. -/
noncomputable def modTensorMap {Z : Scheme.{u}} {L L' M M' : Z.Modules}
    (e : L ⟶ L') (e' : M ⟶ M') : modTensor L M ⟶ modTensor L' M' :=
  (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).map
    (MonoidalCategory.tensorHom
      ((SheafOfModules.forget _).map e) ((SheafOfModules.forget _).map e'))

/-- **`modTensorMap` acts on `tensorSection` componentwise.**

This is STEP (iii) of the three-step bridge that `flt-lean-309` compiler-checked
on 2026-07-28 and recorded in the docstring of `exists_modPullback_modTensor`
but could not DECLARE, because at that time its only consumer belonged to
another owner and a declaration with no consumer is free-floating.  It has a
consumer now — `modPullbackTensorComparison_tensorSection` below — so it is
declared here, in the morphism (not iso) generality.

The owner of `exists_trivialization_tensorPow` / `exists_trivialization_modTensor`
should use THIS rather than re-deriving it; specialise `e`, `e'` to `.hom` of an
iso to recover the form quoted in that docstring. -/
lemma modTensorMap_tensorSection {Z : Scheme.{u}} {L L' M M' : Z.Modules}
    (e : L ⟶ L') (e' : M ⟶ M') (a : Γ(L, ⊤)) (b : Γ(M, ⊤)) :
    (modTensorMap e e').val.app (op ⊤) (tensorSection a b) =
      tensorSection (e.val.app (op ⊤) a) (e'.val.app (op ⊤) b) := by
  unfold tensorSection modTensorMk modTensorMap
  have hn := (PresheafOfModules.sheafificationAdjunction (𝟙 Z.ringCatSheaf.obj)).unit.naturality
    (MonoidalCategory.tensorHom ((SheafOfModules.forget _).map e)
      ((SheafOfModules.forget _).map e'))
  exact congr($(hn).app (op ⊤) (a ⊗ₜ b)).symm

set_option backward.isDefEq.respectTransparency false in
/-- **`ν₀` AT ONE OPEN.**  `PresheafOfModules.Monoidal.tensorObj` is objectwise
and `(f_*A).val.obj V` is `ModuleCat.restrictScalars (f^♯_V)` applied to
`A.val.obj (f ⁻¹ᵁ V)`, so at `V` the required map is literally mathlib's lax
monoidal structure map of `ModuleCat.restrictScalars` followed by
`restrictScalars` of the sheafification unit `modTensorMk`:

    Γ(f_*A, V) ⊗_{Γ(Y,V)} Γ(f_*B, V)  --μ-->  Γ(A, f⁻¹V) ⊗_{Γ(X,f⁻¹V)} Γ(B, f⁻¹V)
                                      --a-->  Γ(A ⊗ B, f⁻¹V)

reading both sides as `Γ(Y,V)`-modules.  `μ` is where the four bilinearity
obligations of the failed hand-rolled attempt live, discharged once and for all
in mathlib. -/
noncomputable def modPushforwardTensorPreApp {X Y : Scheme.{u}} (f : X ⟶ Y) (A B : X.Modules)
    (V : (Opens ↥Y)ᵒᵖ) :
    (PresheafOfModules.Monoidal.tensorObj (R := Y.presheaf)
        ((Scheme.Modules.pushforward f).obj A).val
        ((Scheme.Modules.pushforward f).obj B).val).obj V ⟶
      (((Scheme.Modules.pushforward f).obj (modTensor A B)).val).obj V :=
  Functor.LaxMonoidal.μ (ModuleCat.restrictScalars _) (A.val.obj (op (f ⁻¹ᵁ V.unop)))
      (B.val.obj (op (f ⁻¹ᵁ V.unop))) ≫
    (ModuleCat.restrictScalars _).map ((modTensorMk A B).app (op (f ⁻¹ᵁ V.unop)))

set_option backward.isDefEq.respectTransparency false in
/-- **The pinning clause, at one open.**  `restrictScalars_μ_tmul` is exactly
this; the two `letI`s are the re-keying described in
`exists_modPushforwardTensorPre`'s docstring, and the trailing `rfl` inside
`Eq.trans` absorbs `(restrictScalars _).map φ` being `φ` on elements. -/
lemma modPushforwardTensorPreApp_tmul {X Y : Scheme.{u}} (f : X ⟶ Y) (A B : X.Modules)
    (V : (Opens ↥Y)ᵒᵖ)
    (a : ↑(((Scheme.Modules.pushforward f).obj A).val.obj V))
    (b : ↑(((Scheme.Modules.pushforward f).obj B).val.obj V)) :
    modPushforwardTensorPreApp f A B V (a ⊗ₜ b) =
      (modTensorMk A B).app (op (f ⁻¹ᵁ V.unop)) (a ⊗ₜ b) := by
  letI : CommRing ↑(Y.ringCatSheaf.obj.obj V) := inferInstanceAs (CommRing ↑(Y.presheaf.obj V))
  letI : CommRing ↑(X.ringCatSheaf.obj.obj (op (f ⁻¹ᵁ V.unop))) :=
    inferInstanceAs (CommRing ↑(X.presheaf.obj (op (f ⁻¹ᵁ V.unop))))
  unfold modPushforwardTensorPreApp
  rw [ConcreteCategory.comp_apply]
  exact Eq.trans (congrArg _ (ModuleCat.restrictScalars_μ_tmul _ _ _ _ _)) rfl

set_option backward.isDefEq.respectTransparency false in
/-- **PROVEN 2026-07-30 (plumbing — contains NO mathematics): the presheaf-level
lax monoidal structure map of `f_*`.**

`ν₀ : f_*A ⊗ f_*B ⟶ f_*(A ⊗ B)` at the level of presheaves of modules, PINNED
by its value on every pure tensor over every open — which determines it
completely, since `PresheafOfModules.Monoidal.tensorObj` is objectwise and each
`M₁.obj V ⊗ M₂.obj V` is generated by pure tensors.  So, unlike the `Nonempty`
form this development replaced, there is no room for an adversary here: any two
witnesses are equal.

Route, and the trap (the pre-proof audit, kept verbatim; read the AMENDMENT
below it): see the section docstring above.  In one sentence — do NOT
try to build this with `ModuleCat.MonoidalCategory.tensorLift` directly; supply
`(PresheafOfModules.restrictScalars α).LaxMonoidal` objectwise from mathlib's
`(ModuleCat.restrictScalars f).LaxMonoidal` and take `ν₀` to be its `μ`
composed with `restrictScalars` of `modTensorMk`.  `restrictScalars_μ_tmul` is
then exactly the pinning clause below.

`PresheafOfModules.pushforward φ` is definitionally
`pushforward₀ F R ⋙ restrictScalars φ` with `pushforward₀OfCommRingCat` already
strong `Monoidal`, so that one instance finishes the whole lax structure.

**PROVEN 2026-07-30, and by exactly that route — but WITHOUT building the
missing instance.**  The route audit above is right that
`(PresheafOfModules.restrictScalars α).LaxMonoidal` is what packages the
plumbing, and it is right that mathlib has the objectwise input
(`ModuleCat.restrictScalars_μ_tmul`).  What it over-priced is the packaging:
`ν₀` needs only the OBJECT part of that instance, and a presheaf tensor is
objectwise, so the whole instance is not required — `modPushforwardTensorPreApp`
below is mathlib's `μ` at each open, and its naturality is
`PresheafOfModules.naturality_apply` for `modTensorMk` on pure tensors.  Nothing
here is bilinearity: `μ` carries all four obligations, which is precisely why
the hand-rolled `tensorLift` attempt recorded above died and this does not.

THE ONE REAL OBSTACLE, recorded because it is not the one the audit predicted
and it cost the first attempt at this leaf.  `Γ(Z, V)` has TWO spellings here,
`↑(Z.ringCatSheaf.obj.obj V)` and `↑((Z.presheaf ⋙ forget₂ CommRingCat
RingCat).obj V)`.  They are definitionally equal, mathlib's `CommRing` instance
(`Presheaf/Monoidal.lean`) is stated for the SECOND, and typeclass search cannot
invert `ringCatSheaf` to reach it — the same re-keying failure that
`presheafOfModulesMonoidal` fixes for `MonoidalCategory`.
`modPushforwardTensorPreApp` itself
elaborates (its rings arrive in the good spelling from the expected type), so
the failure appears only when `ModuleCat.restrictScalars_μ_tmul` is APPLIED, and
it appears as `failed to synthesize CommRing ↑(Y.ringCatSheaf.obj.obj V)` inside
a proof whose statement elaborated fine.  Two `letI`s in the proof below supply
it.  They are deliberately NOT a global instance: a global `CommRing` on that
spelling would sit in a diamond with the `Ring` instance `RingCat` already
carries, and nothing outside this proof needs it. -/
theorem exists_modPushforwardTensorPre {X Y : Scheme.{u}} (f : X ⟶ Y) (A B : X.Modules) :
    ∃ ν₀ : PresheafOfModules.Monoidal.tensorObj (R := Y.presheaf)
        ((Scheme.Modules.pushforward f).obj A).val
        ((Scheme.Modules.pushforward f).obj B).val ⟶
      ((Scheme.Modules.pushforward f).obj (modTensor A B)).val,
      ∀ (V : (Opens ↥Y)ᵒᵖ)
        (a : ↑(((Scheme.Modules.pushforward f).obj A).val.obj V))
        (b : ↑(((Scheme.Modules.pushforward f).obj B).val.obj V)),
        ν₀.app V (a ⊗ₜ b) = (modTensorMk A B).app (op (f ⁻¹ᵁ V.unop)) (a ⊗ₜ b) :=
  ⟨{ app := modPushforwardTensorPreApp f A B
     naturality := fun {V V'} g => by
       apply ModuleCat.MonoidalCategory.tensor_ext
       intro m n
       rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
       show modPushforwardTensorPreApp f A B V'
             ((((Scheme.Modules.pushforward f).obj A).val.map g m) ⊗ₜ
               (((Scheme.Modules.pushforward f).obj B).val.map g n))
           = ((Scheme.Modules.pushforward f).obj (modTensor A B)).val.map g
               (modPushforwardTensorPreApp f A B V (m ⊗ₜ n))
       rw [modPushforwardTensorPreApp_tmul, modPushforwardTensorPreApp_tmul]
       exact PresheafOfModules.naturality_apply (modTensorMk A B)
         ((Opens.map f.base).op.map g) (m ⊗ₜ n) },
    modPushforwardTensorPreApp_tmul f A B⟩

/-- The presheaf-level lax comparison map of `f_*`, named. -/
noncomputable def modPushforwardTensorPre {X Y : Scheme.{u}} (f : X ⟶ Y) (A B : X.Modules) :
    PresheafOfModules.Monoidal.tensorObj (R := Y.presheaf)
        ((Scheme.Modules.pushforward f).obj A).val
        ((Scheme.Modules.pushforward f).obj B).val ⟶
      ((Scheme.Modules.pushforward f).obj (modTensor A B)).val :=
  (exists_modPushforwardTensorPre f A B).choose

/-- `modPushforwardTensorPre` on pure tensors. -/
lemma modPushforwardTensorPre_tmul {X Y : Scheme.{u}} (f : X ⟶ Y) (A B : X.Modules)
    (V : (Opens ↥Y)ᵒᵖ)
    (a : ↑(((Scheme.Modules.pushforward f).obj A).val.obj V))
    (b : ↑(((Scheme.Modules.pushforward f).obj B).val.obj V)) :
    (modPushforwardTensorPre f A B).app V (a ⊗ₜ b) =
      (modTensorMk A B).app (op (f ⁻¹ᵁ V.unop)) (a ⊗ₜ b) :=
  (exists_modPushforwardTensorPre f A B).choose_spec V a b

/-- **The lax monoidal structure map of `f_*` on SHEAVES**, `f_*A ⊗ f_*B ⟶
f_*(A ⊗ B)`: sheafify `modPushforwardTensorPre` and transpose along the
sheafification adjunction (`f_*(A ⊗ B)` is already a sheaf). -/
noncomputable def modPushforwardTensor {X Y : Scheme.{u}} (f : X ⟶ Y) (A B : X.Modules) :
    modTensor ((Scheme.Modules.pushforward f).obj A) ((Scheme.Modules.pushforward f).obj B) ⟶
      (Scheme.Modules.pushforward f).obj (modTensor A B) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).homEquiv _ _).symm
    (modPushforwardTensorPre f A B)

/-- `f_*` carries `a ⊗ b` to `a ⊗ b`.  Note `Γ(f_*M, ⊤) = Γ(M, f ⁻¹ᵁ ⊤)` and
`f ⁻¹ᵁ ⊤ = ⊤` are both DEFINITIONAL, which is why no transport appears. -/
lemma modPushforwardTensor_tensorSection {X Y : Scheme.{u}} (f : X ⟶ Y) (A B : X.Modules)
    (a : Γ((Scheme.Modules.pushforward f).obj A, ⊤))
    (b : Γ((Scheme.Modules.pushforward f).obj B, ⊤)) :
    (modPushforwardTensor f A B).val.app (op ⊤) (tensorSection a b) =
      tensorSection (Z := X) (L := A) (M := B) a b := by
  have h : ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).homEquiv _ _)
      (modPushforwardTensor f A B) = modPushforwardTensorPre f A B :=
    Equiv.apply_symm_apply _ _
  rw [Adjunction.homEquiv_unit] at h
  exact (congr($(h).app (op ⊤) (a ⊗ₜ b))).trans
    (modPushforwardTensorPre_tmul f A B (op ⊤) a b)

/-- **THE CANONICAL COMPARISON MAP** `f^*(L ⊗ M) ⟶ f^*L ⊗ f^*M`, as the
transpose of `(η ⊗ η) ≫ ν`. -/
noncomputable def modPullbackTensorComparison {X Y : Scheme.{u}} (f : X ⟶ Y) (L M : Y.Modules) :
    modPullback f (modTensor L M) ⟶ modTensor (modPullback f L) (modPullback f M) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (modTensorMap ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L)
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
      modPushforwardTensor f (modPullback f L) (modPullback f M))

/-- **THE SECTION IDENTITY, PROVEN**: the canonical comparison map carries
`f^*(a ⊗ b)` to `f^*a ⊗ f^*b`.

This is the clause that `exists_modPullback_modTensor` states, and it is a
theorem here rather than a hypothesis: the adjunction triangle turns
`θ.app ⊤ ∘ modPullbackSection` into "apply the transposed map at `⊤`", and the
transposed map is `(η ⊗ η) ≫ ν`, whose effect on `tensorSection` is
`modTensorMap_tensorSection` followed by `modPushforwardTensor_tensorSection`.
`modPullbackSection f L a` is BY DEFINITION `η.val.app (op ⊤) a`, which is why
the last step is an `exact` and not a rewrite. -/
lemma modPullbackTensorComparison_tensorSection {X Y : Scheme.{u}} (f : X ⟶ Y) (L M : Y.Modules)
    (a : Γ(L, ⊤)) (b : Γ(M, ⊤)) :
    (modPullbackTensorComparison f L M).val.app (op ⊤)
        (modPullbackSection f (modTensor L M) (tensorSection a b)) =
      tensorSection (modPullbackSection f L a) (modPullbackSection f M b) := by
  have h : ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _)
      (modPullbackTensorComparison f L M) =
      modTensorMap ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L)
          ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
        modPushforwardTensor f (modPullback f L) (modPullback f M) :=
    Equiv.apply_symm_apply _ _
  rw [Adjunction.homEquiv_unit] at h
  have h2 := congr($(h).val.app (op ⊤) (tensorSection a b))
  have hR : (modTensorMap ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L)
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
        modPushforwardTensor f (modPullback f L) (modPullback f M)).val.app (op ⊤)
        (tensorSection a b) =
      tensorSection (modPullbackSection f L a) (modPullbackSection f M b) := by
    show (modPushforwardTensor f (modPullback f L) (modPullback f M)).val.app (op ⊤)
        ((modTensorMap ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L)
          ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)).val.app (op ⊤)
            (tensorSection a b)) = _
    rw [modTensorMap_tensorSection]
    exact modPushforwardTensor_tensorSection f (modPullback f L) (modPullback f M) _ _
  exact h2.trans hR

/-- **LEAF (this one IS the mathematics): the canonical comparison map is an
isomorphism.**

Everything else about monoidality of `f^*` in this file is now formal over this
one statement.  Being an `IsIso` on a NAMED map, it is immune to the
under-pinning defect that the `Nonempty` and `∃` forms suffered: there is
nothing to choose.

ROUTES, in increasing order of generality.

* THE OPEN-IMMERSION CASE IS STRICTLY EASIER and is what the trivialization
  calculus below actually consumes.  For an open immersion, restriction is
  itself a LEFT adjoint (`Scheme.Modules.restrictAdjunction`, compared to
  `pullbackPushforwardAdjunction` by `restrictFunctorIsoPullback`), and at
  presheaf level it is a `pushforward₀`, whose `restrictAppIso` is `Iso.refl`
  and which is STRONG monoidal (`Presheaf/PushforwardZeroMonoidal.lean`).  So in
  the open case there is no comparison-is-iso question at presheaf level at all;
  what remains is that sheafification commutes with restriction to an open
  subsite, the mate of `restrictFunctorIsoPullback`.  A prover who only needs
  the consumers in this file should do this case FIRST.
* IN GENERAL — and note `exists_modPushforwardTensorPre` is PROVEN as of
  2026-07-30, so the lax structure it supplies is no longer a hypothesis —
  `CategoryTheory.Functor.Monoidal.ofOplaxMonoidal` upgrades the oplax
  `PresheafOfModules.pullback φ` (via
  `CategoryTheory.Adjunction.leftAdjointOplaxMonoidal`) to strong given
  `IsIso (η F)` and `IsIso (δ F X Y)`, and the residue is
  `modLocW X (δ (PresheafOfModules.pullback φ) P Q)` — the SAME shape as
  `modLocW_whiskerLeft`, and closable by the same input.  `p^*` on presheaves
  over a space is the filtered colimit `colim_{V ⊇ f(U)}` (`opensMapFinal`,
  proven above), which is what makes both statements local.

  **UPDATED 2026-07-29: that input now EXISTS and is proven.**
  `modLocW_whiskerLeft` was a sorry when this route was first written; it has
  since been closed over
  `Fermat/FLT/Mathlib/Algebra/Category/ModuleCat/Presheaf/MonoidalW.lean`
  (`Fermat.SheafificationMonoidal.W_whiskerLeft`), which proves stability of
  local isomorphisms under `X ⊗ -` hands-on, via
  `isLocallySurjective_whiskerLeft` and `isLocallyInjective_whiskerLeft`.
  A prover of THIS leaf should start there: the same two-halves argument
  (locally surjective + locally injective ⇒ local iso) applies to `δ` of the
  presheaf pullback, and `exists_relations` / `key_equalizerSieve` in that file
  are the reusable pieces.  This is now the recommended route, ahead of the
  free/colimit one below.
* The free/colimit route remains available:
  `SheafOfModules.pullbackObjFreeIso` and `pullbackObjUnitToUnit`
  (`Sheaf/PullbackFree.lean`, already imported), with `Sheaf/Generators.lean`'s
  `LocalGeneratorsData` presenting a sheaf of modules locally as a quotient of
  frees.

DEAD at this pin, re-checked 2026-07-28/29 by `grep`: internal hom
(`MonoidalClosed` has zero occurrences under mathlib's presheaf/sheaf
`ModuleCat` directories) and stalks (there is no stalk API for
`PresheafOfModules`/`SheafOfModules` at all). -/
instance isIso_modPullbackTensorComparison {X Y : Scheme.{u}} (f : X ⟶ Y) (L M : Y.Modules) :
    IsIso (modPullbackTensorComparison f L M) := sorry

/-- **Monoidality of `f^*` on objects** (PROVEN 2026-07-29):
`f^*(L ⊗ M) ≅ f^*L ⊗ f^*M`, **with the isomorphism PINNED by its effect on
global sections**: it carries `f^*(a ⊗ b)` to `f^*a ⊗ f^*b`.

**RESTATED 2026-07-28 — the previous `Nonempty` form was UNDER-PINNED, and that
is a defect and not a matter of taste.**  The old statement was

    Nonempty (modPullback f (modTensor L M) ≅
      modTensor (modPullback f L) (modPullback f M))

and an adversary may post-compose any witness with multiplication by a unit `u`
of `Γ(X, ⊤)` — `modTensorMapIso` of the two identity isos, twisted by `u`, is
again an isomorphism between exactly those two objects — so *every* clause of
the old statement survives while every trivialized section is scaled by `u`.
Consequently `a ⊗ b ↦ a · b`, which is the ONLY thing the trivialization
calculus below wants from this leaf, is not a consequence of it.  That is what
forced `exists_trivialization_tensorPow` to be cut as a separate leaf, and it is
why it must be re-derived here rather than assumed: **the `Nonempty` packaging
was not weaker mathematics, it was a statement about a different (larger) set of
isomorphisms.**

The pinning clause below is the standard one and it is TRUE of the canonical
comparison map, by the adjunction triangle: the canonical `θ` is the transpose
of `L ⊗ M ⟶ f_*(f^*L ⊗ f^*M)`, which on `V`-sections is `s ⊗ t ↦ η(s) ⊗ η(t)`,
and `θ ∘ η_{L ⊗ M}` is that very map; `modPullbackSection` is `η` read at `⊤`.
It is stated at `⊤` only, which is all any consumer needs — `trivializedSection`
restricts a GLOBAL section — and it is enough to defeat the unit twist above,
since scaling by `u` changes the left-hand side and not the right.

With `modPullbackUnitIso` PROVEN, this is the only obligation of
`nonempty_modPullback_modTensorPow` — and the only input of the trivialization
calculus below as well (`nonempty_restrict_modTensor` is three lines over it,
via `Scheme.Modules.restrictFunctorIsoPullback`).  So this is still the ONLY
leaf in the module that anything except `exists_trivialization_of_modTensorPow`
waits on.

ROUTE AUDIT — SUPERSEDED 2026-07-29, and the leaf is now PROVEN.

This leaf used to be the sorry.  It is now a three-line corollary of a WRITTEN
comparison map: see the section `The CANONICAL comparison map` above, and
`modPullbackTensorComparison` / `modPullbackTensorComparison_tensorSection` /
`isIso_modPullbackTensorComparison`.  The pinning clause is
`modPullbackTensorComparison_tensorSection`, a theorem, proven exactly by the
adjunction-triangle argument the previous audit predicted.

The 2026-07-28 audit's central claim — that ONE missing instance,
`(PresheafOfModules.restrictScalars α).LaxMonoidal`, stands between here and a
written comparison map — was CHECKED and is CORRECT.  An attempt to bypass it by
writing the lax structure map by hand out of
`ModuleCat.MonoidalCategory.tensorLift` was made and failed on
`restrictScalars` instance plumbing; the failure is recorded in detail in the
section docstring above so that it is not repeated.  What survives of the leaf
is exactly that instance (`exists_modPushforwardTensorPre`, no mathematics) plus
`isIso_modPullbackTensorComparison` (all of the mathematics).

**AMENDED 2026-07-30.**  The audit named the right obstacle and the wrong
granularity: the instance is what *packages* the plumbing, but `ν₀` needs only
its OBJECT part, and mathlib's `ModuleCat.restrictScalars` already supplies that
(`Functor.LaxMonoidal.μ` plus `restrictScalars_μ_tmul`).  So
`exists_modPushforwardTensorPre` is now PROVEN with no new instance at all, and
`isIso_modPullbackTensorComparison` is the module's only remaining leaf on this
route.  Read that as a caution about audits of the form "one missing instance
blocks this": the instance may be blocking a *general* statement while the
particular one factors through a single object.

PIN CHECK 2026-07-28, re-run 2026-07-29 and STANDS:
`Mathlib/Algebra/Category/ModuleCat/Presheaf/PushforwardZeroMonoidal.lean` is
present at this pin, which is what makes `pushforward₀OfCommRingCat` usable as
the strong-monoidal half of the lax structure of `f_*`.

The bridge (i)-(iii) for the OPEN-IMMERSION consumers is unchanged and still
compiler-checked; step (iii) is now DECLARED as `modTensorMap_tensorSection`
(in morphism generality — specialise to `.hom` of an iso to recover the form
below).  Steps (i) and (ii) still have no declared consumer:

    -- (i) `rfl`.  The restriction inside `trivializedSection` IS the unit of
    --     `Scheme.Modules.restrictAdjunction`, read at `⊤`.
    (Scheme.Modules.restrictAppIso (f := U.ι) L ⊤).inv
        (L.presheaf.map (homOfLE le_top).op s)
      = ((Scheme.Modules.restrictAdjunction U.ι).unit.app L).val.app (op ⊤) s

    -- (ii) `Adjunction.unit_leftAdjointUniq_hom_app _ _ A`, since
    --     `modRestrictPullbackIso` is `restrictFunctorIsoPullback`, which is
    --     `(restrictAdjunction f).leftAdjointUniq (pullbackPushforwardAdjunction f)`.
    (Scheme.Modules.restrictAdjunction f).unit.app A ≫
        (Scheme.Modules.pushforward f).map (modRestrictPullbackIso f A).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app A

With (i) and (ii), the pinning clause below transfers verbatim from
`modPullbackSection` to the restriction of a global section along `U.ι`;
`modTensorMap_tensorSection` then pushes it through, and `modTensorUnitLeftIso`
on `tensorSection a b` with both factors in `Γ(𝒪_U, ⊤)` is the multiplication
`a * b` that `exists_trivialization_tensorPow` is after. -/
theorem exists_modPullback_modTensor {X Y : Scheme.{u}} (f : X ⟶ Y) (L M : Y.Modules) :
    ∃ e : modPullback f (modTensor L M) ≅ modTensor (modPullback f L) (modPullback f M),
      ∀ (a : Γ(L, ⊤)) (b : Γ(M, ⊤)),
        e.hom.val.app (op ⊤) (modPullbackSection f (modTensor L M) (tensorSection a b)) =
          tensorSection (modPullbackSection f L a) (modPullbackSection f M b) :=
  ⟨asIso (modPullbackTensorComparison f L M), modPullbackTensorComparison_tensorSection f L M⟩

/-- **Monoidality of `f^*` on objects, forgetting the pinning** (PROVEN
2026-07-28 over `exists_modPullback_modTensor`).

Kept because several consumers — `nonempty_modPullback_modTensorPow`,
`nonempty_restrict_modTensor`, and through them `isAmpleSheaf_modPullback` and
`isInvertibleSheaf_modTensor` — genuinely need nothing more than the existence
of the isomorphism.  Consumers that need the section identity must go through
`exists_modPullback_modTensor` instead; see its docstring for why `Nonempty` is
not enough for them. -/
theorem nonempty_modPullback_modTensor {X Y : Scheme.{u}} (f : X ⟶ Y) (L M : Y.Modules) :
    Nonempty (modPullback f (modTensor L M) ≅
      modTensor (modPullback f L) (modPullback f M)) :=
  ⟨(exists_modPullback_modTensor f L M).choose⟩

/-! ### The non-vanishing locus of a section of the structure sheaf

The "well-definedness of `nonvanishingLocus`" obligation recorded against
`isQuasiAffine_of_isAmpleSheaf_modUnit`.  It is a transition-function
computation, and it needs *less* than the docstring predicted: only that an
endomorphism of `𝒪_U` as an `𝒪_U`-module is multiplication by `β(1)` —
INVERTIBILITY of that factor is never used, because `basicOpen (a * c) ≤
basicOpen a` already suffices in the direction where it is needed.

Note `Γ(modUnit W, ⊤)` and `Γ(W, ⊤)` are DEFEQ at this pin; `unitOne` and
`unitEndoApply` exist only to give the elaborator a place to see that, since
type-class search for `1` and `*` does not unfold `modUnit` on its own. -/

/-- `1 : Γ(W, ⊤)`, read as a section of the unit module. -/
def unitOne (W : Scheme.{u}) : Γ(modUnit W, ⊤) := (1 : Γ(W, ⊤))

/-- An endomorphism of `𝒪_W` (as a module over itself), applied to a global
section, with both sides typed in `Γ(W, ⊤)`. -/
noncomputable def unitEndoApply {W : Scheme.{u}} (β : modUnit W ≅ modUnit W) (a : Γ(W, ⊤)) :
    Γ(W, ⊤) := β.hom.val.app (op ⊤) a

/-- **An endomorphism of the structure sheaf is multiplication by `β(1)`** —
`𝒪_W`-linearity applied to `a = a • 1`. -/
lemma unitEndoApply_eq {W : Scheme.{u}} (β : modUnit W ≅ modUnit W) (a : Γ(W, ⊤)) :
    unitEndoApply β a = a * unitEndoApply β 1 := by
  have h2 : unitEndoApply β (a * 1) = a * unitEndoApply β 1 :=
    (β.hom.val.app (op ⊤)).hom.map_smul a (unitOne W)
  simpa using h2

/-- The CANONICAL trivialization of `𝒪_Z` over `U` computes the ordinary
restriction map `Γ(Z, ⊤) ⟶ Γ(U, ⊤)`.  Uses `Scheme.Opens.ι_appIso`, which says
the comparison isomorphism of an open immersion of the form `U.ι` is
`Iso.refl`. -/
lemma trivializedSection_restrictUnitIso {Z : Scheme.{u}} (U : Z.Opens) (r : Γ(Z, ⊤)) :
    trivializedSection (Scheme.Modules.restrictUnitIso U.ι) r = U.ι.appTop r := by
  unfold trivializedSection
  rw [Scheme.Opens.ι_appTop]
  simp [Scheme.Modules.restrictUnitIso, Scheme.Opens.ι_appIso]
  rfl

/-- Post-composing a trivialization with an endomorphism of `𝒪_U` post-composes
the trivialized section. -/
lemma trivializedSection_trans {Z : Scheme.{u}} {A : Z.Modules} {U : Z.Opens}
    (α : A.restrict U.ι ≅ modUnit (U : Scheme.{u}))
    (β : modUnit (U : Scheme.{u}) ≅ modUnit (U : Scheme.{u})) (s : Γ(A, ⊤)) :
    trivializedSection (α ≪≫ β) s = unitEndoApply β (trivializedSection α s) := rfl

/-- **The non-vanishing locus of a section of the structure sheaf is its basic
open** (PROVEN 2026-07-27).

`⊇` take `U = ⊤` and the canonical trivialization.  `⊆` any trivialization `φ`
factors as `restrictUnitIso ≪≫ β` with `β` an endomorphism of `𝒪_U`, so
`trivializedSection φ r = (r|_U) * β(1)` and
`basicOpen ((r|_U) * β(1)) ≤ basicOpen (r|_U) = U.ι ⁻¹ᵁ Z.basicOpen r`.

This was the ONLY remaining input of `isQuasiAffine_of_isAmpleSheaf_modUnit`,
which is therefore now sorry-free. -/
theorem nonvanishingLocus_modUnit (Z : Scheme.{u}) (r : Γ(Z, ⊤)) :
    nonvanishingLocus (modUnit Z) r = (Z.basicOpen r : Set Z) := by
  have key : ∀ (U : Z.Opens) (φ : (modUnit Z).restrict U.ι ≅ modUnit (U : Scheme.{u})),
      (U : Scheme.{u}).basicOpen (trivializedSection φ r)
        ≤ (U : Scheme.{u}).basicOpen (U.ι.appTop r) := by
    intro U φ
    obtain ⟨β, hφ⟩ : ∃ β : modUnit (U : Scheme.{u}) ≅ modUnit (U : Scheme.{u}),
        φ = Scheme.Modules.restrictUnitIso U.ι ≪≫ β :=
      ⟨(Scheme.Modules.restrictUnitIso U.ι).symm ≪≫ φ,
        Eq.symm (Iso.self_symm_id_assoc _ _)⟩
    have e1 : trivializedSection φ r = (U.ι.appTop r) * unitEndoApply β 1 := by
      rw [hφ]
      exact (trivializedSection_trans _ _ _).trans
        ((congrArg (unitEndoApply β) (trivializedSection_restrictUnitIso U r)).trans
          (unitEndoApply_eq β _))
    rw [e1, Scheme.basicOpen_mul]
    exact inf_le_left
  ext z
  constructor
  · rintro ⟨U, hz, φ, hmem⟩
    have h1 := key U φ hmem
    have h2 : (⟨z, hz⟩ : (U : Scheme.{u})) ∈ U.ι ⁻¹ᵁ Z.basicOpen r :=
      (Scheme.preimage_basicOpen_top U.ι r).symm ▸ h1
    exact h2
  · intro hzr
    refine ⟨⊤, trivial, Scheme.Modules.restrictUnitIso (⊤ : Z.Opens).ι, ?_⟩
    have h3 : (⟨z, trivial⟩ : ((⊤ : Z.Opens) : Scheme.{u}))
        ∈ (⊤ : Z.Opens).ι ⁻¹ᵁ Z.basicOpen r := hzr
    have h4 := (Scheme.preimage_basicOpen_top (⊤ : Z.Opens).ι r) ▸ h3
    exact (congrArg ((⊤ : Z.Opens) : Scheme.{u}).basicOpen
      (trivializedSection_restrictUnitIso (⊤ : Z.Opens) r)).ge h4

/-! ### Restriction of a trivialization to a smaller open

A trivialization is a datum over an OPEN, and every comparison of two
trivializations has to happen over their intersection.  This section builds that
move.

**Route changed 2026-07-28.**  It used to go through `modPullback`, to dodge the
`[IsOpenImmersion f]` instance argument that `restrictFunctor` carries — but that
made `modRestrictLEIso` a composite of `Adjunction.leftAdjointUniq` components,
which compute on sections not at all, and `trivializedSection_trivializationOfLE`
was left open because of it.  The instance juggling was never the problem:
`Scheme.Modules.restrictFunctorCongr` **is** the congruence, it is already in the
pin, and both it and `restrictFunctorComp` have `_app_app` lemmas that are `rfl`
and read `A.presheaf.map (eqToHom _).op`.  So the calculus is now written off
those two, everything on sections is an honest presheaf map, and the leaf is
proven. -/

/-- **Restriction commutes with `modTensor`** (PROVEN 2026-07-28 over
`nonempty_modPullback_modTensor`, in three lines).

This — not the general pullback statement — is what the ampleness theory below
actually consumes, and it is strictly weaker; see the ROUTE AUDIT on
`nonempty_modPullback_modTensor`. -/
theorem nonempty_restrict_modTensor {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (L M : Y.Modules) :
    Nonempty ((modTensor L M).restrict f ≅ modTensor (L.restrict f) (M.restrict f)) := by
  obtain ⟨e⟩ := nonempty_modPullback_modTensor f L M
  exact ⟨modRestrictPullbackIso f _ ≪≫ e ≪≫
    modTensorMapIso (modRestrictPullbackIso f L).symm (modRestrictPullbackIso f M).symm⟩

/-- **Restricting a trivialization restricts the trivialized section** (PROVEN
2026-07-28).  Pure plumbing — no mathematics — but it took three attempts, and
the thing that unlocked it was changing `modRestrictLEIso` (now HOISTED to
`RelativePicard.lean`, and hoisted in its NEW `restrictFunctorCongr` form)
rather than changing the proof.

The skeleton, since the same shape recurs everywhere in this file:

* one `have hcomp : ∀ x, … = … := fun _ => rfl` naming each factor's
  `.val.app (op ⊤)` explicitly.  `simp` will NOT split a composite
  `.val.app` — `Iso.trans_hom` and `Functor.mapIso_hom` fire, but
  `SheafOfModules.comp_val`, `PresheafOfModules.comp_app` and
  `ConcreteCategory.comp_apply` are all reported UNUSED and the composite stays
  one opaque application;
* `toApp`, converting `.val.app (op V)` to `Scheme.Modules.Hom.app _ V`, which is
  the form mathlib's `_app_app` simp lemmas are stated in;
* `hpush`, `restrictFunctor` being a pushforward, so its `map` shifts the open;
* `hnat`, `PresheafOfModules.naturality_apply` for `φ.hom.val`;
* `step5`, `restrictUnitIso ∘ restriction = appTop`, via `Scheme.Hom.appIso_hom`
  and `Scheme.homOfLE_app` / `homOfLE_appTop`.

Two notes that cost time. `rw [← step5, ← hnat]` on the RIGHT-hand side, then
`congr 1`, is what lets the argument goal be produced by the tactic instead of
written out by hand. And `rw [← Functor.map_comp]` does NOT fire on
`Z.presheaf.map _ ≫ Z.presheaf.map _` — `erw` does; the elaborated functor is not
syntactically the `Z.presheaf` one writes.  The final step in both branches is
that `Opens Z` is a POSET, so any two parallel morphisms are `Subsingleton.elim`
equal and `Quiver.Hom.unop_inj` lifts that to the opposite category. -/
theorem trivializedSection_trivializationOfLE {Z : Scheme.{u}} {A : Z.Modules} {W U : Z.Opens}
    (h : W ≤ U) (φ : A.restrict U.ι ≅ modUnit (U : Scheme.{u})) (s : Γ(A, ⊤)) :
    trivializedSection (trivializationOfLE h φ) s
      = (Z.homOfLE h).appTop (trivializedSection φ s) := by
  have hcomp : ∀ x : Γ(A.restrict W.ι, ⊤),
      (trivializationOfLE h φ).hom.val.app (op ⊤) x
        = (Scheme.Modules.restrictUnitIso (Z.homOfLE h)).hom.val.app (op ⊤)
            (((Scheme.Modules.restrictFunctor (Z.homOfLE h)).map φ.hom).val.app (op ⊤)
              (((Scheme.Modules.restrictFunctorComp (Z.homOfLE h) U.ι).hom.app A).val.app (op ⊤)
                (((Scheme.Modules.restrictFunctorCongr
                    (Z.homOfLE_ι h).symm).hom.app A).val.app (op ⊤) x))) :=
    fun _ => rfl
  have toApp : ∀ {S : Scheme.{u}} {M N : S.Modules} (ψ : M ⟶ N) (V : S.Opens) (y : Γ(M, V)),
      ψ.val.app (op V) y = Scheme.Modules.Hom.app ψ V y := fun _ _ _ => rfl
  unfold trivializedSection
  rw [hcomp]
  simp only [toApp, Scheme.Modules.restrictFunctorCongr_hom_app_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app]
  have hpush : ∀ (y : Γ((A.restrict U.ι).restrict (Z.homOfLE h), ⊤)),
      Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctor (Z.homOfLE h)).map φ.hom) ⊤ y
        = Scheme.Modules.Hom.app φ.hom ((Z.homOfLE h).opensFunctor.obj ⊤) y := fun _ => rfl
  rw [hpush]
  set t : Γ(A.restrict U.ι, ⊤) :=
    (Scheme.Modules.restrictAppIso U.ι A ⊤).inv (A.presheaf.map (homOfLE le_top).op s) with ht
  have hnat : Scheme.Modules.Hom.app φ.hom ((Z.homOfLE h).opensFunctor.obj ⊤)
        ((A.restrict U.ι).val.map (homOfLE (le_top)).op t)
      = (modUnit (U : Scheme.{u})).val.map (homOfLE (le_top)).op
          (Scheme.Modules.Hom.app φ.hom ⊤ t) :=
    PresheafOfModules.naturality_apply φ.hom.val (homOfLE le_top).op t
  have step5 : ∀ (u : Γ((U : Scheme.{u}), ⊤)),
      Scheme.Modules.Hom.app (Scheme.Modules.restrictUnitIso (Z.homOfLE h)).hom ⊤
          ((modUnit (U : Scheme.{u})).val.map (homOfLE (le_top)).op u)
        = (Z.homOfLE h).appTop u := by
    intro u
    have hru : ∀ (a : Γ((U : Scheme.{u}), (Z.homOfLE h).opensFunctor.obj ⊤)),
        Scheme.Modules.Hom.app (Scheme.Modules.restrictUnitIso (Z.homOfLE h)).hom ⊤ a
          = ((Z.homOfLE h).appIso ⊤).hom a := fun _ => rfl
    rw [hru, Scheme.Hom.appIso_hom, Scheme.homOfLE_app, Scheme.homOfLE_appTop]
    simp only [Scheme.Opens.toScheme_presheaf_map]
    have hmu : ∀ (y : Γ((U : Scheme.{u}), ⊤)),
        (modUnit (U : Scheme.{u})).val.map
            (homOfLE (le_top : (Z.homOfLE h) ''ᵁ (⊤ : (W : Scheme.{u}).Opens) ≤ ⊤)).op y
          = (U : Scheme.{u}).presheaf.map
            (homOfLE (le_top : (Z.homOfLE h) ''ᵁ (⊤ : (W : Scheme.{u}).Opens) ≤ ⊤)).op y :=
      fun _ => rfl
    rw [hmu]
    simp only [Scheme.Opens.toScheme_presheaf_map, ← ConcreteCategory.comp_apply]
    congr 1
    erw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (fun m => ConcreteCategory.hom (Z.presheaf.map m))
      (Quiver.Hom.unop_inj (Subsingleton.elim _ _))
  rw [← step5, ← hnat]
  congr 1
  have hIW : ∀ (x : Γ(A, W.ι ''ᵁ (⊤ : (W : Scheme.{u}).Opens))),
      (Scheme.Modules.restrictAppIso W.ι A ⊤).inv x = x := fun _ => rfl
  have hrm : ∀ (y : Γ(A.restrict U.ι, ⊤)),
      (A.restrict U.ι).val.map
          (homOfLE (le_top : (Z.homOfLE h) ''ᵁ (⊤ : (W : Scheme.{u}).Opens) ≤ ⊤)).op y
        = A.presheaf.map (U.ι.opensFunctor.map
            (homOfLE (le_top : (Z.homOfLE h) ''ᵁ (⊤ : (W : Scheme.{u}).Opens) ≤ ⊤))).op y :=
    fun _ => rfl
  have hIU : ∀ (x : Γ(A, U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens))),
      (Scheme.Modules.restrictAppIso U.ι A ⊤).inv x = x := fun _ => rfl
  rw [ht, hIU, hrm, hIW]
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  congr 1
  erw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun m => (ConcreteCategory.hom (A.presheaf.map m)) s)
    (Quiver.Hom.unop_inj (Subsingleton.elim _ _))

/-- The membership form of `trivializedSection_trivializationOfLE`, which is how
every consumer below uses it. -/
lemma mem_basicOpen_trivializationOfLE {Z : Scheme.{u}} {A : Z.Modules} {W U : Z.Opens}
    (h : W ≤ U) (φ : A.restrict U.ι ≅ modUnit (U : Scheme.{u})) (s : Γ(A, ⊤)) {z : Z}
    (hzW : z ∈ W) :
    ((⟨z, hzW⟩ : (W : Scheme.{u})) ∈
        (W : Scheme.{u}).basicOpen (trivializedSection (trivializationOfLE h φ) s)) ↔
      ((⟨z, h hzW⟩ : (U : Scheme.{u})) ∈
        (U : Scheme.{u}).basicOpen (trivializedSection φ s)) := by
  rw [trivializedSection_trivializationOfLE, ← Scheme.preimage_basicOpen_top]
  show (Z.homOfLE h).base ⟨z, hzW⟩ ∈ (U : Scheme.{u}).basicOpen (trivializedSection φ s) ↔
    (⟨z, h hzW⟩ : (U : Scheme.{u})) ∈ (U : Scheme.{u}).basicOpen (trivializedSection φ s)
  rw [show (Z.homOfLE h).base ⟨z, hzW⟩ = (⟨z, h hzW⟩ : (U : Scheme.{u})) from
    Scheme.homOfLE_apply' h z hzW]
  exact Iff.rfl

/-! ### Well-definedness of the non-vanishing locus

`NonvanishingAt A s z` is an `∃` over trivializations near `z`.  This is the
lemma that says the `∃` is a `∀` once ONE trivialization is in hand — the
general form of the `key` computation inside `nonvanishingLocus_modUnit`, and it
needs exactly as little as that one did: two trivializations over a common open
differ by an endomorphism of `𝒪`, which is multiplication by `β(1)`, and
`basicOpen (a * c) ≤ basicOpen a` does the rest.  INVERTIBILITY of `β(1)` is
never used. -/

/-- **The non-vanishing locus, read through any one trivialization** (PROVEN
2026-07-28). -/
theorem nonvanishingAt_iff_trivializedSection {Z : Scheme.{u}} {A : Z.Modules} (s : Γ(A, ⊤))
    {U : Z.Opens} (φ : A.restrict U.ι ≅ modUnit (U : Scheme.{u})) {z : Z} (hz : z ∈ U) :
    NonvanishingAt A s z ↔
      (⟨z, hz⟩ : (U : Scheme.{u})) ∈ (U : Scheme.{u}).basicOpen (trivializedSection φ s) := by
  constructor
  · rintro ⟨V, hzV, ψ, hmem⟩
    have hzW : z ∈ U ⊓ V := ⟨hz, hzV⟩
    set φW := trivializationOfLE (inf_le_left : U ⊓ V ≤ U) φ with hφW
    set ψW := trivializationOfLE (inf_le_right : U ⊓ V ≤ V) ψ with hψW
    have hmemW : (⟨z, hzW⟩ : ((U ⊓ V : Z.Opens) : Scheme.{u})) ∈
        ((U ⊓ V : Z.Opens) : Scheme.{u}).basicOpen (trivializedSection ψW s) :=
      (mem_basicOpen_trivializationOfLE inf_le_right ψ s hzW).2 hmem
    have hsplit : ψW = φW ≪≫ (φW.symm ≪≫ ψW) := Eq.symm (Iso.self_symm_id_assoc _ _)
    have hval : trivializedSection ψW s
        = trivializedSection φW s * unitEndoApply (φW.symm ≪≫ ψW) 1 := by
      conv_lhs => rw [hsplit]
      exact (trivializedSection_trans _ _ _).trans (unitEndoApply_eq _ _)
    rw [hval, Scheme.basicOpen_mul] at hmemW
    exact (mem_basicOpen_trivializationOfLE inf_le_left φ s hzW).1 hmemW.1
  · exact fun hmem => ⟨U, hz, φ, hmem⟩

/-! ### Invertibility, and the NUMERICAL-SEMIGROUP bridge

This section is the FAITHFULNESS AUDIT that
`nonvanishingLocus_modPullback_of_isAmpleSheaf` was flagged as needing.  See
`isInvertibleSheaf_of_isAmpleSheaf` for the verdict and its proof sketch. -/

/-- **A tensor product of invertible sheaves is invertible** (PROVEN over
`nonempty_restrict_modTensor`): trivialize both over `U ⊓ V`.

Deliberately NOT hoisted to `RelativePicard.lean` with the rest of the free
calculus (2026-07-28), and the reason is worth recording: this declaration is
the ONLY consumer of `nonempty_restrict_modTensor`, which in turn is the only
consumer of `nonempty_modPullback_modTensor`.  Moving it up would have left
both of those free-floating and silently orphaned that leaf's owner's work.
`RelativePicard.lean` therefore carries its own
`isInvertibleSheaf_modTensorPic`, over its own twin of the pullback leaf; the
two collapse into one when `nonempty_modPullback_modTensor` is settled and the
hoist described there is carried out. -/
theorem isInvertibleSheaf_modTensor {Z : Scheme.{u}} {L M : Z.Modules}
    (hL : IsInvertibleSheaf L) (hM : IsInvertibleSheaf M) : IsInvertibleSheaf (modTensor L M) := by
  intro z
  obtain ⟨U, hzU, ⟨φ⟩⟩ := hL z
  obtain ⟨V, hzV, ⟨ψ⟩⟩ := hM z
  obtain ⟨e⟩ := nonempty_restrict_modTensor (U ⊓ V : Z.Opens).ι L M
  exact ⟨U ⊓ V, ⟨hzU, hzV⟩, ⟨e ≪≫ modTensorMapIso (trivializationOfLE inf_le_left φ)
    (trivializationOfLE inf_le_right ψ) ≪≫ modTensorUnitLeftIso _⟩⟩

/-- **Every tensor power of an invertible sheaf is invertible** (PROVEN). -/
theorem isInvertibleSheaf_modTensorPow {Z : Scheme.{u}} {L : Z.Modules}
    (hL : IsInvertibleSheaf L) : ∀ n : ℕ, IsInvertibleSheaf (modTensorPow L n)
  | 0 => isInvertibleSheaf_modUnit Z
  | (n + 1) => isInvertibleSheaf_modTensor hL (isInvertibleSheaf_modTensorPow hL n)

/-- **AN INVERTIBLE SHEAF OF MODULES IS LOCALLY FREE OF RANK ONE** (sorry leaf,
cut 2026-07-29 out of `exists_trivialization_of_modTensorPow`) — Stacks 0B8L /
01CV, Hartshorne II.6.12, in its classical TWO-FACTOR form: if `L ⊗ N` is trivial
on `U` for SOME `N`, then `L` is trivial near each point of `U`.

**This is the single mathematical leaf of the module** (`modLocW_whiskerLeft` and
`nonempty_modPullback_modTensor` aside), and it is the whole content of the
numerical-semigroup worry recorded against
`nonvanishingLocus_modPullback_of_isAmpleSheaf`.

**FAITHFUL, and strictly stronger than the tensor-power form it came from.**
`modTensorPow A (j+1)` is `modTensor A (modTensorPow A j)` definitionally, so the
power statement is the special case `N = A^{⊗j}`; the `0 < k` hypothesis of the
consumer is exactly what produces the `j`.  Nothing else about `N` is used or
true: `N` is an arbitrary `𝒪_Z`-module, as in Stacks, and the statement holds
over an arbitrary RINGED SPACE — no quasi-coherence, no scheme hypothesis beyond
what `Z.Modules` already carries.

WHY IT IS TRUE.  Near a point, `ν⁻¹(1) = Σ_{i≤m} s_i ⊗ t_i` for finitely many
sections; writing `λ_i(x) := ν(x ⊗ t_i)` one has `Σ_i λ_i(s_i) = ν(ν⁻¹ 1) = 1`,
so some `λ_i(s_i)` is a unit on a neighbourhood `W` of the given point (a sum of
sections equal to `1` cannot have every term in the maximal ideal at a point, so
the basic opens `W_i := basicOpen (λ_i(s_i))` cover).  On that `W`, `s_i`
generates and `c⁻¹λ_i` is inverse to `r ↦ r·s_i`.

**ROUTE AUDIT 2026-07-29 — this CORRECTS the audit that stood here.**  The old
note said the blocker is the missing STALK-MODULE structure.  That is true of the
route it had in mind and it is not the whole story, and naming only stalks sends
a prover at the wrong subtree.  Re-running the checks:

* **CONFIRMED, and it is the old note's one surviving claim.**
  `grep -rln stalk Mathlib/Algebra/Category/ModuleCat/{Presheaf,Sheaf}/` is still
  **EMPTY** at this pin, so `A_y` cannot even be *said* to be invertible over
  `𝒪_y`.  (`Scheme.Modules.restrictStalkNatIso` exists but is a stalk of the
  underlying `Ab`-presheaf and carries no `Module` structure.)
* **NEWLY FOUND, and NOT previously recorded: the LOCAL PRESENTATION half is
  already available.**  `Mathlib/Algebra/Category/ModuleCat/Presheaf/Sheafify.lean`
  carries `instance : IsLocallySurjective J (toSheafify α φ)` (line 352 at this
  pin), and `PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app`
  identifies `modTensorMk` with `CategoryTheory.toSheafify` on underlying
  presheaves.  So "`ν⁻¹(1)` is locally a finite sum of pure tensors" needs no new
  theory — only the unfolding of local surjectivity over the Opens topology into
  its pointwise form.  Refuting check: the `grep` above on `Sheafify.lean`.
* **THE OBSTRUCTION IS THE SYMMETRY, NOT THE STALKS.**  The endgame is the
  generation identity `x = Σ_i λ_i(x)·s_i`, and it is NOT a consequence of
  `Σ_i λ_i(s_i) = 1` by any amount of bilinearity: the derivation is
  `x ⊗ 1 = Σ_i x ⊗ s_i ⊗ t_i ↦ Σ_i s_i ⊗ x ⊗ t_i = Σ_i λ_i(x)·s_i ⊗ 1`, which
  uses the ASSOCIATOR and the BRAIDING of `L ⊗ L ⊗ N`.  (Equivalently: the two
  maps `L⊗N⊗L⊗N → 𝒪`, `ν₁₄·ν₃₂` and `ν₁₂·ν₃₄`, agree on `ν⁻¹(1) ⊗ x ⊗ u` — a
  symmetry statement.)  Both structures EXIST here, through
  `nonempty_modTensor_assoc` and the braiding of `ModLM Z` — but only ABSTRACTLY:
  `Localization.Monoidal.μ` comes from the localization's universal property, so
  its effect on `modTensorMk`-image sections does not compute.  This is the same
  defect, one level up, that forced `exists_trivialization_modTensor` to be cut,
  and the fix there (build a canonical MORPHISM out of the sheafification instead
  of reading an abstract iso) does not apply, because here the needed map goes
  INTO a tensor product.
* **CONSEQUENCE WORTH ACTING ON: one piece of machinery closes two of this
  module's four remaining leaves.**  The monoidal stalk functor named as route 3
  of `modLocW_whiskerLeft` — `colim_{V ∋ y} (X(V) ⊗_{𝒪(V)} Y(V)) ≅ X_y ⊗_{𝒪_y} Y_y`
  — supplies BOTH: it closes `modLocW_whiskerLeft` (stalkwise `𝟙 ⊗ g_y`), and it
  reduces this leaf to commutative algebra over the local ring `𝒪_y`, where the
  symmetry is mathlib's own `TensorProduct.comm` and computes.  A prover sent at
  the stalk functor is therefore worth two leaves, not one.
* Unchanged and still useful: `Mathlib/Algebra/Category/ModuleCat/Sheaf/`
  `LocallyFree.lean` EXISTS, supplying `SheafOfModules.IsLocallyFree`,
  `LocalGeneratorsData.IsLocallyFreeData` and `GeneratingSections`.  Those are
  DEFINITIONS, not this theorem — "invertible implies locally free of rank one"
  is still absent from the pin — but the finite-generation half above is literally
  a `LocalGeneratorsData`, and `free.generatingSections` gives the rank-one model.

Do NOT weaken this to a hypothesis on the consumers instead: `IsAmpleSheaf` is
what the consumer `exists_isAmpleSheaf_cube_of_isAlgClosed` produces, and it
produces `IsInvertibleSheaf` beside it — so the ALTERNATIVE repair (thread
`IsInvertibleSheaf L` through `nonvanishingLocus_modPullback_of_isAmpleSheaf` and
`isAmpleSheaf_modPullback`, and stop discarding it at the call site in
`AbelianSchemeIsogeny.lean`, where it is currently bound to `-`) is available and
costs nothing mathematically.  It is not taken here because the statement as
given is TRUE, and weakening a true statement to dodge a proof is exactly what
the faithfulness rule forbids. -/
theorem exists_trivialization_of_modTensor_trivial {Z : Scheme.{u}} {L N : Z.Modules}
    {U : Z.Opens}
    (hν : Nonempty ((modTensor L N).restrict U.ι ≅ modUnit (U : Scheme.{u})))
    {z : Z} (hz : z ∈ U) :
    ∃ W : Z.Opens, W ≤ U ∧ z ∈ W ∧ Nonempty (L.restrict W.ι ≅ modUnit (W : Scheme.{u})) := sorry

/-- **AN INVERTIBLE SHEAF OF MODULES IS LOCALLY FREE OF RANK ONE, in the tensor
power form the audit needs** (PROVEN 2026-07-29 over
`exists_trivialization_of_modTensor_trivial`): if SOME positive tensor power of
`A` is trivial on `U`, then `A` itself is trivial on a smaller neighbourhood of
each point of `U`.

One line, because `modTensorPow A (j+1)` IS `modTensor A (modTensorPow A j)`
definitionally; `hk` is used exactly to produce the `j`.  The mathematics, and
the route audit, are on `exists_trivialization_of_modTensor_trivial` above.

The paragraph below is retained from the previous version of this docstring
because its analysis of the argument is still exactly right; note only that the
"stalks are the blocker" reading of it is corrected above.

Stalks first: sheafification preserves
stalks and `(P ⊗ Q)_y = P_y ⊗_{𝒪_y} Q_y` (filtered colimits commute with `⊗`), so
`(A^{⊗k})|_U ≅ 𝒪_U` gives `A_y^{⊗k} ≅ 𝒪_y` for every `y ∈ U`, hence `A_y` is an
invertible module over the LOCAL ring `𝒪_y`, hence free of rank one.  Stalkwise
freeness is NOT enough — that is the step that fails for a general sheaf of
modules, which is why `Z.Modules` being non-quasi-coherent makes this a theorem
rather than an observation.  What supplies the missing finiteness is the tensor
inverse itself: `A|_U ⊗ (A^{⊗(k-1)})|_U ≅ 𝒪_U` means that near each point
`1 = Σ_{i≤m} s_i ⊗ t_i` for FINITELY many sections, and the standard
`m = Σ_i ⟨t_i, m⟩ s_i` computation then shows `A` is generated by `s_1, …, s_m`
there.  Finite type plus a free stalk gives local triviality.

Two amendments to that paragraph, both 2026-07-29 and both recorded in full on
`exists_trivialization_of_modTensor_trivial`: the "near each point
`1 = Σ_i s_i ⊗ t_i`" step is NOT missing from the pin (it is local surjectivity
of the sheafification unit, `Sheafify.lean`'s
`instance : IsLocallySurjective J (toSheafify α φ)`), and the
`m = Σ_i ⟨t_i, m⟩ s_i` step needs the BRAIDING, which is what is actually
blocked here — not merely the stalks. -/
theorem exists_trivialization_of_modTensorPow {Z : Scheme.{u}} {A : Z.Modules} {U : Z.Opens}
    {k : ℕ} (hk : 0 < k) (ψ : (modTensorPow A k).restrict U.ι ≅ modUnit (U : Scheme.{u}))
    {z : Z} (hz : z ∈ U) :
    ∃ W : Z.Opens, W ≤ U ∧ z ∈ W ∧ Nonempty (A.restrict W.ι ≅ modUnit (W : Scheme.{u})) := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = j + 1 := ⟨k - 1, (Nat.succ_pred_eq_of_pos hk).symm⟩
  exact exists_trivialization_of_modTensor_trivial ⟨ψ⟩ hz

/-- **AMPLE IMPLIES INVERTIBLE** (PROVEN 2026-07-28 over
`exists_trivialization_of_modTensorPow`) — **and this is the FAITHFULNESS VERDICT
that `nonvanishingLocus_modPullback_of_isAmpleSheaf` was flagged as needing.**

The recorded worry was: `IsAmpleSheaf L` guarantees only that at each `z` SOME
power `L^{⊗m}` has a trivializing section, and the set of such `m` is a numerical
SEMIGROUP, not all of `ℕ`; so it is not obvious that it says anything about the
particular power `n` appearing in that leaf.  **The worry is real and the
conclusion is that the leaf is nevertheless TRUE**, by the following two steps:

1.  `IsAmpleSheaf L` gives, at each `z`, an `m > 0` and a trivialization of
    `L^{⊗m}` on some `U ∋ z` (that trivialization is inside `NonvanishingAt`
    itself — this is the step that makes ampleness, as defined here, carry local
    triviality at all).
2.  `exists_trivialization_of_modTensorPow` turns a trivialization of `L^{⊗m}`
    into one of `L`.  **This is where the semigroup collapses**: once `L` itself
    is locally trivial, every power is, and `n` is no longer special.

So no hypothesis needs adding anywhere.  The counterexample recorded on
`nonvanishingLocus_modPullback_of_isAmpleSheaf` (the skyscraper `k` at the origin
of `Spec k[u]`) is still exactly right about why the hypothesis-free statement is
FALSE, and it is ruled out here at step 1: no power of that skyscraper is
locally trivial at the origin. -/
theorem isInvertibleSheaf_of_isAmpleSheaf {Z : Scheme.{u}} {L : Z.Modules}
    (h : IsAmpleSheaf L) : IsInvertibleSheaf L := by
  intro z
  obtain ⟨m, hm, s, V, hzV, -, hloc⟩ := h z
  have hz : z ∈ nonvanishingLocus (modTensorPow L m) s := by rw [hloc]; exact hzV
  obtain ⟨U, hzU, φ, -⟩ := hz
  obtain ⟨W, -, hzW, hW⟩ := exists_trivialization_of_modTensorPow hm φ hzU
  exact ⟨W, hzW, hW⟩

/-! ### Tensor powers of a global section -/

/-! `modTensorMk` and `tensorSection` used to be declared here.  They were
HOISTED (2026-07-28) to `§ Tensor products of global sections`, immediately after
`modTensorPowUnitIso`, because `exists_modPullback_modTensor` states its pinning
clause in terms of `tensorSection`.  Nothing else about them changed. -/

/-- **`s^{⊗k}`**, right-nested onto `1 ∈ Γ(𝒪_Z, ⊤)` exactly as `modTensorPow` is
right-nested onto `modUnit`. -/
noncomputable def tensorPowSection {Z : Scheme.{u}} {A : Z.Modules} (s : Γ(A, ⊤)) :
    ∀ k : ℕ, Γ(modTensorPow A k, ⊤)
  | 0 => unitOne Z
  | (k + 1) => tensorSection s (tensorPowSection s k)

/-! ### The CANONICAL trivialization of a tensor product

**NEW BLOCK, 2026-07-29.**  Everything from here to
`exists_trivialization_modTensor` exists to build a trivialization of `L ⊗ M`
over `U` whose effect on `tensorSection` is KNOWN.  The route recorded on that
leaf ("strengthen `nonempty_restrict_modTensor` to a named comparison
`(L ⊗ M)|_U ≅ L|_U ⊗ M|_U`, which wants a canonical
`nonempty_modPullback_modTensor`") is NOT the route taken, and does not have to
be: a canonical comparison is more than the leaf needs.

What the leaf needs is a canonical MORPHISM `(L ⊗ M)|_U ⟶ 𝒪_U` with the right
effect on sections, plus the knowledge — from any `Nonempty` comparison — that
`(L ⊗ M)|_U` is abstractly trivial.  The morphism direction is free from the
universal property of sheafification, because it maps OUT of `modTensor`:

* `pushUnitMul` — `(f_*𝒪_X) ⊗ (f_*𝒪_X) ⟶ f_*𝒪_X`, multiplication.  This is the
  only genuinely new construction, and it is elementary: restriction along
  `Opens.map f.base` is a ring map, so multiplication is `Γ(Y,V)`-balanced.
* `pushUnitOfTrivialization` — `φ : L|_U ≅ 𝒪_U` read as `L ⟶ (U.ι)_*𝒪_U`, by
  the unit of `restrictAdjunction`.
* `tensorPairing` — `L.val ⊗ M.val ⟶ ((U.ι)_*𝒪_U).val`, `x ⊗ y ↦ φ(x)·χ(y)`,
  at PRESHEAF level, where the tensor product is objectwise.
* `tensorPairingSheaf` / `trivializationMulHom` — its transposes across the
  sheafification adjunction and `restrictAdjunction`.  Both counits COMPUTE
  (`restrictAdjunction_counit_app_app` is `rfl`; the sheafification counit is
  `modSheafifyValIso`), which is why the section identity is provable.

That `trivializationMulHom` is an ISO is then a one-line unit argument, and this
is the step that consumes the anonymous comparison: writing `ν` for any
isomorphism `(L ⊗ M)|_U ≅ 𝒪_U` (from `nonempty_restrict_modTensor`, `φ`, `χ`),
`ν⁻¹ ≫ trivializationMulHom φ χ` is an ENDOMORPHISM of `𝒪_U`, hence
multiplication by its value `c` at `1` (`unitHomApply_eq`).  Evaluating at the
distinguished section `tensorUnitSection = φ⁻¹(1) ⊗ χ⁻¹(1)`, whose image under
`trivializationMulHom` is `1` by construction, gives `d · c = 1`.  So `c` is a
unit, `isIso_of_isUnit_unitHom` applies, and no property of `ν` beyond its
existence is ever used — which is exactly the right shape, since `ν` is
anonymous.

So this block waits on `nonempty_modPullback_modTensor` (through
`nonempty_restrict_modTensor`) for EXISTENCE only, and on nothing else. -/

section PushforwardUnit
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- `f_*𝒪_X`, as an `𝒪_Y`-module. -/
noncomputable abbrev pushUnit : Y.Modules := (Scheme.Modules.pushforward f).obj (modUnit X)

/-- `(f_*𝒪_X).val`, retyped over `Y.presheaf ⋙ forget₂ _ _` so that the monoidal
structure on `ModuleCat` at each open is found by instance search. -/
noncomputable abbrev pushUnitVal :
    PresheafOfModules.{u} (Y.presheaf ⋙ forget₂ CommRingCat RingCat) := (pushUnit f).val

/-- `Γ(f_*𝒪_X, V) = Γ(X, f⁻¹V)` is definitional; this names the direction into
the module, so that `*` and `+` can be written on the other side. -/
noncomputable def pushUnitEq {V : Y.Opensᵒᵖ} (x : Γ(X, f ⁻¹ᵁ V.unop)) :
    ((pushUnitVal f).obj V) := x

/-- The inverse retyping of `pushUnitEq`. -/
noncomputable def pushUnitEq' {V : Y.Opensᵒᵖ} (x : ((pushUnitVal f).obj V)) :
    Γ(X, f ⁻¹ᵁ V.unop) := x

/-- Multiplication on `f_*𝒪_X` over one open.  Balanced over `Γ(Y, V)` because
the `Γ(Y,V)`-action is through the ring map `f.app V`. -/
noncomputable def pushUnitMulApp (V : Y.Opensᵒᵖ) :
    (pushUnitVal f).obj V ⊗ (pushUnitVal f).obj V ⟶ (pushUnitVal f).obj V :=
  ModuleCat.MonoidalCategory.tensorLift
    (fun x y => pushUnitEq f (pushUnitEq' f x * pushUnitEq' f y))
    (by intro x₁ x₂ y
        show pushUnitEq f ((pushUnitEq' f x₁ + pushUnitEq' f x₂) * pushUnitEq' f y)
          = pushUnitEq f (pushUnitEq' f x₁ * pushUnitEq' f y
              + pushUnitEq' f x₂ * pushUnitEq' f y)
        rw [add_mul])
    (by intro a x y
        show pushUnitEq f ((f.app V.unop a * pushUnitEq' f x) * _) = _
        show _ = pushUnitEq f (f.app V.unop a * (pushUnitEq' f x * pushUnitEq' f y))
        rw [mul_assoc])
    (by intro x y₁ y₂
        show pushUnitEq f (pushUnitEq' f x * (pushUnitEq' f y₁ + pushUnitEq' f y₂))
          = pushUnitEq f (pushUnitEq' f x * pushUnitEq' f y₁
              + pushUnitEq' f x * pushUnitEq' f y₂)
        rw [mul_add])
    (by intro a x y
        show pushUnitEq f (pushUnitEq' f x * (f.app V.unop a * pushUnitEq' f y)) = _
        show _ = pushUnitEq f (f.app V.unop a * (pushUnitEq' f x * pushUnitEq' f y))
        rw [mul_left_comm])

/-- **Multiplication `(f_*𝒪_X) ⊗ (f_*𝒪_X) ⟶ f_*𝒪_X`** (PROVEN 2026-07-29).
Naturality is `map_mul` for the restriction ring map. -/
noncomputable def pushUnitMul :
    PresheafOfModules.Monoidal.tensorObj (R := Y.presheaf) (pushUnitVal f) (pushUnitVal f) ⟶
      pushUnitVal f where
  app V := pushUnitMulApp f V
  naturality := by
    intro V W i
    refine ModuleCat.MonoidalCategory.tensor_ext (fun x y => ?_)
    show pushUnitEq f (X.presheaf.map ((Opens.map f.base).map i.unop).op (pushUnitEq' f x)
          * X.presheaf.map ((Opens.map f.base).map i.unop).op (pushUnitEq' f y))
      = pushUnitEq f (X.presheaf.map ((Opens.map f.base).map i.unop).op
          (pushUnitEq' f x * pushUnitEq' f y))
    rw [map_mul]

end PushforwardUnit

section TensorTrivialization
variable {Z : Scheme.{u}} {L M : Z.Modules} {U : Z.Opens}

/-- `φ : L|_U ≅ 𝒪_U`, read as a morphism `L ⟶ (U.ι)_* 𝒪_U` on `Z`. -/
noncomputable def pushUnitOfTrivialization
    (φ : L.restrict U.ι ≅ modUnit (U : Scheme.{u})) : L ⟶ pushUnit U.ι :=
  (Scheme.Modules.restrictAdjunction U.ι).unit.app L ≫
    (Scheme.Modules.pushforward U.ι).map φ.hom

lemma pushUnitOfTrivialization_app (φ : L.restrict U.ι ≅ modUnit (U : Scheme.{u}))
    (V : Z.Opens) (x : Γ(L, V)) :
    pushUnitEq' U.ι ((pushUnitOfTrivialization φ).val.app (op V) x)
      = φ.hom.val.app (op (U.ι ⁻¹ᵁ V))
          (L.presheaf.map (homOfLE (U.ι.image_preimage_le V)).op x) := rfl

/-- The presheaf-level pairing `L ⊗ M ⟶ (U.ι)_* 𝒪_U`, `x ⊗ y ↦ φ(x)·χ(y)`. -/
noncomputable def tensorPairing (φ : L.restrict U.ι ≅ modUnit (U : Scheme.{u}))
    (χ : M.restrict U.ι ≅ modUnit (U : Scheme.{u})) :
    PresheafOfModules.Monoidal.tensorObj (R := Z.presheaf) L.val M.val ⟶ pushUnitVal U.ι :=
  PresheafOfModules.Monoidal.tensorHom (pushUnitOfTrivialization φ).val
      (pushUnitOfTrivialization χ).val ≫ pushUnitMul U.ι

/-- Its transpose across the sheafification adjunction, written with the counit
(`modSheafifyValIso`) rather than `homEquiv`, so that it computes.  Going through
`Adjunction.homEquiv` instead makes the evaluation lemma below time out, because
the `restrictScalars (𝟙 _)` in the right adjoint has to be defeq-unfolded. -/
noncomputable def tensorPairingSheaf (φ : L.restrict U.ι ≅ modUnit (U : Scheme.{u}))
    (χ : M.restrict U.ι ≅ modUnit (U : Scheme.{u})) :
    modTensor L M ⟶ pushUnit U.ι :=
  (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).map (tensorPairing φ χ) ≫
    (modSheafifyValIso (pushUnit U.ι)).hom

/-- **The canonical trivialization morphism `(L ⊗ M)|_U ⟶ 𝒪_U`.** -/
noncomputable def trivializationMulHom (φ : L.restrict U.ι ≅ modUnit (U : Scheme.{u}))
    (χ : M.restrict U.ι ≅ modUnit (U : Scheme.{u})) :
    (modTensor L M).restrict U.ι ⟶ modUnit (U : Scheme.{u}) :=
  (Scheme.Modules.restrictFunctor U.ι).map (tensorPairingSheaf φ χ) ≫
    (Scheme.Modules.restrictAdjunction U.ι).counit.app (modUnit (U : Scheme.{u}))

/-- Applying a presheaf-of-modules morphism equation at one open and one section. -/
lemma presheafHom_congr_apply {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    {A B : PresheafOfModules.{u} R} {m₁ m₂ : A ⟶ B} (h : m₁ = m₂) (V : Cᵒᵖ) (z : A.obj V) :
    m₁.app V z = m₂.app V z := by rw [h]

/-- The transpose undoes the sheafification unit: naturality of the unit plus the
right triangle identity. -/
lemma tensorPairingSheaf_modTensorMk (φ : L.restrict U.ι ≅ modUnit (U : Scheme.{u}))
    (χ : M.restrict U.ι ≅ modUnit (U : Scheme.{u})) (V : Z.Opensᵒᵖ)
    (z : (PresheafOfModules.Monoidal.tensorObj (R := Z.presheaf) L.val M.val).obj V) :
    (tensorPairingSheaf φ χ).val.app V ((modTensorMk L M).app V z)
      = (tensorPairing φ χ).app V z := by
  have hnat := presheafHom_congr_apply
    ((PresheafOfModules.sheafificationAdjunction (𝟙 Z.ringCatSheaf.obj)).unit.naturality
      (tensorPairing φ χ)) V z
  have htri := presheafHom_congr_apply
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 Z.ringCatSheaf.obj)).right_triangle_components (pushUnit U.ι)) V
      ((tensorPairing φ χ).app V z)
  have hnat' : ((PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).map
        (tensorPairing φ χ)).val.app V ((modTensorMk L M).app V z)
      = ((PresheafOfModules.sheafificationAdjunction (𝟙 Z.ringCatSheaf.obj)).unit.app
          (pushUnitVal U.ι)).app V ((tensorPairing φ χ).app V z) := hnat.symm
  have htri' : ((modSheafifyValIso (pushUnit U.ι)).hom).val.app V
        (((PresheafOfModules.sheafificationAdjunction (𝟙 Z.ringCatSheaf.obj)).unit.app
          (pushUnitVal U.ι)).app V ((tensorPairing φ χ).app V z))
      = (tensorPairing φ χ).app V z := htri
  show ((modSheafifyValIso (pushUnit U.ι)).hom).val.app V
      (((PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).map (tensorPairing φ χ)).val.app V
        ((modTensorMk L M).app V z)) = _
  rw [hnat']
  exact htri'

/-- `trivializedSection` for a bare morphism rather than an isomorphism. -/
noncomputable def trivializedSectionHom {A : Z.Modules}
    (θ : A.restrict U.ι ⟶ modUnit (U : Scheme.{u})) (s : Γ(A, ⊤)) : Γ((U : Scheme.{u}), ⊤) :=
  θ.val.app (op ⊤)
    ((Scheme.Modules.restrictAppIso (f := U.ι) A ⊤).inv
      (A.presheaf.map (homOfLE le_top).op s))

lemma restrictAppIso_inv_apply {A : Z.Modules} (W : (U : Scheme.{u}).Opens)
    (x : Γ(A, U.ι ''ᵁ W)) :
    (Scheme.Modules.restrictAppIso (f := U.ι) A W).inv x = x := rfl

/-- `Z.Opens` is a thin category, so any endomorphism of an open acts trivially. -/
lemma presheafMap_self_apply {A : Z.Modules} {V : Z.Opens}
    (g : op V ⟶ op V) (y : Γ(A, V)) : A.presheaf.map g y = y := by
  rw [Subsingleton.elim g (𝟙 _), CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]

lemma pushUnitOfTrivialization_top (φ : L.restrict U.ι ≅ modUnit (U : Scheme.{u}))
    (x : Γ(L, U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens))) :
    (U : Scheme.{u}).presheaf.map (eqToHom (U.ι.preimage_image_eq ⊤).symm).op
      (pushUnitEq' U.ι ((pushUnitOfTrivialization φ).val.app
        (op (U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens))) x))
      = φ.hom.val.app (op (⊤ : (U : Scheme.{u}).Opens)) x := by
  rw [pushUnitOfTrivialization_app]
  calc (U : Scheme.{u}).presheaf.map (eqToHom (U.ι.preimage_image_eq ⊤).symm).op
        (φ.hom.val.app (op (U.ι ⁻¹ᵁ (U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens))))
          (L.presheaf.map (homOfLE (U.ι.image_preimage_le _)).op x))
      = φ.hom.val.app (op (⊤ : (U : Scheme.{u}).Opens))
          (L.presheaf.map ((Scheme.Hom.opensFunctor U.ι).map
              (eqToHom (U.ι.preimage_image_eq ⊤).symm)).op
            (L.presheaf.map (homOfLE (U.ι.image_preimage_le _)).op x)) :=
        (PresheafOfModules.naturality_apply φ.hom.val
          (X := op (U.ι ⁻¹ᵁ (U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens))))
          (Y := op (⊤ : (U : Scheme.{u}).Opens))
          (eqToHom (U.ι.preimage_image_eq ⊤).symm).op _).symm
    _ = φ.hom.val.app (op (⊤ : (U : Scheme.{u}).Opens)) x := by
        refine congrArg _ ?_
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, presheafMap_self_apply]

lemma pushUnitOfTrivialization_top_global (φ : L.restrict U.ι ≅ modUnit (U : Scheme.{u}))
    (a : Γ(L, ⊤)) :
    (U : Scheme.{u}).presheaf.map (eqToHom (U.ι.preimage_image_eq ⊤).symm).op
      (pushUnitEq' U.ι ((pushUnitOfTrivialization φ).val.app
        (op (U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens))) (L.presheaf.map (homOfLE le_top).op a)))
      = trivializedSection φ a := by
  rw [pushUnitOfTrivialization_top]
  unfold trivializedSection
  rw [restrictAppIso_inv_apply]

lemma trivializationMulHom_app_top (φ : L.restrict U.ι ≅ modUnit (U : Scheme.{u}))
    (χ : M.restrict U.ι ≅ modUnit (U : Scheme.{u}))
    (w : Γ(modTensor L M, U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens))) :
    (trivializationMulHom φ χ).val.app (op ⊤) w
      = (U : Scheme.{u}).presheaf.map (eqToHom (U.ι.preimage_image_eq ⊤).symm).op
          (pushUnitEq' U.ι ((tensorPairingSheaf φ χ).val.app
            (op (U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens))) w)) := rfl

lemma tensorSection_restrict (a : Γ(L, ⊤)) (b : Γ(M, ⊤)) :
    (modTensor L M).presheaf.map
        (homOfLE (le_top : U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens) ≤ ⊤)).op (tensorSection a b)
      = (modTensorMk L M).app (op (U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens)))
          (L.presheaf.map (homOfLE le_top).op a ⊗ₜ M.presheaf.map (homOfLE le_top).op b) :=
  (PresheafOfModules.naturality_apply (modTensorMk L M)
    (X := op (⊤ : Z.Opens)) (Y := op (U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens)))
    (homOfLE le_top).op (a ⊗ₜ b)).symm

lemma tensorPairing_tmul (φ : L.restrict U.ι ≅ modUnit (U : Scheme.{u}))
    (χ : M.restrict U.ι ≅ modUnit (U : Scheme.{u})) (V : Z.Opens)
    (x : Γ(L, V)) (y : Γ(M, V)) :
    pushUnitEq' U.ι ((tensorPairing φ χ).app (op V) (x ⊗ₜ y))
      = pushUnitEq' U.ι ((pushUnitOfTrivialization φ).val.app (op V) x)
        * pushUnitEq' U.ι ((pushUnitOfTrivialization χ).val.app (op V) y) := rfl

/-- **The canonical trivialization morphism multiplies sections** (PROVEN
2026-07-29).  This is the identity the leaf below asks for; what is left there is
only that the morphism is invertible. -/
theorem trivializedSectionHom_trivializationMulHom
    (φ : L.restrict U.ι ≅ modUnit (U : Scheme.{u}))
    (χ : M.restrict U.ι ≅ modUnit (U : Scheme.{u})) (a : Γ(L, ⊤)) (b : Γ(M, ⊤)) :
    trivializedSectionHom (trivializationMulHom φ χ) (tensorSection a b)
      = trivializedSection φ a * trivializedSection χ b := by
  unfold trivializedSectionHom
  rw [restrictAppIso_inv_apply, trivializationMulHom_app_top, tensorSection_restrict,
    tensorPairingSheaf_modTensorMk, tensorPairing_tmul, map_mul,
    pushUnitOfTrivialization_top_global, pushUnitOfTrivialization_top_global]

/-! #### Endomorphisms of `𝒪_W`

The general form of the transition-function computation already done at `⊤` in
`nonvanishingLocus_modUnit`: an endomorphism of `𝒪_W` is multiplication by its
value at `1`, and it is an isomorphism as soon as that value is a unit. -/

/-- `1 : Γ(W, V)`, read as a section of the unit module over `V`. -/
def unitOneAt (W : Scheme.{u}) (V : W.Opens) : Γ(modUnit W, V) := (1 : Γ(W, V))

/-- An endomorphism of `𝒪_W` applied to a section over `V`, both sides typed in
`Γ(W, V)`.  Same role as `unitEndoApply` above, for a bare morphism and over an
arbitrary open. -/
noncomputable def unitHomApply {W : Scheme.{u}} (α : modUnit W ⟶ modUnit W) {V : W.Opens}
    (a : Γ(W, V)) : Γ(W, V) := α.val.app (op V) a

lemma unitHomApply_eq {W : Scheme.{u}} (α : modUnit W ⟶ modUnit W) {V : W.Opens}
    (a : Γ(W, V)) :
    unitHomApply α a = a * unitHomApply α (1 : Γ(W, V)) := by
  have h2 : unitHomApply α (a * 1) = a * unitHomApply α (1 : Γ(W, V)) :=
    (α.val.app (op V)).hom.map_smul a (unitOneAt W V)
  simpa using h2

lemma unitHom_app_one {W : Scheme.{u}} (α : modUnit W ⟶ modUnit W) (V : W.Opens) :
    unitHomApply α (1 : Γ(W, V))
      = W.presheaf.map (homOfLE le_top).op (unitHomApply α (1 : Γ(W, ⊤))) := by
  have h1 : ((modUnit W).val.map (homOfLE (le_top : V ≤ ⊤)).op) (unitOneAt W ⊤)
      = unitOneAt W V :=
    PresheafOfModules.unit_map_one W.ringCatSheaf.obj (homOfLE le_top).op
  have hnat := PresheafOfModules.naturality_apply α.val
    (X := op (⊤ : W.Opens)) (Y := op V) (homOfLE le_top).op (unitOneAt W ⊤)
  rw [h1] at hnat
  exact hnat

/-- The compatible family of restrictions of a global section of `𝒪_W`. -/
noncomputable def unitSectionOf {W : Scheme.{u}} (c : Γ(W, ⊤)) : (modUnit W).sections :=
  PresheafOfModules.sectionsMk (fun V => W.presheaf.map (homOfLE le_top).op c)
    (fun V V' g => by
      show W.presheaf.map g (W.presheaf.map (homOfLE le_top).op c) = _
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      congr 1)

/-- Multiplication by a global section of `𝒪_W`, as an endomorphism of `𝒪_W`.
Built through `SheafOfModules.unitHomEquiv`, so no naturality proof is needed. -/
noncomputable def unitMulHom {W : Scheme.{u}} (c : Γ(W, ⊤)) : modUnit W ⟶ modUnit W :=
  (SheafOfModules.unitHomEquiv (modUnit W)).symm (unitSectionOf c)

lemma unitMulHom_app_one {W : Scheme.{u}} (c : Γ(W, ⊤)) (V : W.Opens) :
    unitHomApply (unitMulHom c) (1 : Γ(W, V))
      = W.presheaf.map (homOfLE le_top).op c :=
  congrArg (fun s : (modUnit W).sections => s.val (op V))
    ((SheafOfModules.unitHomEquiv (modUnit W)).apply_symm_apply (unitSectionOf c))

/-- **An endomorphism of `𝒪_W` whose value at `1` is a unit is an isomorphism**
(PROVEN 2026-07-29). -/
theorem isIso_of_isUnit_unitHom {W : Scheme.{u}} (α : modUnit W ⟶ modUnit W)
    (h : IsUnit (unitHomApply α (1 : Γ(W, ⊤)))) : IsIso α := by
  obtain ⟨v, hv⟩ := h
  refine ⟨unitMulHom ((v⁻¹ : (Γ(W, ⊤))ˣ) : Γ(W, ⊤)), ?_, ?_⟩
  · refine (SheafOfModules.unitHomEquiv (modUnit W)).injective
      (PresheafOfModules.sections_ext _ _ (fun V => ?_))
    show unitHomApply (unitMulHom ((v⁻¹ : (Γ(W, ⊤))ˣ) : Γ(W, ⊤)))
        (unitHomApply α (1 : Γ(W, V.unop))) = (1 : Γ(W, V.unop))
    rw [unitHom_app_one, unitHomApply_eq, unitMulHom_app_one, ← map_mul, ← hv,
      v.mul_inv, map_one]
  · refine (SheafOfModules.unitHomEquiv (modUnit W)).injective
      (PresheafOfModules.sections_ext _ _ (fun V => ?_))
    show unitHomApply α (unitHomApply (unitMulHom ((v⁻¹ : (Γ(W, ⊤))ˣ) : Γ(W, ⊤)))
        (1 : Γ(W, V.unop))) = (1 : Γ(W, V.unop))
    rw [unitMulHom_app_one, unitHomApply_eq, unitHom_app_one, ← map_mul, ← hv,
      v.inv_mul, map_one]

/-- `φ⁻¹(1) ⊗ χ⁻¹(1)`, a section of `L ⊗ M` over `U`.  This is the witness that
makes `trivializationMulHom` surjective on `𝒪_U`, and it is where `φ` and `χ`
being ISOMORPHISMS (rather than mere maps) is used. -/
noncomputable def tensorUnitSection (φ : L.restrict U.ι ≅ modUnit (U : Scheme.{u}))
    (χ : M.restrict U.ι ≅ modUnit (U : Scheme.{u})) :
    Γ(modTensor L M, U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens)) :=
  (modTensorMk L M).app (op (U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens)))
    (φ.inv.val.app (op ⊤) (unitOne (U : Scheme.{u})) ⊗ₜ
      χ.inv.val.app (op ⊤) (unitOne (U : Scheme.{u})))

lemma trivializationMulHom_tensorUnitSection
    (φ : L.restrict U.ι ≅ modUnit (U : Scheme.{u}))
    (χ : M.restrict U.ι ≅ modUnit (U : Scheme.{u})) :
    (trivializationMulHom φ χ).val.app (op ⊤) (tensorUnitSection φ χ)
      = (1 : Γ((U : Scheme.{u}), ⊤)) := by
  have hφ : φ.hom.val.app (op (⊤ : (U : Scheme.{u}).Opens))
      (φ.inv.val.app (op ⊤) (unitOne (U : Scheme.{u}))) = (1 : Γ((U : Scheme.{u}), ⊤)) :=
    presheafHom_congr_apply (congrArg SheafOfModules.Hom.val φ.inv_hom_id) (op ⊤) _
  have hχ : χ.hom.val.app (op (⊤ : (U : Scheme.{u}).Opens))
      (χ.inv.val.app (op ⊤) (unitOne (U : Scheme.{u}))) = (1 : Γ((U : Scheme.{u}), ⊤)) :=
    presheafHom_congr_apply (congrArg SheafOfModules.Hom.val χ.inv_hom_id) (op ⊤) _
  rw [tensorUnitSection, trivializationMulHom_app_top, tensorPairingSheaf_modTensorMk,
    tensorPairing_tmul, map_mul, pushUnitOfTrivialization_top, pushUnitOfTrivialization_top,
    hφ, hχ, mul_one]

end TensorTrivialization

/-- **A TRIVIALIZATION OF A TENSOR PRODUCT MULTIPLIES SECTIONS** (PROVEN
2026-07-29; cut 2026-07-28 out of `exists_trivialization_tensorPow`).

Given trivializations of `L` and `M` over one open `U`, there is a trivialization
of `L ⊗ M` over `U` that carries `a ⊗ b` to the PRODUCT of the two trivialized
sections.

**WHY THIS LEAF EXISTS — the ROUTE recorded on `exists_trivialization_tensorPow`
could not work as written, and this is a correction, not a restatement.**  That
route said: "induct on `k`, building `ψ` out of `nonempty_restrict_modTensor` and
`modTensorUnitLeftIso` exactly as `isInvertibleSheaf_modTensor` does, and check
the section identity against `tensorSection`'s definition".  The induction is
fine and is now discharged below.  The "check the section identity" step is not:
**`nonempty_restrict_modTensor` delivers `Nonempty`, i.e. an ARBITRARY
isomorphism**, and `trivializedSection` through an arbitrary isomorphism is not
computable by any amount of unfolding.  Concretely, post-composing that anonymous
iso with multiplication by any unit `c : Γ(U, ⊤)ˣ` satisfies every clause
`nonempty_restrict_modTensor` states while multiplying the trivialized section by
`c` — so the identity `a ⊗ₜ b ↦ a * b` is simply not pinned by the stated inputs.
The missing ingredient is a comparison isomorphism with a KNOWN effect on
sections, which is what this leaf asks for.

**Not vacuous, and not under-pinned.**  The `∀ a b` clause pins `θ` on every pure
tensor of global sections, which is exactly what the consumer consumes; a `θ`
differing by a unit fails it.  It is also satisfiable: the presheaf tensor is
OBJECTWISE (`PresheafOfModules.Monoidal.tensorObj` sends `X` to
`M₁.obj X ⊗ M₂.obj X`), and the left unitor sends `r ⊗ₜ m` to `r • m`, so the
canonical comparison composed with `modTensorMapIso φ χ ≪≫ modTensorUnitLeftIso`
has precisely this effect.

**THE RECORDED ROUTE WAS NOT NEEDED — corrected 2026-07-29.**  It read:

> the honest form is to strengthen `nonempty_restrict_modTensor` from `Nonempty`
> to a NAMED comparison isomorphism `(L ⊗ M)|_f ≅ L|_f ⊗ M|_f` carrying
> `(a ⊗ b)|_f` to `a|_f ⊗ b|_f`, which in turn wants a canonical
> `nonempty_modPullback_modTensor` rather than an anonymous one … the whole
> content is that sheafification commutes with restriction to an open subsite.

Every clause of that is TRUE and none of it is required, because a canonical
comparison ISOMORPHISM is strictly more than this leaf asks for.  The leaf asks
for a map `(L ⊗ M)|_U ⟶ 𝒪_U` with a known effect on sections, and maps OUT of
`modTensor` are free: `modTensor` is a sheafification, so its universal property
supplies them from presheaf-level data, where `⊗` is objectwise.  Nothing has to
commute with anything.  See the section heading above for the construction; the
one new ingredient is `pushUnitMul`, multiplication on `(U.ι)_*𝒪_U`.

The `Nonempty` comparison is still used — but only for EXISTENCE of some
trivialization, never for its value, which is exactly the strength it has.  So
this leaf did not, after all, need "strictly more than
`nonempty_modPullback_modTensor` gives"; it needed the same thing used
differently. -/
theorem exists_trivialization_modTensor {Z : Scheme.{u}} {L M : Z.Modules} {U : Z.Opens}
    (φ : L.restrict U.ι ≅ modUnit (U : Scheme.{u}))
    (χ : M.restrict U.ι ≅ modUnit (U : Scheme.{u})) :
    ∃ θ : (modTensor L M).restrict U.ι ≅ modUnit (U : Scheme.{u}),
      ∀ (a : Γ(L, ⊤)) (b : Γ(M, ⊤)),
        trivializedSection θ (tensorSection a b)
          = trivializedSection φ a * trivializedSection χ b := by
  obtain ⟨e⟩ := nonempty_restrict_modTensor U.ι L M
  obtain ⟨ν⟩ : Nonempty ((modTensor L M).restrict U.ι ≅ modUnit (U : Scheme.{u})) :=
    ⟨e ≪≫ modTensorMapIso φ χ ≪≫ modTensorUnitLeftIso _⟩
  have hfac : trivializationMulHom φ χ = ν.hom ≫ (ν.inv ≫ trivializationMulHom φ χ) := by
    rw [← Category.assoc, ν.hom_inv_id, Category.id_comp]
  have hu : IsUnit (unitHomApply (ν.inv ≫ trivializationMulHom φ χ)
      (1 : Γ((U : Scheme.{u}), ⊤))) := by
    have h1 : (trivializationMulHom φ χ).val.app (op ⊤) (tensorUnitSection φ χ)
        = unitHomApply (ν.inv ≫ trivializationMulHom φ χ)
            (ν.hom.val.app (op ⊤) (tensorUnitSection φ χ)) :=
      presheafHom_congr_apply (congrArg SheafOfModules.Hom.val hfac) (op ⊤) _
    rw [trivializationMulHom_tensorUnitSection, unitHomApply_eq, mul_comm] at h1
    exact IsUnit.of_mul_eq_one _ h1.symm
  haveI hiso : IsIso (ν.inv ≫ trivializationMulHom φ χ) := isIso_of_isUnit_unitHom _ hu
  haveI hiso2 : IsIso (trivializationMulHom φ χ) := by rw [hfac]; infer_instance
  exact ⟨asIso (trivializationMulHom φ χ), fun a b =>
    trivializedSectionHom_trivializationMulHom φ χ a b⟩

/-- **`s^{⊗k}` read through the `k`-th power of a trivialization is the `k`-th
power of the trivialized section** (PROVEN 2026-07-28 over
`exists_trivialization_modTensor`).

Induction on `k`, right-nested exactly as `modTensorPow` and `tensorPowSection`
are.  The base case is the canonical trivialization of `𝒪_Z` over `U`, whose
trivialized section is `U.ι.appTop 1 = 1` because `appTop` is a ring map; the
step is one application of `exists_trivialization_modTensor` and `pow_succ'`.

The bookkeeping half of the old ROUTE is therefore discharged; the half that did
not survive contact is recorded on `exists_trivialization_modTensor` above. -/
theorem exists_trivialization_tensorPow {Z : Scheme.{u}} {A : Z.Modules} {U : Z.Opens}
    (φ : A.restrict U.ι ≅ modUnit (U : Scheme.{u})) (s : Γ(A, ⊤)) (k : ℕ) :
    ∃ ψ : (modTensorPow A k).restrict U.ι ≅ modUnit (U : Scheme.{u}),
      trivializedSection ψ (tensorPowSection s k) = trivializedSection φ s ^ k := by
  induction k with
  | zero =>
    refine ⟨Scheme.Modules.restrictUnitIso U.ι, ?_⟩
    rw [pow_zero]
    exact (trivializedSection_restrictUnitIso U (1 : Γ(Z, ⊤))).trans (map_one _)
  | succ k ih =>
    obtain ⟨ψ, hψ⟩ := ih
    obtain ⟨θ, hθ⟩ := exists_trivialization_modTensor φ ψ
    exact ⟨θ, (hθ s (tensorPowSection s k)).trans (by rw [hψ, pow_succ'])⟩

/-- **Tensor powers of a section do not change the non-vanishing locus** (PROVEN
2026-07-28).

**No hypothesis on `A`** — in particular no `V`, no `hloc`, no invertibility.
The `⊇` direction is formal; the `⊆` direction is where
`exists_trivialization_of_modTensorPow` (Stacks 01CV) does its work, converting a
trivialization of `A^{⊗k}` near a point into one of `A`, after which
`Scheme.basicOpen_pow` finishes.  This is the statement that shows
`exists_tensorPowSection`'s `hloc` was inert. -/
theorem nonvanishingLocus_tensorPowSection {Z : Scheme.{u}} (A : Z.Modules) (s : Γ(A, ⊤))
    {k : ℕ} (hk : 0 < k) :
    nonvanishingLocus (modTensorPow A k) (tensorPowSection s k) = nonvanishingLocus A s := by
  ext z
  constructor
  · rintro ⟨U, hzU, ψ, hmem⟩
    obtain ⟨W, -, hzW, ⟨φ⟩⟩ := exists_trivialization_of_modTensorPow hk ψ hzU
    obtain ⟨ψ', hψ'⟩ := exists_trivialization_tensorPow φ s k
    have h1 : NonvanishingAt (modTensorPow A k) (tensorPowSection s k) z := ⟨U, hzU, ψ, hmem⟩
    rw [nonvanishingAt_iff_trivializedSection _ ψ' hzW, hψ', Scheme.basicOpen_pow _ _ hk] at h1
    exact (nonvanishingAt_iff_trivializedSection s φ hzW).2 h1
  · rintro ⟨U, hzU, φ, hmem⟩
    obtain ⟨ψ, hψ⟩ := exists_trivialization_tensorPow φ s k
    refine (nonvanishingAt_iff_trivializedSection _ ψ hzU).2 ?_
    rw [hψ, Scheme.basicOpen_pow _ _ hk]
    exact hmem

/-- **Tensor powers of a global section** (PROVEN 2026-07-28 over
`nonvanishingLocus_tensorPowSection`): `s^{⊗k}`, with the same non-vanishing
locus as `s`.

**FAITHFULNESS — CORRECTED 2026-07-28.**  The note that used to stand here said
that `hloc` "is carried deliberately and is not decoration", because the `⊆` half
"must rule out a point at which `A^{⊗k}` happens to be invertible with `s^{⊗k}` a
generator while `A` itself is not invertible", and concluded that a version
without `V` and `hloc` "should be treated as unproven-and-suspect".

The diagnosis of the hard half is exactly right; the conclusion is wrong on both
counts.  `hloc` does **not** rule that point out — it says nothing whatever about
points outside `V`, which is precisely where the danger is.  What rules it out is
`exists_trivialization_of_modTensorPow` (Stacks 01CV), which needs no `V` and no
`hloc`.  So the general statement `nonvanishingLocus (A^{⊗k}) (s^{⊗k}) =
nonvanishingLocus A s` is TRUE with no hypothesis on `A`, and is proven above;
this leaf is a one-line corollary of it, kept in this shape only because
`isAmpleSheaf_modTensorPow` calls it this way.

`V` and `hloc` are therefore inert, and `hloc` is consumed only as the final
rewrite. -/
theorem exists_tensorPowSection {Z : Scheme.{u}} (A : Z.Modules) (s : Γ(A, ⊤)) {k : ℕ}
    (hk : 0 < k) (V : Z.Opens) (hloc : nonvanishingLocus A s = (V : Set Z)) :
    ∃ t : Γ(modTensorPow A k, ⊤),
      nonvanishingLocus (modTensorPow A k) t = (V : Set Z) :=
  ⟨tensorPowSection s k, by rw [nonvanishingLocus_tensorPowSection A s hk]; exact hloc⟩

/-! ### The pullback of a global section, through the canonical isomorphisms

(PROVEN 2026-07-28.)  Every isomorphism appearing in the trivialization calculus
above is a component of one of the four canonical comparisons — restriction-as-
pullback, pseudo-functoriality, functoriality, and `f^*𝒪 ≅ 𝒪` — and each of them
turns out to be *characterised* by what it does to `modPullbackSection` through a
single adjunction identity already in the pin.  That is the whole content of this
section: five one-step lemmas, from which the section identity for the pullback of
a trivialization follows by composition.

The route the docstring below used to call "the compatibility of
`modPullbackSection` with the adjunction unit" is exactly right, and it is CHEAPER
than it looks, because none of the five needs the adjunction unwound by hand:

* `modPullbackSection_map` is `NatTrans.naturality` of the unit;
* `modPullbackSection_compIso` is `unit_conjugateEquiv` together with mathlib's
  `Scheme.Modules.conjugateEquiv_pullbackComp_inv`;
* `modPullbackSection_congrIso` is `subst` and `rfl`;
* `modPullbackSection_unitIso` is
  `SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit`,
  whose right-hand side `unitToPushforwardObjUnit` is *by definition* the ring map
  `f.app`, which is why the answer comes out as `f.appTop`;
* `modPullbackSection_restrictPullbackIso` is
  `Adjunction.unit_leftAdjointUniq_hom_app`.  Note this is the one place where
  `restrictFunctorIsoPullback` being a `leftAdjointUniq` — recorded elsewhere in
  this file as the REASON a section identity is not definitional — is what makes
  the proof work rather than what obstructs it: `leftAdjointUniq` is *defined* by
  its compatibility with the two units, and the restriction of a global section
  IS the unit of `restrictAdjunction` at `⊤` (`restrictAdjunction_unit_app_app`).

PERFORMANCE NOTE, and it is not incidental.  Composing the six-fold isomorphism
and asking for the identity in one step is *not* feasible: both a single `rfl`
against the fully nested composite and a `rw` chain ending on the last step
exhaust 200000 heartbeats in `isDefEq`, because the trailing `rfl` attempt tries
to unfold the adjunction.  What works is to peel the composite with
`iso_trans_val_app` (a `rfl` lemma at ONE `≪≫` at a time), rewrite with
FULLY-APPLIED instances of the five lemmas, and never let a `rw` end on a goal
that is not already closed — hence the `simp only` and the final `exact`.  The
same consideration is why `modPullbackSection_trivializationStep` is a separate
declaration rather than three more entries in the rewrite list. -/

/-- The restriction of a global section to `U`, as a global section of `A|_U`.

This is the first half of `trivializedSection`, split off so that the composition
lemmas below have something to rewrite against; `trivializedSection φ s` is
`φ` applied to it (`trivializedSection_eq`, which is `rfl`). -/
noncomputable def restrictedSection {Z : Scheme.{u}} (A : Z.Modules) (U : Z.Opens) (s : Γ(A, ⊤)) :
    Γ(A.restrict U.ι, ⊤) :=
  (Scheme.Modules.restrictAppIso U.ι A ⊤).inv (A.presheaf.map (homOfLE le_top).op s)

/-- `trivializedSection` is a trivialization applied to `restrictedSection`. -/
lemma trivializedSection_eq {Z : Scheme.{u}} {A : Z.Modules} {U : Z.Opens}
    (φ : A.restrict U.ι ≅ modUnit (U : Scheme.{u})) (s : Γ(A, ⊤)) :
    trivializedSection φ s = φ.hom.val.app (op ⊤) (restrictedSection A U s) := rfl

/-- Peeling ONE `≪≫` off a composite, on global sections.  Definitional, and
kept as a lemma precisely so that it can be applied one step at a time. -/
lemma iso_trans_val_app {W : Scheme.{u}} {M N P : W.Modules} (α : M ≅ N) (β : N ≅ P)
    (x : Γ(M, ⊤)) :
    (α ≪≫ β).hom.val.app (op ⊤) x = β.hom.val.app (op ⊤) (α.hom.val.app (op ⊤) x) := rfl

/-- The inverse of an isomorphism of modules cancels it on global sections. -/
lemma modIso_inv_hom {W : Scheme.{u}} {M N : W.Modules} (α : M ≅ N) (x : Γ(M, ⊤)) :
    α.inv.val.app (op ⊤) (α.hom.val.app (op ⊤) x) = x := by
  have h : (α.hom ≫ α.inv).val.app (op ⊤) = (𝟙 M :).val.app (op ⊤) := by rw [α.hom_inv_id]
  exact ConcreteCategory.congr_hom h x

/-- **`f^*` of a morphism carries `f^*s` to `f^*` of the image** — naturality of
the unit of the pullback/pushforward adjunction. -/
lemma modPullbackSection_map {X Y : Scheme.{u}} (f : X ⟶ Y) {A B : Y.Modules} (α : A ⟶ B)
    (s : Γ(A, ⊤)) :
    ((Scheme.Modules.pullback f).map α).val.app (op ⊤) (modPullbackSection f A s)
      = modPullbackSection f B (α.val.app (op ⊤) s) := by
  have h := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality α
  have h2 := congrArg (fun m => Scheme.Modules.Hom.app m ⊤) h
  exact (ConcreteCategory.congr_hom h2 s).symm

/-- The `modPullbackMapIso` form of `modPullbackSection_map`. -/
lemma modPullbackSection_mapIso {X Y : Scheme.{u}} (f : X ⟶ Y) {A B : Y.Modules} (e : A ≅ B)
    (s : Γ(A, ⊤)) :
    (modPullbackMapIso f e).hom.val.app (op ⊤) (modPullbackSection f A s)
      = modPullbackSection f B (e.hom.val.app (op ⊤) s) :=
  modPullbackSection_map f e.hom s

/-- **Pseudo-functoriality on sections**: `f^*(g^*s)` is `(f ≫ g)^*s` across
`modPullbackCompIso`.  This is `unit_conjugateEquiv` applied to
`(pullbackComp f g).inv`, whose conjugate mathlib computes to be
`(pushforwardComp f g).hom`; the latter is the IDENTITY on sections
(`pushforwardComp_hom_app_app`), which is what makes the identity come out. -/
lemma modPullbackSection_compIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (L : Z.Modules)
    (s : Γ(L, ⊤)) :
    (modPullbackCompIso f g L).hom.val.app (op ⊤)
        (modPullbackSection f (modPullback g L) (modPullbackSection g L s))
      = modPullbackSection (f ≫ g) L s := by
  have h := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g).inv L
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  have h2 := congrArg (fun m => Scheme.Modules.Hom.app m ⊤) h
  have h3 := ConcreteCategory.congr_hom h2 s
  have h4 : (modPullbackCompIso f g L).hom.val.app (op ⊤)
      ((modPullbackCompIso f g L).inv.val.app (op ⊤) (modPullbackSection (f ≫ g) L s))
      = modPullbackSection (f ≫ g) L s := by
    have h5 : ((modPullbackCompIso f g L).inv ≫ (modPullbackCompIso f g L).hom).val.app (op ⊤)
        = (𝟙 (modPullback (f ≫ g) L) :).val.app (op ⊤) := by
      rw [(modPullbackCompIso f g L).inv_hom_id]
    exact ConcreteCategory.congr_hom h5 _
  rw [← h4]
  exact congrArg _ h3

/-- The inverse form of `modPullbackSection_compIso`. -/
lemma modPullbackSection_compIso_inv {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (L : Z.Modules)
    (s : Γ(L, ⊤)) :
    (modPullbackCompIso f g L).inv.val.app (op ⊤) (modPullbackSection (f ≫ g) L s)
      = modPullbackSection f (modPullback g L) (modPullbackSection g L s) := by
  rw [← modPullbackSection_compIso f g L s]
  exact modIso_inv_hom _ _

/-- **Pullback along equal morphisms** leaves the pulled-back section alone. -/
lemma modPullbackSection_congrIso {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (L : Y.Modules)
    (s : Γ(L, ⊤)) :
    (modPullbackCongrIso h L).hom.val.app (op ⊤) (modPullbackSection f L s)
      = modPullbackSection g L s := by
  subst h
  rfl

/-- **`f^*𝒪_Y ≅ 𝒪_X` computes `f^#` on sections**: the pullback of `r : Γ(𝒪_Y, ⊤)`,
read through `modPullbackUnitIso`, is `f.appTop r`.

This is the one step that produces the arithmetic — everything else in the chain
is transport — and it is immediate from mathlib's
`pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit`, because the
adjoint of `pullbackObjUnitToUnit` is `unitToPushforwardObjUnit`, which is
DEFINED as the ring map underlying `f`. -/
lemma modPullbackSection_unitIso {X Y : Scheme.{u}} (f : X ⟶ Y) (r : Γ(modUnit Y, ⊤)) :
    (modPullbackUnitIso f).hom.val.app (op ⊤) (modPullbackSection f (modUnit Y) r)
      = f.appTop r := by
  have h := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    (Scheme.Hom.toRingCatSheafHom f)
  have h2 := congrArg (fun m => Scheme.Modules.Hom.app m ⊤) h
  exact ConcreteCategory.congr_hom h2 r

/-- **Restriction read as a pullback sends the restricted section to the pulled-back
section** — `Adjunction.unit_leftAdjointUniq_hom_app`, since restricting a global
section IS the unit of `restrictAdjunction` at `⊤`. -/
lemma modPullbackSection_restrictPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (A : Y.Modules) (a : Γ(A, ⊤)) :
    (modRestrictPullbackIso f A).hom.val.app (op ⊤)
        ((Scheme.Modules.restrictAppIso f A ⊤).inv (A.presheaf.map (homOfLE le_top).op a))
      = modPullbackSection f A a := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction f) A
  have h2 := congrArg (fun m => Scheme.Modules.Hom.app m ⊤) h
  exact ConcreteCategory.congr_hom h2 a

/-- `modPullbackSection_restrictPullbackIso` in `restrictedSection` form. -/
lemma modPullbackSection_restrictedSection {Z : Scheme.{u}} (A : Z.Modules) (U : Z.Opens)
    (a : Γ(A, ⊤)) :
    (modRestrictPullbackIso U.ι A).hom.val.app (op ⊤) (restrictedSection A U a)
      = modPullbackSection U.ι A a :=
  modPullbackSection_restrictPullbackIso U.ι A a

/-- The inverse form. -/
lemma modPullbackSection_restrictedSection_inv {Z : Scheme.{u}} (A : Z.Modules) (U : Z.Opens)
    (a : Γ(A, ⊤)) :
    (modRestrictPullbackIso U.ι A).inv.val.app (op ⊤) (modPullbackSection U.ι A a)
      = restrictedSection A U a := by
  rw [← modPullbackSection_restrictedSection A U a]
  exact modIso_inv_hom _ _

/-! ### The geometric step of EGA II 5.1.12 -/

/-- **The pullback of a trivialization**, as real code rather than an `∃`:
`(f^*A)|_{f⁻¹U} ≅ 𝒪_{f⁻¹U}`.

Reading right to left, the chain is restriction-as-pullback, pseudo-functoriality
down to `((f⁻¹U).ι ≫ f)^*A`, the base-change identity
`(f⁻¹U).ι ≫ f = (f ∣_ U) ≫ U.ι` (`morphismRestrict_ι`), pseudo-functoriality back
up to `(f ∣_ U)^*(A|_U)`, `f ∣_ U` applied to `φ`, and finally `f^*𝒪 ≅ 𝒪`.  Every
component is PROVEN above, and `trivializedSection_trivializationOfPullback` says
what it does to sections. -/
noncomputable def trivializationOfPullback {X Y : Scheme.{u}} (f : X ⟶ Y) {A : Y.Modules}
    {U : Y.Opens} (φ : A.restrict U.ι ≅ modUnit (U : Scheme.{u})) :
    (modPullback f A).restrict (f ⁻¹ᵁ U).ι ≅ modUnit ((f ⁻¹ᵁ U : X.Opens) : Scheme.{u}) :=
  modRestrictPullbackIso (f ⁻¹ᵁ U).ι (modPullback f A) ≪≫
    modPullbackCompIso (f ⁻¹ᵁ U).ι f A ≪≫
    modPullbackCongrIso (morphismRestrict_ι f U).symm A ≪≫
    (modPullbackCompIso (f ∣_ U) U.ι A).symm ≪≫
    modPullbackMapIso (f ∣_ U) ((modRestrictPullbackIso U.ι A).symm ≪≫ φ) ≪≫
    modPullbackUnitIso (f ∣_ U)

/-- The `f ∣_ U`-image of `φ`, read on sections.  Split out of
`trivializedSection_trivializationOfPullback` for the performance reason recorded
in the section docstring above: three more rewrites in that proof's `simp only`
list push it over the heartbeat limit. -/
lemma modPullbackSection_trivializationStep {X Y : Scheme.{u}} (f : X ⟶ Y) {A : Y.Modules}
    {U : Y.Opens} (φ : A.restrict U.ι ≅ modUnit (U : Scheme.{u})) (s : Γ(A, ⊤)) :
    (modPullbackMapIso (f ∣_ U) ((modRestrictPullbackIso U.ι A).symm ≪≫ φ)).hom.val.app (op ⊤)
        (modPullbackSection (f ∣_ U) (modPullback U.ι A) (modPullbackSection U.ι A s))
      = modPullbackSection (f ∣_ U) (modUnit (U : Scheme.{u})) (trivializedSection φ s) := by
  rw [modPullbackSection_mapIso (f ∣_ U) ((modRestrictPullbackIso U.ι A).symm ≪≫ φ)
      (modPullbackSection U.ι A s),
    iso_trans_val_app (modRestrictPullbackIso U.ι A).symm φ (modPullbackSection U.ι A s),
    Iso.symm_hom, modPullbackSection_restrictedSection_inv A U s, ← trivializedSection_eq φ s]

/-- **The section identity for `trivializationOfPullback`** (PROVEN 2026-07-28):
`f^*s`, read through the pullback of `φ`, is `f^#` of `s` read through `φ`.

This is the statement the docstring of `exists_trivialization_modPullback` named
as the content of that leaf, and it is proven here by composing the five
one-step lemmas of the previous section. -/
theorem trivializedSection_trivializationOfPullback {X Y : Scheme.{u}} (f : X ⟶ Y) {A : Y.Modules}
    {U : Y.Opens} (φ : A.restrict U.ι ≅ modUnit (U : Scheme.{u})) (s : Γ(A, ⊤)) :
    trivializedSection (trivializationOfPullback f φ) (modPullbackSection f A s)
      = (f ∣_ U).appTop (trivializedSection φ s) := by
  rw [trivializedSection_eq (trivializationOfPullback f φ) (modPullbackSection f A s)]
  simp only [trivializationOfPullback, iso_trans_val_app, Iso.symm_hom,
    modPullbackSection_restrictedSection (modPullback f A) (f ⁻¹ᵁ U)
      (modPullbackSection f A s),
    modPullbackSection_compIso (f ⁻¹ᵁ U).ι f A s,
    modPullbackSection_congrIso (morphismRestrict_ι f U).symm A s,
    modPullbackSection_compIso_inv (f ∣_ U) U.ι A s,
    modPullbackSection_trivializationStep f φ s]
  exact modPullbackSection_unitIso (f ∣_ U) (trivializedSection φ s)

/-- **The pullback of a trivialization trivializes the pullback, and the
pulled-back section has the preimage basic open** (PROVEN 2026-07-28).

The witness is `trivializationOfPullback f φ`, built as real code above, and the
section identity is `trivializedSection_trivializationOfPullback`; what is left
here is the membership half, which is `Scheme.preimage_basicOpen_top (f ∣_ U)`
together with `morphismRestrict_base_coe`.

The ROUTE recorded here before it was proven was correct in every step, and its
one warning is worth keeping: the compatibility of `modPullbackSection` with the
adjunction unit is the whole content, and it is five separate adjunction facts
(see the section `The pullback of a global section, through the canonical
isomorphisms` above), not one.

Note the statement is for an ARBITRARY morphism `f`.  That is not an oversight:
basic opens pull back along any morphism of schemes, so the closed-immersion
hypothesis of the consumer plays no role here — and indeed no hypothesis on `f`
is used anywhere in the proof. -/
theorem exists_trivialization_modPullback {X Y : Scheme.{u}} (f : X ⟶ Y) {A : Y.Modules}
    {U : Y.Opens} (φ : A.restrict U.ι ≅ modUnit (U : Scheme.{u})) (s : Γ(A, ⊤)) :
    ∃ ψ : (modPullback f A).restrict (f ⁻¹ᵁ U).ι ≅ modUnit ((f ⁻¹ᵁ U : X.Opens) : Scheme.{u}),
      ∀ (x : X) (hx : x ∈ f ⁻¹ᵁ U),
        ((⟨x, hx⟩ : ((f ⁻¹ᵁ U : X.Opens) : Scheme.{u})) ∈
            ((f ⁻¹ᵁ U : X.Opens) : Scheme.{u}).basicOpen
              (trivializedSection ψ (modPullbackSection f A s))) ↔
          ((⟨f.base x, hx⟩ : (U : Scheme.{u})) ∈
            (U : Scheme.{u}).basicOpen (trivializedSection φ s)) := by
  refine ⟨trivializationOfPullback f φ, fun x hx => ?_⟩
  rw [trivializedSection_trivializationOfPullback, ← Scheme.preimage_basicOpen_top]
  show (f ∣_ U).base ⟨x, hx⟩ ∈ (U : Scheme.{u}).basicOpen (trivializedSection φ s) ↔ _
  rw [show (f ∣_ U).base ⟨x, hx⟩ = (⟨f.base x, hx⟩ : (U : Scheme.{u})) from
    Subtype.ext (morphismRestrict_base_coe f U ⟨x, hx⟩)]
  exact Iff.rfl

/-- **The geometric step of EGA II 5.1.12** (PROVEN 2026-07-28): for a closed
immersion `f`, the non-vanishing locus of a pulled-back section is the preimage
of the non-vanishing locus.

**FAITHFULNESS — the version of this lemma WITHOUT `hL` is FALSE.**  Take
`Y = Spec k[u]`, `A` the skyscraper `k` at the origin `y₀`, `X = Spec k` and
`f : X ⟶ Y` the closed immersion of `y₀`, and `s = 1 ∈ Γ(A, ⊤) = k`.  Then
`f^*A ≅ 𝒪_X = k` and `f^*s` generates it, so `f^*s` does NOT vanish at the
point of `X`; but `A` admits NO trivialization `A|_U ≅ 𝒪_U` on any neighbourhood
of `y₀` (its sections form a `k`-line while `𝒪(U)` is infinite-dimensional), so
`NonvanishingAt A s y₀` is false and `nonvanishingLocus A s = ∅`.  The
conclusion would read `{pt} = f⁻¹ ∅ = ∅`.

**THE NUMERICAL-SEMIGROUP RISK IS RESOLVED — VERDICT: FAITHFUL AS STATED.**  The
open point recorded here was whether `IsAmpleSheaf L`, which guarantees only that
SOME power of `L` is locally trivial at each point, says anything at the
particular power `n`.  It does, and the bridge is
`isInvertibleSheaf_of_isAmpleSheaf` above (read its docstring for the two-step
argument): a trivialization of `L^{⊗m}` yields one of `L` by Stacks 01CV, after
which every power is locally trivial and `n` is not special.  **No hypothesis
needed adding, and none was added.**

**THREE HYPOTHESES ARE UNUSED, and this is a finding, not an accident.**
`[IsClosedImmersion f]`, `_hn : 0 < n` and `_hV : IsAffineOpen V` play no role.
The closed immersion was believed to be needed for the `⊆` direction, on the
grounds that it induces an isomorphism on residue fields; in fact basic opens
pull back along ANY morphism of schemes (`Scheme.preimage_basicOpen`), so the
whole argument is `Scheme.preimage_basicOpen_top` applied to `f ∣_ U`.  They are
kept because removing them would churn the call site in
`AbelianSchemeIsogeny.lean` for no gain, and because `isAmpleSheaf_modPullback`
wants the instance anyway for `IsAffineOpen.preimage`. -/
theorem nonvanishingLocus_modPullback_of_isAmpleSheaf {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] {L : Y.Modules} (hL : IsAmpleSheaf L) {n : ℕ} (_hn : 0 < n)
    (s : Γ(modTensorPow L n, ⊤)) (V : Y.Opens) (_hV : IsAffineOpen V)
    (hloc : nonvanishingLocus (modTensorPow L n) s = (V : Set Y)) :
    nonvanishingLocus (modPullback f (modTensorPow L n))
        (modPullbackSection f (modTensorPow L n) s) = f.base ⁻¹' (V : Set Y) := by
  have hinv : IsInvertibleSheaf (modTensorPow L n) :=
    isInvertibleSheaf_modTensorPow (isInvertibleSheaf_of_isAmpleSheaf hL) n
  rw [← hloc]
  ext x
  obtain ⟨U, hU, ⟨φ⟩⟩ := hinv (f.base x)
  obtain ⟨ψ, hψ⟩ := exists_trivialization_modPullback f φ s
  have hxU : x ∈ f ⁻¹ᵁ U := hU
  rw [Set.mem_preimage]
  show NonvanishingAt _ _ x ↔ NonvanishingAt _ _ (f.base x)
  rw [nonvanishingAt_iff_trivializedSection _ ψ hxU,
    nonvanishingAt_iff_trivializedSection s φ hU]
  exact hψ x hxU

/-! ### The six original statements, now all PROVEN -/

/-- **Tensor powers add**: `L^{⊗n} ⊗ L^{⊗k} ≅ L^{⊗(n+k)}` — induction on `n`
over `nonempty_modTensor_assoc` and the left unitor. -/
theorem nonempty_modTensorPow_add {Z : Scheme.{u}} (L : Z.Modules) (n k : ℕ) :
    Nonempty (modTensor (modTensorPow L n) (modTensorPow L k) ≅ modTensorPow L (n + k)) := by
  induction n with
  | zero =>
    refine ⟨modTensorUnitLeftIso _ ≪≫ eqToIso ?_⟩
    rw [Nat.zero_add]
  | succ n ih =>
    obtain ⟨e⟩ := ih
    obtain ⟨a⟩ := nonempty_modTensor_assoc L (modTensorPow L n) (modTensorPow L k)
    exact ⟨a ≪≫ modTensorMapIso (Iso.refl L) e ≪≫ eqToIso (by rw [Nat.succ_add]; rfl)⟩

/-- **Tensor powers multiply**: `(L^{⊗n})^{⊗m} ≅ L^{⊗(n*m)}` — induction on `m`
over `nonempty_modTensorPow_add`. -/
theorem nonempty_modTensorPow_mul {Z : Scheme.{u}} (L : Z.Modules) (n m : ℕ) :
    Nonempty (modTensorPow (modTensorPow L n) m ≅ modTensorPow L (n * m)) := by
  induction m with
  | zero => exact ⟨eqToIso (by rw [Nat.mul_zero]; rfl)⟩
  | succ m ih =>
    obtain ⟨e⟩ := ih
    obtain ⟨a⟩ := nonempty_modTensorPow_add L n (n * m)
    exact ⟨modTensorMapIso (Iso.refl _) e ≪≫ a ≪≫ eqToIso (by rw [Nat.mul_succ, Nat.add_comm])⟩

/-- **Ampleness is invariant under isomorphism** (PROVEN 2026-07-27).

`modTensorPowMapIso` transports the tensor power and `nonvanishingLocus_of_iso`
transports the locus; both were the obligations recorded here. -/
theorem isAmpleSheaf_of_iso {Z : Scheme.{u}} {L M : Z.Modules} (e : L ≅ M)
    (h : IsAmpleSheaf L) : IsAmpleSheaf M := by
  intro z
  obtain ⟨n, hn, s, V, hzV, hV, hloc⟩ := h z
  refine ⟨n, hn, (modTensorPowMapIso e n).hom.val.app (op ⊤) s, V, hzV, hV, ?_⟩
  rw [nonvanishingLocus_of_iso]
  exact hloc

/-- **A positive tensor power of an ample sheaf is ample** (PROVEN 2026-07-27,
over `nonempty_modTensor_assoc` and `exists_tensorPowSection`).

Given the ampleness datum `s : Γ(L^{⊗m}, ⊤)` at `z`, the witness for
`L^{⊗n}` is `s^{⊗n}`, read through
`(L^{⊗m})^{⊗n} ≅ L^{⊗(m*n)} = L^{⊗(n*m)} ≅ (L^{⊗n})^{⊗m}`. -/
theorem isAmpleSheaf_modTensorPow {Z : Scheme.{u}} {L : Z.Modules} {n : ℕ} (hn : 0 < n)
    (h : IsAmpleSheaf L) : IsAmpleSheaf (modTensorPow L n) := by
  intro z
  obtain ⟨m, hm, s, V, hzV, hV, hloc⟩ := h z
  obtain ⟨t, ht⟩ := exists_tensorPowSection (modTensorPow L m) s hn V hloc
  obtain ⟨e1⟩ := nonempty_modTensorPow_mul L m n
  obtain ⟨e2⟩ := nonempty_modTensorPow_mul L n m
  have e : modTensorPow (modTensorPow L m) n ≅ modTensorPow (modTensorPow L n) m :=
    e1 ≪≫ eqToIso (by rw [Nat.mul_comm]) ≪≫ e2.symm
  refine ⟨m, hm, e.hom.val.app (op ⊤) t, V, hzV, hV, ?_⟩
  rw [nonvanishingLocus_of_iso, ht]

/-- **`f^* 𝒪_Y ≅ 𝒪_X`** (PROVEN 2026-07-27 — free from the pin, via
`opensMapFinal`). -/
theorem nonempty_modPullback_modUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Nonempty (modPullback f (modUnit Y) ≅ modUnit X) := ⟨modPullbackUnitIso f⟩

/-- **`f^*` commutes with tensor powers** (PROVEN 2026-07-27 over
`nonempty_modPullback_modTensor`): `f^*(L^{⊗n}) ≅ (f^*L)^{⊗n}`, by induction,
with the base case `f^* 𝒪_Y ≅ 𝒪_X` now proven. -/
theorem nonempty_modPullback_modTensorPow {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules) (n : ℕ) :
    Nonempty (modPullback f (modTensorPow L n) ≅ modTensorPow (modPullback f L) n) := by
  induction n with
  | zero => exact ⟨modPullbackUnitIso f⟩
  | succ n ih =>
    obtain ⟨e⟩ := ih
    obtain ⟨e0⟩ := nonempty_modPullback_modTensor f L (modTensorPow L n)
    exact ⟨e0 ≪≫ modTensorMapIso (Iso.refl _) e⟩

/-- **The restriction of an ample sheaf to a closed subscheme is ample**
(PROVEN 2026-07-27 over `nonempty_modPullback_modTensor` and
`nonvanishingLocus_modPullback_of_isAmpleSheaf`) — EGA II 5.1.12,
Hartshorne III Ex. 5.7. -/
theorem isAmpleSheaf_modPullback {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    {L : Y.Modules} (h : IsAmpleSheaf L) : IsAmpleSheaf (modPullback f L) := by
  intro x
  obtain ⟨n, hn, s, V, hxV, hV, hloc⟩ := h (f.base x)
  obtain ⟨e⟩ := nonempty_modPullback_modTensorPow f L n
  refine ⟨n, hn, e.hom.val.app (op ⊤) (modPullbackSection f (modTensorPow L n) s),
    f ⁻¹ᵁ V, hxV, hV.preimage f, ?_⟩
  rw [nonvanishingLocus_of_iso]
  exact nonvanishingLocus_modPullback_of_isAmpleSheaf f h hn s V hV hloc

/-- **A quasi-compact scheme with AMPLE STRUCTURE SHEAF is QUASI-AFFINE**
(PROVEN 2026-07-27 over `nonvanishingLocus_modUnit`) — EGA II 5.1.2, and the
last step of the classical proof of the consumer.

The UNITOR obligation recorded here is discharged by `modTensorPowUnitIso`; the
well-definedness obligation is exactly `nonvanishingLocus_modUnit`.  The mathlib
half is `Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen`. -/
theorem isQuasiAffine_of_isAmpleSheaf_modUnit (Z : Scheme.{u}) [CompactSpace Z]
    (h : IsAmpleSheaf (modUnit Z)) : Z.IsQuasiAffine := by
  refine Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen Z fun z => ?_
  obtain ⟨n, hn, s, V, hzV, hV, hloc⟩ := h z
  have hb : Z.basicOpen ((modTensorPowUnitIso n).hom.val.app (op ⊤) s) = V := by
    refine SetLike.coe_injective ?_
    rw [← nonvanishingLocus_modUnit, nonvanishingLocus_of_iso, hloc]
  exact ⟨(modTensorPowUnitIso n).hom.val.app (op ⊤) s, hb ▸ hV, hb ▸ hzV⟩

/-! ### THE PICARD GROUP: inverses, cancellation, and `RelPicEquiv` as an
equivalence relation

(New block, 2026-07-28, added for `relPicEquiv_sectionIdeal_of_aj_eq` in
`ModularCurve/X0.lean`.  Placed here rather than in `RelativePicard.lean` —
where `modTensor`, `IsInvertibleSheaf` and `RelPicEquiv` are *defined* —
because everything below consumes the tensor calculus of THIS module, and
`RelativePicard.lean` is upstream of it.)

**THIS BLOCK REFUTES A CLAIM THAT WAS IN TWO DOCSTRINGS.**  The docstring of
`relPicEquiv_sectionIdeal_of_aj_eq` asserted, dated 2026-07-28, that
"`modTensor` has no algebraic API anywhere in this development — no
associativity, no symmetry, no unit, and in particular no cancellation of an
invertible factor", and that `grep -rn 'modTensor' Fermat/` returns "**not one
lemma**".  Every clause of that is false.

*Not one lemma* — this module already held `modTensorMapIso` (functoriality on
isos), `modTensorUnitLeftIso`, `nonempty_modTensor_assoc`,
`modPullbackUnitIso`, `modPullbackMapIso`, `nonempty_modPullback_modTensor`,
`isInvertibleSheaf_modUnit` and `isInvertibleSheaf_modTensor`, all but two of
them PROVEN (`nonempty_modPullback_modTensor` is a leaf, and
`nonempty_modTensor_assoc` rests on `modLocW_whiskerLeft`).  It reaches
`X0.lean`: that file `public import`s `AbelianSchemeIsogeny`, which
`public import`s this one.

*No associativity* — `nonempty_modTensor_assoc`.

*No unit* — `modTensorUnitLeftIso`, and `modTensorUnitRightIso` below.

*No symmetry* — `modTensorComm` below, one line over mathlib's
`SymmetricCategory` instance on `PresheafOfModules`.  This is the clause that
cost the most: believing it, an earlier draft of this very block cut the
inverse leaf in a two-sided form it does not need.

*No cancellation of an invertible factor* — this was the ONE true clause, and
it is now `nonempty_iso_of_modTensor_left` / `RelPicEquiv.cancel_left` below,
PROVEN over the single new leaf.  The claim has been corrected in place at
`relPicEquiv_sectionIdeal_of_aj_eq`; the same assertion also stands, as of
2026-07-28, in the docstring of `relPicEquiv_sectionIdeal_of_aj_add_eq`
(X0.lean, the degree-`2` sibling), which is another owner's declaration and
has been left alone and reported instead.

What is genuinely missing is exactly ONE statement — that an invertible sheaf
has a tensor INVERSE (`exists_modTensor_inv`, now UPSTREAM in
`ModularCurve/RelativePicard.lean`) — from which cancellation, and with it
symmetry and transitivity of `RelPicEquiv`, are formal.  The corrected
inventory is recorded on that leaf. -/

/-- **THE BRAIDING**, `L ⊗ M ≅ M ⊗ L` (PROVEN, one line) — `modTensor` is
SYMMETRIC.

Mathlib gives `PresheafOfModules.{u} (R ⋙ forget₂ _ _)` a
`SymmetricCategory` instance (`PresheafOfModules.Monoidal.symmetricCategory`,
`Mathlib/Algebra/Category/ModuleCat/Presheaf/Monoidal.lean:145`) on **exactly
the same category** as the `monoidalCategory` instance one screen above it —
so `β_ L.val M.val` is available wherever `λ_ L.val` is, and sheafifying it is
the whole construction.

**Recorded because it was nearly missed.**  An earlier draft of this block
asserted that `Z.Modules` has no braiding at this pin, on the strength of a
grep of `Mathlib/Algebra/Category/ModuleCat/{Presheaf,Sheaf}/` that returned
nothing — the grep had been run on the ORCHESTRATION host, where
`.lake/packages` does not exist (it is a symlink into machine-local
`/scratch` on the worker host, so the path silently resolves to nothing and
every mathlib grep returns empty).  Run mathlib greps on the host that owns
`.lake`.  Had the claim stood, `exists_modTensor_inv` (upstream) would have
been cut twice as strong as it needs to be. -/
noncomputable def modTensorComm {Z : Scheme.{u}} (L M : Z.Modules) :
    modTensor L M ≅ modTensor M L :=
  (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).mapIso (β_ L.val M.val)

/-! #### HOISTED to `ModularCurve/RelativePicard.lean` (2026-07-29)

`modTensorUnitRightIso` (the right unitor), `isIso_of_locally_isIso` (isomorphy
is local on the base), `exists_modDual` (the dual sheaf and its evaluation
pairing) and `exists_modTensor_inverse` were declared HERE on 2026-07-28 and are
now declared UPSTREAM, in `RelativePicard.lean`, where the last of them is named
`exists_modTensor_inv`.

**The hoist was forced, and it removed a duplicated leaf rather than tidying
one.**  `RelativePicard.lean` is `public import`ed by this module and states the
same inverse theorem as a leaf of its own, because its relative-Picard calculus
consumes it — so nothing proved here could ever reach it, and the two copies of
`exists_modDual` could only both stay open forever.  The right unitor was a
genuine double declaration (`Fermat.modTensorUnitRightIso has already been
declared`); the other three were twins under different names.

Everything below still resolves: the hoisted declarations are inherited by
import, unchanged, and `exists_modTensor_inverse`'s two consumers here —
`nonempty_iso_of_modTensor_left` and `RelPicEquiv.symm` — now call
`exists_modTensor_inv`. -/

/-- **CANCELLATION OF AN INVERTIBLE TENSOR FACTOR** (PROVEN over
`exists_modTensor_inv` and `nonempty_modTensor_assoc`): if `L` is
invertible then `L ⊗ A ≅ L ⊗ B` forces `A ≅ B`.

Tensor on the left with a left inverse `M` of `L` — obtained from the right
inverse through `modTensorComm` — and reassociate; `A` and `B` are arbitrary
`𝒪_Z`-modules, no invertibility of them is used or needed. -/
theorem nonempty_iso_of_modTensor_left {Z : Scheme.{u}} {L A B : Z.Modules}
    (hL : IsInvertibleSheaf L) (e : modTensor L A ≅ modTensor L B) : Nonempty (A ≅ B) := by
  obtain ⟨M, -, ⟨eLM⟩⟩ := exists_modTensor_inv hL
  have eML : modTensor M L ≅ modUnit Z := modTensorComm M L ≪≫ eLM
  obtain ⟨aA⟩ := nonempty_modTensor_assoc M L A
  obtain ⟨aB⟩ := nonempty_modTensor_assoc M L B
  exact ⟨(modTensorUnitLeftIso A).symm ≪≫ modTensorMapIso eML.symm (Iso.refl A) ≪≫ aA ≪≫
    modTensorMapIso (Iso.refl M) e ≪≫ aB.symm ≪≫ modTensorMapIso eML (Iso.refl B) ≪≫
    modTensorUnitLeftIso B⟩

section RelPicGroupoid

variable {X S T : Scheme.{u}} {strX : X ⟶ S} {g : T ⟶ S}

/-- **`RelPicEquiv` is REFLEXIVE** (PROVEN): take `N := 𝒪_T` and use the right
unitor together with `f^* 𝒪_T ≅ 𝒪_{X_T}`. -/
theorem RelPicEquiv.refl (L : (curveBaseChange strX g).Modules) : RelPicEquiv strX g L L :=
  ⟨modUnit T, isInvertibleSheaf_modUnit T,
    ⟨(modTensorUnitRightIso L).symm ≪≫
      modTensorMapIso (Iso.refl L) (modPullbackUnitIso _).symm⟩⟩

/-- **`RelPicEquiv` is TRANSITIVE** (PROVEN over `nonempty_modTensor_assoc`
and `nonempty_modPullback_modTensor`): the twisting sheaves multiply, and
`M ⊗ N` is invertible by `isInvertibleSheaf_modTensor`. -/
theorem RelPicEquiv.trans {L L' L'' : (curveBaseChange strX g).Modules}
    (h : RelPicEquiv strX g L L') (h' : RelPicEquiv strX g L' L'') : RelPicEquiv strX g L L'' := by
  obtain ⟨N, hN, ⟨e⟩⟩ := h
  obtain ⟨M, hM, ⟨e'⟩⟩ := h'
  obtain ⟨a⟩ := nonempty_modTensor_assoc L'' (modPullback (curveBaseChangeProj strX g) M)
    (modPullback (curveBaseChangeProj strX g) N)
  obtain ⟨pmn⟩ := nonempty_modPullback_modTensor (curveBaseChangeProj strX g) M N
  exact ⟨modTensor M N, isInvertibleSheaf_modTensor hM hN,
    ⟨e ≪≫ modTensorMapIso e' (Iso.refl _) ≪≫ a ≪≫ modTensorMapIso (Iso.refl L'') pmn.symm⟩⟩

/-- **`RelPicEquiv` is SYMMETRIC** (PROVEN over `exists_modTensor_inv`):
twist back by the inverse of the twisting sheaf.

This is the step that makes `RelPicEquiv` an equivalence relation, and hence
`Pic(X_T)/Pic(T)` a group rather than a preorder — which is what its consumers
in `ModularCurve/X0.lean` (`aj_spec` read at two different points) silently
assume. -/
theorem RelPicEquiv.symm {L L' : (curveBaseChange strX g).Modules}
    (h : RelPicEquiv strX g L L') : RelPicEquiv strX g L' L := by
  obtain ⟨N, hN, ⟨e⟩⟩ := h
  obtain ⟨M, hM, ⟨eNM⟩⟩ := exists_modTensor_inv hN
  obtain ⟨a⟩ := nonempty_modTensor_assoc L' (modPullback (curveBaseChangeProj strX g) N)
    (modPullback (curveBaseChangeProj strX g) M)
  obtain ⟨pnm⟩ := nonempty_modPullback_modTensor (curveBaseChangeProj strX g) N M
  exact ⟨M, hM, ⟨(modTensorUnitRightIso L').symm ≪≫
    modTensorMapIso (Iso.refl L') ((modPullbackUnitIso _).symm ≪≫
      modPullbackMapIso _ eNM.symm ≪≫ pnm) ≪≫ a.symm ≪≫
    modTensorMapIso e.symm (Iso.refl _)⟩⟩

/-- **CANCELLATION IN THE RELATIVE PICARD GROUP** (PROVEN over
`nonempty_iso_of_modTensor_left`): an invertible factor common to both sides
of a `RelPicEquiv` may be deleted.

`A` and `B` are arbitrary — only the CANCELLED factor `L` has to be
invertible.  This is what lets `IsRelPicZeroOf.aj_spec`, which is an equation
about `𝒪(x − o) ⊗ 𝒪(−x)`, be turned into a statement about `𝒪(−x)` alone. -/
theorem RelPicEquiv.cancel_left {L A B : (curveBaseChange strX g).Modules}
    (hL : IsInvertibleSheaf L)
    (h : RelPicEquiv strX g (modTensor L A) (modTensor L B)) : RelPicEquiv strX g A B := by
  obtain ⟨N, hN, ⟨e⟩⟩ := h
  obtain ⟨a⟩ := nonempty_modTensor_assoc L B (modPullback (curveBaseChangeProj strX g) N)
  obtain ⟨f⟩ := nonempty_iso_of_modTensor_left hL (e ≪≫ a)
  exact ⟨N, hN, ⟨f⟩⟩

end RelPicGroupoid

end Fermat
