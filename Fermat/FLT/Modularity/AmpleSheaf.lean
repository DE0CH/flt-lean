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

PROVEN (free from the pin): `modPullbackCompIso`, `modPullbackCongrIso`,
`modPullbackMapIso` — pseudo-functoriality of `modPullback`, straight off
`Scheme.Modules.pullbackComp` / `pullbackCongr` / `Functor.mapIso`.

OPEN, and each one names what it needs:

* `isAmpleSheaf_of_iso` and `isAmpleSheaf_modTensorPow` need `modTensor` to be
  FUNCTORIAL (and, for the second, ASSOCIATIVE).  `modTensor` is deliberately
  object-only — `RelativePicard.lean` says so — but the morphism part is not
  far away: `PresheafOfModules.Monoidal` has `tensorHom`, and
  `PresheafOfModules.sheafification` is a functor, so `modTensorMap` can be
  defined the same way `modTensor` was.  The ASSOCIATOR is the genuinely
  missing piece, and it is the statement that sheafification is monoidal.
* `nonempty_modPullback_modTensorPow` is monoidality of `f^*`, i.e.
  `f^*(L ⊗ M) ≅ f^*L ⊗ f^*M`; `nonempty_modPullback_modUnit` is `f^*𝒪 ≅ 𝒪`.
  Mathlib has `SheafOfModules.pullbackObjUnitToUnit`, an iso when the site
  functor is final, which is not automatic for `Opens.map f`.
* `isAmpleSheaf_modPullback` is EGA II 5.1.12 in the case of a closed
  immersion (Hartshorne III Ex. 5.7): the restriction of an ample sheaf to a
  closed subscheme is ample.
* `isQuasiAffine_of_isAmpleSheaf_modUnit` is EGA II 5.1.2 read backwards, and
  it is the one whose mathlib half already exists:
  `AlgebraicGeometry.IsQuasiAffine.of_forall_exists_mem_basicOpen` wants an
  affine `X.basicOpen r` around every point, and `IsAmpleSheaf (modUnit Z)`
  gives exactly that once `𝒪^{⊗n} ≅ 𝒪` is available (the UNITOR — the same
  missing associativity as above) and once the non-vanishing locus is known to
  be independent of the trivialization used to compute it.

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
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

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

/-! ### Pseudo-functoriality of `modPullback` (PROVEN — free from the pin) -/

/-- **`f^*(g^* L) ≅ (f ≫ g)^* L`** — `Scheme.Modules.pullbackComp`, read on an
object. -/
noncomputable def modPullbackCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (L : Z.Modules) :
    modPullback f (modPullback g L) ≅ modPullback (f ≫ g) L :=
  (Scheme.Modules.pullbackComp f g).app L

/-- **Pullbacks along equal morphisms agree** — `Scheme.Modules.pullbackCongr`,
read on an object.  Needed because `pullback.condition` is an equality of
morphisms, not a definitional identity. -/
noncomputable def modPullbackCongrIso {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (L : Y.Modules) :
    modPullback f L ≅ modPullback g L :=
  (Scheme.Modules.pullbackCongr h).app L

/-- **`f^*` carries isomorphisms to isomorphisms** — it is a functor. -/
noncomputable def modPullbackMapIso {X Y : Scheme.{u}} (f : X ⟶ Y) {L M : Y.Modules} (e : L ≅ M) :
    modPullback f L ≅ modPullback f M :=
  (Scheme.Modules.pullback f).mapIso e

/-! ### The sheaf-theoretic leaves

Six statements, none of them containing abelian-variety content.  Each names
in its docstring the piece of missing machinery it is waiting on; between them
they are the ampleness theory that `Mathlib/AlgebraicGeometry/` does not have
(`grep -rl Ample Mathlib/AlgebraicGeometry/` is EMPTY at this pin — re-run it
before believing this sentence). -/

/-- **Ampleness is invariant under isomorphism** (sorry leaf).

BLOCKED ON: functoriality of `modTensor`.  Transporting the ampleness data
across `e : L ≅ M` needs `modTensorPow L n ≅ modTensorPow M n`, i.e. the
morphism part of `⊗`, which `RelativePicard.lean` deliberately did not define.
It is the cheapest of the six: `PresheafOfModules.Monoidal.tensorHom` exists
and `PresheafOfModules.sheafification` is a functor, so `modTensorMap` is
definable exactly as `modTensor` was.  A second, smaller obligation: that
`NonvanishingAt` transports, which is a computation with `trivializedSection`
and the restriction of `e`. -/
theorem isAmpleSheaf_of_iso {Z : Scheme.{u}} {L M : Z.Modules} (e : L ≅ M)
    (h : IsAmpleSheaf L) : IsAmpleSheaf M := sorry

/-- **A positive tensor power of an ample sheaf is ample** (sorry leaf).

BLOCKED ON: the ASSOCIATOR.  The proof is
`modTensorPow (modTensorPow L n) m ≅ modTensorPow L (n * m)`, which is
associativity of `⊗`, i.e. the statement that SHEAFIFICATION IS MONOIDAL.
That is a genuine theorem and is the deepest of the six; it is also what
`RelativePicard.lean` names as the reason it built only the object part. -/
theorem isAmpleSheaf_modTensorPow {Z : Scheme.{u}} {L : Z.Modules} {n : ℕ} (hn : 0 < n)
    (h : IsAmpleSheaf L) : IsAmpleSheaf (modTensorPow L n) := sorry

/-- **The restriction of an ample sheaf to a closed subscheme is ample** (sorry
leaf) — EGA II 5.1.12, Hartshorne III Ex. 5.7.

BLOCKED ON: monoidality of `f^*` (to move `modTensorPow` across the pullback,
i.e. `nonempty_modPullback_modTensorPow` below), plus the geometric step that
a closed immersion pulls an affine `Z_s` back to an affine `X_{f^*s}`
(`IsAffineOpen` is preserved by `IsClosedImmersion`, which the pin does have)
and that non-vanishing is preserved.  No new *theory* is needed here beyond
the tensor obligations — this one is task-scale once they land. -/
theorem isAmpleSheaf_modPullback {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    {L : Y.Modules} (h : IsAmpleSheaf L) : IsAmpleSheaf (modPullback f L) := sorry

/-- **A quasi-compact scheme with AMPLE STRUCTURE SHEAF is QUASI-AFFINE**
(sorry leaf) — EGA II 5.1.2, and the last step of the classical proof of the
consumer.

BLOCKED ON: two things, both named. (1) The UNITOR: `IsAmpleSheaf (modUnit Z)`
produces a section of `modTensorPow (modUnit Z) n`, and turning that into an
element of `Γ(Z, ⊤)` needs `𝒪^{⊗n} ≅ 𝒪`.  (2) Well-definedness of
`nonvanishingLocus` for `modUnit Z` — that the locus computed through an
arbitrary trivialization is `Z.basicOpen r`; two trivializations differ by a
unit, so this is the transition-function computation.

The mathlib half is already there and is what makes this leaf worth stating in
this shape: `AlgebraicGeometry.IsQuasiAffine.of_forall_exists_mem_basicOpen`
asks for exactly an affine `Z.basicOpen r` around each point. -/
theorem isQuasiAffine_of_isAmpleSheaf_modUnit (Z : Scheme.{u}) [CompactSpace Z]
    (h : IsAmpleSheaf (modUnit Z)) : Z.IsQuasiAffine := sorry

/-- **`f^*` commutes with tensor powers** (sorry leaf): `f^*(L^{⊗n}) ≅ (f^*L)^{⊗n}`.

BLOCKED ON: monoidality of the pullback functor, `f^*(L ⊗ M) ≅ f^*L ⊗ f^*M`.
`Scheme.Modules.pullback` is a left adjoint and the presheaf-level tensor is a
colimit-friendly construction, so this is expected to follow once `modTensor`
has its morphism part; it is stated separately because the consumer needs
exactly this instance and nothing more. -/
theorem nonempty_modPullback_modTensorPow {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules) (n : ℕ) :
    Nonempty (modPullback f (modTensorPow L n) ≅ modTensorPow (modPullback f L) n) := sorry

/-- **`f^* 𝒪_Y ≅ 𝒪_X`** (sorry leaf).

BLOCKED ON: mathlib has the comparison morphism
`SheafOfModules.pullbackObjUnitToUnit`, and an `IsIso` instance for it under a
FINALITY hypothesis on the site functor which `Opens.map f.base` does not
satisfy in general.  The scheme-level statement is nonetheless true and
standard; supplying it is a matter of computing the pullback of the unit
directly, or of finding the right cofinality argument. -/
theorem nonempty_modPullback_modUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Nonempty (modPullback f (modUnit Y) ≅ modUnit X) := sorry

end Fermat
