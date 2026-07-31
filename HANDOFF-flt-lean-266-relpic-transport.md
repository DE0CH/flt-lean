# HANDOFF — the local/global TRANSPORT for `exists_relPicPoincare_of_localUniversal`

`flt-lean-266`, 2026-07-31, verified against the built olean of
`Fermat.FLT.ModularCurve.RelativePicard` at commit `370485ba`
(`lake env lean` on a scratch importing that module: **zero errors, zero
warnings**).

This is the first of the two obligations left in
`Fermat.exists_relPicPoincare_of_localUniversal` (`ModularCurve/RelativePicard.lean`).
It is **not committed into the module**, because nothing consumes it yet and this
project forbids free-floating declarations. Paste it in as part of the recut that
consumes it — see "how to consume it" below.

Three route notes in that file call these two sublemmas "routine" and say they are
"not stated as a leaf here because nothing in the assembly consumes them". They are
routine. They are also ~35 lines, and the second one lands on a mathlib isomorphism
whose projection compatibility is **on the nose**, which is the fact that makes the
whole transport cheap and which no note records:

    pullbackLeftPullbackSndIso_hom_snd : hom ≫ pullback.snd _ _ = pullback.snd _ _

i.e. the comparison `(X ×_S V) ×_V T ≅ X ×_S T` commutes with the projection to `T`
definitionally, so `RelPicEquiv` — whose twisting sheaf is pulled back along exactly
that projection — has nothing to fight.

## The verified text

```lean
/-- a `V`-point of `pstr ∣_ V` is an `S`-point of `pstr` over `gV ≫ V.ι` -/
def relPointOfRestrict {P S : Scheme.{u}} (pstr : P ⟶ S) (V : S.Opens) {T : Scheme.{u}}
    {gV : T ⟶ (V : Scheme.{u})} (y : RelPoint (pstr ∣_ V) gV) :
    RelPoint pstr (gV ≫ V.ι) :=
  ⟨y.1 ≫ (pstr ⁻¹ᵁ V).ι, by
    rw [Category.assoc, ← morphismRestrict_ι pstr V, ← Category.assoc, y.2]⟩

/-- and conversely -/
noncomputable def relPointToRestrict {P S : Scheme.{u}} (pstr : P ⟶ S) (V : S.Opens)
    {T : Scheme.{u}} {gV : T ⟶ (V : Scheme.{u})} (x : RelPoint pstr (gV ≫ V.ι)) :
    RelPoint (pstr ∣_ V) gV :=
  ⟨(isPullback_morphismRestrict pstr V).lift gV x.1 x.2.symm,
    (isPullback_morphismRestrict pstr V).lift_fst _ _ _⟩

theorem relPointOfRestrict_toRestrict {P S : Scheme.{u}} (pstr : P ⟶ S) (V : S.Opens)
    {T : Scheme.{u}} {gV : T ⟶ (V : Scheme.{u})} (x : RelPoint pstr (gV ≫ V.ι)) :
    relPointOfRestrict pstr V (relPointToRestrict pstr V x) = x :=
  Subtype.ext ((isPullback_morphismRestrict pstr V).lift_snd _ _ _)

theorem relPointToRestrict_ofRestrict {P S : Scheme.{u}} (pstr : P ⟶ S) (V : S.Opens)
    {T : Scheme.{u}} {gV : T ⟶ (V : Scheme.{u})} (y : RelPoint (pstr ∣_ V) gV) :
    relPointToRestrict pstr V (relPointOfRestrict pstr V y) = y := by
  refine Subtype.ext ((isPullback_morphismRestrict pstr V).hom_ext ?_ ?_)
  · exact ((isPullback_morphismRestrict pstr V).lift_fst _ _ _).trans y.2.symm
  · exact (isPullback_morphismRestrict pstr V).lift_snd _ _ _

/-- **the curve base-changed to `T` is the same computed over `V` or over `S`**,
and the comparison commutes with the projection to `T` ON THE NOSE -/
noncomputable def curveBaseChangeRestrictIso {X S : Scheme.{u}} (strX : X ⟶ S) (V : S.Opens)
    {T : Scheme.{u}} (gV : T ⟶ (V : Scheme.{u})) :
    curveBaseChange (curveBaseChangeProj strX V.ι) gV ≅ curveBaseChange strX (gV ≫ V.ι) :=
  pullbackLeftPullbackSndIso strX V.ι gV

theorem curveBaseChangeRestrictIso_hom_proj {X S : Scheme.{u}} (strX : X ⟶ S) (V : S.Opens)
    {T : Scheme.{u}} (gV : T ⟶ (V : Scheme.{u})) :
    (curveBaseChangeRestrictIso strX V gV).hom ≫ curveBaseChangeProj strX (gV ≫ V.ι)
      = curveBaseChangeProj (curveBaseChangeProj strX V.ι) gV :=
  pullbackLeftPullbackSndIso_hom_snd strX V.ι gV
```

Needs `open CategoryTheory AlgebraicGeometry CategoryTheory.Limits` (the module has
the first two; `pullbackLeftPullbackSndIso` and `IsPullback` want the third, or
qualify them).

## Mathlib names, checked at this pin rather than recalled

* `AlgebraicGeometry.morphismRestrict_ι : f ∣_ U ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f`
  (`Mathlib/AlgebraicGeometry/Restrict.lean:575`);
* `AlgebraicGeometry.isPullback_morphismRestrict :`
  `IsPullback (f ∣_ U) (f ⁻¹ᵁ U).ι U.ι f` (same file, `:580`) — note the ORDER of
  the four maps, which is what `lift`/`lift_fst`/`lift_snd`/`hom_ext` key on;
* `CategoryTheory.Limits.pullbackLeftPullbackSndIso f g g' :`
  `pullback (pullback.snd f g) g' ≅ pullback f (g' ≫ g)`
  (`Mathlib/CategoryTheory/Limits/Shapes/Pullback/Pasting.lean:525`), with
  `_hom_fst`, `_hom_snd`, `_inv_fst`, `_inv_snd_fst`, `_inv_snd_snd` all `@[simp]`
  and `@[reassoc]`.

## How to consume it — the recut this is for

Restate `exists_relPicPoincare_of_localUniversal`'s hypothesis in the GLOBAL world,
so that the leaf is purely the gluing and contains no local/global mismatch at all:

    _hloc : ∀ V : S.Opens, IsAffineOpen V →
      ∃ U : (curveBaseChange strX ((pstr ⁻¹ᵁ V).ι ≫ pstr)).Modules,
        IsInvertibleSheaf U ∧ <U classifies every g factoring through V>

and PROVE the bridge from the present `_hloc` (which is in the local world) using the
text above. Missing piece for the bridge, and it is the one thing not written here: a
version of the PROVEN `relPicEquiv_modPullback` for a general comparison morphism
`φ : curveBaseChange strX' g' ⟶ curveBaseChange strX g` satisfying
`φ ≫ curveBaseChangeProj strX g = curveBaseChangeProj strX' g'`, instead of for
`curveBaseChangeMap`. Its proof is that theorem's, verbatim, with the projection
identity supplied as a hypothesis rather than by `curveBaseChangeMap_proj`; generalise
it in place and re-derive the existing statement from it, so no call site moves.

After that recut the leaf is: **rigidify the `U_V` along `_o` and glue them**, which
needs descent for `SheafOfModules` along an open cover. `Mathlib/CategoryTheory/Sites/Descent/`
(`IsStack.lean`, `DescentData.lean`, `IsPrestack.lean`) exists at this pin; whether the
fibred category of sheaves of modules is registered as a stack there has NOT been
checked, and that check is the first thing the gluing half should do.
