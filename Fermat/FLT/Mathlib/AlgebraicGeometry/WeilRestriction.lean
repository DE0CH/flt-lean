/-
Mathlib/AlgebraicGeometry/WeilRestriction.lean — own work for the Fermat
project (not vendored from the FLT project).

# Descending a nonconstant map to an abelian scheme along a finite separable extension

This module isolates, and decomposes, the *base-point* residue of
`ModularCurve/X1.lean`'s

    exists_nonconstant_toAbelianScheme_of_notGeometricallyRational

namely the leaf cut out of it on 2026-07-30 as

    exists_nonconstant_toAbelianScheme_of_baseChange_relPoint

> a smooth proper geometrically connected curve `C/K` which acquires a
> nonconstant map to an abelian variety over *every* extension `L/K` at
> which `C_L` has an `L`-rational point, already has one over `K`.

The obstruction the leaf names is real and classical: Abel–Jacobi is
`x ↦ [x] − [o]` and needs a base point `o ∈ C(K)`, while a smooth proper
geometrically connected curve over a non-closed field need not have one —
a genus-`1` curve with `C(K) = ∅` is the standard witness.

## The classical repair, and the two atoms it leaves

1.  `hconn` makes `C` nonempty and `hproper` makes it finite type over
    `K`, so `C` has a closed point; `hsmooth` makes some closed point have
    residue field `L` a **finite separable** extension of `K` — the
    `K^sep`-points of a smooth `K`-scheme are dense.  That is
    `exists_finiteEtale_point_of_smooth` below, ATOM 1.
2.  The graph of that point is an `L`-rational point of `C_L`, so the
    hypothesis applies at `L` and yields an abelian variety `A/L` with a
    nonconstant `c : C_L ⟶ A`.  This step is pure category theory and is
    **proven** here (`pullback.lift` of the point against `𝟙`).
3.  Weil restriction `Res_{L/K} A` along the finite étale `Spec L ⟶ Spec K`
    is an abelian variety over `K`; the unit `C ⟶ Res_{L/K}(C_L)` is a
    `K`-morphism; the composite `C ⟶ Res_{L/K}(C_L) ⟶ Res_{L/K}(A)` is the
    required map, and it is nonconstant because base changing to `L` and
    composing with the counit `(Res_{L/K} A)_L ⟶ A` recovers `c`.  That is
    `exists_nonconstant_toAbelianScheme_of_finiteEtale_descent` below,
    ATOM 2.

**Weil restriction does not exist at this pin.**  Checked 2026-07-30 and
re-checked 2026-07-31 with
`grep -rniE "weil.?restriction" Fermat/ .lake/packages/mathlib/Mathlib/`:
the only hits are two prose mentions in `Modularity/MoretBailly.lean`.
`~/cs/FLT` has none either.  Do **not** run the check as
`grep restrictScalars`: that returns two dozen hits in
`Modularity/HeckeFrameForm.lean`, all `Submodule.restrictScalars`, which
is module theory and unrelated.

**SCOPE.**  Only Weil restriction along a **finite separable field
extension** is needed, not the general finite-locally-free relative case,
and ATOM 2 is stated in exactly the applied form the consumer needs
rather than as a construction.  Nobody should assume that closing ATOM 2
makes a general `Res_{S'/S}` available.

## Why separability is load-bearing, and where

`Spec L ⟶ Spec K` is étale exactly when `L/K` is finite separable
(`Mathlib.RingTheory.Etale.Field`), and étaleness of `ℓ` is what makes
`Res_{L/K} A ⟶ Spec K` **smooth**, hence what lets the Weil restriction
carry an `AbelianSchemeStruct` at all.  A merely finite `ℓ` gives a
`Res` that is proper but not smooth in general (`Res_{k(t^{1/p})/k(t)}`
of an abelian variety in characteristic `p`), so the separability in
ATOM 1 is not a convenience: dropping `Etale ℓ` from ATOM 2 makes ATOM 2
**false**.

## The tempting shortcut, and why it fails

`A ⟶ Spec L ⟶ Spec K` is proper (finite ∘ proper) and smooth (étale ∘
smooth), so two of the three geometric conditions of
`AbelianSchemeStruct` survive viewing `A` as a `K`-scheme directly.  The
third does not: `A ×_K K̄ = ⊔_{σ : L ↪ K̄} A^σ_{K̄}` has `[L : K]`
components, so `astr ≫ ℓ` is **not** geometrically connected, and it is
not a group over `K` either — `RelPoint (astr ≫ ℓ) (𝟙 (Spec K))` is the
set of `x : Spec K ⟶ A` with `x ≫ astr ≫ ℓ = 𝟙`, which forces a
`K`-algebra map `L → K` and is therefore **empty** for `L ≠ K`, so it has
no zero.  Weil restriction is not avoidable by bookkeeping.

## A note for whoever proves ATOM 2 through a universal property

The natural route is to introduce `IsWeilRestriction astr ℓ rstr`, an
equivalence `RelPoint rstr g ≃ RelPoint astr (curveBaseChangeProj g ℓ)`
natural in `g : X ⟶ Spec K`, and to derive the applied form from it.
Transporting **nonconstancy** across that equivalence has one step that
is easy to miss.  Suppose `c' = cstr ≫ s` for some `s : C ⟶ R`, and put
`t := s ≫ rstr : Spec K ⟶ Spec K`.  Naturality is available only at the
base point `t`, and one needs `t = 𝟙` to identify `pullback t ℓ` with
`Spec L` and read off a genuine constant.  It *is* `𝟙`, but only because
`C` is nonempty: `c' ≫ rstr = cstr` gives `cstr ≫ t = cstr`, i.e.
`α ∘ t^♯ = α` for the structure map `α : K → Γ(C, 𝒪_C)`, and `α` is
injective because `K` is a field and `Γ(C, 𝒪_C) ≠ 0`.  Hence `t^♯ = id`.
This is why ATOM 2 carries `hne : Nonempty C` — the hypothesis is not
decoration, and it is supplied for free at the call site by the point
ATOM 1 produces.

(For `C = ∅` the applied statement is in fact vacuously true, since every
morphism out of the initial object is unique and so `hnc` fails; but the
degenerate case is not worth making a prover handle, and the consumer has
`Nonempty C` in hand.)

## Relocation

Nothing here is `Γ₁`- or even modular-specific.  `X0.lean`'s open
`exists_nonconstant_toAbelianScheme_of_one_le_x0Genus` needs the same
descent verbatim, which is why this lives under `Fermat/FLT/Mathlib/`
rather than in a curve file.
-/
module

public import Fermat.FLT.ModularCurve.RelativePicard
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Geometrically.Connected

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

namespace Fermat.WeilRestriction

/-! ### ATOM 1 — a smooth curve has a point over a finite separable extension -/

/-- **A nonempty smooth finite-type `K`-scheme has a point over a finite
separable extension of `K`** (sorry leaf).

Concretely: there are a field `L`, a finite étale `ℓ : Spec L ⟶ Spec K`
— which for a morphism of spectra of fields says exactly that `L/K` is
finite separable — and a `K`-morphism `p : Spec L ⟶ C`.

**THE MATHEMATICS.**  `hconn` gives `Nonempty C` (mathlib derives
`[GeometricallyConnected f] : Surjective f` as a low-priority instance,
and `Spec K` is nonempty), and `hproper` gives `LocallyOfFiniteType cstr`.
A nonempty finite-type scheme over a field has a closed point, and at a
closed point `x` the morphism `C.fromSpecResidueField x` is locally of
finite type (`Mathlib.AlgebraicGeometry.Morphisms.Finite`, the
`IsClosed {x} ↔ LocallyOfFiniteType (X.fromSpecResidueField x)`
characterisation), so `κ(x)/K` is a finite extension by Zariski's lemma.
That much is available at this pin and is *not* the content of this leaf.

**THE CONTENT is separability**, and it is the only place smoothness is
used: a smooth morphism admits sections étale-locally (EGA IV 17.16.3),
equivalently the points of a smooth `K`-scheme whose residue field is
separable over `K` are dense.  Over a perfect `K` every finite extension
is separable and the leaf is immediate from the paragraph above; over an
imperfect `K` it is not, and a non-smooth witness shows the hypothesis is
needed: `Spec k(t^{1/p})` over `k(t)` in characteristic `p` is finite,
proper, geometrically connected and has *no* point over any finite
separable extension, being purely inseparable.  So `hsmooth` is
load-bearing and `SmoothOfRelativeDimension 1` is used only through
`Smooth`.

**NOT VACUOUS**: `C = Spec K` itself satisfies the conclusion with
`L = K`, `ℓ = 𝟙`.

**RELATED MATERIAL AT THIS PIN**, for whoever attacks it:
`Mathlib.AlgebraicGeometry.Sites.EtalePoint` has
`Scheme.exists_fac_of_etale_of_isSepClosed`, which lifts a point valued
in a separably closed field through an étale morphism; and
`Mathlib.RingTheory.Etale.Field` characterises étale field extensions.
The missing direction is the descent from a `K^sep`-point to a point over
a *finite* subextension, which is a finite-presentation/spreading-out
argument. -/
theorem exists_finiteEtale_point_of_smooth
    {C : Scheme.{0}} {K : Type} [Field K] {cstr : C ⟶ Spec (CommRingCat.of K)}
    (hproper : IsProper cstr) (hsmooth : SmoothOfRelativeDimension 1 cstr)
    (hconn : GeometricallyConnected cstr) :
    ∃ (L : Type) (_ : Field L) (ℓ : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K))
      (p : Spec (CommRingCat.of L) ⟶ C), IsFinite ℓ ∧ Etale ℓ ∧ p ≫ cstr = ℓ :=
  sorry

/-! ### ATOM 2 — Weil restriction along a finite étale extension of fields -/

/-- **Weil restriction, in applied form: a nonconstant map to an abelian
scheme over a finite separable extension descends to the base field**
(sorry leaf).

Given `ℓ : Spec L ⟶ Spec K` finite étale (equivalently `L/K` finite
separable), an abelian scheme `astr : A ⟶ Spec L` and a nonconstant
`L`-morphism `c : C_L ⟶ A`, there is an abelian scheme over `K` receiving
a nonconstant `K`-morphism from `C`.

**THE CONSTRUCTION** is `A' := Res_{L/K} A`, with `c'` the ADJOINT of
`c` under `Hom_K(C, Res_{L/K} A) ≅ Hom_L(C_L, A)`.  (Equivalently
`c' = (unit : C ⟶ Res_{L/K}(C_L)) ≫ Res_{L/K}(c)`, but the adjoint form
needs neither the unit nor functoriality of `Res`, so a prover should
take the universal property as the definition and never build either.)
Weil restriction
along a finite locally free morphism preserves properness and, because
`ℓ` is étale, smoothness; it preserves geometrically connected fibres
because `(Res_{L/K} A)_{K̄} = ∏_{σ : L ↪ K̄} A^σ_{K̄}` is a product of
connected schemes; and the group structure transports through the
universal property `Hom_K(X, Res_{L/K} A) ≅ Hom_L(X_L, A)`, which is
exactly an isomorphism of the functor of points and hence of
`RelPoint`-valued functors — the presentation `AbelianSchemeStruct` uses.

**REPRESENTABILITY, which is the real dependency**: `Res_{L/K} X` is
representable for `X` quasi-projective over `L` (Weil; BLR *Néron
Models* 7.6/4, whose hypothesis is that every finite set of points of
`X` lies in an affine open).  It applies here because a proper smooth
group scheme with geometrically connected fibres over a *field* is an
abelian variety and abelian varieties are projective — so `ab` is
load-bearing a second time, beyond supplying the group law.  A prover
who only wants the applied statement does **not** need functoriality of
`Res`, a unit, a counit, or the general finite-locally-free case; the
universal property at the single test object `C` is enough.

**NONCONSTANCY** is the half that is not formal: base changing `c'` to
`L` and composing with the counit `(Res_{L/K} A)_L ⟶ A` recovers `c`, and
both operations send a constant map to a constant map.  See the module
docstring for the `t = 𝟙` step, which is where `hne` is consumed.

**`het` IS LOAD-BEARING**: without it `A'` need not be smooth over `K`,
so no `AbelianSchemeStruct` exists on it — `Res` along a purely
inseparable finite extension in characteristic `p` is the standard
counterexample.  `hfin` is load-bearing because Weil restriction is not
representable along an arbitrary affine morphism.

**NOT VACUOUS and the junk witness is killed by the nonconstancy clause
alone**: `A' = Spec K` with `astr' = 𝟙` forces `c' = cstr = cstr ≫ 𝟙`, so
the final clause fails at `s = 𝟙`.  A prover must produce a genuinely
positive-dimensional `A'`.

**`hne` is not decoration** — see the module docstring.  It is available
free at the only call site, from the point ATOM 1 produces. -/
theorem exists_nonconstant_toAbelianScheme_of_finiteEtale_descent
    {C : Scheme.{0}} {K L : Type} [Field K] [Field L]
    {cstr : C ⟶ Spec (CommRingCat.of K)}
    {ℓ : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K)}
    (hfin : IsFinite ℓ) (het : Etale ℓ) (hne : Nonempty C)
    {A : Scheme.{0}} {astr : A ⟶ Spec (CommRingCat.of L)}
    (ab : AbelianSchemeStruct astr) (c : curveBaseChange cstr ℓ ⟶ A)
    (hc : c ≫ astr = curveBaseChangeProj cstr ℓ)
    (hnc : ∀ s : Spec (CommRingCat.of L) ⟶ A, c ≠ curveBaseChangeProj cstr ℓ ≫ s) :
    ∃ (A' : Scheme.{0}) (astr' : A' ⟶ Spec (CommRingCat.of K)) (_ : AbelianSchemeStruct astr')
      (c' : C ⟶ A'), c' ≫ astr' = cstr ∧
        ∀ s : Spec (CommRingCat.of K) ⟶ A', c' ≠ cstr ≫ s :=
  sorry

/-! ### The assembly -/

/-- **THE SECTION, ISOLATED: a nonconstant map to an abelian variety
descends from a finite extension over which the curve acquires a rational
point** (PROVEN here over ATOM 1 and ATOM 2 above).

This is the statement cut out of
`exists_nonconstant_toAbelianScheme_of_notGeometricallyRational` in
`ModularCurve/X1.lean` on 2026-07-30 under the name
`exists_nonconstant_toAbelianScheme_of_baseChange_relPoint`, reproduced
verbatim.  That declaration should be replaced by a one-line delegation
to this one; it is stated here rather than there because nothing in it is
`Γ₁`-specific and `X0.lean`'s
`exists_nonconstant_toAbelianScheme_of_one_le_x0Genus` wants the same
theorem.

**WHAT THE PROOF DOES.**  Only the middle step — turning the point ATOM 1
produces into a relative point of the base-changed curve, so that `hsec`
applies — is done here, and it is pure category theory: the graph of
`p : Spec L ⟶ C` over `ℓ` is `pullback.lift p (𝟙 _)`, and
`pullback.lift_snd` says it is a section of `curveBaseChangeProj cstr ℓ`.
The two genuinely mathematical steps are the atoms.

**FALSITY AUDIT (done 2026-07-30, not repeated here).**  The tempting
reading is that `hsec` at `L = K`, `ℓ = 𝟙` already *is* the conclusion,
making the leaf trivial.  It is not: `hsec` is usable only at an `L` for
which `C_L` HAS an `L`-rational point, and the whole difficulty is that
`L = K` need not be such an `L`.  Conversely `hsec` is not vacuous — its
consumer discharges it for every `L` at once from
`exists_nonconstant_toAbelianScheme_of_hasNoFibreAffineLine`.  `hproper`,
`hsmooth` and `hconn` are each load-bearing for a different step: finite
type, separability, and nonemptiness respectively. -/
theorem exists_nonconstant_toAbelianScheme_of_baseChange_relPoint
    {C : Scheme.{0}} {K : Type} [Field K] {cstr : C ⟶ Spec (CommRingCat.of K)}
    (hproper : IsProper cstr) (hsmooth : SmoothOfRelativeDimension 1 cstr)
    (hconn : GeometricallyConnected cstr)
    (hsec : ∀ (L : Type) [Field L] (ℓ : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K)),
      RelPoint (curveBaseChangeProj cstr ℓ) (𝟙 (Spec (CommRingCat.of L))) →
      ∃ (A : Scheme.{0}) (astr : A ⟶ Spec (CommRingCat.of L)) (_ : AbelianSchemeStruct astr)
        (c : curveBaseChange cstr ℓ ⟶ A),
        c ≫ astr = curveBaseChangeProj cstr ℓ ∧
          ∀ s : Spec (CommRingCat.of L) ⟶ A, c ≠ curveBaseChangeProj cstr ℓ ≫ s) :
    ∃ (A : Scheme.{0}) (astr : A ⟶ Spec (CommRingCat.of K)) (_ : AbelianSchemeStruct astr)
      (c : C ⟶ A), c ≫ astr = cstr ∧
        ∀ s : Spec (CommRingCat.of K) ⟶ A, c ≠ cstr ≫ s := by
  obtain ⟨L, _, ℓ, p, hfin, het, hp⟩ :=
    exists_finiteEtale_point_of_smooth hproper hsmooth hconn
  -- `C` is nonempty: it receives a morphism from the nonempty `Spec L`.
  have hne : Nonempty C := ⟨p.base default⟩
  -- The graph of `p`, as an `L`-rational point of `C_L`.
  have hgraph : (pullback.lift p (𝟙 _) (by rw [hp, Category.id_comp]) :
      Spec (CommRingCat.of L) ⟶ curveBaseChange cstr ℓ) ≫ curveBaseChangeProj cstr ℓ = 𝟙 _ :=
    pullback.lift_snd _ _ _
  obtain ⟨A, astr, ab, c, hc, hnc⟩ := hsec L ℓ ⟨_, hgraph⟩
  exact exists_nonconstant_toAbelianScheme_of_finiteEtale_descent hfin het hne ab c hc hnc

end Fermat.WeilRestriction
