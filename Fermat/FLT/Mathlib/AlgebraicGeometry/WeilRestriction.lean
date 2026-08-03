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

1.  `hconn` makes `C` nonempty and `hsmooth` makes some point have
    residue field `L` a **finite separable** extension of `K` — the
    `K^sep`-points of a smooth `K`-scheme are dense.  That is
    `exists_finiteEtale_point_of_smooth` below, ATOM 1, **PROVEN
    2026-08-01** over the single commutative-algebra leaf
    `exists_finiteSeparable_algHom_of_smooth_of_infinite`: a nonzero
    smooth algebra over an INFINITE field admits a `K`-algebra map to a
    finite separable extension.  The perfect-field case (which covers
    every finite field) is proven, as is all of the scheme-to-ring glue,
    so nothing about schemes, curves or properness is left in the leaf.
    Note `hproper` turned out NOT to be used by ATOM 1 at all.
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
(`Mathlib.RingTheory.Etale.Field`), and étaleness of `ℓ` is what lets the
Weil restriction carry an `AbelianSchemeStruct` at all.  Dropping
`Etale ℓ` from ATOM 2 makes ATOM 2 **false**, so the separability in
ATOM 1 is not a convenience.

**CORRECTED 2026-08-02 — the clause that fails is PROPERNESS, not
smoothness.**  This paragraph read "a merely finite `ℓ` gives a `Res`
that is proper but not smooth in general", and the witness it named
refutes the opposite clause.  Take `K = k(t)`, `L = k(t^{1/p})` in
characteristic `p`.  Then `L ⊗_K K̄ ≅ K̄[ε]/(ε^p)` is NON-REDUCED, so
`Res_{L/K} A ×_K K̄` is the Greenberg/jet group of `A` over
`K̄[ε]/(ε^p)`: an extension of `A_{K̄}` by a unipotent group of dimension
`(p−1)·dim A`.  That is smooth and connected, and it contains `𝔾_a`, so
it is not PROPER.  Weil restriction along a finite locally free morphism
does preserve smoothness; what separability buys is that
`L ⊗_K K̄ ≅ K̄^{[L:K]}` is reduced, so that
`Res_{L/K} A ×_K K̄ ≅ ∏_{σ : L ↪ K̄} A^σ_{K̄}` is a PRODUCT OF ABELIAN
VARIETIES — which is where properness, smoothness and geometric
connectedness all come from at once.

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

Nothing here is `Γ₁`- or even modular-specific, which is why this lives
under `Fermat/FLT/Mathlib/` rather than in a curve file.

**CORRECTED 2026-08-02.**  This paragraph, and the two `RELOCATION NOTE`
paragraphs in `X1.lean` that it was copied from, justified the placement by
*"`X0.lean`'s OPEN `exists_nonconstant_toAbelianScheme_of_one_le_x0Genus`
needs the same descent verbatim"*.  That declaration is **PROVEN** — it is a
two-line assembly over `exists_nonconstant_toAbelianScheme_of_nontrivial_cuspForm`
at `X0.lean:64325` — and it does not consume anything here.  The placement is
still right (the material genuinely mentions no level and no modular curve),
but do not queue anyone at the `Γ₀` side on the strength of that sentence.
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

/-- **A nonzero étale algebra over a field maps to a finite separable field
extension** (PROVEN).  This is the last step of ATOM 1's route, isolated so
that whoever attacks the residual leaf below does not have to redo it:
`Algebra.Etale.iff_exists_algEquiv_prod` writes a nonzero étale `K`-algebra as
a nonempty finite product of finite separable extensions, and one projects. -/
theorem exists_finiteSeparable_algHom_of_etale (K : Type) [Field K] (B : Type) [CommRing B]
    [Nontrivial B] [Algebra K B] [Algebra.Etale K B] :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L),
      Module.Finite K L ∧ Algebra.IsSeparable K L ∧ Nonempty (B →ₐ[K] L) := by
  obtain ⟨I, _, Ai, _, _, e, hAi⟩ := (Algebra.Etale.iff_exists_algEquiv_prod K B).mp ‹_›
  have hI : Nonempty I := by
    by_contra h
    rw [not_nonempty_iff] at h
    haveI : Subsingleton B := e.injective.subsingleton
    exact false_of_nontrivial_of_subsingleton B
  obtain ⟨i⟩ := hI
  exact ⟨Ai i, inferInstance, inferInstance, (hAi i).1, (hAi i).2,
    ⟨(Pi.evalAlgHom K Ai i).comp e.toAlgHom⟩⟩

/-- **THE COMMUTATIVE-ALGEBRA CORE OF ATOM 1, over an INFINITE field**
(sorry leaf).  A nonzero smooth algebra over an infinite field `K` admits a
`K`-algebra map to a finite separable extension of `K`.

**THIS IS THE WHOLE CONTENT OF ATOM 1.**  Everything else that leaf used to
bundle — nonemptiness of `C`, the passage to an affine chart, the fact that
the residue field of a closed point is finite, and the translation between
`Module.Finite`/`Algebra.IsSeparable` and the scheme-level `IsFinite`/`Etale`
— is proven below.  The statement mentions no scheme, no curve, no
properness and no relative dimension, and it is exactly the classical
assertion that *the separable points of a smooth scheme over a field are
dense*.

**WHY `Infinite K` IS FREE.**  The complementary case is discharged by
`exists_finiteSeparable_algHom_of_smooth_of_perfectField` below: a finite
field is perfect, and over a perfect field every finite extension is
separable, so any maximal ideal will do and smoothness is not needed at all.
Since `PerfectField` is implied by `Finite`, splitting on
`finite_or_infinite K` covers everything — see
`exists_finiteSeparable_algHom_of_smooth`.  So the hypothesis costs a prover
nothing and buys the density of `K`-rational points that the route below
needs.

**THE ROUTE, which is EGA IV 17.15.x / Stacks 056U, and the pieces that are
already at this pin.**  `A` smooth over `K` is Zariski-locally standard
smooth, so some nonzero localisation `A_f` admits, by
`Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`
(`Mathlib.RingTheory.RingHom.StandardSmooth`), an étale `K`-algebra map
`K[X_1, …, X_n] → A_f`.  An étale morphism is open, so the image of
`Spec A_f` in affine `n`-space contains a nonempty basic open `D(h)`;
because `K` is infinite there is `a ∈ K^n` with `h(a) ≠ 0`
(`MvPolynomial.exists_eval_ne_zero_of_ne_zero`-style), i.e. a `K`-rational
point of that open.  The fibre `A_f ⊗_{K[X]} K` over it is then a NONZERO
étale `K`-algebra, and
`exists_finiteSeparable_algHom_of_etale` above finishes.

**LOAD-BEARING, and the witness for smoothness is the original one**: over
an imperfect `K` of characteristic `p`, `K = k(t)`, the finite type
`K`-algebra `K[X]/(X^p - t)` is a field, purely inseparable over `K`, and
has NO `K`-algebra map to any separable extension.  It is not smooth, and
that is the only thing that excludes it.

**NOT VACUOUS**: `A = K` satisfies the conclusion with `L = K`. -/
theorem exists_finiteSeparable_algHom_of_smooth_of_infinite
    (K : Type) [Field K] [Infinite K] (A : Type) [CommRing A] [Nontrivial A]
    [Algebra K A] [Algebra.Smooth K A] :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L),
      Module.Finite K L ∧ Algebra.IsSeparable K L ∧ Nonempty (A →ₐ[K] L) :=
  sorry

/-- **Over a PERFECT field the core needs no smoothness** (PROVEN): a nonzero
finite-type algebra has a maximal ideal, its residue field is finite over `K`
by Zariski's lemma (`finite_of_finite_type_of_isJacobsonRing`), and a finite —
indeed any algebraic — extension of a perfect field is separable. -/
theorem exists_finiteSeparable_algHom_of_smooth_of_perfectField
    (K : Type) [Field K] [PerfectField K] (A : Type) [CommRing A] [Nontrivial A]
    [Algebra K A] [Algebra.FiniteType K A] :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L),
      Module.Finite K L ∧ Algebra.IsSeparable K L ∧ Nonempty (A →ₐ[K] L) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType K (A ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K m) Ideal.Quotient.mk_surjective
  haveI : Module.Finite K (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ m)
  haveI : Algebra.IsAlgebraic K (A ⧸ m) := Algebra.IsAlgebraic.of_finite K (A ⧸ m)
  exact ⟨A ⧸ m, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨Ideal.Quotient.mkₐ K m⟩⟩

/-- **The core of ATOM 1 over an arbitrary field** (PROVEN over the leaf
above): split on `finite_or_infinite K`, a finite field being perfect. -/
theorem exists_finiteSeparable_algHom_of_smooth (K : Type) [Field K] (A : Type) [CommRing A]
    [Nontrivial A] [Algebra K A] [Algebra.Smooth K A] :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L),
      Module.Finite K L ∧ Algebra.IsSeparable K L ∧ Nonempty (A →ₐ[K] L) := by
  rcases finite_or_infinite K with h | h
  · exact exists_finiteSeparable_algHom_of_smooth_of_perfectField K A
  · exact exists_finiteSeparable_algHom_of_smooth_of_infinite K A

/-- `Spec` of a finite extension is a finite morphism (PROVEN). -/
theorem isFinite_specMap_algebraMap (K L : Type) [Field K] [Field L] [Algebra K L]
    [Module.Finite K L] : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  rw [IsFinite.SpecMap_iff, CommRingCat.hom_ofHom]
  exact RingHom.finite_algebraMap.mpr inferInstance

/-- `Spec` of a finite separable extension is an étale morphism (PROVEN). -/
theorem etale_specMap_algebraMap (K L : Type) [Field K] [Field L] [Algebra K L]
    [Module.Finite K L] [Algebra.IsSeparable K L] :
    Etale (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  haveI : Algebra.FinitePresentation K L := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  haveI : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  haveI : Algebra.Etale K L := ⟨inferInstance, inferInstance⟩
  rw [HasRingHomProperty.Spec_iff (P := @Etale), CommRingCat.hom_ofHom]
  exact RingHom.etale_algebraMap.mpr inferInstance

/-- **A nonempty smooth finite-type `K`-scheme has a point over a finite
separable extension of `K`** (**PROVEN 2026-08-01** over the single
commutative-algebra leaf
`exists_finiteSeparable_algHom_of_smooth_of_infinite` above; it was a sorry
leaf until then).

Concretely: there are a field `L`, a finite étale `ℓ : Spec L ⟶ Spec K`
— which for a morphism of spectra of fields says exactly that `L/K` is
finite separable — and a `K`-morphism `p : Spec L ⟶ C`.

**WHAT THE PROOF DOES.**  `hconn` gives `Surjective cstr` (a low-priority
mathlib instance) and `Spec K` is nonempty, so `C` has a point `x`; take an
affine open `Spec R` around it.  `Smooth cstr` and `Smooth j` for the open
immersion make the composite smooth, and since both ends are affine it is
`Spec.map` of a ring map, so `R` is a nonzero smooth `K`-algebra.  The core
leaf above hands back a finite separable `L` and a `K`-algebra map
`R →ₐ[K] L`; `Spec` of it, composed with `j`, is the point, and
`isFinite_specMap_algebraMap` / `etale_specMap_algebraMap` supply the two
morphism properties.  The compatibility `p ≫ cstr = ℓ` is `AlgHom.commutes`.

**`hproper` IS NOT USED, and that was a genuine discovery of 2026-08-01.**
The docstring this replaces said properness was what supplied
`LocallyOfFiniteType cstr`.  It is not needed: smoothness already gives
local finite presentation, hence finite type, and the affine-chart route
never asks for a CLOSED point — any point of a nonempty affine chart does.
The binder is kept, named `_hproper`, because the sole call site holds it
for free and an unused hypothesis costs a prover nothing; a successor who
wants the sharp statement may delete it, and nothing in this file would
change.

**`hsmooth` IS load-bearing**, and the witness is the classical one:
`Spec k(t^{1/p})` over `k(t)` in characteristic `p` is finite, proper and
geometrically connected, and has *no* point over any finite separable
extension, being purely inseparable.  It fails only smoothness.
`SmoothOfRelativeDimension 1` is used only through `Smooth`, so the
relative dimension is decoration here.

**NOT VACUOUS**: `C = Spec K` itself satisfies the conclusion with
`L = K`, `ℓ = 𝟙`. -/
theorem exists_finiteEtale_point_of_smooth
    {C : Scheme.{0}} {K : Type} [Field K] {cstr : C ⟶ Spec (CommRingCat.of K)}
    (_hproper : IsProper cstr) (hsmooth : SmoothOfRelativeDimension 1 cstr)
    (hconn : GeometricallyConnected cstr) :
    ∃ (L : Type) (_ : Field L) (ℓ : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K))
      (p : Spec (CommRingCat.of L) ⟶ C), IsFinite ℓ ∧ Etale ℓ ∧ p ≫ cstr = ℓ := by
  haveI := hsmooth
  haveI := hconn
  haveI : Smooth cstr := SmoothOfRelativeDimension.smooth 1 cstr
  obtain ⟨x, -⟩ := (Surjective.surj (f := cstr)) (default : Spec (CommRingCat.of K))
  obtain ⟨R, j, hj, hx, -⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (X := C) (x := x) (U := ⊤) (by simp)
  haveI := hj
  have hspec : Spec.map (Spec.preimage (j ≫ cstr)) = j ≫ cstr := Spec.map_preimage _
  algebraize [(Spec.preimage (j ≫ cstr)).hom]
  haveI : Algebra.Smooth K R := by
    have h1 : Smooth (Spec.map (Spec.preimage (j ≫ cstr))) := by rw [hspec]; infer_instance
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)] at h1
    exact RingHom.smooth_algebraMap.mp h1
  haveI : Nontrivial R := PrimeSpectrum.nontrivial (Set.mem_range.mp hx).choose
  obtain ⟨L, _, _, hfin, hsep, ⟨ψ⟩⟩ := exists_finiteSeparable_algHom_of_smooth K R
  refine ⟨L, inferInstance, Spec.map (CommRingCat.ofHom (algebraMap K L)),
    Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ j, isFinite_specMap_algebraMap K L,
    etale_specMap_algebraMap K L, ?_⟩
  rw [Category.assoc, ← hspec, ← Spec.map_comp]
  congr 1
  ext k
  exact ψ.commutes k

/-! ### ATOM 2 — Weil restriction along a finite étale extension of fields

The leaf is `exists_weilRestriction_of_finiteEtale`: the CONSTRUCTION, and
nothing else.  Everything between it and the applied statement — the group
law, the `t = 𝟙` step, the nonconstancy transfer — is proven below. -/

/-- **Base change of a morphism `h : X ⟶ Y` OVER the base**, i.e. the induced
`X ×_S T ⟶ Y ×_S T`.

Not to be confused with `curveBaseChangeMap`, which changes the BASE `T` and
fixes the source; this one fixes `T` and moves the source, and is what the
naturality of a Weil-restriction adjunction is stated against. -/
noncomputable def weilSrcMap {X Y S T : Scheme.{0}} {xstr : X ⟶ S} {ystr : Y ⟶ S}
    (ℓ : T ⟶ S) (h : X ⟶ Y) (hh : h ≫ ystr = xstr) :
    curveBaseChange xstr ℓ ⟶ curveBaseChange ystr ℓ :=
  pullback.lift (pullback.fst xstr ℓ ≫ h) (pullback.snd xstr ℓ)
    (by rw [Category.assoc, hh, pullback.condition])

@[reassoc]
theorem weilSrcMap_proj {X Y S T : Scheme.{0}} {xstr : X ⟶ S} {ystr : Y ⟶ S}
    (ℓ : T ⟶ S) (h : X ⟶ Y) (hh : h ≫ ystr = xstr) :
    weilSrcMap ℓ h hh ≫ curveBaseChangeProj ystr ℓ = curveBaseChangeProj xstr ℓ :=
  pullback.lift_snd _ _ _

@[reassoc]
theorem weilSrcMap_fst {X Y S T : Scheme.{0}} {xstr : X ⟶ S} {ystr : Y ⟶ S}
    (ℓ : T ⟶ S) (h : X ⟶ Y) (hh : h ≫ ystr = xstr) :
    weilSrcMap ℓ h hh ≫ pullback.fst ystr ℓ = pullback.fst xstr ℓ ≫ h :=
  pullback.lift_fst _ _ _

/-- **An endomorphism of `Spec K` under which a NONEMPTY `K`-scheme is
invariant is the identity** (PROVEN).

This is the `t = 𝟙` step the module docstring flags as the one easy-to-miss
point of the nonconstancy transfer, and it is the only place `Nonempty C` is
spent.  `Hom(Spec K, Spec K)` is `Hom(K, K)`, which is NOT a subsingleton —
Frobenius on `𝔽_p(t)`, complex conjugation on `ℚ(i)` — so the hypothesis is
not decoration.

The argument: `cstr ≫ t = cstr` gives `Γ(t) ≫ Γ(cstr) = Γ(cstr)` on global
sections; `Γ(C, ⊤)` is nontrivial because `C` is nonempty
(`Scheme.component_nontrivial`), so the ring map `K ⟶ Γ(C, ⊤)` underlying
`cstr` is injective — a ring hom out of a FIELD into a nonzero ring — hence a
mono, and cancels.  `AlgebraicGeometry.ext_to_Spec` returns the conclusion. -/
theorem eq_id_of_comp_eq_self {C : Scheme.{0}} {K : Type} [Field K]
    {cstr : C ⟶ Spec (CommRingCat.of K)} (hne : Nonempty C)
    {t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K)}
    (h : cstr ≫ t = cstr) : t = 𝟙 _ := by
  haveI : Nonempty ((⊤ : C.Opens) : Type) := ⟨⟨hne.some, trivial⟩⟩
  haveI : Nontrivial (Scheme.Γ.obj (Opposite.op C) : CommRingCat) :=
    (inferInstance : Nontrivial Γ(C, ⊤))
  have hmono : Mono ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ Scheme.Γ.map cstr.op) :=
    ConcreteCategory.mono_of_injective _ (RingHom.injective _)
  have hmonoβ : Mono (Scheme.Γ.map cstr.op) := by
    have h2 : Mono ((Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫
        ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ Scheme.Γ.map cstr.op)) := mono_comp _ _
    simpa using h2
  have key : Scheme.Γ.map t.op ≫ Scheme.Γ.map cstr.op = 𝟙 _ ≫ Scheme.Γ.map cstr.op := by
    rw [Category.id_comp, ← Scheme.Γ.map_comp, ← op_comp, h]
  have ht : Scheme.Γ.map t.op = 𝟙 _ := (cancel_mono _).mp key
  refine AlgebraicGeometry.ext_to_Spec ?_
  rw [ht]
  simp

/-- **THE LEAF: Weil restriction along a finite étale extension of fields
exists, is proper, smooth and geometrically connected, and represents the
expected functor** (sorry leaf, cut 2026-08-02 out of
`exists_nonconstant_toAbelianScheme_of_finiteEtale_descent` below).

`Res_{L/K} A`, together with the adjunction

    Hom_K(X, Res_{L/K} A) ≅ Hom_L(X ×_K L, A)

natural in the `K`-scheme `X`, which is the whole of what a consumer needs.
`Φ` is stated on `RelPoint`s, i.e. in the slice over the base, because that
is the presentation `AbelianSchemeStruct` uses; the naturality clause is the
same bijection's compatibility with a morphism `h : X ⟶ Y` over `Spec K`.

**WHAT THE CITATION IS.**  Representability is Weil / BLR *Néron Models*
7.6/4, whose hypothesis — every finite set of points lies in an affine open —
holds because `A` is an abelian variety over a field, hence projective; that
is the second place `ab` is load-bearing, beyond supplying the group law.
Properness, smoothness and geometric connectedness of `Res` are BLR 7.6/5.
No functoriality of `Res`, no unit and no counit are needed: only the
bijection at a general test object and its naturality.

**WHY THE CONCLUSION CARRIES NO GROUP LAW.**  It does not need to.
`AbelianSchemeStruct` presents an abelian scheme by its functor of points, so
`Φ` transports the group structure from `ab` verbatim — that is
`abelianSchemeStruct_of_weilRestriction` below, and all nine group fields of
the structure are formal consequences of the bijection plus its naturality.
Only the three GEOMETRIC conditions have to be asserted here.

**FALSITY AUDIT (2026-08-02, this statement; the audit on the parent covers a
different statement and does not transfer).**

*Not vacuous*: at `L = K`, `ℓ = 𝟙` — which is finite and étale — take
`R = A`, `rstr = astr` and for `Φ` the canonical bijection coming from
`pullback xstr (𝟙 _) ≅ X`; the three geometric clauses are `ab.proper`,
`ab.smooth`, `ab.connected`.

*`het` is load-bearing, and the reason is PROPERNESS rather than smoothness*
— correcting the parent's docstring, which attributes the failure to
smoothness.  Take `K = k(t)`, `L = k(t^{1/p})` in characteristic `p`, so
`ℓ` is finite and purely inseparable.  Then `L ⊗_K K̄ ≅ K̄[ε]/(ε^p)` is
NON-REDUCED, so the geometric fibre of `Res_{L/K} A` is the Greenberg/jet
group of `A` over `K̄[ε]/(ε^p)`: an extension of `A_{K̄}` by a unipotent
group of dimension `(p−1)·dim A`.  It is still smooth and connected, and it
contains `𝔾_a`, so it is NOT proper — hence not an abelian scheme.  For
`L/K` separable, `L ⊗_K K̄ ≅ K̄^{[L:K]}` and
`Res_{L/K} A ×_K K̄ ≅ ∏_{σ : L ↪ K̄} A^σ_{K̄}`, a product of abelian
varieties, which is where all three geometric clauses come from at once.

*`hfin` is load-bearing*: Weil restriction is not representable along an
arbitrary affine morphism.

*`ab` is load-bearing twice*: for projectivity (hence representability, see
above) and for the group law the consumer transports. -/
theorem exists_weilRestriction_of_finiteEtale {K L : Type} [Field K] [Field L]
    {ℓ : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K)}
    (hfin : IsFinite ℓ) (het : Etale ℓ)
    {A : Scheme.{0}} {astr : A ⟶ Spec (CommRingCat.of L)}
    (ab : AbelianSchemeStruct astr) :
    ∃ (R : Scheme.{0}) (rstr : R ⟶ Spec (CommRingCat.of K))
      (Φ : ∀ (X : Scheme.{0}) (xstr : X ⟶ Spec (CommRingCat.of K)),
             RelPoint rstr xstr ≃ RelPoint astr (curveBaseChangeProj xstr ℓ)),
      IsProper rstr ∧ Smooth rstr ∧ GeometricallyConnected rstr ∧
        ∀ (X Y : Scheme.{0}) (xstr : X ⟶ Spec (CommRingCat.of K))
          (ystr : Y ⟶ Spec (CommRingCat.of K)) (h : X ⟶ Y) (hh : h ≫ ystr = xstr)
          (f : RelPoint rstr ystr),
          Φ X xstr (RelPoint.pre h hh f)
            = RelPoint.pre (weilSrcMap ℓ h hh) (weilSrcMap_proj ℓ h hh) (Φ Y ystr f) :=
  sorry

/-- **The group structure transports through the universal property**
(PROVEN) — the formal half of ATOM 2.

`AbelianSchemeStruct` is the functor-of-points presentation, so a bijection
`RelPoint rstr xstr ≃ RelPoint astr (curveBaseChangeProj xstr ℓ)` natural in
`X` carries the group law across with nothing to check beyond transporting
the axioms along an `Equiv`.  The two naturality fields `pre_add`/`pre_zero`
are exactly where `hnat` is spent; the three geometric fields are handed in.

This is why the leaf above may assert the geometric conditions ALONE. -/
noncomputable def abelianSchemeStruct_of_weilRestriction {K L : Type} [Field K] [Field L]
    {ℓ : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K)}
    {A R : Scheme.{0}} {astr : A ⟶ Spec (CommRingCat.of L)}
    {rstr : R ⟶ Spec (CommRingCat.of K)} (ab : AbelianSchemeStruct astr)
    (Φ : ∀ (X : Scheme.{0}) (xstr : X ⟶ Spec (CommRingCat.of K)),
           RelPoint rstr xstr ≃ RelPoint astr (curveBaseChangeProj xstr ℓ))
    (hnat : ∀ (X Y : Scheme.{0}) (xstr : X ⟶ Spec (CommRingCat.of K))
        (ystr : Y ⟶ Spec (CommRingCat.of K)) (h : X ⟶ Y) (hh : h ≫ ystr = xstr)
        (f : RelPoint rstr ystr),
        Φ X xstr (RelPoint.pre h hh f)
          = RelPoint.pre (weilSrcMap ℓ h hh) (weilSrcMap_proj ℓ h hh) (Φ Y ystr f))
    (hproper : IsProper rstr) (hsmooth : Smooth rstr)
    (hconn : GeometricallyConnected rstr) :
    AbelianSchemeStruct rstr where
  add {T} {g} x y := (Φ T g).symm (ab.add (Φ T g x) (Φ T g y))
  zero {T} g := (Φ T g).symm (ab.zero _)
  neg {T} {g} x := (Φ T g).symm (ab.neg (Φ T g x))
  add_assoc := by
    intro T g x y z
    simp only [Equiv.apply_symm_apply]
    rw [ab.add_assoc]
  add_comm := by
    intro T g x y
    exact congrArg (Φ T g).symm (ab.add_comm _ _)
  zero_add := by
    intro T g x
    simp only [Equiv.apply_symm_apply, ab.zero_add, Equiv.symm_apply_apply]
  neg_add := by
    intro T g x
    simp only [Equiv.apply_symm_apply, ab.neg_add]
  pre_add := by
    intro T' T h g g' hg x y
    apply (Φ _ _).injective
    simp only [hnat, Equiv.apply_symm_apply, ab.pre_add]
  pre_zero := by
    intro T' T h g g' hg
    apply (Φ _ _).injective
    simp only [hnat, Equiv.apply_symm_apply, ab.pre_zero]
  proper := hproper
  smooth := hsmooth
  connected := hconn

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

**`het` IS LOAD-BEARING**: without it no `AbelianSchemeStruct` exists on
`A'` — `Res` along a purely inseparable finite extension in
characteristic `p` is the standard counterexample.  (This sentence used
to say the failing clause is SMOOTHNESS; it is PROPERNESS, and the
correction with the witness worked out is in the module docstring and
restated in the falsity audit of `exists_weilRestriction_of_finiteEtale`
below.)  `hfin` is load-bearing because Weil restriction is not
representable along an arbitrary affine morphism.

**NOT VACUOUS and the junk witness is killed by the nonconstancy clause
alone**: `A' = Spec K` with `astr' = 𝟙` forces `c' = cstr = cstr ≫ 𝟙`, so
the final clause fails at `s = 𝟙`.  A prover must produce a genuinely
positive-dimensional `A'`.

**`hne` is not decoration** — see the module docstring.  It is available
free at the only call site, from the point ATOM 1 produces.

**RECUT 2026-08-02, count unchanged `1 → 1`.**  Everything above is
still true and this theorem is now **PROVEN**, over the single leaf
`exists_weilRestriction_of_finiteEtale` below.  What left the leaf is
everything that is not the construction: the group law (transported
through the universal property by `abelianSchemeStruct_of_weilRestriction`
— `AbelianSchemeStruct` presents an abelian scheme by its functor of
points, so *all nine* group fields are formal), the `t = 𝟙` step
(`eq_id_of_comp_eq_self`, which is where `hne` is spent) and the
nonconstancy transfer.  The residue mentions no group law, no
`AbelianSchemeStruct`, no curve and no nonconstancy. -/
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
        ∀ s : Spec (CommRingCat.of K) ⟶ A', c' ≠ cstr ≫ s := by
  obtain ⟨R, rstr, Φ, hproper, hsmooth, hconn, hnat⟩ :=
    exists_weilRestriction_of_finiteEtale hfin het ab
  refine ⟨R, rstr, abelianSchemeStruct_of_weilRestriction ab Φ hnat hproper hsmooth hconn,
    ((Φ C cstr).symm ⟨c, hc⟩).1, ((Φ C cstr).symm ⟨c, hc⟩).2, ?_⟩
  intro s hs
  -- The base point `t := s ≫ rstr` of the alleged constant is forced to be the identity;
  -- this is the only place `hne` is used.
  have hcst : cstr ≫ (s ≫ rstr) = cstr := by
    rw [← Category.assoc, ← hs]; exact ((Φ C cstr).symm ⟨c, hc⟩).2
  have ht : s ≫ rstr = 𝟙 _ := eq_id_of_comp_eq_self hne hcst
  have hcid : cstr ≫ 𝟙 (Spec (CommRingCat.of K)) = cstr := Category.comp_id _
  -- so `c'` is `cstr` precomposed with a genuine relative point over the identity, and
  -- naturality of `Φ` reads that back on the `L`-side.
  have hpre : (Φ C cstr).symm ⟨c, hc⟩ = RelPoint.pre cstr hcid ⟨s, ht⟩ := Subtype.ext hs
  have hΦ : (⟨c, hc⟩ : RelPoint astr (curveBaseChangeProj cstr ℓ))
      = RelPoint.pre (weilSrcMap ℓ cstr hcid) (weilSrcMap_proj ℓ cstr hcid)
          (Φ _ (𝟙 _) ⟨s, ht⟩) := by
    rw [← hnat, ← hpre, Equiv.apply_symm_apply]
  have hc' : c = weilSrcMap ℓ cstr hcid ≫ (Φ _ (𝟙 _) ⟨s, ht⟩).1 := congrArg Subtype.val hΦ
  -- `Spec L` maps into `(Spec K) ×_K L` compatibly with the two base changes, which turns
  -- the right-hand factor into an honest constant and contradicts `hnc`.
  have hj : curveBaseChangeProj cstr ℓ ≫
      pullback.lift ℓ (𝟙 (Spec (CommRingCat.of L))) (by simp) = weilSrcMap ℓ cstr hcid := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, weilSrcMap_fst]
      exact pullback.condition.symm
    · rw [Category.assoc, pullback.lift_snd, Category.comp_id, weilSrcMap_proj]
  exact hnc (pullback.lift ℓ (𝟙 (Spec (CommRingCat.of L))) (by simp) ≫
    (Φ _ (𝟙 _) ⟨s, ht⟩).1) (by rw [hc', ← hj, Category.assoc])

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
