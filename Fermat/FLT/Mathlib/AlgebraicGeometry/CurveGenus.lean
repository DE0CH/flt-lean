/-
Mathlib/AlgebraicGeometry/CurveGenus.lean — own work for the Fermat project
(not vendored from the FLT project).

# The genus of a curve over a field, via Riemann's theorem

This module supplies the layer that every audit in `ModularCurve/X0.lean` has
recorded as absent, in the words of the 2026-07-31 audit of
`finrank_cuspForm_eq_x0Genus`:

> There is NO genus of a scheme, NO `arithmeticGenus`, NO `geometricGenus`, NO
> Riemann–Roch for schemes, and NO compact Riemann surface anywhere in mathlib
> at this pin or in `Fermat/`.

That is still true of `mathlib` — `grep genus` over the pin returns nothing —
but it is *not* true that the genus cannot be **stated** here.  What the pin
does have, and what nobody had used, is enough to write down the Riemann–Roch
space of a divisor:

* `AlgebraicGeometry.Scheme.functionField` (`Mathlib/AlgebraicGeometry/
  FunctionField.lean`) — the function field `K(X)` of an integral scheme, with
  a `Field` instance;
* `AlgebraicGeometry.Scheme.ord` (`Mathlib/AlgebraicGeometry/
  OrderOfVanishing.lean`, 2025) — the order of vanishing
  `ord_z : K(X) → ℤ` at a point of codimension one of a locally Noetherian
  integral scheme;
* `AlgebraicGeometry.Scheme.Hom.residueDegree` (`Mathlib/AlgebraicGeometry/
  ResidueField.lean`) — `[κ(z) : κ(f z)]`, which over `Spec k` is the local
  degree `[κ(z) : k]` that weights a point in the degree of a divisor.

So `L(D) = {f ∈ K(X) : f = 0 ∨ div(f) + D ≥ 0}` and
`deg D = ∑_z D(z) · [κ(z) : k]` are both writable, and with them the genus is
writable too.

## The definition of the genus taken here, and why

`IsCurveGenus strX g` says **Riemann's theorem holds with the number `g`**:
there is a bound `B` such that every divisor of degree `≥ B` satisfies

    ℓ(D) = deg D + 1 − g.

This is a *characterisation*, not the classical *definition* (`g = dim H¹(X, 𝒪)`
or `g = dim H⁰(X, Ω¹)`), and it is chosen deliberately over both:

* **It needs no cohomology and no sheaf of differentials.**  mathlib has
  neither for schemes — there is no `Ω[X/S]` for a morphism of schemes at this
  pin, and no coherent cohomology — so the classical definitions cannot be
  written at all, which is exactly why no earlier attempt got past the
  statement.  Riemann's asymptotic form uses only the three ingredients listed
  above.
* **It pins `g` uniquely** (`IsCurveGenus.unique` below, PROVEN), given a
  single closed point of finite positive residue degree — so it is not a
  definition that could be satisfied by two different numbers and quietly make
  a consumer's leaf vacuous.
* **It is the form consumers want.**  `ℓ(D) = deg D + 1 − g` for `deg D ≫ 0` is
  precisely the input to the Abel–Jacobi and point-counting arguments in
  `ModularCurve/X0.lean` (`card_jacobian_of_isWeilEigenvalues`) and
  `ModularCurve/EllipticScheme.lean`; the Serre-duality refinement
  `ℓ(D) − ℓ(K − D) = deg D + 1 − g` is *not* needed by either, and demanding it
  would have forced the canonical divisor — hence `Ω¹` — into the statement.

What is given up is the small-degree range: this says nothing about `ℓ(D)` for
`deg D < B`, in particular nothing about `ℓ(0) = 1` or `ℓ(K) = g`.  A consumer
needing those needs Riemann–Roch proper, and should state it against `ell`
below rather than re-cutting the genus.

## What is a leaf here and what is proven

Exactly one leaf: `exists_isCurveGenus`, Riemann's theorem itself.  Everything
else in this file is a definition or is proven — including the uniqueness of
the genus, which is what makes the leaf non-vacuous to state.
-/
module

public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected

@[expose] public section

open CategoryTheory TopologicalSpace Order

namespace AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {k : Type u} [Field k]

/-- **The `k`-algebra structure on the function field of an integral scheme over
`Spec k`.**

`Mathlib` deliberately has no `Algebra K X.functionField` instance — see the
discussion on `not_surjective_specPreimage_of_smoothOfRelativeDimension_one` in
`Fermat/FLT/Mathlib/AlgebraicGeometry/BirationalFunctionField.lean`, which
declines to declare one because it would fix a particular instance in the
statement of a leaf.  The same reasoning applies here, so this is a `def` and
not an `instance`: it is used only inside `ell` below, through `letI`, where
the *result* type is `ℕ` and no instance escapes into any statement.

The map is the canonical one and there is nothing to choose: `Scheme.Spec` is
fully faithful, so `Spec.preimage` inverts it on the structure morphism of the
generic point, `Spec K(X) ⟶ X ⟶ Spec k`. -/
@[implicit_reducible]
noncomputable def functionFieldAlgebra [IsIntegral X] (strX : X ⟶ Spec (CommRingCat.of k)) :
    Algebra k X.functionField :=
  (Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ strX)).hom.toAlgebra

/-- **The Riemann–Roch space of a divisor**, as a subSET of the function field:
`L(D) = {f : f = 0 ∨ div(f) + D ≥ 0}`.

**The `f = 0` disjunct is load-bearing and is not cosmetic.**  `Scheme.ord`
carries the junk value `ord 0 z = 0` (`Scheme.ord_zero`), so without the
disjunct `0 ∈ L(D)` would hold if and only if `D ≥ 0` pointwise, and `L(D)`
would fail to be a subgroup at every divisor with a negative coefficient —
silently, and exactly at the divisors a Riemann–Roch argument spends its time
on.  With the disjunct, `0 ∈ L(D)` unconditionally and the set is the classical
one.

Points of codimension `≠ 1` are ignored, which is what makes this the *divisor*
condition rather than a condition at the generic point: `ord` is junk-valued
`0` off codimension one as well, so quantifying over all `z` would impose
`0 ≤ D z` at the generic point for every `f`. -/
def rrSet [IsIntegral X] [IsLocallyNoetherian X] (D : X → ℤ) : Set X.functionField :=
  {f | f = 0 ∨ ∀ z : X, coheight z = 1 → 0 ≤ Scheme.ord f z + D z}

/-- **`ℓ(D)`, the dimension over `k` of the Riemann–Roch space.**

**Why `Submodule.span` and not the set itself.**  `rrSet` is a `k`-subspace of
`K(X)` exactly when the stalks at the codimension-one points are discrete
valuation rings and the nonzero scalars of `k` are units there — both true for
a smooth curve over `k`, which is the only situation this file states anything
about.  It is *not* true for an arbitrary integral locally Noetherian scheme
(`Scheme.ord_add` in `Mathlib` carries `[IsDiscreteValuationRing
(X.presheaf.stalk x)]` as a hypothesis for precisely this reason), so the set
cannot be bundled as a `Submodule` unconditionally, and a definition that
demanded the hypothesis would put it into every statement downstream.

Taking the span keeps the definition total, and under the hypotheses of
`exists_isCurveGenus` — the only place this is used — the span equals the set,
so `ell` is the classical `ℓ(D)`.  A consumer who needs that identification
explicitly should state it; it is not needed to state or to use the genus, and
proving it requires identifying `algebraMap k K(X)` with the germ of the
structure map at `⊤`, which is the `appTop` computation
`BirationalFunctionField.lean` documents as the expensive step. -/
noncomputable def ell [IsIntegral X] [IsLocallyNoetherian X]
    (strX : X ⟶ Spec (CommRingCat.of k)) (D : X → ℤ) : ℕ :=
  letI := functionFieldAlgebra strX
  Module.finrank k (Submodule.span k (rrSet (X := X) D))

/-- **The degree of a divisor on a scheme over `Spec k`**:
`deg D = ∑_z D(z) · [κ(z) : k]`.

Written as a `finsum` rather than a `Finset.sum` so that no finiteness proof
enters the definition: `∑ᶠ` is `0` when the summand has infinite support, which
is the right junk value and keeps `IsCurveGenus` free of a finiteness side
condition in its *statement* (it carries one in `IsDivisorOn`, where it belongs).

`strX.residueDegree z` is `[κ(z) : κ(strX z)]`, and `Spec k` has one point with
residue field `k`, so this is `[κ(z) : k]` — `0` when that degree is infinite,
which for a divisor on a curve over `k` happens only at the generic point,
where `D` vanishes. -/
noncomputable def divisorDegree (strX : X ⟶ Spec (CommRingCat.of k)) (D : X → ℤ) : ℤ :=
  ∑ᶠ z : X, D z * (strX.residueDegree z : ℤ)

/-- **`D` is a Weil divisor on `X`**: finite support, concentrated in
codimension one.  A bare `X → ℤ` is used as the carrier rather than
`AlgebraicGeometry.AlgebraicCycle X ℤ` (mathlib's locally-finsupp functions)
because on the proper curves this file is about the two agree, and the bare
function needs no bundling at the call sites. -/
def IsDivisorOn (X : Scheme.{u}) (D : X → ℤ) : Prop :=
  (Function.support D).Finite ∧ ∀ z : X, D z ≠ 0 → coheight z = 1

/-- The divisor `n · [z]`. -/
noncomputable def pointDivisor (z : X) (n : ℤ) : X → ℤ := Set.indicator {z} (fun _ => n)

/-- **`n · [z]` is a divisor** (PROVEN) when `z` has codimension one. -/
theorem isDivisorOn_pointDivisor {z : X} (hz : coheight z = 1) (n : ℤ) :
    IsDivisorOn X (pointDivisor z n) := by
  have hsupp : ∀ w : X, pointDivisor z n w ≠ 0 → w = z := by
    intro w hw
    by_contra h
    exact hw (Set.indicator_of_notMem (by simpa using h) _)
  refine ⟨(Set.finite_singleton z).subset (fun w hw => ?_), fun w hw => ?_⟩
  · exact hsupp w hw
  · rw [hsupp w hw]; exact hz

/-- **`deg (n · [z]) = n · [κ(z) : k]`** (PROVEN). -/
theorem divisorDegree_pointDivisor (strX : X ⟶ Spec (CommRingCat.of k)) (z : X) (n : ℤ) :
    divisorDegree strX (pointDivisor z n) = n * (strX.residueDegree z : ℤ) := by
  rw [divisorDegree, finsum_eq_single _ z (fun w hw => ?_)]
  · rw [pointDivisor, Set.indicator_of_mem (Set.mem_singleton z)]
  · rw [pointDivisor, Set.indicator_of_notMem (by simpa using hw), zero_mul]

/-- **`g` is the genus of the curve `strX`**: Riemann's theorem holds for `strX`
with the number `g`.

See the module docstring for why this rather than `dim H¹(X, 𝒪_X)` or
`dim H⁰(X, Ω¹)`: neither of those can be written at this pin, and this one can.

**It is a genuine characterisation, not a convention.**  `IsCurveGenus.unique`
below shows two witnesses coincide as soon as `X` has one point of codimension
one and finite positive residue degree over `k` — which every proper curve over
`k` has.  So a consumer that obtains `g` from `exists_isCurveGenus` and then
computes it by two different routes is comparing the same number, and a leaf
stated against `IsCurveGenus strX g` cannot be discharged by choosing a
convenient `g`.

**It is not vacuous.**  A curve over `k` has divisors of arbitrarily large
degree (`pointDivisor z n` for `n → ∞`), so the universally quantified clause
has infinitely many instances whatever `B` is; that is exactly the content of
the uniqueness proof. -/
def IsCurveGenus [IsIntegral X] [IsLocallyNoetherian X]
    (strX : X ⟶ Spec (CommRingCat.of k)) (g : ℕ) : Prop :=
  ∃ B : ℤ, ∀ D : X → ℤ, IsDivisorOn X D → B ≤ divisorDegree strX D →
    (ell strX D : ℤ) = divisorDegree strX D + 1 - g

/-- **The genus is unique** (PROVEN), given one point of codimension one whose
residue field is a finite nontrivial extension of `k`.

The hypothesis cannot be dropped: over a `k` with `X = Spec k` there is no
codimension-one point at all, every divisor is `0`, `deg D = 0`, and any `g`
with `B > 0` satisfies the condition vacuously.  On a proper curve it is
automatic — closed points exist and have finite residue degree — but supplying
it as a hypothesis keeps this lemma independent of the properness theory.

The proof takes `D = n · [z]` with `n ≥ max (B, B', 0)`; then
`deg D = n · d ≥ n ≥ B, B'` because `d ≥ 1`, so both witnesses apply to the same
divisor and their two values of `ℓ(D)` must agree. -/
theorem IsCurveGenus.unique [IsIntegral X] [IsLocallyNoetherian X]
    {strX : X ⟶ Spec (CommRingCat.of k)} {g g' : ℕ}
    {z : X} (hz : coheight z = 1) (hdz : 0 < strX.residueDegree z)
    (h : IsCurveGenus strX g) (h' : IsCurveGenus strX g') : g = g' := by
  obtain ⟨B, hB⟩ := h
  obtain ⟨B', hB'⟩ := h'
  have hd1 : (1 : ℤ) ≤ (strX.residueDegree z : ℤ) := by exact_mod_cast hdz
  set d : ℤ := (strX.residueDegree z : ℤ) with hdd
  set n : ℤ := max (max B B') 0 with hn
  have hn0 : (0 : ℤ) ≤ n := le_max_right _ _
  have hnB : B ≤ n := le_trans (le_max_left B B') (le_max_left _ _)
  have hnB' : B' ≤ n := le_trans (le_max_right B B') (le_max_left _ _)
  have hle : n ≤ n * d := by nlinarith
  have hdiv := isDivisorOn_pointDivisor (X := X) hz n
  have hdeg := divisorDegree_pointDivisor strX z n
  have e1 := hB _ hdiv (by rw [hdeg]; linarith)
  have e2 := hB' _ hdiv (by rw [hdeg]; linarith)
  omega

/-- **RIEMANN'S THEOREM: a smooth proper geometrically connected curve over a
field has a genus** (sorry leaf, stated 2026-07-31).

`ℓ(D) = deg D + 1 − g` for every divisor of large enough degree.  Classical;
Hartshorne IV.1.3 / Stacks `0B5B`, or Fulton, *Algebraic Curves*, Ch. 8 for the
elementary treatment that does not go through cohomology (Riemann's inequality
`ℓ(D) ≥ deg D + 1 − g` with `g := max_D (deg D + 1 − ℓ(D))`, followed by the
stabilisation argument).  **The elementary route is the one to take here**: it
needs no `Ω¹` and no coherent cohomology, neither of which exists at this pin,
and it produces `g` as a supremum rather than as the dimension of a space that
cannot be written down.

**FAITHFULNESS.**  Every hypothesis is load-bearing.

* *Properness*.  Drop it and take `X = 𝔸¹_k`: `ℓ(D) = deg D + 1` for `D ≥ 0`
  supported at closed points but `L(D)` is infinite-dimensional as soon as `D`
  has a pole allowance nowhere — more sharply, `deg` is not constant on
  principal divisors on an affine curve, so no `g` can satisfy the identity for
  all large-degree `D`.
* *Smoothness of relative dimension one*.  At relative dimension `0`, `X = Spec
  k`, there are no codimension-one points, `deg D = 0` and `ell D = 1` for every
  divisor, so the identity forces `1 = 0 + 1 − g`, i.e. `g = 0`: the statement is
  TRUE but degenerate.  At relative dimension `≥ 2` the divisor theory is not
  the one `ell` computes and the statement is false.  Singular curves are
  excluded because `Scheme.ord_add` — hence the subgroup property of `rrSet`,
  hence the identification of `ell` with the classical `ℓ` — needs discrete
  valuation rings as stalks.
* *Geometric connectedness*.  A disjoint union of two curves of genus `g₁`, `g₂`
  has `ℓ(D) = ℓ(D₁) + ℓ(D₂) = deg D + 2 − g₁ − g₂` for large degree ON EACH
  COMPONENT, and no single `g` works for divisors of large total degree
  concentrated on one component.  It is also what makes `X` integral in the
  first place, which `ell` presupposes.  Note `GeometricallyConnected` rather
  than `ConnectedSpace` is used only because that is what the callers hold;
  connectedness alone would do for this statement, but geometric connectedness
  is what makes `g` a *geometric* invariant, and both consumers need that.

**WHAT THIS DOES NOT SAY.**  It gives no bound on `B`, and in particular does
not assert `ℓ(D) = deg D + 1 − g` for `deg D ≥ 2g − 1`, which is the sharp
form.  Nothing in the two consumers needs the sharp bound; a prover who obtains
it should state it separately rather than strengthen this. -/
theorem exists_isCurveGenus [IsIntegral X] [IsLocallyNoetherian X]
    (strX : X ⟶ Spec (CommRingCat.of k)) (hsm : SmoothOfRelativeDimension 1 strX)
    (hpr : IsProper strX) (hconn : GeometricallyConnected strX) :
    ∃ g : ℕ, IsCurveGenus strX g :=
  sorry

end AlgebraicGeometry
