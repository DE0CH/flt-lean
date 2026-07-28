/-
HasseBound.lean — the Hasse bound `|q + 1 − #Wbar(𝔽_q)| ≤ 2√q` for an
elliptic curve over a prime field, together with the *isogeny-degree*
infrastructure it is proven over.

WHAT THIS MODULE IS FOR.  `Fermat/FLT/FreyCurve/MazurTorsion.lean` needs
Hasse's bound (`hasse_bound_natCard_affine_point`) and the Lefschetz
congruence `#Wbar(𝔽_q) ≡ det(1 − F)` on the `N`-torsion
(`natCard_affine_point_eq_det_one_sub_frobeniusTorsionEnd`).  Both are
consequences of ONE classical statement — that the degree of the
endomorphism `[m] − [n]∘F` of `Wbar` over `𝔽̄_q` is the binary quadratic
form `m² − a·m·n + n²·q` — and that statement is what this module
isolates, as `natCard_ker_degreeFormEnd`.  Building it once here rather
than twice inside `MazurTorsion.lean` is deliberate: it is shared
infrastructure between two separately owned leaves, and it is small
enough to elaborate in seconds, which a 33k-line module is not.

THE CUT, AND WHY IT IS THIS ONE.  An audit of 2026-07-27 recorded in
`MazurTorsion.lean` rejected three cuts of Hasse's bound — degree-form
positivity `∀ m n, 0 ≤ m² − a·m·n + n²q`, an interface-only existential,
and the character-sum/Stepanov route — the first two because they are
*equivalent* to the bound (a binary quadratic form over `ℤ` with leading
coefficient `1` is positive semidefinite exactly when its discriminant is
`≤ 0`), the third because it is a multi-hundred-line polynomial-counting
development.  That audit is correct on its own axis.  The axis it did not
search, and the one taken here, is the ISOGENY axis:

  **give the form a MEANING, so that its positivity becomes free.**

`m² − a·m·n + n²q` is not merely a quadratic form: when `q ∤ m` it is the
CARDINALITY of the kernel of `[m] − [n]∘F`.  A cardinality is a natural
number, so `0 ≤ m² − a·m·n + n²q` is then a `Nat.cast_nonneg` and the
whole bound follows by evaluating at two explicit points.  The leaf that
remains, `natCard_ker_degreeFormEnd`, is therefore NOT equivalent to
Hasse's bound — it is strictly stronger, and it is the classical theorem
(Silverman *AEC* III.6.2 + V.1.1) rather than an inert inequality that no
argument can get a grip on.  That is the trade this module makes, and it
is made with eyes open: the frontier does not shrink, but the surviving
leaf is a NAMED theorem with a textbook proof, it is shared between two
leaves instead of belonging to one, and every step downstream of it is
now machine-checked.

SECOND CUT, 2026-07-27.  The `(m, n) = (1, 1)` evaluation is no longer a
consequence of the leaf but an INPUT to it, and it is PROVEN.  It reads
`#ker([1] − F) = #Wbar(𝔽_q)`, i.e. the fixed-point identity
`Wbar(𝔽̄_q)^F = Wbar(𝔽_q)`, and it is
`natCard_ker_one_sub_frobeniusPointEnd` below.  Proving it lets the
surviving leaf, `exists_natCard_ker_degreeFormEnd`, quantify its middle
coefficient EXISTENTIALLY: the leaf asserts only that the kernel count is
a binary quadratic form `m² − c·m·n + n²q` in `(m, n)`, and the pinning
`c = q + 1 − #Wbar(𝔽_q) = frobeniusTrace` is then a theorem, obtained by
evaluating at `(1, 1)`.  So `frobeniusTrace` no longer occurs anywhere in
the frontier, and `natCard_ker_degreeFormEnd` — the statement two other
leaves consume — is PROVEN.

`natCard_ker_one_sub_frobeniusPointEnd` is also the "cheap first step"
that `natCard_affine_point_eq_det_one_sub_frobeniusTorsionEnd`'s
docstring points its owner at, and it is now available to that owner
without waiting for the degree theory.

THIRD CUT, 2026-07-28: `exists_natCard_ker_degreeFormEnd` is PROVEN, over
three smaller leaves, along the ENDOMORPHISM-ALGEBRA axis its own
docstring recommended.  What closed, and it is the reusable part:

* `degreeFormEnd_mul_conj` / `conj_mul_degreeFormEnd` — `ψ ∘ ψ' = ψ' ∘ ψ
  = [m² − c·m·n + n²q]` for the conjugate `ψ' = [m − n·c] + [n]∘F`.  Pure
  ring algebra in `ℤ[F]` over the characteristic equation.
* `surjective_degreeFormEnd` — BOTH factors are surjective, because each
  is a left factor of the surjective `[d]`.  The route note of 2026-07-27
  listed this as a side condition to be discharged separately; it is
  free, and in particular no rationality certificate for `[m] − [n]∘F` is
  needed anywhere, which is what keeps the characteristic-`p` dual — which
  `Isogeny.lean` machine-refutes — out of the argument.
* `natCard_ker_mul_natCard_ker_conj` — `#ker ψ · #ker ψ' = d²` for
  `q ∤ d`, from `Isogeny.card_ker_comp` and `TorsionCard.card_torsionBy`.

What remains open, and each is strictly smaller than what it replaced:
`exists_sq_frobeniusPointEnd` (the Frobenius characteristic equation on
points, `F² = c·F − q`), `natCard_ker_degreeFormEnd_le` (separable degree
≤ degree, one-sided, no hypothesis on `m`), and
`natCard_ker_degreeFormEnd_of_dvd` (the `q`-primary case `q ∣ d`, reduced
in its docstring to the single ordinary `q`-torsion count
`#ker([c] − F) = q`).

A NOTE FOR WHOEVER OWNS THE CHARACTERISTIC EQUATION.  The 2026-07-27 plan
placed it in `FreyCurve/MazurTorsion.lean` as
`charEquation_point_map_frobAlgHom`.  That is not implementable in that
direction: `MazurTorsion.lean` `public import`s this module, so anything
stated there is downstream of every consumer here.  It is stated here
instead, as `exists_sq_frobeniusPointEnd`.
-/
module

public import Fermat.FLT.EllipticCurve.WeilPairing
-- `Isogeny.card_ker_comp` (`#ker (h ∘ f) = #ker h · #ker f` for surjective `f`,
-- pure group theory) and `WeierstrassCurve.zsmul_surjective_algClosed`.  This
-- adds ten `Fermat` modules to this file's cone and NONE to any consumer's:
-- `MazurTorsion.lean`, the only importer of this module, already imports
-- `Isogeny` directly.
public import Fermat.FLT.EllipticCurve.Isogeny

@[expose] public section

open _root_.WeierstrassCurve
open _root_.WeierstrassCurve.Affine

namespace HasseBound

/-- The `q`-power Frobenius as a `ℤ`-linear endomorphism of the group of
`𝔽̄_q`-points of a Weierstrass curve over `𝔽_q`.

This is the point-level companion of `WeilPairing.frobeniusTorsionEnd`,
which is its restriction to the `N`-torsion: both are built from the same
`Affine.Point.map (frobAlgHom q)`. -/
noncomputable def frobeniusPointEnd (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) :
    Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point) :=
  AddMonoidHom.toIntLinearMap
    (WeierstrassCurve.Affine.Point.map (W' := Wbar) (S := ZMod q)
      (WeilPairing.frobAlgHom q))

/-- The endomorphism `[m] − [n]∘F` of `Wbar` over `𝔽̄_q`, whose degree is
the binary quadratic form `m² − a·m·n + n²q`. -/
noncomputable def degreeFormEnd (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) (m n : ℤ) :
    Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point) :=
  m • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)) -
    n • frobeniusPointEnd q Wbar

/-- The **Frobenius trace** `a = q + 1 − #Wbar(𝔽_q)` of an elliptic curve
over `𝔽_q`, as a rational integer.  Hasse's bound is `a² ≤ 4q`. -/
noncomputable def frobeniusTrace (q : ℕ) (Wbar : WeierstrassCurve (ZMod q)) : ℤ :=
  (q : ℤ) + 1 - (Nat.card Wbar.toAffine.Point : ℤ)

/-! ### The rational points are the Frobenius-fixed points

This section proves the `(m, n) = (1, 1)` evaluation of the degree form,
`#ker([1] − F) = #Wbar(𝔽_q)`.  It is an INPUT of the leaf below, not a
specialization of it: it is exactly what pins the middle coefficient of
the quadratic form to the Frobenius trace, and it is what lets the leaf
be stated with an *unnamed* coefficient (see `exists_natCard_ker_degreeFormEnd`).
-/

/-- **The `q`-power map fixes exactly the prime field of `𝔽̄_q`**: an
element with `x ^ q = x` lies in the image of `ZMod q`.

Counting, through `WeilPairing.frobFixedFinset`: the image of
`algebraMap (ZMod q) 𝔽̄_q` is a `q`-element subset of the `q`-element
root set of `X ^ q − X`, hence all of it. -/
theorem exists_algebraMap_eq_of_pow_card_eq (q : ℕ) [Fact q.Prime]
    {x : AlgebraicClosure (ZMod q)} (hx : x ^ q = x) :
    ∃ c : ZMod q, algebraMap (ZMod q) (AlgebraicClosure (ZMod q)) c = x := by
  classical
  haveI : NeZero q := ⟨(Fact.out : q.Prime).pos.ne'⟩
  have hinj : Function.Injective (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))) :=
    (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))).injective
  have key : Finset.image (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))) Finset.univ
      = WeilPairing.frobFixedFinset q 1 := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro z hz
      rw [Finset.mem_image] at hz
      obtain ⟨c, -, rfl⟩ := hz
      rw [WeilPairing.mem_frobFixedFinset_iff q one_ne_zero, WeilPairing.mem_frobFixed_iff,
        pow_one, ← map_pow, ZMod.pow_card]
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, ZMod.card,
        WeilPairing.card_frobFixedFinset q one_ne_zero, pow_one]
  have hxmem : x ∈ WeilPairing.frobFixedFinset q 1 := by
    rw [WeilPairing.mem_frobFixedFinset_iff q one_ne_zero, WeilPairing.mem_frobFixed_iff,
      pow_one]
    exact hx
  rw [← key, Finset.mem_image] at hxmem
  obtain ⟨c, -, hc⟩ := hxmem
  exact ⟨c, hc⟩

/-- Membership in the kernel of `degreeFormEnd q Wbar 1 1 = [1] − F` is
being fixed by the `q`-power Frobenius. -/
theorem mem_ker_degreeFormEnd_one_one_iff (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q))
    {P : (Wbar⁄(AlgebraicClosure (ZMod q))).Point} :
    P ∈ LinearMap.ker (degreeFormEnd q Wbar 1 1) ↔ frobeniusPointEnd q Wbar P = P := by
  rw [LinearMap.mem_ker]
  have hval : (degreeFormEnd q Wbar 1 1) P = P - frobeniusPointEnd q Wbar P := by
    show (1 : ℤ) • P - (1 : ℤ) • (frobeniusPointEnd q Wbar) P = _
    rw [one_smul, one_smul]
  rw [hval, sub_eq_zero, eq_comm]

/-- **`#ker([1] − F) = #Wbar(𝔽_q)`** (PROVEN 2026-07-27): the points of
`Wbar(𝔽̄_q)` fixed by the `q`-power Frobenius are exactly the
`𝔽_q`-rational points.

This is the `(m, n) = (1, 1)` value of the degree form, and the whole
arithmetic content of the Frobenius trace: `Wbar(𝔽_q) ↪ Wbar(𝔽̄_q)` is
injective (`Point.map_injective`) with image inside the fixed points
(`Point.map_baseChange`), and a fixed affine point has both coordinates
in `{x | x ^ q = x}`, which is the prime field
(`exists_algebraMap_eq_of_pow_card_eq`), so the inclusion is onto. -/
theorem natCard_ker_one_sub_frobeniusPointEnd (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) :
    Nat.card (LinearMap.ker (degreeFormEnd q Wbar 1 1))
      = Nat.card Wbar.toAffine.Point := by
  classical
  have hmem : ∀ P : Wbar.toAffine.Point,
      WeierstrassCurve.Affine.Point.baseChange (W' := Wbar) (ZMod q)
        (AlgebraicClosure (ZMod q)) P ∈ LinearMap.ker (degreeFormEnd q Wbar 1 1) := by
    intro P
    rw [mem_ker_degreeFormEnd_one_one_iff]
    exact WeierstrassCurve.Affine.Point.map_baseChange (W' := Wbar)
      (F := ZMod q) (K := AlgebraicClosure (ZMod q)) (L := AlgebraicClosure (ZMod q))
      (WeilPairing.frobAlgHom q) P
  refine (Nat.card_congr (Equiv.ofBijective
      (fun P : Wbar.toAffine.Point =>
        (⟨WeierstrassCurve.Affine.Point.baseChange (W' := Wbar) (ZMod q)
            (AlgebraicClosure (ZMod q)) P, hmem P⟩ :
          LinearMap.ker (degreeFormEnd q Wbar 1 1))) ⟨?_, ?_⟩)).symm
  · intro P₁ P₂ hP
    exact WeierstrassCurve.Affine.Point.map_injective _ (congrArg Subtype.val hP)
  · rintro ⟨P, hP⟩
    rw [mem_ker_degreeFormEnd_one_one_iff] at hP
    cases P with
    | zero => exact ⟨0, Subtype.ext (map_zero _)⟩
    | some x y h =>
      have hP' : WeierstrassCurve.Affine.Point.map (W' := Wbar) (S := ZMod q)
          (WeilPairing.frobAlgHom q) (WeierstrassCurve.Affine.Point.some x y h)
          = WeierstrassCurve.Affine.Point.some x y h := hP
      rw [WeierstrassCurve.Affine.Point.map_some] at hP'
      obtain ⟨hx, hy⟩ := WeierstrassCurve.Affine.Point.some.inj hP'
      have hx' : x ^ q = x := hx
      have hy' : y ^ q = y := hy
      obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_pow_card_eq q hx'
      obtain ⟨d, hd⟩ := exists_algebraMap_eq_of_pow_card_eq q hy'
      subst hc
      subst hd
      have hns : (Wbar⁄(ZMod q)).Nonsingular c d :=
        (WeierstrassCurve.Affine.baseChange_nonsingular (W := Wbar)
          (f := Algebra.ofId (ZMod q) (AlgebraicClosure (ZMod q)))
          (Algebra.ofId (ZMod q) (AlgebraicClosure (ZMod q))).injective c d).mp h
      exact ⟨WeierstrassCurve.Affine.Point.some c d hns, Subtype.ext rfl⟩

/-! ### Generic `Module.End`/kernel plumbing

Three statements about an arbitrary `ℤ`-module, isolated from the curve so
that the arithmetic below reads as arithmetic.  Nothing here is specific to
elliptic curves; `natCard_ker_mul` is `Isogeny.card_ker_comp` transported
from `AddMonoidHom` to `Module.End`.
-/

/-- A left factor of a surjective composite is surjective.  Used with
`h : ψ ∘ ψ' = [d]` and the divisibility of `Wbar(𝔽̄_q)`: it is what makes the
surjectivity side condition of `Isogeny.card_ker_comp` free here, so that no
rationality certificate for `[m] − [n]∘F` is needed. -/
theorem surjective_of_mul_eq_zsmul {M : Type*} [AddCommGroup M]
    {f g : Module.End ℤ M} {d : ℤ} (h : f * g = d • (1 : Module.End ℤ M))
    (hd : Function.Surjective fun P : M => d • P) : Function.Surjective f := by
  intro P
  obtain ⟨Q, hQ⟩ := hd P
  refine ⟨g Q, ?_⟩
  have happ : f (g Q) = d • Q := congrArg (fun e : Module.End ℤ M => e Q) h
  rw [happ]
  exact hQ

/-- The kernel of a `ℤ`-linear endomorphism, counted as an `AddMonoidHom`
kernel: the two carriers are the same set. -/
theorem natCard_ker_toAddMonoidHom {M : Type*} [AddCommGroup M] (f : Module.End ℤ M) :
    Nat.card (AddMonoidHom.ker f.toAddMonoidHom) = Nat.card (LinearMap.ker f) :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => by
    simp only [AddMonoidHom.mem_ker, LinearMap.mem_ker, LinearMap.toAddMonoidHom_coe])

/-- **Kernel counts multiply along a composite whose right factor is
surjective** — `Isogeny.card_ker_comp` in `Module.End` form. -/
theorem natCard_ker_mul {M : Type*} [AddCommGroup M] (f g : Module.End ℤ M)
    (hg : Function.Surjective g) :
    Nat.card (LinearMap.ker (f * g))
      = Nat.card (LinearMap.ker f) * Nat.card (LinearMap.ker g) := by
  have hcomp : f.toAddMonoidHom.comp g.toAddMonoidHom = (f * g).toAddMonoidHom := by
    ext P
    rfl
  have hg' : Function.Surjective (g.toAddMonoidHom) := hg
  have key := _root_.WeierstrassCurve.Isogeny.card_ker_comp
    g.toAddMonoidHom f.toAddMonoidHom hg'
  rw [hcomp, natCard_ker_toAddMonoidHom, natCard_ker_toAddMonoidHom,
    natCard_ker_toAddMonoidHom] at key
  exact key

/-- The kernel of `[d]` is the `d`-torsion. -/
theorem ker_zsmul_one {M : Type*} [AddCommGroup M] (d : ℤ) :
    LinearMap.ker (d • (1 : Module.End ℤ M)) = Submodule.torsionBy ℤ M d := by
  ext P
  simp only [LinearMap.mem_ker, LinearMap.smul_apply, Module.End.one_apply,
    Submodule.mem_torsionBy_iff]

/-! ### The conjugate endomorphism

`ψ = [m] − [n]∘F` has a CONJUGATE `ψ' = [m − n·c] + [n]∘F` inside the
commutative subring `ℤ[F] ⊆ End(Wbar(𝔽̄_q))`, and the Frobenius characteristic
equation makes `ψ ∘ ψ' = ψ' ∘ ψ = [m² − c·m·n + n²q]`.  That single identity
is what carries the whole endomorphism-algebra route: it makes both factors
surjective (a left factor of the surjective `[d]`), so `Isogeny.card_ker_comp`
applies with no rationality input, and it identifies `ker (ψ ∘ ψ')` with the
`d`-torsion, which `TorsionCard.card_torsionBy` counts.
-/

/-- **The characteristic equation of the `q`-power Frobenius, on points**
(sorry leaf, opened 2026-07-28; Silverman *AEC* V.2.3.1): there is an integer
`c` with `F² = c·F − q` in `Module.End ℤ (Wbar(𝔽̄_q))`.

WHERE THIS LEAF HAD TO LIVE, and it is not where it was planned.  The cut of
2026-07-27 recorded this step as belonging in `FreyCurve/MazurTorsion.lean`
(as `charEquation_point_map_frobAlgHom`).  That is not implementable:
`MazurTorsion.lean` `public import`s THIS module (line 114 there), so anything
stated in it is strictly downstream and cannot be consumed here.  The leaf is
therefore stated here, where its consumers are.

THE COEFFICIENT IS EXISTENTIAL ON PURPOSE.  Naming `c = q + 1 − #Wbar(𝔽_q)`
would fold the `(1, 1)` evaluation into this leaf; that evaluation is already
PROVEN separately as `natCard_ker_one_sub_frobeniusPointEnd`, and
`natCard_ker_degreeFormEnd` below does the pinning.  So `frobeniusTrace` does
not occur in this statement and must not be introduced into it.

WHY IT IS NOT VACUOUS.  `c = 0` is *not* a free choice: `F² = −q` would give
`#ker([1] − F) = 1 + q` through `natCard_ker_degreeFormEnd`, hence
`#Wbar(𝔽_q) = q + 1` for every curve, which is false already for
`y² = x³ + 1` over `𝔽₅` (`#E(𝔽₅) = 6 = q + 1` there, but `y² = x³ + x` over
`𝔽₅` has `#E(𝔽₅) = 8`).  Any `c` satisfying this leaf is forced to be
`q + 1 − #Wbar(𝔽_q)`, by `natCard_ker_degreeFormEnd`'s own argument.

ROUTE.  `Wbar(𝔽̄_q)` is a TORSION group — every point is defined over some
finite subfield — so an identity in `End` may be checked on each `E[ℓ^k]`
separately.  For `ℓ ≠ q` the module `E[ℓ^k]` is free of rank `2` over
`ZMod (ℓ^k)` (`WeierstrassCurve.p_torsion_rank`, `Torsion.lean`, which needs
only `(ℓ : 𝔽̄_q) ≠ 0` and *no* characteristic-zero hypothesis), and
Cayley–Hamilton for a `2 × 2` matrix gives `F² = tr(F)·F − det(F)` there; the
arithmetic input is `det(F | E[ℓ^k]) = q` and the compatibility of `tr` across
`ℓ` and `k`.  THE CHECK THAT WOULD REFUTE the claim that this is the cheapest
route: a proof of `F² − cF + q = 0` that does not pass through a torsion
representation — the classical alternative is the dual isogeny, and the dual
is machine-refuted in characteristic `p` in `Isogeny.lean`
(`Isogeny.NotIsRationalMapDualHom`), so it is unavailable. -/
theorem exists_sq_frobeniusPointEnd (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] :
    ∃ c : ℤ, frobeniusPointEnd q Wbar * frobeniusPointEnd q Wbar
      = c • frobeniusPointEnd q Wbar
        - (q : ℤ) • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)) :=
  sorry

/-- **`ψ ∘ ψ' = [m² − c·m·n + n²q]`** (PROVEN over `exists_sq_frobeniusPointEnd`):
the conjugate of `ψ = [m] − [n]∘F` is `ψ' = [m − n·c] + [n]∘F`, which is
`degreeFormEnd q Wbar (m − n·c) (−n)`, and the product is multiplication by the
value of the degree form.  Pure ring algebra in `ℤ[F]`, using the
characteristic equation once. -/
theorem degreeFormEnd_mul_conj (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) {c : ℤ}
    (hc : frobeniusPointEnd q Wbar * frobeniusPointEnd q Wbar
      = c • frobeniusPointEnd q Wbar
        - (q : ℤ) • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)))
    (m n : ℤ) :
    degreeFormEnd q Wbar m n * degreeFormEnd q Wbar (m - n * c) (-n)
      = (m ^ 2 - c * m * n + n ^ 2 * (q : ℤ)) •
        (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)) := by
  simp only [degreeFormEnd, neg_smul, sub_neg_eq_add, sub_mul, mul_add,
    smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, hc, smul_sub]
  module

/-- **`ψ' ∘ ψ = [m² − c·m·n + n²q]`** (PROVEN): the same product in the other
order, which is what makes `ψ'` surjective as well as `ψ`.  `ℤ[F]` is
commutative, but the two products are different *terms*, so both are needed. -/
theorem conj_mul_degreeFormEnd (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) {c : ℤ}
    (hc : frobeniusPointEnd q Wbar * frobeniusPointEnd q Wbar
      = c • frobeniusPointEnd q Wbar
        - (q : ℤ) • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)))
    (m n : ℤ) :
    degreeFormEnd q Wbar (m - n * c) (-n) * degreeFormEnd q Wbar m n
      = (m ^ 2 - c * m * n + n ^ 2 * (q : ℤ)) •
        (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)) := by
  simp only [degreeFormEnd, neg_smul, sub_neg_eq_add, mul_sub, add_mul,
    smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, hc, smul_sub]
  module

/-- **The degree form is invariant under conjugation** (PROVEN, `ring`): the
conjugate `(m − n·c, −n)` of `(m, n)` has the same value.  This is what lets a
one-sided bound on the kernel count be applied to BOTH factors. -/
theorem degreeForm_conj (c m n q : ℤ) :
    (m - n * c) ^ 2 - c * (m - n * c) * (-n) + (-n) ^ 2 * q
      = m ^ 2 - c * m * n + n ^ 2 * q := by
  ring

/-- **Both `ψ` and its conjugate are surjective** as soon as the degree form
does not vanish (PROVEN): each is a left factor of `[d]`, which is surjective
by divisibility of the points of an elliptic curve over an algebraically
closed field (`WeierstrassCurve.zsmul_surjective_algClosed`, valid in every
characteristic). -/
theorem surjective_degreeFormEnd (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] {c : ℤ}
    (hc : frobeniusPointEnd q Wbar * frobeniusPointEnd q Wbar
      = c • frobeniusPointEnd q Wbar
        - (q : ℤ) • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)))
    {m n : ℤ} (hd : m ^ 2 - c * m * n + n ^ 2 * (q : ℤ) ≠ 0) :
    Function.Surjective (degreeFormEnd q Wbar m n) ∧
      Function.Surjective (degreeFormEnd q Wbar (m - n * c) (-n)) := by
  classical
  haveI : ((Wbar⁄(AlgebraicClosure (ZMod q))).toAffine).IsElliptic :=
    inferInstanceAs
      (Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).IsElliptic
  have hsurj : Function.Surjective
      fun P : (Wbar⁄(AlgebraicClosure (ZMod q))).Point =>
        (m ^ 2 - c * m * n + n ^ 2 * (q : ℤ)) • P :=
    _root_.WeierstrassCurve.zsmul_surjective_algClosed
      (Wbar⁄(AlgebraicClosure (ZMod q))).toAffine hd
  exact ⟨surjective_of_mul_eq_zsmul (degreeFormEnd_mul_conj q Wbar hc m n) hsurj,
    surjective_of_mul_eq_zsmul (conj_mul_degreeFormEnd q Wbar hc m n) hsurj⟩

/-- **`#ker ψ · #ker ψ' = d²`** (PROVEN over `exists_sq_frobeniusPointEnd`,
where `d = m² − c·m·n + n²q`): the composite is `[d]`, whose kernel is the
`d`-torsion, of order `d²` by `TorsionCard.card_torsionBy`; the factors' kernel
counts multiply by `Isogeny.card_ker_comp`, whose surjectivity side condition
is `surjective_degreeFormEnd`.

`q ∤ d` is exactly the hypothesis of `card_torsionBy` and is genuinely needed:
at `q = 5`, `c = 1`, `(m, n) = (1, 1)` one has `d = 5`, and an ordinary curve
there has `#E[5] = 5`, not `25`. -/
theorem natCard_ker_mul_natCard_ker_conj (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] {c : ℤ}
    (hc : frobeniusPointEnd q Wbar * frobeniusPointEnd q Wbar
      = c • frobeniusPointEnd q Wbar
        - (q : ℤ) • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)))
    {m n : ℤ} (hd : ¬ ((q : ℤ) ∣ m ^ 2 - c * m * n + n ^ 2 * (q : ℤ))) :
    (Nat.card (LinearMap.ker (degreeFormEnd q Wbar m n)) : ℤ)
        * (Nat.card (LinearMap.ker (degreeFormEnd q Wbar (m - n * c) (-n))) : ℤ)
      = (m ^ 2 - c * m * n + n ^ 2 * (q : ℤ)) ^ 2 := by
  classical
  set d : ℤ := m ^ 2 - c * m * n + n ^ 2 * (q : ℤ) with hdef
  have hd0 : d ≠ 0 := by
    intro h
    exact hd (by rw [h]; exact dvd_zero _)
  obtain ⟨-, hsurj'⟩ := surjective_degreeFormEnd q Wbar hc (m := m) (n := n) hd0
  have hprod := natCard_ker_mul (degreeFormEnd q Wbar m n)
    (degreeFormEnd q Wbar (m - n * c) (-n)) hsurj'
  rw [degreeFormEnd_mul_conj q Wbar hc m n, ← hdef, ker_zsmul_one] at hprod
  -- the `d`-torsion is the `|d|`-torsion, and has `d²` elements
  have habs : Submodule.torsionBy ℤ (Wbar⁄(AlgebraicClosure (ZMod q))).Point d
      = Submodule.torsionBy ℤ (Wbar⁄(AlgebraicClosure (ZMod q))).Point (d.natAbs : ℤ) := by
    rcases Int.natAbs_eq d with h | h
    · rw [← h]
    · ext P
      simp only [Submodule.mem_torsionBy_iff]
      constructor
      · intro hP
        rw [h, neg_smul, neg_eq_zero] at hP
        exact hP
      · intro hP
        rw [h, neg_smul, hP, neg_zero]
  have hqdvd : ¬ (q ∣ d.natAbs) := by
    intro h
    exact hd (Int.natAbs_dvd_natAbs.mp (by simpa using h))
  haveI : CharP (AlgebraicClosure (ZMod q)) q :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))).injective q
  have hqd : ((d.natAbs : ℕ) : AlgebraicClosure (ZMod q)) ≠ 0 := by
    intro h0
    exact hqdvd ((CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod q)) q _).mp h0)
  have hcard : Nat.card (Submodule.torsionBy ℤ
      (Wbar⁄(AlgebraicClosure (ZMod q))).Point (d.natAbs : ℤ)) = d.natAbs ^ 2 :=
    TorsionCard.card_torsionBy
      (Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))) d.natAbs hqd
  rw [habs, hcard] at hprod
  have hZ : ((d.natAbs : ℕ) : ℤ) ^ 2 = d ^ 2 := by
    rw [Int.natCast_natAbs, sq_abs]
  have h2 : ((d.natAbs : ℕ) : ℤ) ^ 2
      = (Nat.card (LinearMap.ker (degreeFormEnd q Wbar m n)) : ℤ)
        * (Nat.card (LinearMap.ker (degreeFormEnd q Wbar (m - n * c) (-n))) : ℤ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℤ)) hprod
  rw [hZ] at h2
  linarith [h2]

/-! ### The degree form -/

/-- **Separable degree ≤ degree** (sorry leaf, opened 2026-07-28; the first of
the two halves of step 4 of the endomorphism-algebra route):
`#ker([m] − [n]∘F) ≤ m² − c·m·n + n²q`, for `c` the coefficient of the
Frobenius characteristic equation and with NO hypothesis on `m`.

Classically this is the trivial half — `deg = deg_sep · deg_insep`, so
`#ker ψ = deg_sep ψ ≤ deg ψ = m² − c·m·n + n²q` — and it is trivial only once
`deg` exists, which in characteristic `p` it does not (see the MACHINERY AUDIT
below).  It is stated one-sidedly and without `q ∤ m` on purpose:

* **one-sided**, because `degreeForm_conj` makes the value of the form
  invariant under `(m, n) ↦ (m − n·c, −n)`, so the SAME bound applied to `ψ`
  and to its conjugate `ψ'`, together with the proven
  `#ker ψ · #ker ψ' = d²`, pins both to `d`.  Two applications of an
  inequality replace an equality;
* **without `q ∤ m`**, because the inequality is true for inseparable `ψ` too
  (there it is strict: `#ker(−[n]∘F) = n²` against the form's value `n²q`),
  and dropping the hypothesis costs nothing while making the leaf usable at
  the conjugate `(m − n·c, −n)`, whose first coordinate is divisible by `q`
  in exactly the case `q ∣ d`.

`hc` IS LOAD-BEARING: without it `c` is a free integer and the statement is
false for `c` large and positive (the right-hand side goes negative while the
left-hand side is a cardinality).

NON-VACUITY.  At `n = 0` the bound reads `#ker [m] ≤ m²`, which
`TorsionCard.card_torsionBy` meets with equality for `q ∤ m`; at
`(m, n) = (1, 1)` it reads `#Wbar(𝔽_q) ≤ 1 − c + q`
(`natCard_ker_one_sub_frobeniusPointEnd`), which is an equality, so the bound
is sharp exactly where it is used and carries the arithmetic. -/
theorem natCard_ker_degreeFormEnd_le (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] {c : ℤ}
    (hc : frobeniusPointEnd q Wbar * frobeniusPointEnd q Wbar
      = c • frobeniusPointEnd q Wbar
        - (q : ℤ) • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)))
    (m n : ℤ) :
    (Nat.card (LinearMap.ker (degreeFormEnd q Wbar m n)) : ℤ)
      ≤ m ^ 2 - c * m * n + n ^ 2 * (q : ℤ) :=
  sorry

/-- **The `q`-primary case** (sorry leaf, opened 2026-07-28; the second half of
step 4): when `q ∤ m` but `q ∣ d = m² − c·m·n + n²q`, the kernel count is still
the value of the form.

WHY THIS CASE IS SEPARATE, and it is not an artefact of the proof.  The proven
`natCard_ker_mul_natCard_ker_conj` evaluates `#ker ψ · #ker ψ'` as `#E[d]`,
and `TorsionCard.card_torsionBy` computes `#E[d] = d²` only for `q ∤ d`.  For
`q ∣ d` that is FALSE: at `q = 5`, `c = 1`, `(m, n) = (1, 1)` one has `d = 5`,
and an ordinary curve over `𝔽₅` has `#E[5] = 5`, not `25`.  So the whole
`q ∤ d` argument is unavailable here and something new is needed.

WHAT IS NEEDED, reduced as far as it goes (route note, 2026-07-28; the axis
searched was the factorisation of `ℤ[F]` by powers of `F`).  Note first that
`q ∣ d` and `q ∤ m` FORCE `q ∤ c`: modulo `q`, `d ≡ m·(m − c·n)`, so `q ∣ d`
with `q ∤ m` gives `m ≡ c·n`, which needs both `q ∤ c` and `q ∤ n`.  That is
the ORDINARY case; the supersingular case (`q ∣ c`) never reaches this leaf,
because there `d ≡ m² ≢ 0`.

Now write `F̄ = [c] − F`, so that `F ∘ F̄ = [q]` — this is the characteristic
equation again, and it is `degreeFormEnd_mul_conj` at `(m, n) = (0, −1)`.  Any
`α = [M] − [N]∘F` with `q ∣ M`, say `M = q·M₀`, factors as
`α = F ∘ ([c·M₀ − N] − [M₀]∘F)`, and `F` is BIJECTIVE on `Wbar(𝔽̄_q)`
(injective because `x ↦ x^q` is; surjective because `𝔽̄_q` is algebraically
closed), so `#ker α` is unchanged by peeling `F` off.  Peeling until the first
coordinate is prime to `q` writes `ψ' = F^k ∘ β` with `q ∤` the first
coordinate of `β` and `N(β) = d / q^k`, whence
`#ker ψ · #ker β = #E[d] = #E[q^k] · (d/q^k)²`.  The `q ∤ d` case of this very
theorem gives `#ker β = d / q^k`, so the leaf collapses to

    #E[q^k] = q^k   for  q ∤ c,   equivalently   #ker([c] − F) = q,

the `q`-torsion count of an ORDINARY curve.  THE CHECK THAT WOULD REFUTE this
reduction: a proof of `#ker([c] − F) = q` for `q ∤ c` that does not go through
`F` being bijective — or, in the other direction, an `#E[q^∞]` structure
theorem already in this tree, which a name-level grep of `Fermat/`,
`.lake/packages/mathlib/` and `~/cs/FLT` did not find. -/
theorem natCard_ker_degreeFormEnd_of_dvd (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] {c : ℤ}
    (hc : frobeniusPointEnd q Wbar * frobeniusPointEnd q Wbar
      = c • frobeniusPointEnd q Wbar
        - (q : ℤ) • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)))
    {m n : ℤ} (hm : ¬ ((q : ℤ) ∣ m))
    (hd : (q : ℤ) ∣ m ^ 2 - c * m * n + n ^ 2 * (q : ℤ)) :
    (Nat.card (LinearMap.ker (degreeFormEnd q Wbar m n)) : ℤ)
      = m ^ 2 - c * m * n + n ^ 2 * (q : ℤ) :=
  sorry

/-- **The degree of `[m] − [n]∘F` is a binary quadratic form of
discriminant `c² − 4q`, counted by its kernel** (sorry leaf, opened
2026-07-27; the ONLY remaining input of Hasse's bound
`hasse_bound_natCard_affine_point`): for `q ∤ m` the endomorphism
`[m] − [n]∘F` of `Wbar(𝔽̄_q)` is separable, so its degree is the
cardinality of its kernel, and that degree is `m² − c·m·n + n²q` for a
coefficient `c` independent of `(m, n)`.

Silverman *AEC*: III.6.2 (`deg` is a positive definite quadratic form on
`End(E)`, via the dual isogeny), III.5.5/V.1.1 (`[m] − [n]∘F` is
separable iff `char ∤ m`), V.1.1 (the evaluation `deg F = q`, hence the
displayed form).

WHY THE COEFFICIENT IS EXISTENTIALLY QUANTIFIED, and this is the whole
cut of 2026-07-27.  The classical statement names `c = q + 1 − #Wbar(𝔽_q)`,
and naming it there bundles *two* separate things: the SHAPE of the form
(a quadratic form in `(m, n)` with leading coefficients `1` and `q`),
which needs the whole missing degree theory, and the VALUE of its middle
coefficient, which needs only the `(m, n) = (1, 1)` evaluation
`deg(1 − F) = #ker(1 − F) = #Wbar(𝔽_q)`.  The second half is PROVEN, as
`natCard_ker_one_sub_frobeniusPointEnd`, so `natCard_ker_degreeFormEnd`
below is now a theorem over this leaf.  That is a genuine reduction: the
Frobenius trace, `frobeniusTrace`, no longer appears anywhere in the
frontier.

An earlier version of this docstring recorded the classical three-way
decomposition (parallelogram law; `deg F = q` and `deg(1 − F) = #E(𝔽_q)`;
`#ker φ = deg φ` for separable `φ`) and rejected cutting along it,
because every piece needs the same absent `deg`.  That reasoning is still
correct **on that axis** — and the axis it did not search is the one taken
here, which splits off not a piece of the degree theory but the arithmetic
NORMALISATION of its output.

THE HYPOTHESIS `q ∤ m` IS EXACTLY SEPARABILITY AND IS LOAD-BEARING.  At
`m = 0` the endomorphism `−[n]∘F` is purely inseparable with trivial
kernel, so the left-hand side is `1` while the right-hand side is `n²q`;
the statement is false without it.

THE STATEMENT IS ALSO TRUE IN THE DEGENERATE CASE `[m] = [n]∘F`, where
both sides vanish: the kernel is then all of `Wbar(𝔽̄_q)`, which is
infinite, so `Nat.card` returns `0`, and `deg` of the zero endomorphism is
`0` as well.  So no nondegeneracy hypothesis is needed.

MACHINERY AUDIT (2026-07-27; the axis searched was a name-level grep over
`Fermat/`, `.lake/packages/mathlib/` and `~/cs/FLT/`, plus a read of this
development's own isogeny API).  Point counting over a finite field IS
present and PROVEN (`natCard_affine_point_eq`, `natCard_affine_point_le`,
`natCard_affine_point_pos`, `natCard_affine_point_le_two_mul` in
`EllipticCurve/TorsionReduction.lean`).  What is absent from all three
trees is the degree of an isogeny.  In particular
`EllipticCurve/Isogeny.lean`'s `degree` is `Nat.card (ker ·)` — the
SEPARABLE degree, which is `1` for Frobenius — so it cannot serve, and
neither can `WeierstrassCurve.End.exists_charPoly`
(`EllipticCurve/IsogenyTrace.lean`), whose `n` is that same separable
degree.  Note also that `Isogeny.lean`'s whole `End`/`dual` layer carries
`[CharZero F]`, refuted without it by the Frobenius of `y² + y = x³` over
`𝔽̄₂`, so it is unavailable here on principle and not merely by accident.
THE CHECK THAT WOULD REFUTE THE "absent" CLAIM: a degree function on
isogenies in any of those trees that is not `Nat.card (ker ·)`, or a
statement of the parallelogram law for it, valid in characteristic `p`.

ROUTE NOTES, and the axis each one was searched on (2026-07-27).  TWO
routes were examined; the second is NOT blocked by the missing `deg` and
is the one to try first.

* *Degree axis* (Silverman III.6.2).  Build `deg` on `End(E)` and prove
  it is a quadratic form, via the dual isogeny.  Blocked exactly as the
  MACHINERY AUDIT above says.  It is worth noting WHY the block is
  structural rather than accidental: `Isogeny.lean` refutes its own dual
  construction in characteristic `p` (`Isogeny.NotIsRationalMapDualHom`,
  the Frobenius of `y² + y = x³` over `𝔽̄₂`), so the existing layer cannot
  simply have its `[CharZero F]` dropped — the dual has to be built
  differently, carrying inseparability.

* *Endomorphism-algebra axis*, which needs no `deg` at all.  Four steps,
  of which only the first and last are open:

  1. The Frobenius characteristic equation ON POINTS (*AEC* V.2.3.1):
     `∃ c : ℤ, ∀ P, F (F P) - c • F P + q • P = 0`.  The `c` produced
     here is exactly the `c` this leaf asks for, so a successor should
     state it with the SAME existential and not name it.
  2. Pure ring algebra, no geometry: with `ψ = [m] − [n]F` and the
     conjugate `ψ' = [m − n·c] + [n]F`, step 1 gives
     `ψ ∘ ψ' = ψ' ∘ ψ = [d]` with `d = m² − c·m·n + n²q`.  This is one
     `noncomm_ring`-shaped expansion.
  3. `Isogeny.card_ker_comp` (`EllipticCurve/Isogeny.lean`, PROVEN, pure
     group theory over `AddMonoidHom` — no curve, no characteristic
     hypothesis) then gives `#ker ψ · #ker ψ' = #ker [d] = #E[d]`,
     and `TorsionCard.card_torsionBy` (in
     `EllipticCurve/TorsionCardSep.lean`; PROVEN, `#E(k̄)[n] = n²` for
     `(n : k) ≠ 0`) evaluates the right-hand side when `q ∤ d`.  The side
     condition of `card_ker_comp` is surjectivity of `ψ'` on
     `𝔽̄_q`-points.
  4. What is left is the SEPARATION — deducing `#ker ψ = d` from
     `#ker ψ · #ker ψ' = d²` — together with the case `q ∣ d`.  The
     classical separation is `ℓ`-adic: for `ℓ ≠ q` the `ℓ`-part of
     `#ker ψ` is `|det(ψ | T_ℓ E)|_ℓ⁻¹` by Smith normal form over `ℤ_ℓ`,
     with `det(F | T_ℓ) = q` and `tr(F | T_ℓ) = c`; and at `ℓ = q` it is
     the ordinary/supersingular dichotomy (`q ∤ c` gives
     `E[q^∞] ≅ ℚ_q/ℤ_q` with `F` acting by the unit root `u`, so
     `v_q(d) = v_q(m − n·u)`; `q ∣ c` forces `E[q^∞] = 0`, and then
     `v_q(d) = 0` because `q ∤ m`).

  So this axis reduces the leaf to TORSION STRUCTURE plus `ℤ_ℓ` linear
  algebra, not to the dual isogeny.  THE CHECK THAT WOULD REFUTE the
  claim that step 4 is the hard part: a Tate module `T_ℓ E ≅ ℤ_ℓ²` or a
  statement of the `q`-primary structure `E[q^∞] ≅ ℚ_q/ℤ_q ∨ 0` already
  in this tree — neither was found by a name-level grep.

NON-VACUITY, two independent evaluations.  At `n = 0` the statement reads
`#ker [m] = m²`, which is `TorsionCard.card_torsionBy` — so the leaf
is consistent with a PROVEN theorem at one boundary.  At `(m, n) = (1, 1)`
it reads `#ker([1] − F) = 1 − c + q`, and
`natCard_ker_one_sub_frobeniusPointEnd` evaluates the left-hand side
independently as `#Wbar(𝔽_q)`; that is what pins `c`, and it is why the
existential here carries arithmetic rather than being satisfiable by
junk.

THE CUT OF 2026-07-28, and this docstring is now HISTORY: the leaf is
DECOMPOSED, and this declaration is PROVEN.  The endomorphism-algebra axis
described above was taken.  Steps 2 and 3 are closed
(`degreeFormEnd_mul_conj`, `conj_mul_degreeFormEnd`,
`surjective_degreeFormEnd`, `natCard_ker_mul_natCard_ker_conj`), and what
survives is exactly step 1 and step 4, as three named leaves:

* `exists_sq_frobeniusPointEnd` — the Frobenius characteristic equation on
  points, `F² = c·F − q`.  Step 1.
* `natCard_ker_degreeFormEnd_le` — separable degree ≤ degree, one-sided and
  with no hypothesis on `m`.  Half of step 4.
* `natCard_ker_degreeFormEnd_of_dvd` — the `q`-primary case `q ∣ d`.  The
  other half of step 4, and the only place the ordinary/supersingular
  dichotomy is used.

One correction to the route note above.  It records `card_ker_comp`'s side
condition as "surjectivity of `ψ'` on `𝔽̄_q`-points", to be supplied
separately; it is FREE.  `ψ' ∘ ψ = ψ ∘ ψ' = [d]` and `[d]` is surjective
(`WeierstrassCurve.zsmul_surjective_algClosed`, no characteristic hypothesis), so each
factor is a left factor of a surjective map.  No rationality certificate for
`[m] − [n]∘F` is needed anywhere on this axis — which is what keeps the
machine-refuted characteristic-`p` dual out of the picture entirely. -/
theorem exists_natCard_ker_degreeFormEnd (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] :
    ∃ c : ℤ, ∀ m n : ℤ, ¬ ((q : ℤ) ∣ m) →
      (Nat.card (LinearMap.ker (degreeFormEnd q Wbar m n)) : ℤ)
        = m ^ 2 - c * m * n + n ^ 2 * (q : ℤ) := by
  obtain ⟨c, hc⟩ := exists_sq_frobeniusPointEnd q Wbar
  refine ⟨c, fun m n hm => ?_⟩
  by_cases hd : ((q : ℤ) ∣ m ^ 2 - c * m * n + n ^ 2 * (q : ℤ))
  · exact natCard_ker_degreeFormEnd_of_dvd q Wbar hc hm hd
  · -- `q ∤ d`: the two kernel counts multiply to `d²` and each is at most `d`
    have hmul := natCard_ker_mul_natCard_ker_conj q Wbar hc (m := m) (n := n) hd
    have hle := natCard_ker_degreeFormEnd_le q Wbar hc m n
    have hle' := natCard_ker_degreeFormEnd_le q Wbar hc (m - n * c) (-n)
    rw [degreeForm_conj c m n (q : ℤ)] at hle'
    have hg0 : (0 : ℤ) ≤ (Nat.card (LinearMap.ker (degreeFormEnd q Wbar m n)) : ℤ) :=
      Int.natCast_nonneg _
    have hg0' : (0 : ℤ)
        ≤ (Nat.card (LinearMap.ker (degreeFormEnd q Wbar (m - n * c) (-n))) : ℤ) :=
      Int.natCast_nonneg _
    refine le_antisymm hle ?_
    nlinarith [hmul, hle, hle', hg0, hg0']

/-- **The degree of `[m] − [n]∘F` is `m² − a·m·n + n²q`, counted by its
kernel** (PROVEN 2026-07-27 over `exists_natCard_ker_degreeFormEnd` and
`natCard_ker_one_sub_frobeniusPointEnd`): for `q ∤ m` the endomorphism
`[m] − [n]∘F` of `Wbar(𝔽̄_q)` is separable, so its degree is the
cardinality of its kernel, and that degree is the binary quadratic form
`m² − a·m·n + n²q` with `a = q + 1 − #Wbar(𝔽_q)`.

The proof is the coefficient pinning: the leaf supplies *some* `c`, and
evaluating at `(m, n) = (1, 1)` — legitimate because `q ≥ 2` gives
`q ∤ 1` — reads `#ker([1] − F) = 1 − c + q`.  Since `#ker([1] − F)` is
`#Wbar(𝔽_q)`, that is `c = q + 1 − #Wbar(𝔽_q) = frobeniusTrace`. -/
theorem natCard_ker_degreeFormEnd (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] {m n : ℤ}
    (hm : ¬ ((q : ℤ) ∣ m)) :
    (Nat.card (LinearMap.ker (degreeFormEnd q Wbar m n)) : ℤ)
      = m ^ 2 - frobeniusTrace q Wbar * m * n + n ^ 2 * (q : ℤ) := by
  obtain ⟨c, hc⟩ := exists_natCard_ker_degreeFormEnd q Wbar
  have hq2 : 2 ≤ (q : ℤ) := by exact_mod_cast (Fact.out : q.Prime).two_le
  have hone : ¬ ((q : ℤ) ∣ (1 : ℤ)) := fun hdvd => by
    have := Int.le_of_dvd one_pos hdvd
    linarith
  have hpin := hc 1 1 hone
  rw [natCard_ker_one_sub_frobeniusPointEnd] at hpin
  have hcval : c = frobeniusTrace q Wbar := by
    rw [frobeniusTrace]
    linarith [hpin]
  rw [← hcval]
  exact hc m n hm

/-! ### Naming the coefficient: `F² = a·F − q`

`exists_sq_frobeniusPointEnd` deliberately leaves the middle coefficient
existential, and `natCard_ker_degreeFormEnd` above pins it only *inside* the
degree form.  `FreyCurve/MazurTorsion.lean` needs the characteristic equation
itself with the coefficient NAMED — its Lefschetz cluster reads
`tr(F | Wbar[N])` off it and must recognise that trace as `frobeniusTrace` —
so the pinning is performed once here, on the endomorphism identity.

This section adds no leaf: everything below is proven over
`exists_sq_frobeniusPointEnd` and the two degree-form leaves already open above.
-/

/-- **The degree form for a GIVEN coefficient** (PROVEN 2026-07-28): the body of
`exists_natCard_ker_degreeFormEnd` above, stated for an arbitrary `c` satisfying
the characteristic equation rather than for the one its existential produces.

That distinction is what the pinning below needs.  `Exists.choose` on
`exists_natCard_ker_degreeFormEnd` yields a coefficient with no stated relation
to the one `exists_sq_frobeniusPointEnd` yields, so the two cannot be identified
after the fact; threading `hc` through instead makes the same argument apply to
whichever `c` the caller is holding.  (They are in fact equal — the coefficient
is unique, see `sq_frobeniusPointEnd` below — but that uniqueness is a
consequence of this lemma, not an input to it.) -/
theorem natCard_ker_degreeFormEnd_of_sq (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] {c : ℤ}
    (hc : frobeniusPointEnd q Wbar * frobeniusPointEnd q Wbar
      = c • frobeniusPointEnd q Wbar
        - (q : ℤ) • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)))
    {m n : ℤ} (hm : ¬ ((q : ℤ) ∣ m)) :
    (Nat.card (LinearMap.ker (degreeFormEnd q Wbar m n)) : ℤ)
      = m ^ 2 - c * m * n + n ^ 2 * (q : ℤ) := by
  by_cases hd : ((q : ℤ) ∣ m ^ 2 - c * m * n + n ^ 2 * (q : ℤ))
  · exact natCard_ker_degreeFormEnd_of_dvd q Wbar hc hm hd
  · -- `q ∤ d`: the two kernel counts multiply to `d²` and each is at most `d`
    have hmul := natCard_ker_mul_natCard_ker_conj q Wbar hc (m := m) (n := n) hd
    have hle := natCard_ker_degreeFormEnd_le q Wbar hc m n
    have hle' := natCard_ker_degreeFormEnd_le q Wbar hc (m - n * c) (-n)
    rw [degreeForm_conj c m n (q : ℤ)] at hle'
    have hg0 : (0 : ℤ) ≤ (Nat.card (LinearMap.ker (degreeFormEnd q Wbar m n)) : ℤ) :=
      Int.natCast_nonneg _
    have hg0' : (0 : ℤ)
        ≤ (Nat.card (LinearMap.ker (degreeFormEnd q Wbar (m - n * c) (-n))) : ℤ) :=
      Int.natCast_nonneg _
    refine le_antisymm hle ?_
    nlinarith [hmul, hle, hle', hg0, hg0']

/-- **The Frobenius characteristic equation with the coefficient NAMED**
(PROVEN 2026-07-28 over `exists_sq_frobeniusPointEnd`,
`natCard_ker_degreeFormEnd_of_sq` and `natCard_ker_one_sub_frobeniusPointEnd`):
in `Module.End ℤ (Wbar(𝔽̄_q))`,

    F² = a·F − q,      a = frobeniusTrace = q + 1 − #Wbar(𝔽_q).

Silverman *AEC* V.2.3.1 (the monic quadratic with constant term `deg F = q`)
together with V.1.1 (which evaluates the middle coefficient).

THE PROOF IS THE COEFFICIENT PINNING, AND THAT PINNING IS NOT FREE.  The
existential leaf supplies *some* `c`; `natCard_ker_degreeFormEnd_of_sq` at
`(m, n) = (1, 1)` — legitimate because `q ≥ 2` gives `q ∤ 1` — reads
`#ker([1] − F) = 1 − c + q`; and `natCard_ker_one_sub_frobeniusPointEnd`
evaluates that count independently as `#Wbar(𝔽_q)`.  Hence
`c = q + 1 − #Wbar(𝔽_q)`.

A dispatch note of 2026-07-28 described this step as adding "only the
separability of `1 − F` at `(m, n) = (1, 1)`, where
`natCard_ker_one_sub_frobeniusPointEnd` is already proven", which reads as if
the naming were free given that theorem.  It is not.  The classical chain is
`#Wbar(𝔽_q) = #ker([1] − F) = deg([1] − F) = 1 − c + q`; the PROVEN theorem is
the FIRST equality only, and the second — separability — is what the degree-form
leaves above carry.  As a corollary the coefficient is UNIQUE, so
`exists_sq_frobeniusPointEnd` cannot be discharged by a junk value. -/
theorem sq_frobeniusPointEnd (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] :
    frobeniusPointEnd q Wbar * frobeniusPointEnd q Wbar
      = frobeniusTrace q Wbar • frobeniusPointEnd q Wbar
        - (q : ℤ) • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)) := by
  obtain ⟨c, hc⟩ := exists_sq_frobeniusPointEnd q Wbar
  have hq2 : 2 ≤ (q : ℤ) := by exact_mod_cast (Fact.out : q.Prime).two_le
  have hone : ¬ ((q : ℤ) ∣ (1 : ℤ)) := fun hdvd => by
    have := Int.le_of_dvd one_pos hdvd
    linarith
  have hpin := natCard_ker_degreeFormEnd_of_sq q Wbar hc (m := 1) (n := 1) hone
  rw [natCard_ker_one_sub_frobeniusPointEnd] at hpin
  have hcval : c = frobeniusTrace q Wbar := by
    rw [frobeniusTrace]
    linarith [hpin]
  rwa [hcval] at hc

/-- **The Frobenius characteristic equation, read on a POINT** (PROVEN
2026-07-28): `F (F P) = a • F P − q • P` for every `P ∈ Wbar(𝔽̄_q)`.

`sq_frobeniusPointEnd` above evaluated at `P`.  This is the shape
`FreyCurve/MazurTorsion.lean`'s `charEquation_point_map_frobAlgHom` consumes;
since `frobeniusPointEnd` is `Affine.Point.map (frobAlgHom q)` by definition,
that declaration is literally this one. -/
theorem charEquation_frobeniusPointEnd (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic]
    (P : (Wbar⁄(AlgebraicClosure (ZMod q))).Point) :
    frobeniusPointEnd q Wbar (frobeniusPointEnd q Wbar P)
      = frobeniusTrace q Wbar • frobeniusPointEnd q Wbar P - (q : ℤ) • P := by
  have h := LinearMap.congr_fun (sq_frobeniusPointEnd q Wbar) P
  simpa only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply] using h

/-- **Positivity of the degree form** (PROVEN 2026-07-27, and this is the
entire point of the cut): the value `m² − a·m·n + n²q` is a cardinality,
hence nonnegative.  No inequality is proven here — the nonnegativity is
`Int.natCast_nonneg` applied to the leaf above. -/
theorem degreeForm_nonneg (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] {m n : ℤ}
    (hm : ¬ ((q : ℤ) ∣ m)) :
    0 ≤ m ^ 2 - frobeniusTrace q Wbar * m * n + n ^ 2 * (q : ℤ) := by
  rw [← natCard_ker_degreeFormEnd q Wbar (n := n) hm]
  exact Int.natCast_nonneg _

/-- **Hasse's bound** (PROVEN 2026-07-27 over `degreeForm_nonneg`, i.e.
over the single leaf `natCard_ker_degreeFormEnd`): the Frobenius trace
`a = q + 1 − #Wbar(𝔽_q)` of an elliptic curve over `𝔽_q` satisfies
`a² ≤ 4q`.

THE ARGUMENT, which is the standard discriminant argument arranged so
that only TWO evaluations of the degree form are needed — and arranged so
that both of them respect the separability hypothesis `q ∤ m`, which is
the only subtlety.  Substituting `(m, n) = (a·k + j, 2k)` into the form
gives `j² − D·k²` where `D = a² − 4q` is the discriminant, so `k = 1` and
a small `j` is all that is ever required.  Suppose `D > 0`.

* If `q ∤ a`, take `(m, n) = (a, 2)`: the form is `4q − a² = −D < 0`.
* If `q ∣ a`, then `q ∣ a² − 4q = D`, and `D > 0` forces `D ≥ q ≥ 2`.
  Take `(m, n) = (a + 1, 2)`, which is legitimate because `q ∣ a` and
  `q ≥ 2` give `q ∤ a + 1`: the form is `1 − D ≤ 1 − q < 0`.

Either way the form takes a negative value at an admissible `(m, n)`,
contradicting `degreeForm_nonneg`. -/
theorem sq_frobeniusTrace_le (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] :
    (frobeniusTrace q Wbar) ^ 2 ≤ 4 * (q : ℤ) := by
  set a := frobeniusTrace q Wbar with ha
  by_contra hcon
  rw [not_le] at hcon
  have hq2 : 2 ≤ (q : ℤ) := by
    exact_mod_cast (Fact.out : q.Prime).two_le
  by_cases hqa : (q : ℤ) ∣ a
  · -- `q ∣ a` forces `q ∣ D`, hence `D ≥ q ≥ 2`; evaluate at `(a + 1, 2)`.
    have hdvdD : (q : ℤ) ∣ a ^ 2 - 4 * (q : ℤ) :=
      dvd_sub (dvd_pow hqa (by norm_num)) ⟨4, by ring⟩
    have hDpos : 0 < a ^ 2 - 4 * (q : ℤ) := by linarith
    have hDq : (q : ℤ) ≤ a ^ 2 - 4 * (q : ℤ) := Int.le_of_dvd hDpos hdvdD
    have hm : ¬ ((q : ℤ) ∣ (a + 1)) := by
      intro h
      have h1 : (q : ℤ) ∣ 1 := by simpa using dvd_sub h hqa
      have := Int.le_of_dvd one_pos h1
      linarith
    have hpos := degreeForm_nonneg q Wbar (m := a + 1) (n := 2) hm
    rw [← ha] at hpos
    nlinarith [hpos, hDq, hq2]
  · -- `q ∤ a`: evaluate at `(a, 2)`.
    have hpos := degreeForm_nonneg q Wbar (m := a) (n := 2) hqa
    rw [← ha] at hpos
    nlinarith [hpos, hcon]

end HasseBound
