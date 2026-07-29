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

FOURTH CUT, 2026-07-28: `natCard_ker_degreeFormEnd_of_dvd` — the `q`-primary
case — is PROVEN, over ONE new leaf that is the ordinary `q`-torsion count
`natCard_torsionBy_q` (`#E[q] = q` for `q ∤ c`).  That is precisely the
collapse its own route note predicted, and the note over-asked in two places:
no `#E[q^∞]` structure theorem is needed (`natCard_torsionBy_mul` splits one
`q` off any torsion count with no coprimality hypothesis), and no induction
over repeated peels is needed (the conjugate of the once-peeled endomorphism
already has first coordinate `n`, and `q ∤ n` is in hand).  The degenerate
value `d = 0`, which `hc` alone does not exclude, is absorbed by
`natCard_ker_degreeFormEnd_le` rather than by a new leaf.

The `q ∤ d` branch, which the two consumers carried inline and identically, is
hoisted to `natCard_ker_degreeFormEnd_of_not_dvd`; it is where the `q`-primary
induction bottoms out.

The leaf COUNT is unchanged at three — this is a substitution, not a
subtraction, and saying otherwise would misreport the frontier.  What changed
is which three:

* `exists_sq_frobeniusPointEnd` — the Frobenius characteristic equation on
  points, `F² = c·F − q`.  Unchanged.
* `natCard_ker_degreeFormEnd_le` — separable degree ≤ degree, one-sided, no
  hypothesis on `m`.  Unchanged, and see its docstring for why every
  decomposition of it must contain an archimedean piece.
* `natCard_torsionBy_q` — `#E[q] = q` for `q ∤ c`, REPLACING
  `natCard_ker_degreeFormEnd_of_dvd`.  A single cardinality of a single
  torsion subgroup, in place of an identity quantified over all `(m, n)`.

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
is sharp exactly where it is used and carries the arithmetic.

MACHINERY CORRECTION, 2026-07-28 — a claim recorded twice in this file is
STALE.  `exists_sq_frobeniusPointEnd`'s route note says a Tate module
`T_ℓ E ≅ ℤ_ℓ²`, or the rank-`2` structure of the torsion, "was not found by a
name-level grep", and `exists_natCard_ker_degreeFormEnd`'s (now historical)
docstring says the same.  The RANK-`2` STRUCTURE IS IN THE TREE:
`WeierstrassCurve.n_torsion_dimension` (`EllipticCurve/Torsion.lean`) gives
`E.nTorsion N ≃+ ZMod N × ZMod N` for `(N : k) ≠ 0` over a SEPARABLY CLOSED
field, with NO characteristic-zero hypothesis — and `AlgebraicClosure (ZMod q)`
is separably closed, so it applies here for every `N` with `q ∤ N`.
`WeierstrassCurve.p_torsion_rank` is its rank form and is already consumed
elsewhere in this development.  What is genuinely absent is the `ℓ`-ADIC LIMIT
(the Tate module itself) and the determinant of an endomorphism on it; the
finite-level structure is not.

WHAT THAT BUYS, AND WHERE IT STOPS.  With `E[N] ≅ (ZMod N)²` one can restrict
`ψ` and `ψ'` to `E[|d|]`, where `ψ' = adj ψ` (because `ψ + ψ' = [2m − n·c]` is
the trace and `ψ ∘ ψ' = [d]` the determinant), and Smith normal form over
`ℤ_ℓ` then gives the `ℓ`-part of `#ker ψ` as `ℓ^{v_ℓ(d)}` for every `ℓ ≠ q`,
hence `#ker ψ = |d|` up to its `q`-part.  That is the whole `p`-adic content of
this leaf and it is reachable.  It does NOT give the leaf, because `≤ |d|` is
not `≤ d`.

THE ARCHIMEDEAN OBSTRUCTION, and it is why this leaf should NOT be split.  The
conclusion `#ker ψ = d` of the consumers forces `0 ≤ d`, i.e. `c² ≤ 4q`, i.e.
Hasse's bound; and `0 ≤ d` is invisible to every `p`-adic argument, since a
determinant over `ℤ_ℓ` has no sign.  So ANY decomposition of this leaf
contains a sub-leaf equivalent to Hasse's bound.  Splitting it into
`0 ≤ m² − c·m·n + n²q` plus `#ker ψ ≤ |d|` is therefore a faithful
decomposition and a TRACTABILITY REGRESSION: the first half is exactly the
inert positivity statement that the 2026-07-27 audit rejected as a cut of
Hasse's bound (a binary quadratic form with leading coefficient `1` is
positive semidefinite iff its discriminant is `≤ 0`, so it IS the bound), and
it would arrive stripped of the geometric meaning that makes the present
statement provable.  Classically the sign comes from `deg` being the degree of
a MORPHISM, i.e. from geometry, not from linear algebra — which is why this
leaf is stated as the classical theorem and left whole.

THE CHECK THAT WOULD REFUTE the "must contain an archimedean piece" claim: a
proof of `0 ≤ m² − c·m·n + n²q` from `hc` and the finite-level torsion
structure alone.  Note `hc` really does pin `c` (if `c` and `c'` both satisfy
it then `(c − c') • F = 0`, and `F` is surjective onto an infinite group, so
`c = c'`), so `c` is the true Frobenius trace and the statement is TRUE; the
question is only whether its sign is derivable without geometric input. -/
theorem natCard_ker_degreeFormEnd_le (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] {c : ℤ}
    (hc : frobeniusPointEnd q Wbar * frobeniusPointEnd q Wbar
      = c • frobeniusPointEnd q Wbar
        - (q : ℤ) • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)))
    (m n : ℤ) :
    (Nat.card (LinearMap.ker (degreeFormEnd q Wbar m n)) : ℤ)
      ≤ m ^ 2 - c * m * n + n ^ 2 * (q : ℤ) :=
  sorry

/-- **The `q ∤ d` case of the degree form** (PROVEN over
`natCard_ker_degreeFormEnd_le`): two applications of the one-sided bound, to
`ψ` and to its conjugate, together with `#ker ψ · #ker ψ' = d²`, pin `#ker ψ`
to `d`.

This is the body that `exists_natCard_ker_degreeFormEnd` and
`natCard_ker_degreeFormEnd_of_sq` each carried inline and identically before
2026-07-28.  It is hoisted because `natCard_ker_degreeFormEnd_of_dvd` needs it
as the BASE CASE of its induction: the `q`-primary argument peels Frobenius
factors until it reaches an endomorphism whose degree form is prime to `q`, and
that is where this lemma is consumed.  Note it needs no hypothesis on `m` —
the one-sided bound has none either. -/
theorem natCard_ker_degreeFormEnd_of_not_dvd (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] {c : ℤ}
    (hc : frobeniusPointEnd q Wbar * frobeniusPointEnd q Wbar
      = c • frobeniusPointEnd q Wbar
        - (q : ℤ) • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)))
    {m n : ℤ} (hd : ¬ ((q : ℤ) ∣ m ^ 2 - c * m * n + n ^ 2 * (q : ℤ))) :
    (Nat.card (LinearMap.ker (degreeFormEnd q Wbar m n)) : ℤ)
      = m ^ 2 - c * m * n + n ^ 2 * (q : ℤ) := by
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

/-! ### Peeling Frobenius, and the `q`-primary torsion count

The `q`-primary case `q ∣ d` is out of reach of `natCard_ker_mul_natCard_ker_conj`,
whose evaluation of `#E[d]` needs `q ∤ d`.  What replaces it is the observation
that `F` is BIJECTIVE on `Wbar(𝔽̄_q)` — `x ↦ x^q` is injective on a field and
`𝔽̄_q` is algebraically closed — so an endomorphism whose first coordinate is
divisible by `q` factors as `F ∘ β` with the same kernel and a degree form
smaller by a factor `q`.  Four proven statements and ONE leaf carry this.
-/

/-- **The `q`-power Frobenius is injective on points** (PROVEN): it is
`Affine.Point.map` of a field homomorphism, and `Point.map_injective` needs no
hypothesis beyond that. -/
theorem injective_frobeniusPointEnd (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) :
    Function.Injective (frobeniusPointEnd q Wbar) :=
  WeierstrassCurve.Affine.Point.map_injective (W' := Wbar)
    (f := WeilPairing.frobAlgHom q)

/-- **Peeling `F` off a composite does not change the kernel** (PROVEN from
injectivity).  This is what makes the `q`-primary induction cheap: no
`card_ker_comp`, hence no surjectivity side condition, is needed on this step. -/
theorem ker_frobeniusPointEnd_mul (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q))
    (g : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)) :
    LinearMap.ker (frobeniusPointEnd q Wbar * g) = LinearMap.ker g := by
  ext P
  simp only [LinearMap.mem_ker, Module.End.mul_apply]
  refine ⟨fun h => injective_frobeniusPointEnd q Wbar (h.trans (map_zero _).symm), fun h => ?_⟩
  rw [h, map_zero]

/-- **`[q·M₀] − [n]∘F = F ∘ ([c·M₀ − n] − [M₀]∘F)`** (PROVEN, pure ring algebra
in `ℤ[F]` over the characteristic equation): an endomorphism whose FIRST
coordinate is divisible by `q` has a Frobenius factored out of it on the left.

The identity behind it is `F ∘ ([c] − F) = [q]`, i.e. the characteristic
equation read as a factorisation of `[q]`.  Its arithmetic shadow is
`(q·M₀)² − c(q·M₀)n + n²q = q·((c·M₀ − n)² − c(c·M₀ − n)M₀ + M₀²q)`, i.e. the
degree form drops by exactly one factor of `q`; that is checked by `ring` where
it is used. -/
theorem degreeFormEnd_q_mul (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) {c : ℤ}
    (hc : frobeniusPointEnd q Wbar * frobeniusPointEnd q Wbar
      = c • frobeniusPointEnd q Wbar
        - (q : ℤ) • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)))
    (M₀ n : ℤ) :
    degreeFormEnd q Wbar ((q : ℤ) * M₀) n
      = frobeniusPointEnd q Wbar * degreeFormEnd q Wbar (c * M₀ - n) M₀ := by
  simp only [degreeFormEnd, mul_sub, mul_smul_comm, mul_one, hc, smul_sub, smul_smul]
  module

/-- **`#E[a·b] = #E[a] · #E[b]` for `b ≠ 0`** (PROVEN): `[a·b] = [a] ∘ [b]` and
`[b]` is surjective on the points over an algebraically closed field
(`zsmul_surjective_algClosed`), so `natCard_ker_mul` applies.

No coprimality is needed — this is not a CRT decomposition but the kernel
count of a composite — which is exactly why the `q`-primary argument below can
split off one `q` at a time without ever meeting a coprime-splitting lemma. -/
theorem natCard_torsionBy_mul (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] {a b : ℤ} (hb : b ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ (Wbar⁄(AlgebraicClosure (ZMod q))).Point (a * b))
      = Nat.card (Submodule.torsionBy ℤ (Wbar⁄(AlgebraicClosure (ZMod q))).Point a)
        * Nat.card (Submodule.torsionBy ℤ (Wbar⁄(AlgebraicClosure (ZMod q))).Point b) := by
  classical
  haveI : ((Wbar⁄(AlgebraicClosure (ZMod q))).toAffine).IsElliptic :=
    inferInstanceAs
      (Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).IsElliptic
  have hsurj : Function.Surjective
      (b • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point))) := by
    intro P
    obtain ⟨Q, hQ⟩ := _root_.WeierstrassCurve.zsmul_surjective_algClosed
      (Wbar⁄(AlgebraicClosure (ZMod q))).toAffine hb P
    exact ⟨Q, hQ⟩
  have key := natCard_ker_mul
    (a • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)))
    (b • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point))) hsurj
  have hmul : (a • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)))
      * (b • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)))
      = (a * b) • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)) := by
    rw [smul_mul_assoc, mul_smul_comm, mul_one, smul_smul]
  rw [hmul, ker_zsmul_one, ker_zsmul_one, ker_zsmul_one] at key
  exact key

/-- **`#E[N] = N²` for `q ∤ N`**, stated for an INTEGER `N` (PROVEN):
`TorsionCard.card_torsionBy` with the `natAbs` bridge, which
`natCard_ker_mul_natCard_ker_conj` performs inline and which is factored out
here because the `q`-primary induction needs it at a second place. -/
theorem natCard_torsionBy_of_not_dvd (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] {N : ℤ}
    (hN : ¬ ((q : ℤ) ∣ N)) :
    (Nat.card (Submodule.torsionBy ℤ (Wbar⁄(AlgebraicClosure (ZMod q))).Point N) : ℤ)
      = N ^ 2 := by
  classical
  have habs : Submodule.torsionBy ℤ (Wbar⁄(AlgebraicClosure (ZMod q))).Point N
      = Submodule.torsionBy ℤ (Wbar⁄(AlgebraicClosure (ZMod q))).Point (N.natAbs : ℤ) := by
    rcases Int.natAbs_eq N with h | h
    · rw [← h]
    · ext P
      simp only [Submodule.mem_torsionBy_iff]
      constructor
      · intro hP
        rw [h, neg_smul, neg_eq_zero] at hP
        exact hP
      · intro hP
        rw [h, neg_smul, hP, neg_zero]
  have hqdvd : ¬ (q ∣ N.natAbs) := by
    intro h
    exact hN (Int.natAbs_dvd_natAbs.mp (by simpa using h))
  haveI : CharP (AlgebraicClosure (ZMod q)) q :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))).injective q
  have hqd : ((N.natAbs : ℕ) : AlgebraicClosure (ZMod q)) ≠ 0 := by
    intro h0
    exact hqdvd ((CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod q)) q _).mp h0)
  have hcard : Nat.card (Submodule.torsionBy ℤ
      (Wbar⁄(AlgebraicClosure (ZMod q))).Point (N.natAbs : ℤ)) = N.natAbs ^ 2 :=
    TorsionCard.card_torsionBy
      (Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))) N.natAbs hqd
  rw [habs, hcard]
  push_cast
  exact sq_abs N

/-- **The `q`-torsion of an ORDINARY curve has exactly `q` points** (sorry leaf,
opened 2026-07-28): `#Wbar(𝔽̄_q)[q] = q` when `q ∤ c`.

THIS IS THE ONLY GEOMETRIC RESIDUE OF THE `q`-PRIMARY CASE, and it is the
statement the 2026-07-28 route note of `natCard_ker_degreeFormEnd_of_dvd`
predicted it would collapse to (it wrote it as `#ker([c] − F) = q`, which is
the same count: `F ∘ ([c] − F) = [q]` and `F` is injective, so
`ker([c] − F) = ker [q] = E[q]` — the two forms are interchangeable and this
one avoids naming `F` in the statement).

WHY `q ∤ c` IS LOAD-BEARING, and it is the ordinary/supersingular dichotomy in
its smallest form.  `q ∤ c` is exactly ordinarity, where `E[q] ≅ ℤ/q`; for a
SUPERSINGULAR curve (`q ∣ c`) one has `E[q] = 0` and the count is `1`, not `q`,
so the hypothesis cannot be dropped.  The leaf is never reached in the
supersingular case: `q ∣ c` together with `q ∤ m` gives `d ≡ m² ≢ 0 (mod q)`,
so `q ∣ d` fails and `natCard_ker_degreeFormEnd_of_not_dvd` handles it instead.
That derivation is performed in the consumer, so `q ∤ c` arrives there as a
theorem rather than as an assumption on the curve.

NON-VACUITY.  The count is neither `1` nor `q²`: `TorsionCard.card_torsionBy`
gives `#E[N] = N²` only for `(N : 𝔽̄_q) ≠ 0`, which fails at `N = q`, and the
`q`-torsion is where that theorem's hypothesis is exactly what breaks.  So this
leaf is the one value of the torsion count that the proven theory cannot see.

WHAT WOULD REFUTE THE REDUCTION: a proof of `natCard_ker_degreeFormEnd_of_dvd`
that never evaluates a `q`-primary torsion count.  The argument below reduces
`#E[d]` for `q ∣ d` to `#E[d/q] · #E[q]` through `natCard_torsionBy_mul`, so
`#E[q]` is consumed exactly once and nothing else about `q`-primary torsion is
used — in particular NO structure theorem for `E[q^∞]`, which the earlier route
note asked for and which is not needed. -/
theorem natCard_torsionBy_q (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] {c : ℤ}
    (hc : frobeniusPointEnd q Wbar * frobeniusPointEnd q Wbar
      = c • frobeniusPointEnd q Wbar
        - (q : ℤ) • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)))
    (hcq : ¬ ((q : ℤ) ∣ c)) :
    Nat.card (Submodule.torsionBy ℤ (Wbar⁄(AlgebraicClosure (ZMod q))).Point (q : ℤ)) = q :=
  sorry

/-- **Every `N`-torsion subgroup with `N ≠ 0` is finite and nonempty** (PROVEN
over `natCard_torsionBy_q`): strong induction on `|N|`, splitting off one
factor of `q` at a time through `natCard_torsionBy_mul` and bottoming out at
`natCard_torsionBy_of_not_dvd`.

`Nat.card` returns `0` on an infinite type, so this is what licenses the
cancellation at the end of `natCard_ker_degreeFormEnd_of_dvd`: without it a
product identity between cardinalities carries no information. -/
theorem natCard_torsionBy_pos (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] {c : ℤ}
    (hc : frobeniusPointEnd q Wbar * frobeniusPointEnd q Wbar
      = c • frobeniusPointEnd q Wbar
        - (q : ℤ) • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)))
    (hcq : ¬ ((q : ℤ) ∣ c)) :
    ∀ N : ℤ, N ≠ 0 →
      0 < Nat.card (Submodule.torsionBy ℤ (Wbar⁄(AlgebraicClosure (ZMod q))).Point N) := by
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  suffices H : ∀ k : ℕ, ∀ N : ℤ, N.natAbs = k → N ≠ 0 →
      0 < Nat.card (Submodule.torsionBy ℤ (Wbar⁄(AlgebraicClosure (ZMod q))).Point N) by
    intro N hN
    exact H N.natAbs N rfl hN
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro N hk hN
    by_cases hq : (q : ℤ) ∣ N
    · obtain ⟨N', rfl⟩ := hq
      have hN' : N' ≠ 0 := by
        rintro rfl
        exact hN (by ring)
      rw [natCard_torsionBy_mul q Wbar hN', natCard_torsionBy_q q Wbar hc hcq]
      have hlt : N'.natAbs < k := by
        subst hk
        rw [Int.natAbs_mul, Int.natAbs_natCast]
        have h1 : 0 < N'.natAbs := Int.natAbs_pos.mpr hN'
        nlinarith
      exact Nat.mul_pos (by omega) (ih _ hlt N' rfl hN')
    · have h := natCard_torsionBy_of_not_dvd q Wbar hq
      have hsq : (N : ℤ) ^ 2 ≠ 0 := pow_ne_zero _ hN
      rw [← h] at hsq
      exact Nat.pos_of_ne_zero (by exact_mod_cast hsq)

/-- **`#ker ψ · #ker ψ' = #E[d]` for `d ≠ 0`** (PROVEN): the same product as
`natCard_ker_mul_natCard_ker_conj`, but stopping at the torsion subgroup
instead of evaluating it.

The distinction is the whole point of the `q`-primary case: the evaluation
`#E[d] = d²` is what needs `q ∤ d`, while the product identity itself needs
only `d ≠ 0` (through the surjectivity of `ψ'`). -/
theorem natCard_ker_mul_conj_torsion (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] {c : ℤ}
    (hc : frobeniusPointEnd q Wbar * frobeniusPointEnd q Wbar
      = c • frobeniusPointEnd q Wbar
        - (q : ℤ) • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)))
    {m n : ℤ} (hd : m ^ 2 - c * m * n + n ^ 2 * (q : ℤ) ≠ 0) :
    Nat.card (LinearMap.ker (degreeFormEnd q Wbar m n))
        * Nat.card (LinearMap.ker (degreeFormEnd q Wbar (m - n * c) (-n)))
      = Nat.card (Submodule.torsionBy ℤ (Wbar⁄(AlgebraicClosure (ZMod q))).Point
          (m ^ 2 - c * m * n + n ^ 2 * (q : ℤ))) := by
  obtain ⟨-, hsurj'⟩ := surjective_degreeFormEnd q Wbar hc (m := m) (n := n) hd
  have hprod := natCard_ker_mul (degreeFormEnd q Wbar m n)
    (degreeFormEnd q Wbar (m - n * c) (-n)) hsurj'
  rw [degreeFormEnd_mul_conj q Wbar hc m n, ker_zsmul_one] at hprod
  exact hprod.symm

/-- **The `q`-primary case** (PROVEN 2026-07-28 over the single leaf
`natCard_torsionBy_q`; the second half of step 4): when `q ∤ m` but
`q ∣ d = m² − c·m·n + n²q`, the kernel count is still the value of the form.

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
`.lake/packages/mathlib/` and `~/cs/FLT` did not find.

THE PROOF ACTUALLY TAKEN (2026-07-28), and it is SHORTER than the route note
above: there is no peeling INDUCTION and no `#E[q^k]`, only ONE peel.

The route note proposed peeling `F` off `ψ'` repeatedly until the first
coordinate is prime to `q`, which is genuinely necessary — the peel can be
needed twice, e.g. `q = 5`, `c = 3`, `(m, n) = (18, 1)`, where `d = 275` and
`ψ' = ψ(15, −1)` peels to `ψ(10, 3)` and only then to `ψ(3, 2)`.  What removes
the induction over peels is that the CONJUGATE of the once-peeled `β` is
`ψ(n, −M₀)`, whose first coordinate is `n`, and `q ∤ n` is already known.  So
one peel plus one conjugation lands on an endomorphism to which the theorem
applies at a strictly smaller `|d|`, and a single strong induction on
`|m² − c·m·n + n²q|` closes it.  Concretely, with `M = m − n·c = q·M₀`:

* `#ker ψ · #ker ψ' = #E[d]`               (`natCard_ker_mul_conj_torsion`, `d ≠ 0`);
* `#ker ψ' = #ker β`, `β = ψ(c·M₀ + n, M₀)` (`degreeFormEnd_q_mul`, `F` injective);
* `#ker β · #ker ψ(n, −M₀) = #E[d/q]`       (the same product one level down);
* `#ker ψ(n, −M₀) = d/q`                    (induction, or the `q ∤ d` base case);
* `#E[d] = #E[d/q] · #E[q]`                 (`natCard_torsionBy_mul`, no coprimality);
* `#E[q] = q`                               (`natCard_torsionBy_q`, THE LEAF).

Cancelling `#ker β`, which is nonzero because `#E[d/q] > 0`
(`natCard_torsionBy_pos`), gives `#ker ψ = d`.

TWO CORRECTIONS TO THE ROUTE NOTE ABOVE, both found by carrying it out.
(i) The degenerate value `d = 0` is not excluded by `q ∤ m` and is not
formally excluded by `hc` either — `hc` alone does not know that `c² < 4q` —
but it needs no new leaf: `natCard_ker_degreeFormEnd_le` bounds a cardinality
by `0`, and a cardinality is nonnegative, so the count is `0` and the identity
holds.  (ii) The `#E[q^∞]` structure theorem the note asked for is NOT needed;
`natCard_torsionBy_mul` splits one factor of `q` off any torsion count with no
coprimality hypothesis, so only the single value `#E[q]` is ever consumed. -/
theorem natCard_ker_degreeFormEnd_of_dvd (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] {c : ℤ}
    (hc : frobeniusPointEnd q Wbar * frobeniusPointEnd q Wbar
      = c • frobeniusPointEnd q Wbar
        - (q : ℤ) • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)))
    {m n : ℤ} (hm : ¬ ((q : ℤ) ∣ m))
    (hd : (q : ℤ) ∣ m ^ 2 - c * m * n + n ^ 2 * (q : ℤ)) :
    (Nat.card (LinearMap.ker (degreeFormEnd q Wbar m n)) : ℤ)
      = m ^ 2 - c * m * n + n ^ 2 * (q : ℤ) := by
  have hqprime : q.Prime := Fact.out
  have hqZ : Prime (q : ℤ) :=
    Int.prime_iff_natAbs_prime.mpr (by simpa using hqprime)
  suffices H : ∀ k : ℕ, ∀ m n : ℤ,
      (m ^ 2 - c * m * n + n ^ 2 * (q : ℤ)).natAbs = k →
      ¬ ((q : ℤ) ∣ m) → (q : ℤ) ∣ (m ^ 2 - c * m * n + n ^ 2 * (q : ℤ)) →
      (Nat.card (LinearMap.ker (degreeFormEnd q Wbar m n)) : ℤ)
        = m ^ 2 - c * m * n + n ^ 2 * (q : ℤ) by
    exact H _ m n rfl hm hd
  clear hm hd
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro m n hk hm hd
  -- the degenerate value `d = 0` is pinned by the one-sided bound alone
  rcases eq_or_ne (m ^ 2 - c * m * n + n ^ 2 * (q : ℤ)) 0 with hd0 | hd0
  · have hle := natCard_ker_degreeFormEnd_le q Wbar hc m n
    have hg0 : (0 : ℤ) ≤ (Nat.card (LinearMap.ker (degreeFormEnd q Wbar m n)) : ℤ) :=
      Int.natCast_nonneg _
    rw [hd0] at hle ⊢
    omega
  -- `q ∤ m` together with `q ∣ d` forces `q ∤ c` and `q ∤ n` — the ORDINARY case
  have hmcn : (q : ℤ) ∣ m - c * n := by
    have h1 : (q : ℤ) ∣ m * (m - c * n) := by
      obtain ⟨t, ht⟩ := hd
      exact ⟨t - n ^ 2, by linarith [ht]⟩
    rcases (hqZ.dvd_mul.mp h1) with h | h
    · exact absurd h hm
    · exact h
  have hnq : ¬ ((q : ℤ) ∣ n) := by
    intro h
    exact hm (by simpa using dvd_add hmcn (Dvd.dvd.mul_left h c))
  have hcq : ¬ ((q : ℤ) ∣ c) := by
    intro h
    exact hm (by simpa using dvd_add hmcn (Dvd.dvd.mul_right h n))
  -- the CONJUGATE has first coordinate divisible by `q`, so a Frobenius peels off it
  obtain ⟨M₀, hM₀⟩ : (q : ℤ) ∣ m - n * c := by
    rw [show m - n * c = m - c * n by ring]; exact hmcn
  set e : ℤ := n ^ 2 - c * n * (-M₀) + (-M₀) ^ 2 * (q : ℤ) with he
  have hqe : (q : ℤ) * e = m ^ 2 - c * m * n + n ^ 2 * (q : ℤ) := by
    have hm' : m = (q : ℤ) * M₀ + n * c := by linarith [hM₀]
    rw [he, hm']; ring
  have he0 : e ≠ 0 := by
    intro h
    rw [h, mul_zero] at hqe
    exact hd0 hqe.symm
  have hA := natCard_ker_mul_conj_torsion q Wbar hc (m := m) (n := n) hd0
  have hB : Nat.card (LinearMap.ker (degreeFormEnd q Wbar (m - n * c) (-n)))
      = Nat.card (LinearMap.ker (degreeFormEnd q Wbar (c * M₀ + n) M₀)) := by
    rw [hM₀, degreeFormEnd_q_mul q Wbar hc M₀ (-n), ker_frobeniusPointEnd_mul,
      show c * M₀ - -n = c * M₀ + n by ring]
  have hCe : (c * M₀ + n) ^ 2 - c * (c * M₀ + n) * M₀ + M₀ ^ 2 * (q : ℤ) = e := by
    rw [he]; ring
  have hC := natCard_ker_mul_conj_torsion q Wbar hc (m := c * M₀ + n) (n := M₀)
    (by rw [hCe]; exact he0)
  rw [hCe, show c * M₀ + n - M₀ * c = n by ring] at hC
  -- the conjugate of `β` is `ψ(n, −M₀)`, whose FIRST coordinate is prime to `q`;
  -- its degree form is `d/q`, so the induction descends
  have hD : (Nat.card (LinearMap.ker (degreeFormEnd q Wbar n (-M₀))) : ℤ) = e := by
    by_cases hqd : (q : ℤ) ∣ e
    · refine ih e.natAbs ?_ n (-M₀) rfl hnq ?_
      · rw [← hk, ← hqe, Int.natAbs_mul, Int.natAbs_natCast]
        have h1 : 0 < e.natAbs := Int.natAbs_pos.mpr he0
        have h2 : 2 ≤ q := hqprime.two_le
        nlinarith
      · rw [he] at hqd; exact hqd
    · have hnd := natCard_ker_degreeFormEnd_of_not_dvd q Wbar hc (m := n) (n := -M₀)
        (by rw [← he]; exact hqd)
      rw [hnd]
  -- `#E[d] = #E[e] · q`, and `#E[e] > 0`
  have hE : (Nat.card (Submodule.torsionBy ℤ (Wbar⁄(AlgebraicClosure (ZMod q))).Point
      (m ^ 2 - c * m * n + n ^ 2 * (q : ℤ))) : ℤ)
      = (Nat.card (Submodule.torsionBy ℤ (Wbar⁄(AlgebraicClosure (ZMod q))).Point e) : ℤ)
        * (q : ℤ) := by
    rw [← hqe, mul_comm ((q : ℤ)) e,
      natCard_torsionBy_mul q Wbar (a := e) (b := (q : ℤ)) (by exact_mod_cast hqprime.pos.ne'),
      natCard_torsionBy_q q Wbar hc hcq]
    push_cast
    ring
  have hF : 0 < Nat.card (Submodule.torsionBy ℤ
      (Wbar⁄(AlgebraicClosure (ZMod q))).Point e) :=
    natCard_torsionBy_pos q Wbar hc hcq e he0
  have hC' : (Nat.card (LinearMap.ker (degreeFormEnd q Wbar (c * M₀ + n) M₀)) : ℤ) * e
      = (Nat.card (Submodule.torsionBy ℤ (Wbar⁄(AlgebraicClosure (ZMod q))).Point e) : ℤ) := by
    have hC0 : (Nat.card (LinearMap.ker (degreeFormEnd q Wbar (c * M₀ + n) M₀)) : ℤ)
        * (Nat.card (LinearMap.ker (degreeFormEnd q Wbar n (-M₀))) : ℤ)
        = (Nat.card (Submodule.torsionBy ℤ (Wbar⁄(AlgebraicClosure (ZMod q))).Point e) : ℤ) := by
      exact_mod_cast hC
    rw [hD] at hC0
    exact hC0
  have hA' : (Nat.card (LinearMap.ker (degreeFormEnd q Wbar m n)) : ℤ)
      * (Nat.card (LinearMap.ker (degreeFormEnd q Wbar (c * M₀ + n) M₀)) : ℤ)
      = (Nat.card (Submodule.torsionBy ℤ (Wbar⁄(AlgebraicClosure (ZMod q))).Point
          (m ^ 2 - c * m * n + n ^ 2 * (q : ℤ))) : ℤ) := by
    rw [← hB]
    exact_mod_cast hA
  have hbne : (Nat.card (LinearMap.ker (degreeFormEnd q Wbar (c * M₀ + n) M₀)) : ℤ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hC'
    exact hF.ne' (by exact_mod_cast hC'.symm)
  have hfinal : (Nat.card (LinearMap.ker (degreeFormEnd q Wbar m n)) : ℤ)
      * (Nat.card (LinearMap.ker (degreeFormEnd q Wbar (c * M₀ + n) M₀)) : ℤ)
      = (m ^ 2 - c * m * n + n ^ 2 * (q : ℤ))
        * (Nat.card (LinearMap.ker (degreeFormEnd q Wbar (c * M₀ + n) M₀)) : ℤ) := by
    rw [hA', hE, ← hC', ← hqe]
    ring
  exact mul_right_cancel₀ hbne hfinal

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
  · exact natCard_ker_degreeFormEnd_of_not_dvd q Wbar hc hd

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
  · exact natCard_ker_degreeFormEnd_of_not_dvd q Wbar hc hd

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
