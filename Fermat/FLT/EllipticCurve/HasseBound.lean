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
-/
module

public import Fermat.FLT.EllipticCurve.WeilPairing

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

/-! ### The degree form -/

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
junk. -/
theorem exists_natCard_ker_degreeFormEnd (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] :
    ∃ c : ℤ, ∀ m n : ℤ, ¬ ((q : ℤ) ∣ m) →
      (Nat.card (LinearMap.ker (degreeFormEnd q Wbar m n)) : ℤ)
        = m ^ 2 - c * m * n + n ^ 2 * (q : ℤ) :=
  sorry

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
