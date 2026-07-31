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
case — is PROVEN, over the peeling machinery below (`F` is bijective;
`degreeFormEnd_peel`; `exists_natCard_ker_mul_pow`), and the reduction its
docstring proposed is carried out.  What that leaf bottoms out at is the
SINGLE ordinary `q`-torsion count `#ker([c] − F) = q` for `q ∤ c`, which is
its own `(m, n) = (c, 1)` instance, `natCard_ker_frobeniusConj`.

FIFTH CUT, 2026-07-29: `natCard_ker_frobeniusConj` is PROVEN, and what
survives of it is the pure EXISTENCE statement `exists_ne_zero_qTorsion` —
the curve has a nonzero `q`-torsion point when `q ∤ c`.  Two things changed,
and the first is a CORRECTION of the note above.

* The upper half `#E[q] ∣ q` was recorded as "already free" from
  `natCard_ker_degreeFormEnd_le` at `(c, 1)`.  It was not: that declaration is
  itself an open leaf, so the `q`-primary count was resting on it.  The upper
  half really is free, but from `TorsionCharP.exists_zsmul_eq_of_charP`
  (cyclicity of the `q`-torsion in characteristic `q`, PROVEN 2026-07-25 out
  of the vanishing of `ΨSqₚ′`), which is now imported.  So nothing `q`-primary
  depends on `natCard_ker_degreeFormEnd_le` any more.
* The dependency between `#E[q] = q` and `#ker([c] − F) = q` is REVERSED.
  `natCard_ker_zsmul_q` is now the primitive — that is where the upper bound
  is available — and `natCard_ker_frobeniusConj` is derived from it through
  `V ∘ F = [q]` with `#ker F = 1`.

The surviving leaf is not derivable from this module's algebra: see the model
in its docstring, in which every identity proven here holds and `A[q] = 0`.
Its docstring carries an elementary route (Deuring's congruence via character
sums, twice) whose cost is the missing `𝔽_{q^n}` point-counting
infrastructure rather than the argument.

SIXTH CUT, 2026-07-30, and it is two things: a BRICK and a HALF-LEAF.

* `F` is BIJECTIVE on `Wbar(𝔽̄_q)` — `bijective_frobeniusPointEnd` — and now
  UNCONDITIONALLY, i.e. with no `hc`.  Three declarations here had asked for
  this and the previous `surjective_frobeniusPointEnd` could not serve them:
  it derived surjectivity from `hc` (as a left factor of the surjective `[q]`),
  and the two characteristic-equation leaves are *upstream* of `hc` — they are
  what produces it.  The unconditional proof does not use the curve at all:
  `frobAlgHom q` is an AUTOMORPHISM of `𝔽̄_q` (injective as a field map,
  surjective because every element of an algebraically closed field has a
  `q`-th root), and `Point.map` along its inverse undoes `F`.
* The SUPERSINGULAR half of `sq_frobeniusPointEnd_qPrimary` is machine-checked.
  `E[q] = 0` forces `E[q^∞] = 0` (`eq_zero_of_qPow_zsmul_eq_zero`, induction on
  `k`), so the hypothesis `q^k • P = 0` forces `P = 0` and the conclusion is
  `hc` at `n = 1`.  What survives is `sq_frobeniusPointEnd_qPrimary_ordinary`,
  the same statement with the extra hypothesis that a nonzero `q`-torsion point
  exists — which is where the unit-root argument actually lives, and where
  `E[q^k]` becomes cyclic of order `q^k` so that `F` acts on it by a single
  unit `ε_k` and the leaf becomes the congruence `ε_k² − c·ε_k + q ≡ 0` — which
  the SEVENTH CUT below then carries out, so this is now history rather than a
  route note.

SEVENTH CUT, 2026-07-30: the ORDINARY `q`-primary structure theory is
machine-checked, and the surviving `q`-primary leaf is NO LONGER ABOUT POINTS.
From the bare existence of one nonzero `q`-torsion point:

* `natCard_ker_zsmul_q_of_ordinary` — `#E[q] = q`, and
  `natCard_ker_zsmul_q_pow_of_ordinary` — `#E[q^v] = q^v`.  These are the
  `hc`-free cores of `natCard_ker_zsmul_q` / `natCard_ker_zsmul_q_pow`, which are
  now one-line wrappers; the hypotheses `hc` and `q ∤ c` those carried were only
  ever used to produce the point, through `exists_ne_zero_qTorsion`.  Splitting
  them out is what makes the count available UPSTREAM of `hc`, where the
  characteristic-equation leaves live.
* `exists_addOrderOf_eq_qPow` — a point of order EXACTLY `q^(k+1)`, by dividing
  by `q` repeatedly.
* `exists_zsmul_eq_of_qPow_zsmul_eq_zero` — `E[q^k]` is CYCLIC, generated by any
  such point.  Proven by counting, not by the structure theorem for finite
  abelian groups: the subgroup it generates has the same cardinality `q^k`.
* `exists_zsmul_eq_frobeniusPointEnd_qPow` — therefore `F` acts on `E[q^k]` as
  multiplication by a SINGLE integer `ε`.

`sq_frobeniusPointEnd_qPrimary_ordinary` is PROVEN over these, and what is left
is `sq_frobeniusPointEnd_qPrimary_unitRoot`: `q^k ∣ ε² − c·ε + q`.  A
divisibility in `ℤ`.  That is the unit-root statement in its minimal form, and it
is where the geometry (Verschiebung, or Deuring's congruence) has to enter.

EIGHTH CUT, 2026-07-30: **the whole `q`-primary half of the characteristic
equation is GONE, not shrunk.**  `sq_frobeniusPointEnd_of_prime_to_char` proves

> `F² = c·F − q` on every point of order prime to `q`  ⟹  `F² = c·F − q` on EVERY
> point,

so the torsion-primary split that the FOURTH cut introduced is no longer a split
at all: the prime-to-`q` leaf implies the `q`-primary statement outright.  What
closed with it is the last surviving `q`-primary leaf,
`sq_frobeniusPointEnd_qPrimary_unitRoot`.

The mechanism is the one thing the earlier route notes never considered, and they
were explicitly (and correctly) pessimistic about every alternative: `ℤ[F]`-algebra
cannot transport an identity across the splitting `A′ ⊕ A_q`, and the model in
`exists_ne_zero_qTorsion`'s docstring still shows that.  But `F² − c·F + [q]` is
not an arbitrary group endomorphism — it is a MORPHISM, and

  **a nonzero isogeny has FINITE kernel** (`WeierstrassCurve.IsIsogeny.finite_ker`),

while `F² − c·F + [q]` kills `Wbar[n]` for every `n` prime to `q` and
`#Wbar[n] = n²` is unbounded.  So it has infinite kernel and is `0`.  That is the
geometry the notes asked for; it is neither the Verschiebung nor Deuring's
congruence, both of which are strictly more expensive and neither of which this
tree has.

What that cost, and it is the reason it was not available earlier: `IsIsogeny`
demands a rational-function certificate, and the `q`-power Frobenius had none in
the tree — `Isogeny.lean`'s `isIsogeny_frobPt` lives inside the `𝔽₂`
FALSITY-AUDIT namespace, for one curve.  The general certificate is
`isRationalMap_frobeniusPointEnd`, over `exists_pow_eq_linear`
(`y^n = c_n(x)·y + d_n(x)` on the curve, induction on `n` through
`y² = −a₁xy − a₃y + f(x)`).  `bijective_frobeniusPointEnd` moved up in the file to
sit above it; nothing about those six declarations changed.

NINTH CUT, 2026-07-31: **the degree form never vanishes off the origin.**
`degreeForm_ne_zero` proves `m² − c·m·n + n²q ≠ 0` for `(m, n) ≠ (0, 0)` —
equivalently `X² − c·X + q` is irreducible over `ℤ`, equivalently `c² − 4q` is
not a perfect square.  It closes no leaf; what it does is:

* it is the "degenerate case `d = 0`" that the ROUTE UPDATE on
  `natCard_ker_degreeFormEnd_le` named as the second piece of work a re-cut would
  have to write, so that piece exists now;
* it takes `natCard_ker_degreeFormEnd_of_dvd` OFF `natCard_ker_degreeFormEnd_le`
  — that `d = 0` branch used to cite the open leaf, and is now vacuous;
* the load-bearing step is NOT the elementary one the old sketch proposed.  That
  sketch needs both factors of `(F ∓ 1)(F ∓ q) = 0` to have finite kernel, and
  `F − [q] ≠ 0` is invisible to every counting fact here (`#ker F = 1` is
  consistent with `F = [q]`, which is the supersingular case).  What supplies it
  is the WEIL PAIRING: `frobeniusPointEnd_ne_zsmul` — `F` is not multiplication
  by any integer — from `det(F | Wbar[p]) = q` against `det([r] | Wbar[p]) = r²`
  for every prime `p ≠ q`, forcing `r² = q`.  So the determinant, which the
  audits below correctly say cannot see the SIGN of `d`, does decide that `F` is
  not a scalar.
* it opens a route to Hasse that the counter-model `A` of
  `natCard_ker_degreeFormEnd_le`'s audit does NOT refute — Pell on the (now
  provably non-square) discriminant produces a unit of `ℤ[F]` invertible in
  `WeierstrassCurve.End`, and the single missing atom is **an isogeny invertible
  in `End` has finite multiplicative order** (Aut-finiteness), which is exactly
  what `A` fails.  The full route is in the section header above
  `exists_point_ne_zero`; `EllipticCurve/AutomorphismExponent.lean` already has
  the group-theoretic half.

What remains open is EXACTLY THREE declarations, and this list is the one to
dispatch from — verified against the build's `declaration uses 'sorry'` warning
set on 2026-07-31, three warnings and three `sorry` tokens, so there are no
anonymous inner sorries here either:
`exists_sq_frobeniusPointEnd_prime_to_char` (the Frobenius characteristic
equation on the torsion of order prime to `q`, and by the EIGHTH CUT the ONLY
remaining input to `F² = c·F − q` — the umbrellas `exists_sq_frobeniusPointEnd`,
`sq_frobeniusPointEnd_qPrimary`, `sq_frobeniusPointEnd_qPrimary_ordinary` and
`sq_frobeniusPointEnd_qPrimary_unitRoot` are all PROVEN over it, so do NOT
dispatch at any of those four names),
`natCard_ker_degreeFormEnd_le` (separable degree ≤ degree, one-sided, no
hypothesis on `m`), and `exists_ne_zero_qTorsion` (the curve is ORDINARY when
`q ∤ c`).

SIXTH CUT, 2026-07-30: `sq_frobeniusPointEnd_qPrimary` is PROVEN, over the
strictly smaller `sq_frobeniusPointEnd_qPrimary_ordinary`.  Its own docstring
had already recorded that "only the ordinary case is real work"; that
observation is now carried out rather than left to the next owner.  The
supersingular case is discharged in place, from the single fact that a group
with no element of order `q` has no element of order `q^k` (an induction
peeling one `q` at a time, so it needs nothing about elliptic curves at all),
after which the conclusion is `0 = 0`.  The frontier count is UNCHANGED at four
— this is a decomposition, not a closure — but what survives now carries the
hypothesis `hord` that the `q`-torsion is nonzero, which is exactly the input
the unit-root argument needs.

A NOTE FOR WHOEVER OWNS THE CHARACTERISTIC EQUATION.  The 2026-07-27 plan
placed it in `FreyCurve/MazurTorsion.lean` as
`charEquation_point_map_frobAlgHom`.  That is not implementable in that
direction: `MazurTorsion.lean` `public import`s this module, so anything
stated there is downstream of every consumer here.  It is stated here
instead, as `exists_sq_frobeniusPointEnd`.

FOURTH CUT, 2026-07-28: `exists_sq_frobeniusPointEnd` is PROVEN, over the
TORSION-PRIMARY split.  What closed:

* `exists_pos_nsmul_eq_zero` — `Wbar(𝔽̄_q)` is a TORSION group.  Proven from
  scratch (finite-subfield closure of the coordinates, plus finiteness of the
  points over a finite field); this development had not recorded it before, and
  it is what makes any primary-by-primary argument possible.
* the assembly itself — Bézout on `q^k · m`, additivity of `F`.

What remains open in its place, and the two are genuinely different mathematics
rather than two halves of one argument:

* `exists_sq_frobeniusPointEnd_prime_to_char` — one integer `c` works on all
  torsion of order prime to `q`.  Cayley–Hamilton on `Wbar[n] ≅ (ℤ/n)²` with
  `det(F) = q`, PLUS the integrality of the trace, which is the archimedean
  half and is where the difficulty of Hasse's bound actually sits.
* `sq_frobeniusPointEnd_qPrimary` — the same `c` works on the `q`-power
  torsion.  The ordinary/supersingular dichotomy; `F` acts on the ordinary
  `q`-divisible group by the unit root.

Both leaves want `F` bijective on `Wbar(𝔽̄_q)`, as does
`natCard_ker_degreeFormEnd_of_dvd`; that was the obvious shared next brick, and
since the SIXTH CUT it is `bijective_frobeniusPointEnd`, available to all of
them without `hc`.
-/
module

public import Fermat.FLT.EllipticCurve.WeilPairing
-- `Isogeny.card_ker_comp` (`#ker (h ∘ f) = #ker h · #ker f` for surjective `f`,
-- pure group theory) and `WeierstrassCurve.zsmul_surjective_algClosed`.  This
-- adds ten `Fermat` modules to this file's cone and NONE to any consumer's:
-- `MazurTorsion.lean`, the only importer of this module, already imports
-- `Isogeny` directly.
public import Fermat.FLT.EllipticCurve.Isogeny
-- `TorsionCharP.exists_zsmul_eq_of_charP`: the geometric `q`-torsion in
-- characteristic `q` is CYCLIC.  That is the PROVEN upper half of
-- `natCard_ker_zsmul_q` below (`#E[q] ∣ q`), and taking it from here rather than
-- from `natCard_ker_degreeFormEnd_le` is what keeps the `q`-primary count off a
-- still-open leaf.  It adds `WronskianInduction`/`PsiSumCompanion`/`PhiPsiCoprime`
-- to this file's cone and NONE to `MazurTorsion.lean`'s, which already imports
-- `TorsionCharP` directly.
public import Fermat.FLT.EllipticCurve.TorsionCharP

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

/-- `[d]` as a `Module.End` is surjective for `d ≠ 0` (PROVEN): the
`Module.End` repackaging of `WeierstrassCurve.zsmul_surjective_algClosed`. -/
theorem surjective_zsmul_one (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] {d : ℤ} (hd : d ≠ 0) :
    Function.Surjective
      (d • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point))) := by
  haveI : ((Wbar⁄(AlgebraicClosure (ZMod q))).toAffine).IsElliptic :=
    inferInstanceAs (Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).IsElliptic
  exact _root_.WeierstrassCurve.zsmul_surjective_algClosed
    (Wbar⁄(AlgebraicClosure (ZMod q))).toAffine hd

/-- `[a] ∘ [b] = [a·b]` (PROVEN, `ring`-level). -/
theorem zsmul_one_mul_zsmul_one (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) (a b : ℤ) :
    (a • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)))
        * (b • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)))
      = (a * b) • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)) := by
  rw [smul_mul_assoc, one_mul, smul_smul]

/-! ### `F` is bijective

These six declarations were below the degree-form section until 2026-07-30; they
moved up because the ISOGENY section immediately after them consumes
`bijective_frobeniusPointEnd`, and that section is upstream of the whole
characteristic equation.  Nothing about them changed in the move.
-/

/-- **`F` is injective** (PROVEN): `Affine.Point.map` along an injective
algebra map is injective, and `frobAlgHom q` is a ring homomorphism of a
field. -/
theorem injective_frobeniusPointEnd (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) :
    Function.Injective (frobeniusPointEnd q Wbar) :=
  WeierstrassCurve.Affine.Point.map_injective (W' := Wbar) (WeilPairing.frobAlgHom q)

/-- **The `q`-power Frobenius of `𝔽̄_q` is surjective** (PROVEN 2026-07-30):
every element of an algebraically closed field has a `q`-th root.  No
perfectness instance is needed — `IsAlgClosed.exists_pow_nat_eq` is the whole
proof. -/
theorem surjective_frobAlgHom (q : ℕ) [Fact q.Prime] :
    Function.Surjective (WeilPairing.frobAlgHom q) := fun x =>
  IsAlgClosed.exists_pow_nat_eq (k := AlgebraicClosure (ZMod q))
    x (Fact.out : q.Prime).pos

/-- The `q`-power Frobenius of `𝔽̄_q` as an `𝔽_q`-algebra AUTOMORPHISM
(PROVEN 2026-07-30).  It exists because `frobAlgHom` is injective (a ring
homomorphism of a field) and surjective (`surjective_frobAlgHom`), and its
inverse is what transports a point back along the Frobenius. -/
noncomputable def frobAlgEquiv (q : ℕ) [Fact q.Prime] :
    AlgebraicClosure (ZMod q) ≃ₐ[ZMod q] AlgebraicClosure (ZMod q) :=
  AlgEquiv.ofBijective (WeilPairing.frobAlgHom q)
    ⟨(WeilPairing.frobAlgHom q).toRingHom.injective, surjective_frobAlgHom q⟩

/-- `F ∘ F⁻¹ = id` at the level of `𝔽_q`-algebra maps. -/
theorem frobAlgHom_comp_symm (q : ℕ) [Fact q.Prime] :
    (WeilPairing.frobAlgHom q).comp (frobAlgEquiv q).symm.toAlgHom
      = AlgHom.id (ZMod q) (AlgebraicClosure (ZMod q)) :=
  AlgHom.ext fun x => (frobAlgEquiv q).apply_symm_apply x

/-- `Point.map` along the identity is the identity.  Mathlib's `Point.map_id`
is stated for `Algebra.ofId F F`, i.e. with the *field* as the base ring; here
the base ring is `ZMod q`, so the statement is re-proven (both sides are
definitionally equal after a case split). -/
theorem point_map_algHom_id (q : ℕ) [Fact q.Prime] (Wbar : WeierstrassCurve (ZMod q))
    (P : (Wbar⁄(AlgebraicClosure (ZMod q))).Point) :
    WeierstrassCurve.Affine.Point.map (W' := Wbar) (S := ZMod q)
      (AlgHom.id (ZMod q) (AlgebraicClosure (ZMod q))) P = P := by
  cases P <;> rfl

/-- **`F` is surjective** (PROVEN 2026-07-30, UNCONDITIONALLY): pull a point
back along the inverse of the Frobenius automorphism of `𝔽̄_q`.

This replaces an earlier version that derived surjectivity from the
characteristic equation `hc` (as a left factor of the surjective `[q]`), and
that is a genuine strengthening rather than a tidy-up: the surviving
characteristic-equation leaf `exists_sq_frobeniusPointEnd_prime_to_char` is
*upstream* of `hc` — it is what produces it — so an `hc`-dependent bijectivity
is unavailable to it. -/
theorem surjective_frobeniusPointEnd (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) :
    Function.Surjective (frobeniusPointEnd q Wbar) := by
  intro P
  refine ⟨WeierstrassCurve.Affine.Point.map (W' := Wbar) (S := ZMod q)
    (frobAlgEquiv q).symm.toAlgHom P, ?_⟩
  show WeierstrassCurve.Affine.Point.map (W' := Wbar) (S := ZMod q)
    (WeilPairing.frobAlgHom q) _ = P
  rw [WeierstrassCurve.Affine.Point.map_map, frobAlgHom_comp_symm, point_map_algHom_id]

/-- **`F` is BIJECTIVE on `Wbar(𝔽̄_q)`** (PROVEN 2026-07-30, unconditionally):
injective because `x ↦ x^q` is, surjective because `𝔽̄_q` is algebraically
closed.  This is the brick three declarations in this file asked for. -/
theorem bijective_frobeniusPointEnd (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) :
    Function.Bijective (frobeniusPointEnd q Wbar) :=
  ⟨injective_frobeniusPointEnd q Wbar, surjective_frobeniusPointEnd q Wbar⟩

/-! ### `F` is an ISOGENY, and what that buys: the `q`-primary half is free

**EIGHTH CUT, 2026-07-30, and it is the one that removes a whole leaf rather
than shrinking it.**  Everything in this section exists to prove
`sq_frobeniusPointEnd_of_prime_to_char`:

> if `F² = c·F − q` holds on every point of order prime to `q`, then it holds on
> EVERY point.

WHY THAT IS NOT CIRCULAR AND NOT GROUP THEORY.  The two `q`-primary route notes
in this file (and the model in `exists_ne_zero_qTorsion`'s docstring, which is
correct) say that no algebra in `ℤ[F]` can transport the identity from the
prime-to-`q` torsion to `Wbar(𝔽̄_q)[q^∞]`: the group splits as `A′ ⊕ A_q` with
independent summands, and there is a module in which every identity this file
proves holds while `A_q = 0`.  All of that stands.  What breaks the impasse is
that `F² − c·F + [q]` is not an arbitrary group endomorphism — it is a MORPHISM
OF THE CURVE, and

  **a nonzero isogeny has FINITE kernel** (`WeierstrassCurve.IsIsogeny.finite_ker`),

while `F² − c·F + [q]` kills `Wbar[n]` for every `n` prime to `q`, and
`#Wbar[n] = n²` (`TorsionCard.card_torsionBy`) is unbounded.  So the kernel is
infinite and the endomorphism is `0`.  That is the geometry the route notes asked
for, and it is `finite_ker` rather than the Verschiebung or Deuring's congruence
— both of which are strictly more expensive and neither of which this tree has.

WHAT HAD TO BE BUILT, and it is the reason this was not available before: the
`Isogeny.lean` endomorphism ring is indexed by `IsIsogeny`, whose
`isRationalMap` field demands a rational-function certificate, and the `q`-power
Frobenius had no such certificate anywhere in the tree (`Isogeny.lean`'s
`isIsogeny_frobPt` is inside the `𝔽₂` FALSITY-AUDIT namespace
`NotIsRationalMapDualHom`, for the single curve `y² + y = x³`).  The certificate
is supplied here by `exists_pow_eq_linear`: `x(F P) = x(P)^q` needs `A = X^q`,
and `y(F P) = y(P)^q` is linear in `y` because `y² = −a₁xy − a₃y + f(x)` on the
curve, so `y^n = c_n(x)·y + d_n(x)` by induction on `n`.

NOTE THE `[IsAlgClosed]` DEPENDENCE, which is real and is why this is stated over
`𝔽̄_q` only: `IsIsogeny.add` is FALSE over a general field (`Isogeny.lean`'s
FALSITY AUDIT refutes it over `𝔽₅`), so the endomorphism RING — which is what
turns `F² − c·F + [q]` into a single isogeny — exists only over an algebraically
closed base.  `Wbar(𝔽̄_q)` is exactly that base.
-/

/-- **`y^n` is linear in `y` modulo the Weierstrass equation** (PROVEN
2026-07-30): there are polynomials `c, d` over the base field with
`y^n = c(x)·y + d(x)` at every point `(x, y)` of the curve.

This is the whole content of the rational-function certificate for the `q`-power
Frobenius: the `x`-half is `A = X^q, B = 1`, and the `y`-half needs `y^q` to be
`ZMod`-LINEAR in `y`, which the curve equation `y² = −a₁xy − a₃y + f(x)` supplies
by induction.  `IsRationalMap`'s `y`-clause is `y(φP)·E(x) = C(x)·y(P) + D(x)`,
so nothing of higher degree in `y` is admissible and this induction is not
avoidable. -/
theorem exists_pow_eq_linear {F : Type*} [Field F] (W : WeierstrassCurve F) (n : ℕ) :
    ∃ c d : Polynomial F, ∀ x y : F, W.toAffine.Equation x y →
      y ^ n = c.eval x * y + d.eval x := by
  induction n with
  | zero => exact ⟨0, 1, fun x y _ => by simp⟩
  | succ n ih =>
    obtain ⟨c, d, h⟩ := ih
    refine ⟨-(Polynomial.C W.a₁) * Polynomial.X * c - (Polynomial.C W.a₃) * c + d,
      c * (Polynomial.X ^ 3 + Polynomial.C W.a₂ * Polynomial.X ^ 2
        + Polynomial.C W.a₄ * Polynomial.X + Polynomial.C W.a₆), fun x y hxy => ?_⟩
    have hy2 := (W.toAffine.equation_iff x y).mp hxy
    have hn := h x y hxy
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_neg, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
    rw [pow_succ, hn]
    linear_combination (c.eval x) * hy2

/-- `F` raises the `x`-coordinate to the `q`-th power (PROVEN, a case split;
the point at infinity is handled by `0 ^ q = 0`). -/
theorem veluPointX_frobeniusPointEnd (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) (P : (Wbar⁄(AlgebraicClosure (ZMod q))).Point) :
    veluPointX (frobeniusPointEnd q Wbar P) = (veluPointX P) ^ q := by
  cases P with
  | zero =>
    show veluPointX (frobeniusPointEnd q Wbar (0 : (Wbar⁄(AlgebraicClosure (ZMod q))).Point))
      = (0 : AlgebraicClosure (ZMod q)) ^ q
    rw [map_zero]
    simp [(Fact.out : q.Prime).pos.ne']
  | some x y h => rfl

/-- `F` raises the `y`-coordinate to the `q`-th power (PROVEN). -/
theorem veluPointY_frobeniusPointEnd (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) (P : (Wbar⁄(AlgebraicClosure (ZMod q))).Point) :
    veluPointY (frobeniusPointEnd q Wbar P) = (veluPointY P) ^ q := by
  cases P with
  | zero =>
    show veluPointY (frobeniusPointEnd q Wbar (0 : (Wbar⁄(AlgebraicClosure (ZMod q))).Point))
      = (0 : AlgebraicClosure (ZMod q)) ^ q
    rw [map_zero]
    simp [(Fact.out : q.Prime).pos.ne']
  | some x y h => rfl

/-- **`F` is given by rational functions in the coordinates** (PROVEN
2026-07-30): the certificate is `(A, B) = (X^q, 1)` for the `x`-coordinate and
`(C, D, E) = (c_q, d_q, 1)` for the `y`-coordinate, where `c_q, d_q` are the
`exists_pow_eq_linear` polynomials at `n = q`. -/
theorem isRationalMap_frobeniusPointEnd (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) :
    WeierstrassCurve.IsRationalMap (frobeniusPointEnd q Wbar).toAddMonoidHom := by
  obtain ⟨C, D, hCD⟩ := exists_pow_eq_linear (Wbar⁄(AlgebraicClosure (ZMod q))) q
  refine ⟨Polynomial.X ^ q, 1, C, D, 1, one_ne_zero, one_ne_zero, fun P hP => ?_⟩
  have hP0 : P ≠ 0 := by
    rintro rfl
    exact hP (map_zero _)
  cases P with
  | zero => exact absurd rfl hP0
  | some x y h =>
    simp only [LinearMap.toAddMonoidHom_coe]
    refine ⟨?_, ?_⟩
    · rw [veluPointX_frobeniusPointEnd]
      simp
    · rw [veluPointY_frobeniusPointEnd]
      simpa using hCD x y h.1

/-- **`F` is an ISOGENY** (PROVEN 2026-07-30): rational by
`isRationalMap_frobeniusPointEnd`, surjective by `surjective_frobeniusPointEnd`,
and of trivial — hence finite — kernel by `injective_frobeniusPointEnd`.

This is what puts `F` into the endomorphism RING `WeierstrassCurve.End`, and so
what makes `F² − c·F + [q]` an isogeny rather than a bare group endomorphism. -/
theorem isIsogeny_frobeniusPointEnd (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) :
    WeierstrassCurve.IsIsogeny (frobeniusPointEnd q Wbar).toAddMonoidHom where
  isRationalMap := isRationalMap_frobeniusPointEnd q Wbar
  surjective _ := surjective_frobeniusPointEnd q Wbar
  finite_ker _ := by
    have h : (AddMonoidHom.ker (frobeniusPointEnd q Wbar).toAddMonoidHom
        : Set ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)) = {0} := by
      ext P
      simp only [Set.mem_singleton_iff, SetLike.mem_coe, AddMonoidHom.mem_ker,
        LinearMap.toAddMonoidHom_coe]
      exact ⟨fun hh => injective_frobeniusPointEnd q Wbar (by rw [hh, map_zero]),
        fun hh => by rw [hh, map_zero]⟩
    rw [h]
    exact Set.finite_singleton _

/-- **The characteristic equation spreads from the prime-to-`q` torsion to ALL
points** (PROVEN 2026-07-30): if `F² = c·F − q` on every point killed by some
integer prime to `q`, then it holds on every point of `Wbar(𝔽̄_q)`.

THIS IS WHERE THE `q`-PRIMARY HALF OF THE CHARACTERISTIC EQUATION DIES.  It is
the section header's theorem; see there for why it is neither circular nor
group theory, and for the model that shows an `ℤ[F]`-only proof cannot exist.

THE PROOF IN FOUR LINES.  `G := F² − c·F + [q]` lies in `WeierstrassCurve.End`
of the curve over `𝔽̄_q`, because `F` does (`isIsogeny_frobeniusPointEnd`) and
that is a RING.  `G` kills `Wbar[(q+1)^m]` for every `m` — the hypothesis
applies since `q ∤ (q+1)^m` — and `#Wbar[(q+1)^m] = (q+1)^{2m}`
(`TorsionCard.card_torsionBy`), which exceeds any bound.  So `ker G` is infinite,
`IsIsogeny.finite_ker` forces `G = 0`, and `G = 0` applied to a point is the
conclusion.

`(q + 1)^m` RATHER THAN A PRIME POWER, deliberately: `q ∤ q + 1` is one line for
every prime `q` including `2`, whereas "some prime `ℓ ≠ q`" needs a case split
and `Nat.exists_infinite_primes`.  Nothing else about the family matters — only
that the counts are unbounded. -/
theorem sq_frobeniusPointEnd_of_prime_to_char (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] {c : ℤ}
    (hc : ∀ n : ℕ, ¬ (q ∣ n) →
      ∀ P : (Wbar⁄(AlgebraicClosure (ZMod q))).Point, (n : ℤ) • P = 0 →
        frobeniusPointEnd q Wbar (frobeniusPointEnd q Wbar P)
          = c • frobeniusPointEnd q Wbar P - (q : ℤ) • P)
    (P : (Wbar⁄(AlgebraicClosure (ZMod q))).Point) :
    frobeniusPointEnd q Wbar (frobeniusPointEnd q Wbar P)
      = c • frobeniusPointEnd q Wbar P - (q : ℤ) • P := by
  haveI hell : ((Wbar⁄(AlgebraicClosure (ZMod q))).toAffine).IsElliptic :=
    inferInstanceAs (Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).IsElliptic
  set f : WeierstrassCurve.End ((Wbar⁄(AlgebraicClosure (ZMod q))).toAffine) :=
    ⟨(frobeniusPointEnd q Wbar).toAddMonoidHom, isIsogeny_frobeniusPointEnd q Wbar⟩
  set G : WeierstrassCurve.End ((Wbar⁄(AlgebraicClosure (ZMod q))).toAffine) :=
    f * f - (Int.cast c) * f + Int.cast (q : ℤ)
  have hGapp : ∀ Q : (Wbar⁄(AlgebraicClosure (ZMod q))).Point, (G : AddMonoid.End _) Q
      = frobeniusPointEnd q Wbar (frobeniusPointEnd q Wbar Q)
        - c • frobeniusPointEnd q Wbar Q + (q : ℤ) • Q := fun _ => rfl
  -- `G` kills every point of order prime to `q`
  have hker : ∀ n : ℕ, ¬ (q ∣ n) → ∀ Q : (Wbar⁄(AlgebraicClosure (ZMod q))).Point,
      (n : ℤ) • Q = 0 → (G : AddMonoid.End _) Q = 0 := by
    intro n hn Q hQ
    rw [hGapp, hc n hn Q hQ]
    abel
  -- so its kernel is infinite, and an isogeny with infinite kernel is `0`
  have hG0 : G = 0 := by
    by_contra hne
    have hGne : (G : AddMonoid.End ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)) ≠ 0 := by
      intro h
      exact hne (Subtype.ext h)
    obtain ⟨A, hAfin, hAmem⟩ : ∃ A : Set ((Wbar⁄(AlgebraicClosure (ZMod q))).Point),
        A.Finite ∧ ∀ Q, (G : AddMonoid.End _) Q = 0 → Q ∈ A :=
      ⟨_, G.2.finite_ker hGne, fun _ hQ => AddMonoidHom.mem_ker.mpr hQ⟩
    set m : ℕ := A.ncard
    set n : ℕ := (q + 1) ^ m with hn
    have hqn : ¬ (q ∣ n) := by
      intro hdvd
      have h1 : q ∣ q + 1 := (Fact.out : q.Prime).dvd_of_dvd_pow hdvd
      have h2 : q ∣ 1 := (Nat.dvd_add_right (dvd_refl q)).mp h1
      exact (Fact.out : q.Prime).one_lt.ne' (Nat.dvd_one.mp h2)
    haveI : CharP (AlgebraicClosure (ZMod q)) q :=
      charP_of_injective_algebraMap
        (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))).injective q
    have hn0 : ((n : ℕ) : AlgebraicClosure (ZMod q)) ≠ 0 := fun h0 =>
      hqn ((CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod q)) q n).mp h0)
    have hcardn : Nat.card (Submodule.torsionBy ℤ
        (Wbar⁄(AlgebraicClosure (ZMod q))).Point ((n : ℕ) : ℤ)) = n ^ 2 :=
      TorsionCard.card_torsionBy
        (Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))) n hn0
    have hsub : (Submodule.torsionBy ℤ
        (Wbar⁄(AlgebraicClosure (ZMod q))).Point ((n : ℕ) : ℤ) : Set _) ⊆ A := by
      intro Q hQ
      rw [SetLike.mem_coe, Submodule.mem_torsionBy_iff] at hQ
      exact hAmem Q (hker n hqn Q hQ)
    have hle : Nat.card (Submodule.torsionBy ℤ
        (Wbar⁄(AlgebraicClosure (ZMod q))).Point ((n : ℕ) : ℤ)) ≤ m :=
      Set.ncard_le_ncard hsub hAfin
    rw [hcardn] at hle
    have hq1 : 1 < q + 1 := by
      have := (Fact.out : q.Prime).two_le
      omega
    have hlt : m < n := hn ▸ Nat.lt_pow_self hq1
    have hnn : n ≤ n ^ 2 := Nat.le_self_pow two_ne_zero n
    exact absurd ((hle.trans_lt hlt).trans_le hnn) (lt_irrefl _)
  have hP := hGapp P
  rw [hG0] at hP
  have h0 : ((0 : WeierstrassCurve.End ((Wbar⁄(AlgebraicClosure (ZMod q))).toAffine))
      : AddMonoid.End _) P = 0 := rfl
  rw [h0] at hP
  linear_combination (norm := abel) -hP

/-! ### `Wbar(𝔽̄_q)` is a torsion group, and the two primary halves of `F² = c·F − q`

The characteristic equation is an identity of `ℤ`-endomorphisms of
`Wbar(𝔽̄_q)`, and that group is a TORSION group: every point has coordinates in
a finite subfield of `𝔽̄_q`, hence lies in the (finite) group of points of the
curve over that subfield.  So the identity may be checked one torsion-primary
piece at a time — and the two pieces carry genuinely different mathematics:

* away from `q`, `Wbar(𝔽̄_q)[n] ≅ (ℤ/n)²` and the identity is Cayley–Hamilton for
  a `2 × 2` matrix whose determinant is `q` (the Weil pairing), together with the
  INTEGRALITY of the resulting trace;
* at `q`, `Wbar(𝔽̄_q)[q^∞]` is `ℚ_q/ℤ_q` (ordinary) or `0` (supersingular), and
  the identity is the statement that `F` acts there by the *unit root* of the
  same quadratic.

`exists_pos_nsmul_eq_zero` below is the torsion statement, PROVEN; the two halves
are the two leaves `exists_sq_frobeniusPointEnd_prime_to_char` and
`sq_frobeniusPointEnd_qPrimary`; and `exists_sq_frobeniusPointEnd` is their
assembly, PROVEN.
-/

/-- **`Wbar(𝔽̄_q)` is a torsion group** (PROVEN 2026-07-28): every point is
killed by some positive integer.

This is the fact that makes a torsion-primary proof of the characteristic
equation possible at all, and it is the first place this development records it.
The proof is the standard one: a point `(x, y)` has both coordinates algebraic
over `𝔽_q`, so `L = 𝔽_q(x, y)` is a finite extension (`IntermediateField`'s
`finiteDimensional_adjoin`, over `Algebra.IsIntegral`); the point is then the
base change of an `L`-rational point (`Affine.baseChange_nonsingular` transports
nonsingularity back down); `(Wbar⁄L).Point` is finite because `L` is; and
`Affine.Point.baseChange` is an injective group homomorphism, so the order of the
`L`-rational point kills the original point.

NOT SPECIFIC TO ELLIPTIC CURVES: no `IsElliptic` hypothesis is needed, because
finiteness of `(Wbar⁄L).Point` is read off the coordinates directly rather than
from any group structure. -/
theorem exists_pos_nsmul_eq_zero (q : ℕ) [Fact q.Prime] (Wbar : WeierstrassCurve (ZMod q))
    (P : (Wbar⁄(AlgebraicClosure (ZMod q))).Point) :
    ∃ n : ℕ, 0 < n ∧ (n : ℤ) • P = 0 := by
  classical
  cases P with
  | zero => exact ⟨1, one_pos, by rw [Nat.cast_one, one_smul]; rfl⟩
  | some x y h =>
    set L := IntermediateField.adjoin (ZMod q) ({x, y} : Set (AlgebraicClosure (ZMod q)))
      with hL
    haveI : FiniteDimensional (ZMod q) L :=
      IntermediateField.finiteDimensional_adjoin
        (fun z _ => Algebra.IsIntegral.isIntegral z)
    haveI : Finite L := Module.finite_of_finite (ZMod q)
    have hx : x ∈ L := IntermediateField.subset_adjoin _ _ (by simp)
    have hy : y ∈ L := IntermediateField.subset_adjoin _ _ (by simp)
    have h' : (Wbar⁄L).Nonsingular (⟨x, hx⟩ : L) (⟨y, hy⟩ : L) :=
      (WeierstrassCurve.Affine.baseChange_nonsingular (W := Wbar)
        (f := Algebra.ofId L (AlgebraicClosure (ZMod q)))
        (Algebra.ofId L (AlgebraicClosure (ZMod q))).injective
        (⟨x, hx⟩ : L) (⟨y, hy⟩ : L)).mp h
    set P' : (Wbar⁄L).Point := WeierstrassCurve.Affine.Point.some _ _ h' with hP'
    haveI : Finite (Wbar⁄L).Point := by
      have hinj : Function.Injective
          (fun Q : (Wbar⁄L).Point =>
            match Q with
            | 0 => (none : Option (L × L))
            | WeierstrassCurve.Affine.Point.some x y _ => some (x, y)) := by
        rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) hh <;> simp_all
      exact Finite.of_injective _ hinj
    refine ⟨addOrderOf P', addOrderOf_pos_iff.mpr (isOfFinAddOrder_of_finite P'), ?_⟩
    have hmap : WeierstrassCurve.Affine.Point.baseChange (W' := Wbar) L
        (AlgebraicClosure (ZMod q)) P' = WeierstrassCurve.Affine.Point.some x y h := rfl
    rw [← hmap, ← map_zsmul, natCast_zsmul, addOrderOf_nsmul_eq_zero, map_zero]

/-- **The characteristic equation away from `q`** (sorry leaf, opened 2026-07-28;
Silverman *AEC* V.2.3.1, prime-to-`q` half): there is ONE rational integer `c`
with `F(F P) = c·F P − q·P` for every point `P` whose order is prime to `q`.

WHAT IS IN THIS LEAF, and it is two things that classical treatments prove
together but that are separately identifiable here.

* *Cayley–Hamilton at level `n`.*  For `q ∤ n` the group `Wbar(𝔽̄_q)[n]` is free
  of rank `2` over `ZMod n` — `TorsionCard.card_torsionBy` (PROVEN) already
  counts it as `n²`, and `WeierstrassCurve.n_torsion_dimension`
  (`EllipticCurve/Torsion.lean`, PROVEN, and stated for GENERAL `n`) already
  supplies the basis — the Frobenius acts `ZMod n`-linearly on it, and
  `det(F | Wbar[n]) = q`, after which `F² = t_n·F − q` holds on `Wbar[n]` with
  `t_n = tr(F | Wbar[n]) ∈ ZMod n`.

  **DO NOT REBUILD THIS HALF — IT IS ALREADY PROVEN, BUT DOWNSTREAM (audited
  2026-07-30).**  `WeilPairing.det_frobeniusTorsionEnd` is indeed only for PRIME
  `n`, and that is what earlier notes here recorded; but
  `FreyCurve/MazurTorsion.lean` carries the COMPOSITE-LEVEL version, PROVEN, as
  `det_frobeniusTorsionEnd_of_coprime`, together with everything it needs —
  `nonempty_basis_nTorsion`, `pairing_map_eq_det_mul_fin_two`,
  `det_eq_of_conj_of_basis_fin_two`, `sq_eq_trace_smul_sub_det_smul_fin_two`,
  `isPrimitiveRoot_pairing_of_nondegenerate_basis_fin_two`,
  `exists_weilPairing_mu_of_coprime`, `exists_weilPairing_frobenius_of_coprime` —
  over the SINGLE arithmetic leaf `exists_weilPairing_mu_nondeg_of_coprime` (the
  level-`N` re-run of `WeilPairing.exists_weilPairing_mu`), which is separately
  owned there.

  The obstruction is purely architectural: `MazurTorsion.lean` `public import`s
  this module, so none of it can be cited here.  **The repair is a RELOCATION,
  not a proof** — move that block into a module upstream of this one (its own
  file, or the tail of `EllipticCurve/WeilPairing.lean`, keeping the namespace so
  `MazurTorsion.lean`'s existing references still resolve) and this half of the
  leaf closes with NO new sorry, leaving only the trace integrality below.  It is
  not done here because that block sits in a 33 000-line file that had five
  concurrent uncommitted editors when this was written, and a relocation of that
  size is a merge decision rather than a proof.  Note that a naive local re-cut
  is strictly worse: re-stating the composite determinant here as a fresh leaf
  DUPLICATES a statement the tree already proves.
* *Integrality of the trace.*  The residues `t_n` are compatible (each is the
  reduction of the next, because `Wbar[n] ⊆ Wbar[nm]` and `F` is injective), so
  they assemble to an element of `Ẑ`; the content of this leaf is that that
  element is a rational INTEGER.  That is the archimedean half, and it is where
  the difficulty of Hasse's bound actually lives: an element of `Ẑ` is an integer
  exactly when it is bounded, and no purely `ℓ`-adic argument supplies a bound.

The classical supply of the bound is the DEGREE: `deg(1 − F) = #ker(1 − F)` is a
cardinality, and `#ker(1 − F) = #Wbar(𝔽_q)` is PROVEN here as
`natCard_ker_one_sub_frobeniusPointEnd`, so `c = q + 1 − #Wbar(𝔽_q)` is visibly
an integer once one knows `det(1 − F | Wbar[n]) ≡ #Wbar(𝔽_q) (mod n)` — the
LEFSCHETZ CONGRUENCE.

**A ROUTE THAT LOOKS AVAILABLE AND IS CIRCULAR — checked 2026-07-30, recorded so
that nobody spends a cycle on it.**  That congruence is stated downstream, in
`FreyCurve/MazurTorsion.lean`, as
`det_one_sub_frobeniusTorsionEnd_eq_natCard_frobFixed`, and it is PROVEN there.
It is NOT usable here, and not merely because of the import direction: its proof
consumes `charEquation_frobeniusTorsionEnd`, i.e. THIS LEAF.  So relocating it
upstream would produce a cycle, and the only part of that cluster that is
genuinely upstream-able is the Weil-pairing determinant `det F = q` recorded
above.  In other words the Lefschetz congruence in this tree is a CONSEQUENCE of
trace integrality, not a supply of it, and a successor must find the bound
elsewhere — the classical `#ker ψ = deg ψ`/dual-isogeny chain is refuted in
characteristic `q` by `Isogeny.lean` (`isRationalMap_dualHom_is_false`), which is
exactly why this leaf is hard.

THE COEFFICIENT IS EXISTENTIAL ON PURPOSE, for the same reason as in
`exists_sq_frobeniusPointEnd`: naming `c = frobeniusTrace` would fold the
`(m, n) = (1, 1)` evaluation into this leaf, and that evaluation is already
proven separately.

**HOW MUCH OF THE STATEMENT IS REALLY NEEDED, after the EIGHTH CUT.**
`sq_frobeniusPointEnd_of_prime_to_char` derives `F² = c·F − q` on ALL points from
this leaf, and its proof consumes the hypothesis at the levels `n = (q+1)^m`
ONLY — it needs nothing more than that the points covered are UNBOUNDED in number.
So a successor is free to prove any of the following instead, all of which imply
this leaf through that theorem plus the trivial re-quantification, and the second
is the classical `ℓ`-adic statement:

* `∃ c, ∀ m, ∀ P, ((q+1)^m : ℤ) • P = 0 → F² P = c·F P − q·P`;
* the same with `(q+1)^m` replaced by `ℓ^m` for a SINGLE prime `ℓ ≠ q`, i.e. the
  statement about one Tate module `T_ℓ` rather than about all levels at once;
* `∃ c, {P | F² P = c·F P − q·P}` is INFINITE.

NON-VACUITY.  `c = 0` is not a free choice — see the non-vacuity note on
`exists_sq_frobeniusPointEnd` below, which applies verbatim, since that
statement's `c` is produced by this one.  The hypothesis `q ∤ n` is LOAD-BEARING
in the sense that it is what makes `Wbar[n]` free of rank two, and hence what
makes the Cayley–Hamilton half available at all; note that it is NO LONGER
load-bearing for the CONCLUSION, since the EIGHTH CUT shows the `q`-primary case
follows.

THE CHECK THAT WOULD REFUTE the claim that the trace integrality is the hard
half: an `ℓ`-adic-only proof that the compatible system `(t_n)` is bounded. -/
theorem exists_sq_frobeniusPointEnd_prime_to_char (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] :
    ∃ c : ℤ, ∀ n : ℕ, ¬ (q ∣ n) →
      ∀ P : (Wbar⁄(AlgebraicClosure (ZMod q))).Point, (n : ℤ) • P = 0 →
        frobeniusPointEnd q Wbar (frobeniusPointEnd q Wbar P)
          = c • frobeniusPointEnd q Wbar P - (q : ℤ) • P :=
  sorry

/-- **The characteristic equation on the `q`-primary torsion** (sorry leaf,
opened 2026-07-28; Silverman *AEC* V.3.1, the ordinary/supersingular
dichotomy): the SAME coefficient `c` that works away from `q` also works on the
`q`-power torsion.

WHY THIS IS A SEPARATE LEAF AND NOT AN ARTEFACT.  `Wbar(𝔽̄_q)[q^∞]` is invisible
to the prime-to-`q` argument: it is `0` in the supersingular case, and
`ℚ_q/ℤ_q` in the ordinary case, never `(ℚ_q/ℤ_q)²`, so no `2 × 2`
Cayley–Hamilton is available there and the Weil pairing determinant
(`WeilPairing.det_frobeniusTorsionEnd`) explicitly excludes `n = q`.  What has to
be shown is that `F` acts on the ordinary `q`-divisible group by the UNIT ROOT
of `X² − cX + q`, i.e. by the root that is a `q`-adic unit — the other root has
valuation `1` and cannot act invertibly on `ℚ_q/ℤ_q`.

`hc` IS LOAD-BEARING AND THE LEAF IS FALSE WITHOUT IT.  Dropping `hc` leaves `c`
a free integer, and the conclusion at `k = 1` would then assert
`F² = c·F − q` on `Wbar[q]` for EVERY `c`, which fails already for an ordinary
curve (take `c` and `c + 1`, whose difference forces `F P = 0` for all
`P ∈ Wbar[q]`, contradicting injectivity of `F`).  It is the prime-to-`q`
identity that pins `c`, and this leaf is precisely the assertion that the SAME
pinned `c` survives at `q`.

WHAT A SUCCESSOR NEEDS.  Only the ordinary case is real work: in the
supersingular case `Wbar(𝔽̄_q)[q^∞] = 0`, so the hypothesis
`(q^k) • P = 0` forces `P = 0` for `k ≥ 1` and the conclusion is trivial.  The
`k = 0` case is trivial for the same reason (`1 • P = 0` gives `P = 0`).  The
route note of `natCard_ker_degreeFormEnd_of_dvd` below reduces its own
`q`-primary case to the single count `#ker([c] − F) = q` for `q ∤ c`; that count
and this leaf are the same piece of mathematics seen from two sides, so
whichever is proven first should be stated so the other can consume it.  Both
want `F` BIJECTIVE on `Wbar(𝔽̄_q)` (injective because `x ↦ x^q` is; surjective
because `𝔽̄_q` is algebraically closed and perfect); since 2026-07-30 that is
`bijective_frobeniusPointEnd`, proven with no hypothesis on `c`.

THE CHECK THAT WOULD REFUTE the claim that this case is not covered by the leaf
above: a torsion point of `q`-power order that is also killed by an integer
prime to `q`.  There is none other than `0`, which is exactly why the split is
exhaustive and why this leaf is needed.

SIXTH CUT, 2026-07-30: THE SUPERSINGULAR HALF IS NOW MACHINE-CHECKED, and what
survives is the strictly smaller `sq_frobeniusPointEnd_qPrimary_ordinary`, whose
extra hypothesis `hord` is the existence of a nonzero `q`-torsion point.  The
docstring above already recorded "only the ordinary case is real work"; that
observation is now a proof rather than a note, over
`eq_zero_of_qPow_zsmul_eq_zero` (`E[q] = 0 ⟹ E[q^∞] = 0`, an induction on `k`).
Nothing else about the leaf changed: `hc` is still load-bearing for exactly the
reason argued above, and the ordinary case still wants the unit root. -/
theorem eq_zero_of_qPow_zsmul_eq_zero (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q))
    (hss : ∀ R : (Wbar⁄(AlgebraicClosure (ZMod q))).Point, (q : ℤ) • R = 0 → R = 0) :
    ∀ (k : ℕ) (P : (Wbar⁄(AlgebraicClosure (ZMod q))).Point),
      ((q : ℤ) ^ k) • P = 0 → P = 0 := by
  intro k
  induction k with
  | zero => intro P hP; simpa using hP
  | succ k ih =>
    intro P hP
    refine ih P (hss _ ?_)
    rw [smul_smul, ← pow_succ']
    exact hP

/-! #### The ORDINARY `q`-primary structure

`E[q^k]` is CYCLIC of order exactly `q^k` as soon as ONE nonzero `q`-torsion
point exists, and this section proves that from scratch.  Nothing here needs the
characteristic equation — the inputs are `TorsionCharP`'s cyclicity of `E[q]`
(the vanishing of `ΨSqₚ′`) and the divisibility of `Wbar(𝔽̄_q)`.

The point of it is `exists_zsmul_eq_frobeniusPointEnd_qPow` at the end: on a
cyclic group `F` is multiplication by ONE integer, so the `q`-primary
characteristic equation collapses from a statement about points to a
divisibility in `ℤ`.
-/

/-- **`#E[q] = q` from a single nonzero `q`-torsion point** (PROVEN 2026-07-30).
Cyclicity in characteristic `q` says every `q`-torsion point is a multiple of any
nonzero one, so `E[q]` is the cyclic group generated by `R`, of order `q` since
`q` is prime.

This is the `hc`-free core of `natCard_ker_zsmul_q` below, which is now a wrapper
over it.  The two hypotheses that theorem carries (`hc` and `q ∤ c`) are used
ONLY to produce the point, through `exists_ne_zero_qTorsion`; nothing in the
count itself needs them, and the `q`-primary machinery in this section is
upstream of `hc` and so could not use them anyway. -/
theorem natCard_ker_zsmul_q_of_ordinary (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic]
    (hord : ∃ R : (Wbar⁄(AlgebraicClosure (ZMod q))).Point, R ≠ 0 ∧ (q : ℤ) • R = 0) :
    Nat.card (LinearMap.ker
      ((q : ℤ) • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)))) = q := by
  classical
  haveI : CharP (AlgebraicClosure (ZMod q)) q :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))).injective q
  have hchar : ((q : ℕ) : AlgebraicClosure (ZMod q)) = 0 :=
    CharP.cast_eq_zero (AlgebraicClosure (ZMod q)) q
  obtain ⟨P, hP0, hPq⟩ := hord
  have hord' : addOrderOf P = q := by
    have hdvd : (addOrderOf P : ℤ) ∣ ((q : ℕ) : ℤ) :=
      addOrderOf_dvd_iff_zsmul_eq_zero.mpr hPq
    rcases (Fact.out : q.Prime).eq_one_or_self_of_dvd _
      (Int.natCast_dvd_natCast.mp hdvd) with h | h
    · refine absurd ?_ hP0
      have h1 : (1 : ℤ) • P = 0 :=
        addOrderOf_dvd_iff_zsmul_eq_zero.mp (by rw [h]; exact one_dvd _)
      rwa [one_zsmul] at h1
    · exact h
  have hiff : ∀ Z : (Wbar⁄(AlgebraicClosure (ZMod q))).Point,
      Z ∈ LinearMap.ker
          ((q : ℤ) • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)))
        ↔ Z ∈ AddSubgroup.zmultiples P := by
    intro Z
    rw [ker_zsmul_one, Submodule.mem_torsionBy_iff, AddSubgroup.mem_zmultiples_iff]
    constructor
    · intro hZ
      obtain ⟨n, hn⟩ := TorsionCharP.exists_zsmul_eq_of_charP
        (Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))))
        (Fact.out : q.Prime) hchar Z P hZ hPq hP0
      exact ⟨n, hn.symm⟩
    · rintro ⟨n, rfl⟩
      exact (Submodule.mem_torsionBy_iff _ _).mp
        (Submodule.smul_mem _ n ((Submodule.mem_torsionBy_iff _ _).mpr hPq))
  calc Nat.card (LinearMap.ker
        ((q : ℤ) • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point))))
      = Nat.card (AddSubgroup.zmultiples P) :=
        Nat.card_congr (Equiv.subtypeEquivRight hiff)
    _ = addOrderOf P := Nat.card_zmultiples P
    _ = q := hord'

/-- **`#E[q^v] = q^v` from a single nonzero `q`-torsion point** (PROVEN
2026-07-30): `[q^{v+1}] = [q] ∘ [q^v]` with `[q^v]` surjective, so the counts
multiply.  The `hc`-free core of `natCard_ker_zsmul_q_pow`. -/
theorem natCard_ker_zsmul_q_pow_of_ordinary (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic]
    (hord : ∃ R : (Wbar⁄(AlgebraicClosure (ZMod q))).Point, R ≠ 0 ∧ (q : ℤ) • R = 0) :
    ∀ v : ℕ, Nat.card (LinearMap.ker
      (((q : ℤ) ^ v) • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point))))
        = q ^ v := by
  have hqpos : (0 : ℤ) < (q : ℤ) := by exact_mod_cast (Fact.out : q.Prime).pos
  intro v
  induction v with
  | zero => simp
  | succ v ih =>
    have hq0 : (q : ℤ) ^ v ≠ 0 := by positivity
    have hmul : ((q : ℤ) ^ (v + 1))
          • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point))
        = ((q : ℤ) • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)))
          * (((q : ℤ) ^ v)
            • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point))) := by
      rw [zsmul_one_mul_zsmul_one]
      congr 1
      ring
    rw [hmul, natCard_ker_mul _ _ (surjective_zsmul_one q Wbar hq0),
      natCard_ker_zsmul_q_of_ordinary q Wbar hord, ih, pow_succ]
    ring

/-- **A point of additive order EXACTLY `q^(k+1)`** (PROVEN 2026-07-30): start
from the given nonzero `q`-torsion point and divide by `q` repeatedly, which
`WeierstrassCurve.zsmul_surjective_algClosed` permits.  Dividing raises the order
by exactly one factor of `q`: `q^{k+2} • Q = q^{k+1} • P = 0` bounds it above,
and `q^{k+1} • Q = q^k • P ≠ 0` bounds it below. -/
theorem exists_addOrderOf_eq_qPow (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic]
    (hord : ∃ R : (Wbar⁄(AlgebraicClosure (ZMod q))).Point, R ≠ 0 ∧ (q : ℤ) • R = 0) :
    ∀ k : ℕ, ∃ P : (Wbar⁄(AlgebraicClosure (ZMod q))).Point, addOrderOf P = q ^ (k + 1) := by
  have hqpos : (0 : ℤ) < (q : ℤ) := by exact_mod_cast (Fact.out : q.Prime).pos
  intro k
  induction k with
  | zero =>
    obtain ⟨R, hR0, hRq⟩ := hord
    refine ⟨R, ?_⟩
    have hdvd : (addOrderOf R : ℤ) ∣ ((q : ℕ) : ℤ) :=
      addOrderOf_dvd_iff_zsmul_eq_zero.mpr hRq
    rcases (Fact.out : q.Prime).eq_one_or_self_of_dvd _
      (Int.natCast_dvd_natCast.mp hdvd) with h | h
    · refine absurd ?_ hR0
      have h1 : (1 : ℤ) • R = 0 :=
        addOrderOf_dvd_iff_zsmul_eq_zero.mp (by rw [h]; exact one_dvd _)
      rwa [one_zsmul] at h1
    · rw [h, pow_one]
  | succ k ih =>
    obtain ⟨P, hP⟩ := ih
    obtain ⟨Q, hQ⟩ := surjective_zsmul_one q Wbar (d := (q : ℤ)) hqpos.ne' P
    have hQP : (q : ℤ) • Q = P := hQ
    refine ⟨Q, ?_⟩
    have hkill : ((q : ℤ) ^ (k + 2)) • Q = 0 := by
      rw [show ((q : ℤ) ^ (k + 2)) = (q : ℤ) ^ (k + 1) * (q : ℤ) by ring, mul_smul, hQP]
      exact addOrderOf_dvd_iff_zsmul_eq_zero.mp (by rw [hP]; push_cast; exact dvd_rfl)
    have hcast : ∀ j : ℕ, ((q : ℤ) ^ j) = ((q ^ j : ℕ) : ℤ) := by
      intro j; push_cast; ring
    have hdvd : addOrderOf Q ∣ q ^ (k + 2) := by
      have h := addOrderOf_dvd_iff_zsmul_eq_zero.mpr hkill
      rw [hcast] at h
      exact_mod_cast h
    have hne : ¬ (addOrderOf Q ∣ q ^ (k + 1)) := by
      intro hcon
      have h0 : ((q : ℤ) ^ (k + 1)) • Q = 0 := by
        refine addOrderOf_dvd_iff_zsmul_eq_zero.mp ?_
        rw [hcast]
        exact_mod_cast hcon
      have h1 : ((q : ℤ) ^ k) • P = 0 := by
        rw [← hQP, smul_smul, ← pow_succ]
        exact h0
      have h2 : addOrderOf P ∣ q ^ k := by
        have h := addOrderOf_dvd_iff_zsmul_eq_zero.mpr h1
        rw [hcast] at h
        exact_mod_cast h
      rw [hP] at h2
      have hlt := (Nat.pow_dvd_pow_iff_le_right (Fact.out : q.Prime).one_lt).mp h2
      omega
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow (Fact.out : q.Prime)).mp hdvd
    rcases Nat.lt_or_ge j (k + 2) with hlt | hge
    · exact absurd (hjeq ▸ pow_dvd_pow q (by omega)) hne
    · rw [hjeq, show j = k + 2 by omega]

/-- **`E[q^k]` is CYCLIC, generated by any point of order `q^k`** (PROVEN
2026-07-30): the subgroup generated by such a point sits inside `E[q^k]` and has
the same cardinality `q^k`, so it is all of it.  No structure theorem for finite
abelian groups is needed — the count does the work. -/
theorem exists_zsmul_eq_of_qPow_zsmul_eq_zero (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic]
    (hord : ∃ R : (Wbar⁄(AlgebraicClosure (ZMod q))).Point, R ≠ 0 ∧ (q : ℤ) • R = 0)
    (k : ℕ) {P₀ : (Wbar⁄(AlgebraicClosure (ZMod q))).Point}
    (hP₀ : addOrderOf P₀ = q ^ k)
    (Z : (Wbar⁄(AlgebraicClosure (ZMod q))).Point) (hZ : ((q : ℤ) ^ k) • Z = 0) :
    ∃ m : ℤ, Z = m • P₀ := by
  classical
  have hcast : ((q : ℤ) ^ k) = ((q ^ k : ℕ) : ℤ) := by push_cast; ring
  have hmemP₀ : ((q : ℤ) ^ k) • P₀ = 0 := by
    refine addOrderOf_dvd_iff_zsmul_eq_zero.mp ?_
    rw [hcast, hP₀]
  set K : Submodule ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point) :=
    LinearMap.ker (((q : ℤ) ^ k)
      • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point))) with hK
  have hcardK : Nat.card K = q ^ k := natCard_ker_zsmul_q_pow_of_ordinary q Wbar hord k
  have hcardH : Nat.card (AddSubgroup.zmultiples P₀) = q ^ k := by
    rw [Nat.card_zmultiples, hP₀]
  have hsub : (AddSubgroup.zmultiples P₀ : Set ((Wbar⁄(AlgebraicClosure (ZMod q))).Point))
      ⊆ (K : Set ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)) := by
    intro Y hY
    rw [SetLike.mem_coe, AddSubgroup.mem_zmultiples_iff] at hY
    obtain ⟨m, rfl⟩ := hY
    rw [SetLike.mem_coe, hK, ker_zsmul_one, Submodule.mem_torsionBy_iff, smul_comm, hmemP₀]
    exact zsmul_zero _
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hcardK]; exact pow_ne_zero _ (Fact.out : q.Prime).pos.ne')
  have hfin : (K : Set ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)).Finite :=
    Set.finite_coe_iff.mp inferInstance
  have hle : (K : Set ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)).ncard
      ≤ (AddSubgroup.zmultiples P₀
          : Set ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)).ncard := by
    simp only [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hcardK, hcardH]
    exact le_rfl
  have heq := Set.eq_of_subset_of_ncard_le hsub hle hfin
  have hmem : Z ∈ (K : Set ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)) := by
    rw [SetLike.mem_coe, hK, ker_zsmul_one, Submodule.mem_torsionBy_iff]
    exact hZ
  rw [← heq, SetLike.mem_coe, AddSubgroup.mem_zmultiples_iff] at hmem
  obtain ⟨m, hm⟩ := hmem
  exact ⟨m, hm.symm⟩

/-- **`F` acts on `E[q^k]` by ONE integer** (PROVEN 2026-07-30): `E[q^k]` is
cyclic, generated by a point `P₀` of order `q^k`, and `F P₀` lies in `E[q^k]`
because `F` is additive; write `F P₀ = ε • P₀` and every other point of `E[q^k]`
is a multiple of `P₀`.

This is what turns the surviving `q`-primary leaf into a divisibility in `ℤ`. -/
theorem exists_zsmul_eq_frobeniusPointEnd_qPow (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic]
    (hord : ∃ R : (Wbar⁄(AlgebraicClosure (ZMod q))).Point, R ≠ 0 ∧ (q : ℤ) • R = 0)
    (k : ℕ) :
    ∃ ε : ℤ, ∀ P : (Wbar⁄(AlgebraicClosure (ZMod q))).Point, ((q : ℤ) ^ k) • P = 0 →
      frobeniusPointEnd q Wbar P = ε • P := by
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : (Wbar⁄(AlgebraicClosure (ZMod q))).Point,
      addOrderOf P₀ = q ^ k := by
    cases k with
    | zero => exact ⟨0, by simp⟩
    | succ k => exact exists_addOrderOf_eq_qPow q Wbar hord k
  have hcast : ((q : ℤ) ^ k) = ((q ^ k : ℕ) : ℤ) := by push_cast; ring
  have hmemP₀ : ((q : ℤ) ^ k) • P₀ = 0 := by
    refine addOrderOf_dvd_iff_zsmul_eq_zero.mp ?_
    rw [hcast, hP₀]
  have hFP₀ : ((q : ℤ) ^ k) • frobeniusPointEnd q Wbar P₀ = 0 := by
    rw [← map_zsmul, hmemP₀, map_zero]
  obtain ⟨ε, hε⟩ := exists_zsmul_eq_of_qPow_zsmul_eq_zero q Wbar hord k hP₀ _ hFP₀
  refine ⟨ε, fun P hP => ?_⟩
  obtain ⟨m, rfl⟩ := exists_zsmul_eq_of_qPow_zsmul_eq_zero q Wbar hord k hP₀ P hP
  rw [map_zsmul, hε, smul_comm]

/-- **The UNIT-ROOT congruence** (opened as a sorry leaf 2026-07-30 and PROVEN the
same day over `sq_frobeniusPointEnd_of_prime_to_char`; Silverman *AEC* V.3.1,
Deuring): the integer by which the Frobenius acts on `E[q^k]` is a root of
`X² − c·X + q` modulo `q^k`.

WHAT PROVES IT, AND WHY THE OLD ROUTE NOTE WAS LOOKING IN THE WRONG PLACE.  The
note this docstring replaces said "a proof must use the GEOMETRY — classically the
Verschiebung `V ∘ F = [q]`, or Deuring's congruence".  The first half is right and
the list is wrong: the geometry that settles it is
`WeierstrassCurve.IsIsogeny.finite_ker`, i.e. that a nonzero isogeny has finite
kernel, and `sq_frobeniusPointEnd_of_prime_to_char` above turns that into
`F² = c·F − q` on EVERY point directly from `hc`.  Neither a Verschiebung nor a
Hasse invariant is needed.

Given that, this leaf is three lines: take `P₀` of order exactly `q^k`
(`exists_addOrderOf_eq_qPow`, `k ≥ 1`), and `F P₀ = ε • P₀` gives
`F(F P₀) = ε² • P₀` while the characteristic equation gives
`(c·ε − q) • P₀`, so `(ε² − c·ε + q) • P₀ = 0` and the order of `P₀` divides the
coefficient.  At `k = 0` the statement is `1 ∣ _`.

WHAT THE OLD ANALYSIS GOT RIGHT, kept because it is the reason the statement is
shaped this way.  In the ordinary case `Wbar(𝔽̄_q)[q^∞] ≅ ℚ_q/ℤ_q`, on which `F`
acts by the UNIT ROOT `α ∈ ℤ_q^×` of `X² − c·X + q` — the other root has
valuation `1` and cannot act invertibly there.  `E[q^k]` is the `q^k`-torsion of
that, so `ε ≡ α (mod q^k)`, which is exactly the conclusion.

BOTH HYPOTHESES ARE STILL LOAD-BEARING.

* `hc` pins `c`.  It is the unique integer with that property: two solutions
  differ by an integer annihilating `F`'s image, i.e. all of `Wbar(𝔽̄_q)`, which
  has points of order `n` for every `q ∤ n` (`TorsionCard.card_torsionBy`).  Drop
  it and `c` is free, so the conclusion fails at `k = 1` for all but one residue.
* `hord` is what makes `ε` mean anything.  Without it `E[q^k] = 0`, every `ε`
  satisfies `hε` vacuously, and no divisibility can hold for all of them.  It is
  also what supplies the point of exact order `q^k` that the proof evaluates at.

A NOTE FOR A CLEANUP PASS, since this statement is now REDUNDANT rather than
wrong.  `sq_frobeniusPointEnd_of_prime_to_char` proves
`sq_frobeniusPointEnd_qPrimary` outright, so the chain
`_qPrimary ← _qPrimary_ordinary ← this ← exists_zsmul_eq_frobeniusPointEnd_qPow`
could be collapsed to one line.  It is deliberately NOT collapsed here: doing so
would leave `eq_zero_of_qPow_zsmul_eq_zero`,
`exists_zsmul_eq_of_qPow_zsmul_eq_zero`,
`exists_zsmul_eq_frobeniusPointEnd_qPow` and
`sq_frobeniusPointEnd_qPrimary_ordinary` — about 350 lines of proven ordinary
`q`-primary structure theory, including the CYCLICITY of `E[q^k]` — free-floating
and therefore due for deletion, and that material is the natural input to a future
attack on `exists_ne_zero_qTorsion`.  Whoever decides it is not, can collapse the
chain and delete those four; the frontier does not change either way. -/
theorem sq_frobeniusPointEnd_qPrimary_unitRoot (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] {c : ℤ}
    (hc : ∀ n : ℕ, ¬ (q ∣ n) →
      ∀ P : (Wbar⁄(AlgebraicClosure (ZMod q))).Point, (n : ℤ) • P = 0 →
        frobeniusPointEnd q Wbar (frobeniusPointEnd q Wbar P)
          = c • frobeniusPointEnd q Wbar P - (q : ℤ) • P)
    (hord : ∃ R : (Wbar⁄(AlgebraicClosure (ZMod q))).Point, R ≠ 0 ∧ (q : ℤ) • R = 0)
    (k : ℕ) (ε : ℤ)
    (hε : ∀ P : (Wbar⁄(AlgebraicClosure (ZMod q))).Point, ((q : ℤ) ^ k) • P = 0 →
      frobeniusPointEnd q Wbar P = ε • P) :
    ((q : ℤ) ^ k) ∣ ε ^ 2 - c * ε + (q : ℤ) := by
  cases k with
  | zero => simp
  | succ j =>
    obtain ⟨P₀, hP₀⟩ := exists_addOrderOf_eq_qPow q Wbar hord j
    have hcast : ((q : ℤ) ^ (j + 1)) = ((q ^ (j + 1) : ℕ) : ℤ) := by push_cast; ring
    have hmem : ((q : ℤ) ^ (j + 1)) • P₀ = 0 := by
      refine addOrderOf_dvd_iff_zsmul_eq_zero.mp ?_
      rw [hcast, hP₀]
    have hF := hε P₀ hmem
    have hFF := sq_frobeniusPointEnd_of_prime_to_char q Wbar hc P₀
    rw [hF, map_zsmul, hF] at hFF
    have hzero : (ε ^ 2 - c * ε + (q : ℤ)) • P₀ = 0 := by
      linear_combination (norm := module) hFF
    have hdvd := addOrderOf_dvd_iff_zsmul_eq_zero.mpr hzero
    rw [hP₀] at hdvd
    rwa [hcast]

/-- **The characteristic equation on the `q`-primary torsion, ORDINARY case**
(PROVEN 2026-07-30 over `sq_frobeniusPointEnd_qPrimary_unitRoot` and
`exists_zsmul_eq_frobeniusPointEnd_qPow`).

`F` acts on `E[q^k]` as multiplication by a single integer `ε`, so
`F(F P) = ε²·P` and `c·F P − q·P = (c·ε − q)·P`; the two agree exactly when
`(ε² − c·ε + q)·P = 0`, which the unit-root congruence supplies. -/
theorem sq_frobeniusPointEnd_qPrimary_ordinary (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] {c : ℤ}
    (hc : ∀ n : ℕ, ¬ (q ∣ n) →
      ∀ P : (Wbar⁄(AlgebraicClosure (ZMod q))).Point, (n : ℤ) • P = 0 →
        frobeniusPointEnd q Wbar (frobeniusPointEnd q Wbar P)
          = c • frobeniusPointEnd q Wbar P - (q : ℤ) • P)
    (hord : ∃ R : (Wbar⁄(AlgebraicClosure (ZMod q))).Point, R ≠ 0 ∧ (q : ℤ) • R = 0)
    (k : ℕ) (P : (Wbar⁄(AlgebraicClosure (ZMod q))).Point)
    (hP : ((q : ℤ) ^ k) • P = 0) :
    frobeniusPointEnd q Wbar (frobeniusPointEnd q Wbar P)
      = c • frobeniusPointEnd q Wbar P - (q : ℤ) • P := by
  obtain ⟨ε, hε⟩ := exists_zsmul_eq_frobeniusPointEnd_qPow q Wbar hord k
  obtain ⟨t, ht⟩ := sq_frobeniusPointEnd_qPrimary_unitRoot q Wbar hc hord k ε hε
  have h1 : frobeniusPointEnd q Wbar P = ε • P := hε P hP
  have h2 : frobeniusPointEnd q Wbar (frobeniusPointEnd q Wbar P) = (ε * ε) • P := by
    rw [h1, map_zsmul, h1, smul_smul]
  have h0 : (ε * ε) • P - (c * ε) • P + (q : ℤ) • P = 0 := by
    rw [← sub_smul, ← add_smul,
      show ε * ε - c * ε + (q : ℤ) = t * ((q : ℤ) ^ k) by linear_combination ht,
      mul_smul, hP]
    exact zsmul_zero _
  rw [h2, h1, smul_smul]
  refine eq_of_sub_eq_zero ?_
  rw [show (ε * ε) • P - ((c * ε) • P - (q : ℤ) • P)
      = (ε * ε) • P - (c * ε) • P + (q : ℤ) • P by abel]
  exact h0

/-- **The characteristic equation on the `q`-primary torsion** (PROVEN
2026-07-30 over `sq_frobeniusPointEnd_qPrimary_ordinary` and
`eq_zero_of_qPow_zsmul_eq_zero`): the SAME coefficient `c` that works away from
`q` also works on the `q`-power torsion.

The dichotomy is a `by_cases` on whether `E[q]` is trivial.  If it is —
the SUPERSINGULAR branch — then `E[q^∞]` is trivial too, so `hP` forces `P = 0`
and the conclusion is `hc` at `n = 1`.  If it is not, the ordinary leaf
applies. -/
theorem sq_frobeniusPointEnd_qPrimary (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] {c : ℤ}
    (hc : ∀ n : ℕ, ¬ (q ∣ n) →
      ∀ P : (Wbar⁄(AlgebraicClosure (ZMod q))).Point, (n : ℤ) • P = 0 →
        frobeniusPointEnd q Wbar (frobeniusPointEnd q Wbar P)
          = c • frobeniusPointEnd q Wbar P - (q : ℤ) • P)
    (k : ℕ) (P : (Wbar⁄(AlgebraicClosure (ZMod q))).Point)
    (hP : ((q : ℤ) ^ k) • P = 0) :
    frobeniusPointEnd q Wbar (frobeniusPointEnd q Wbar P)
      = c • frobeniusPointEnd q Wbar P - (q : ℤ) • P := by
  by_cases hss : ∀ R : (Wbar⁄(AlgebraicClosure (ZMod q))).Point, (q : ℤ) • R = 0 → R = 0
  · have hP0 : P = 0 := eq_zero_of_qPow_zsmul_eq_zero q Wbar hss k P hP
    refine hc 1 (fun h => (Fact.out : q.Prime).one_lt.ne' (Nat.dvd_one.mp h)) P ?_
    rw [hP0]
    exact zsmul_zero _
  · push Not at hss
    obtain ⟨R, hR2, hR1⟩ := hss
    exact sq_frobeniusPointEnd_qPrimary_ordinary q Wbar hc ⟨R, hR1, hR2⟩ k P hP

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
(PROVEN 2026-07-28 over `exists_pos_nsmul_eq_zero`,
`exists_sq_frobeniusPointEnd_prime_to_char` and `sq_frobeniusPointEnd_qPrimary`;
Silverman *AEC* V.2.3.1): there is an integer `c` with `F² = c·F − q` in
`Module.End ℤ (Wbar(𝔽̄_q))`.

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

ROUTE, AND IT IS THE ONE TAKEN (the cut of 2026-07-28).  `Wbar(𝔽̄_q)` is a
TORSION group — every point is defined over some finite subfield — so an
identity in `End` may be checked one torsion-primary piece at a time.  That is
`exists_pos_nsmul_eq_zero`, now PROVEN, and it is what this declaration's proof
runs on: writing the order of `P` as `q^k · m` with `q ∤ m` and using a Bézout
relation splits `P = P₂ + P₁` with `m • P₂ = 0` and `q^k • P₁ = 0`, and the two
summands are handled by the two leaves.  The identity is additive in `P`, so
that is the whole assembly.

The prime-to-`q` half is the `ℓ`-adic one: for `ℓ ≠ q` the module `E[ℓ^k]` is
free of rank `2` over `ZMod (ℓ^k)` (`WeierstrassCurve.p_torsion_rank`,
`Torsion.lean`, which needs only `(ℓ : 𝔽̄_q) ≠ 0` and *no* characteristic-zero
hypothesis), and Cayley–Hamilton for a `2 × 2` matrix gives
`F² = tr(F)·F − det(F)` there; the arithmetic input is `det(F | E[ℓ^k]) = q`
(the Weil pairing) and the INTEGRALITY of `tr`.  The `q`-primary half is
separate and is the ordinary/supersingular dichotomy.  See the two leaves for
what each of them still owes.

THE CHECK THAT WOULD REFUTE the claim that this is the cheapest route: a proof
of `F² − cF + q = 0` that does not pass through a torsion representation — the
classical alternative is the dual isogeny, and the dual is machine-refuted in
characteristic `p` in `Isogeny.lean` (`Isogeny.NotIsRationalMapDualHom`), so it
is unavailable. -/
theorem exists_sq_frobeniusPointEnd (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] :
    ∃ c : ℤ, frobeniusPointEnd q Wbar * frobeniusPointEnd q Wbar
      = c • frobeniusPointEnd q Wbar
        - (q : ℤ) • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)) := by
  obtain ⟨c, hc⟩ := exists_sq_frobeniusPointEnd_prime_to_char q Wbar
  refine ⟨c, ?_⟩
  have key : ∀ P : (Wbar⁄(AlgebraicClosure (ZMod q))).Point,
      frobeniusPointEnd q Wbar (frobeniusPointEnd q Wbar P)
        = c • frobeniusPointEnd q Wbar P - (q : ℤ) • P := by
    intro P
    obtain ⟨n, hnpos, hn⟩ := exists_pos_nsmul_eq_zero q Wbar P
    obtain ⟨k, m, hmq, hnk⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd hnpos.ne' q (Fact.out : q.Prime).ne_one
    have hcop : Nat.Coprime (q ^ k) m :=
      Nat.Coprime.pow_left k (((Fact.out : q.Prime).coprime_iff_not_dvd).mpr hmq)
    obtain ⟨a, b, hab⟩ : IsCoprime ((q ^ k : ℕ) : ℤ) ((m : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr hcop
    set P₁ : (Wbar⁄(AlgebraicClosure (ZMod q))).Point := (b * (m : ℤ)) • P with hP₁
    set P₂ : (Wbar⁄(AlgebraicClosure (ZMod q))).Point := (a * ((q ^ k : ℕ) : ℤ)) • P with hP₂
    have hnz : ((q ^ k : ℕ) : ℤ) * ((m : ℕ) : ℤ) = (n : ℤ) := by
      rw [← Nat.cast_mul, ← hnk]
    have h1 : ((q : ℤ) ^ k) • P₁ = 0 := by
      rw [hP₁, smul_smul]
      have hb : (q : ℤ) ^ k * (b * (m : ℤ)) = b * ((n : ℤ)) := by
        rw [← hnz]; push_cast; ring
      rw [hb, ← smul_smul, hn]
      exact zsmul_zero _
    have h2 : ((m : ℕ) : ℤ) • P₂ = 0 := by
      rw [hP₂, smul_smul]
      have ha : ((m : ℕ) : ℤ) * (a * ((q ^ k : ℕ) : ℤ)) = a * ((n : ℤ)) := by
        rw [← hnz]; ring
      rw [ha, ← smul_smul, hn]
      exact zsmul_zero _
    have hsplit : P = P₂ + P₁ := by
      rw [hP₁, hP₂]
      match_scalars
      push_cast at hab ⊢
      linarith
    have e1 := hc m hmq P₂ h2
    have e2 := sq_frobeniusPointEnd_qPrimary q Wbar hc k P₁ h1
    rw [hsplit, map_add, map_add, e1, e2]
    module
  refine LinearMap.ext fun P => ?_
  simpa only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply] using key P

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

/-! ### NINTH CUT, 2026-07-31: the degree form never vanishes off the origin

`degreeForm_ne_zero` below proves `m² − c·m·n + n²q ≠ 0` for every
`(m, n) ≠ (0, 0)`, equivalently that `X² − c·X + q` has NO rational root,
equivalently that `c² − 4q` is not a perfect square.  It is exactly the
"degenerate case `d = 0`" that the ROUTE UPDATE on
`natCard_ker_degreeFormEnd_le` below named as the second piece of work a re-cut
would have to write, and it is what removes that leaf from the `d = 0` branch of
`natCard_ker_degreeFormEnd_of_dvd`.

**THE LOAD-BEARING STEP IS NOT ELEMENTARY, and the sketch that leaf carried
skipped it.**  That sketch reads: `d = 0` forces an integer root, so
`(F ∓ 1)(F ∓ q) = 0` "with both factors of finite kernel — a contradiction,
since `Wbar(𝔽̄_q)` is infinite".  The outline is right, but *both factors of
finite kernel* is the whole difficulty: `IsIsogeny.finite_ker` gives it only for
a NONZERO isogeny, and `F − [q] ≠ 0` — i.e. that the `q`-power Frobenius is not
multiplication by the integer `q` — is not visible to any counting argument in
this file.  (`#ker F = 1` is consistent with `F = [q]`: that is the supersingular
case, where `E[q] = 0`.)

What supplies it is the WEIL PAIRING, through `frobeniusPointEnd_ne_zsmul`:
`det(F | Wbar[p]) = q` for every prime `p ≠ q`
(`WeilPairing.det_frobeniusTorsionEnd`), while `[r]` acts on the rank-two
`Wbar[p]` with determinant `r²`.  So `p ∣ r² − q` for EVERY prime `p ≠ q`, which
forces `r² = q` and contradicts primality of `q`.  Note this is a case where the
determinant DOES decide something, contrary to the general steer of the audits
below: those say a determinant cannot see the SIGN of `d`, which is true; here it
is being used to see that `F` is not a scalar, which is a statement `|d|` can
carry.

The composite is then killed without any finiteness bookkeeping at all: two
nonzero isogenies are each SURJECTIVE (`IsIsogeny.surjective`), so their
composite is surjective, and a surjective map onto a group with a nonzero point
is not `0`.

WHAT THIS DOES NOT DO, stated so it is not mistaken for progress on Hasse.  It
rules out `c² − 4q` being a SQUARE; it says nothing about its SIGN, which is the
whole of `natCard_ker_degreeFormEnd_le` and of Hasse's bound.  Concretely it
kills the case `c = ±(q + 1)` (where `X² − cX + q = (X ∓ 1)(X ∓ q)`) and leaves
every non-square positive discriminant standing.

A ROUTE THAT THIS OPENS, and it is NOT refuted by the counter-model `A` of the
audit on `natCard_ker_degreeFormEnd_le` — recorded because that audit's claim
that "no rearrangement of the `ℤ[F]` material in this file … can close this leaf"
is about `ℤ[F]`-only reasoning, and this route leaves `ℤ[F]`:

> Suppose `c² − 4q > 0`.  It is not a square (this section), so `ℤ[α]` with
> `α² = cα − q` is an order in a REAL quadratic field, and PELL
> (`Pell.exists_of_not_isSquare`, mathlib) supplies a unit `u = M + N·α` of norm
> `1` with `N ≠ 0`, hence integers `(M, N)` with
> `M² + c·M·N + N²q = 1`.  Then `ψ := [M] + [N]∘F` satisfies
> `ψ ∘ ψ′ = ψ′ ∘ ψ = [1]` by `degreeFormEnd_mul_conj`/`conj_mul_degreeFormEnd`,
> so `ψ` is INVERTIBLE in `WeierstrassCurve.End`, and so are all its powers
> `ψ^k = [M_k] + [N_k]∘F` with `N_k ≠ 0`.  If `ψ` had FINITE ORDER, say
> `ψ^k = 1`, then `[M_k − 1] + [N_k]∘F = 0`, whose degree-form value is nonzero
> by this section — and a `degreeFormEnd` with nonzero form value is not `0`,
> since `ψ ∘ ψ′ = [d]` and `Wbar(𝔽̄_q)` has points of order exceeding `|d|`.
> Contradiction.  So the ONE missing atom is:
>
>   **an isogeny that is invertible in `WeierstrassCurve.End` has finite
>   multiplicative order.**
>
> That is Aut-finiteness, and it is exactly what the counter-model `A` fails:
> in `A = ⨁_{ℓ ≠ q}(ℚ_ℓ/ℤ_ℓ)²` the companion matrix generates an INFINITE unit
> group, which is why `A` interprets every identity in this file and still
> violates Hasse.  So Aut-finiteness is a genuine escape from `A`, not another
> `ℤ[F]` rearrangement.  `EllipticCurve/AutomorphismExponent.lean` already proves
> the group-theoretic half — the stabiliser of `W` in
> `WeierstrassCurve.VariableChange` has exponent dividing `12` — so what is
> missing is the bridge "an invertible endomorphism of `(W, O)` comes from a
> variable change" (Silverman *AEC* III.3.1(b)).  That bridge is a real piece of
> work and it is a statement about COORDINATES, not about degrees, so it does not
> re-import the degree theory the audits below say this tree lacks.
-/

/-- **`Wbar(𝔽̄_q)` has a nonzero point** (PROVEN 2026-07-31): otherwise the
`(q+1)`-torsion would have one element instead of `(q+1)²`
(`TorsionCard.card_torsionBy`). -/
theorem exists_point_ne_zero (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] :
    ∃ P : (Wbar⁄(AlgebraicClosure (ZMod q))).Point, P ≠ 0 := by
  classical
  by_contra hcon
  have hzero : ∀ P : (Wbar⁄(AlgebraicClosure (ZMod q))).Point, P = 0 := by
    intro P
    by_contra hP
    exact hcon ⟨P, hP⟩
  haveI : CharP (AlgebraicClosure (ZMod q)) q :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))).injective q
  have hqn : ¬ (q ∣ (q + 1)) := by
    intro hdvd
    have h2 : q ∣ 1 := (Nat.dvd_add_right (dvd_refl q)).mp hdvd
    exact (Fact.out : q.Prime).one_lt.ne' (Nat.dvd_one.mp h2)
  have hn0 : (((q + 1 : ℕ)) : AlgebraicClosure (ZMod q)) ≠ 0 := fun h0 =>
    hqn ((CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod q)) q (q + 1)).mp h0)
  have hcard : Nat.card (Submodule.torsionBy ℤ
      (Wbar⁄(AlgebraicClosure (ZMod q))).Point (((q + 1 : ℕ) : ℤ))) = (q + 1) ^ 2 :=
    TorsionCard.card_torsionBy
      (Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))) (q + 1) hn0
  haveI hsub : Subsingleton ((Wbar⁄(AlgebraicClosure (ZMod q))).Point) :=
    ⟨fun a b => by rw [hzero a, hzero b]⟩
  have hone : Nat.card (Submodule.torsionBy ℤ
      (Wbar⁄(AlgebraicClosure (ZMod q))).Point (((q + 1 : ℕ) : ℤ))) = 1 := by
    haveI : Subsingleton (Submodule.torsionBy ℤ
        (Wbar⁄(AlgebraicClosure (ZMod q))).Point (((q + 1 : ℕ) : ℤ))) :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨0⟩⟩
  rw [hone] at hcard
  have h2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  nlinarith [hcard]

/-- **The Frobenius is not multiplication by an integer** (PROVEN 2026-07-31):
for every `r : ℤ` there is a point of `Wbar(𝔽̄_q)` with `F P ≠ r • P`.

This is the one place in this module where the Weil-pairing determinant decides
something, and the mechanism is worth stating because the audits below rightly
warn that a determinant cannot see the sign of the degree form:
`det(F | Wbar[p]) = q` for every prime `p ≠ q`
(`WeilPairing.det_frobeniusTorsionEnd`), whereas `[r]` acts on the rank-two
`Wbar[p]` (`WeierstrassCurve.p_torsion_rank`) with determinant `r²`.  So
`p ∣ r² − q` for EVERY prime `p ≠ q`, and taking `p` larger than
`|r² − q|` forces `r² = q`, contradicting primality of `q`.

The counting facts of this file do NOT give it: `#ker F = 1`
(`natCard_ker_frobeniusPointEnd`) is perfectly consistent with `F = [q]`, which
is the supersingular case `E[q] = 0`. -/
theorem frobeniusPointEnd_ne_zsmul (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] (r : ℤ) :
    ¬ (∀ P : (Wbar⁄(AlgebraicClosure (ZMod q))).Point,
        frobeniusPointEnd q Wbar P = r • P) := by
  intro h
  have key : ∀ p : ℕ, p.Prime → p ≠ q → ((p : ℤ) ∣ r ^ 2 - (q : ℤ)) := by
    intro p hp hpq
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : CharP (AlgebraicClosure (ZMod q)) q :=
      charP_of_injective_algebraMap
        (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))).injective q
    have hpk : ((p : ℕ) : AlgebraicClosure (ZMod q)) ≠ 0 := by
      intro hz
      have h1 : q ∣ p := (CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod q)) q p).mp hz
      rcases (Nat.Prime.eq_one_or_self_of_dvd hp q h1) with h2 | h2
      · exact (Fact.out : q.Prime).one_lt.ne' h2
      · exact hpq h2.symm
    have hrank := WeierstrassCurve.p_torsion_rank
      (Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))) hpk
    have hfr : Module.finrank (ZMod p)
        ((Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).nTorsion p) = 2 :=
      Module.finrank_eq_of_rank_eq (by rw [hrank]; norm_num)
    have hres : WeilPairing.frobeniusTorsionEnd q Wbar p
        = (r : ZMod p) • (1 : Module.End (ZMod p)
            ((Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).nTorsion p)) := by
      refine LinearMap.ext fun x => ?_
      have hr : ((r : ZMod p) • (1 : Module.End (ZMod p)
          ((Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).nTorsion p))) x
          = r • x := by
        rw [LinearMap.smul_apply, Module.End.one_apply, Int.cast_smul_eq_zsmul]
      rw [hr]
      refine Subtype.ext ?_
      show _ = ((r • x.1 : (Wbar⁄(AlgebraicClosure (ZMod q))).Point))
      exact h x.1
    have hdet := WeilPairing.det_frobeniusTorsionEnd q Wbar p (Ne.symm hpq)
    rw [hres, LinearMap.det_smul, Module.End.one_eq_id, LinearMap.det_id, hfr,
      mul_one] at hdet
    have hz : ((r ^ 2 - (q : ℤ) : ℤ) : ZMod p) = 0 := by
      push_cast
      rw [hdet]
      ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes ((r ^ 2 - (q : ℤ)).natAbs + q + 1)
  have hpq : p ≠ q := by omega
  have hdvd := key p hp hpq
  have hzero : r ^ 2 - (q : ℤ) = 0 := by
    by_contra hne
    have h1 : (p : ℤ) ≤ |r ^ 2 - (q : ℤ)| :=
      Int.le_of_dvd (abs_pos.mpr hne) ((dvd_abs _ _).mpr hdvd)
    rw [Int.abs_eq_natAbs] at h1
    omega
  have hq : (r.natAbs) ^ 2 = q := by
    have h3 : ((r.natAbs : ℕ) : ℤ) ^ 2 = ((q : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs, sq_abs]; omega
    exact_mod_cast h3
  have hd : r.natAbs ∣ q := ⟨r.natAbs, by rw [← hq]; ring⟩
  have h2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  rcases (Fact.out : q.Prime).eq_one_or_self_of_dvd _ hd with h1 | h1
  · rw [h1] at hq; omega
  · rw [h1] at hq; nlinarith [hq]

/-- **The Frobenius characteristic polynomial does not split over `ℤ`** (PROVEN
2026-07-31): if `X² − c·X + q = (X − r)(X − r′)` with `r, r′ : ℤ`, then `hc`
factors as `(F − [r]) ∘ (F − [r′]) = 0`.  Both factors are NONZERO
(`frobeniusPointEnd_ne_zsmul`) isogenies, hence SURJECTIVE
(`IsIsogeny.surjective`), so their composite is surjective — while it is `0`,
and `Wbar(𝔽̄_q)` has a nonzero point.

No finiteness bookkeeping is needed: surjectivity of the two factors is what
does the work, and it is free from `IsIsogeny`. -/
theorem not_split_charEquation (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] {c : ℤ}
    (hc : frobeniusPointEnd q Wbar * frobeniusPointEnd q Wbar
      = c • frobeniusPointEnd q Wbar
        - (q : ℤ) • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)))
    {r r' : ℤ} (hsum : r + r' = c) (hprod : r * r' = (q : ℤ)) : False := by
  haveI hell : ((Wbar⁄(AlgebraicClosure (ZMod q))).toAffine).IsElliptic :=
    inferInstanceAs (Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).IsElliptic
  set f : WeierstrassCurve.End ((Wbar⁄(AlgebraicClosure (ZMod q))).toAffine) :=
    ⟨(frobeniusPointEnd q Wbar).toAddMonoidHom, isIsogeny_frobeniusPointEnd q Wbar⟩ with hf
  set g₁ : WeierstrassCurve.End ((Wbar⁄(AlgebraicClosure (ZMod q))).toAffine) :=
    f - Int.cast r with hg₁
  set g₂ : WeierstrassCurve.End ((Wbar⁄(AlgebraicClosure (ZMod q))).toAffine) :=
    f - Int.cast r' with hg₂
  have hg₁app : ∀ P : (Wbar⁄(AlgebraicClosure (ZMod q))).Point,
      (g₁ : AddMonoid.End _) P = frobeniusPointEnd q Wbar P - r • P := fun _ => rfl
  have hg₂app : ∀ P : (Wbar⁄(AlgebraicClosure (ZMod q))).Point,
      (g₂ : AddMonoid.End _) P = frobeniusPointEnd q Wbar P - r' • P := fun _ => rfl
  have hne₁ : (g₁ : AddMonoid.End ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)) ≠ 0 := by
    intro h0
    refine frobeniusPointEnd_ne_zsmul q Wbar r fun P => ?_
    have hP := hg₁app P
    rw [h0] at hP
    have h1 : (0 : AddMonoid.End ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)) P = 0 := rfl
    rw [h1] at hP
    linear_combination (norm := abel) -hP
  have hne₂ : (g₂ : AddMonoid.End ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)) ≠ 0 := by
    intro h0
    refine frobeniusPointEnd_ne_zsmul q Wbar r' fun P => ?_
    have hP := hg₂app P
    rw [h0] at hP
    have h1 : (0 : AddMonoid.End ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)) P = 0 := rfl
    rw [h1] at hP
    linear_combination (norm := abel) -hP
  have hmulapp : ∀ P : (Wbar⁄(AlgebraicClosure (ZMod q))).Point,
      ((g₁ * g₂ : WeierstrassCurve.End _) : AddMonoid.End _) P
        = (g₁ : AddMonoid.End _) ((g₂ : AddMonoid.End _) P) := fun _ => rfl
  have hcomp : ∀ P : (Wbar⁄(AlgebraicClosure (ZMod q))).Point,
      ((g₁ * g₂ : WeierstrassCurve.End _) : AddMonoid.End _) P = 0 := by
    intro P
    have happ : ((g₁ * g₂ : WeierstrassCurve.End _) : AddMonoid.End _) P
        = (g₁ : AddMonoid.End _) ((g₂ : AddMonoid.End _) P) := rfl
    have hcP : frobeniusPointEnd q Wbar (frobeniusPointEnd q Wbar P)
        = (r + r') • frobeniusPointEnd q Wbar P - (r * r') • P := by
      rw [hsum, hprod]
      exact congrArg
        (fun e : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point) => e P) hc
    rw [happ, hg₁app, hg₂app, map_sub, map_zsmul, hcP]
    module
  obtain ⟨P, hP⟩ := exists_point_ne_zero q Wbar
  obtain ⟨Q, hQ⟩ := g₁.2.surjective hne₁ P
  obtain ⟨R, hR⟩ := g₂.2.surjective hne₂ Q
  refine hP ?_
  rw [← hQ, ← hR]
  exact hcomp R

/-- **A vanishing value of the degree form makes `X² − c·X + q` split over `ℤ`**
(PROVEN 2026-07-31, pure arithmetic): the rational-root theorem in the shape
`(2m − cn)² = n²(c² − 4q)`, so `n ∣ 2m − cn` by `Int.pow_dvd_pow_iff`, the
quotient `k` satisfies `k² = c² − 4q`, and `c + k` is even because
`(c − k)(c + k) = 4q`. -/
theorem exists_int_root_of_degreeForm_eq_zero {c qq m n : ℤ}
    (hmn : ¬ (m = 0 ∧ n = 0)) (h : m ^ 2 - c * m * n + n ^ 2 * qq = 0) :
    ∃ r : ℤ, r ^ 2 - c * r + qq = 0 := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hmn ⟨by nlinarith [sq_nonneg m, h], rfl⟩
  have key : (2 * m - c * n) ^ 2 = n ^ 2 * (c ^ 2 - 4 * qq) := by linear_combination 4 * h
  have hdvd : n ^ 2 ∣ (2 * m - c * n) ^ 2 := ⟨c ^ 2 - 4 * qq, key⟩
  have hnk : n ∣ (2 * m - c * n) := (Int.pow_dvd_pow_iff two_ne_zero).mp hdvd
  obtain ⟨k, hk⟩ := hnk
  have hk2 : k ^ 2 = c ^ 2 - 4 * qq := by
    have hsq : n ^ 2 * k ^ 2 = n ^ 2 * (c ^ 2 - 4 * qq) := by
      rw [← key, hk]; ring
    exact mul_left_cancel₀ (pow_ne_zero 2 hn0) hsq
  have hpar : (c - k) * (c + k) = 4 * qq := by linear_combination -hk2
  have h2 : (2 : ℤ) ∣ c + k := by
    by_contra hodd
    have hv : Odd (c + k) := Int.not_even_iff_odd.mp (fun he => hodd he.two_dvd)
    obtain ⟨t, ht⟩ := hv
    have hu : Odd (c - k) := ⟨c - t - 1, by omega⟩
    have hop : Odd ((c - k) * (c + k)) := hu.mul ⟨t, ht⟩
    rw [hpar] at hop
    exact (Int.not_odd_iff_even.mpr ⟨2 * qq, by ring⟩) hop
  obtain ⟨r, hr⟩ := h2
  refine ⟨r, ?_⟩
  have hk' : k = 2 * r - c := by omega
  rw [hk'] at hk2
  have h4 : 4 * (r ^ 2 - c * r + qq) = 0 := by linear_combination hk2
  linarith

/-- **The degree form never vanishes off the origin** (PROVEN 2026-07-31):
`m² − c·m·n + n²q ≠ 0` for `(m, n) ≠ (0, 0)`.

Equivalently `X² − c·X + q` is irreducible over `ℤ`, equivalently `c² − 4q` is
not a perfect square.  See the section header for why the load-bearing step is
the Weil-pairing determinant rather than a counting argument, and for the route
this opens.

It is consumed by `natCard_ker_degreeFormEnd_of_dvd` below, whose `d = 0` branch
used to cite the still-open `natCard_ker_degreeFormEnd_le`; that branch is now
VACUOUS, so the `q`-primary count no longer touches that leaf at all. -/
theorem degreeForm_ne_zero (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] {c : ℤ}
    (hc : frobeniusPointEnd q Wbar * frobeniusPointEnd q Wbar
      = c • frobeniusPointEnd q Wbar
        - (q : ℤ) • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)))
    {m n : ℤ} (hmn : ¬ (m = 0 ∧ n = 0)) :
    m ^ 2 - c * m * n + n ^ 2 * (q : ℤ) ≠ 0 := by
  intro h0
  obtain ⟨r, hr⟩ := exists_int_root_of_degreeForm_eq_zero hmn h0
  exact not_split_charEquation q Wbar hc (r := r) (r' := c - r) (by ring)
    (by linarith [hr])

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

ROUTE UPDATE, 2026-07-28, and it is a possible RE-CUT of this leaf rather than
a proof of it.  The peeling machinery below (`degreeFormEnd_peel`,
`exists_natCard_ker_mul_pow`) is now PROVEN, and it makes this leaf derivable
from the strictly weaker-looking `natCard_ker_degreeFormEnd_of_not_dvd`
(the `q ∤ d` case, currently proven FROM this leaf, so the dependency would
have to be reversed).  The derivation, for `d ≠ 0`, is a three-way split on
the invariant `M − c·N`:

* `q ∤ M − c·N`: `exists_natCard_ker_mul_pow` gives `d = #ker ψ · q^v`, and
  `q^v ≥ 1` with `#ker ψ ≥ 0` gives `#ker ψ ≤ d` — with equality iff `v = 0`;
* `q ∣ M − c·N` and `q ∤ M`: then `q ∣ d ≡ M·(M − c·N)`, so
  `natCard_ker_degreeFormEnd_of_dvd` applies and gives EQUALITY;
* `q ∣ M − c·N` and `q ∣ M`: peel one `F` and recurse on `|d|`, which drops by
  a factor of `q`.

WHY THAT WAS NOT DONE HERE — **and the `d = 0` half of it is now DONE, NINTH
CUT 2026-07-31.**  The degenerate case `d = 0` is not covered by the route above:
there one must show `Nat.card (ker ψ) = 0`, i.e. that `ker ψ` is INFINITE, and
the proof of `natCard_ker_degreeFormEnd_of_dvd` used to discharge `d = 0` by
citing THIS leaf.  It no longer does: `degreeForm_ne_zero` (above the section
`### The degree form`) shows `d = 0` is IMPOSSIBLE for `(m, n) ≠ (0, 0)`, so that
branch is vacuous and the `q`-primary count is off this leaf entirely.

**The sketch this paragraph used to carry was right in outline and skipped its
own hard step, which is worth recording because a successor would repeat it.**
It read: `d = 0` forces `m/n ∈ ℤ` to be a root of `X² − cX + q` dividing `q`,
"hence `±1` … so `(F ∓ 1)(F ∓ q) = 0` with both factors of finite kernel — a
contradiction, since `Wbar(𝔽̄_q)` is infinite".  *Both factors of finite kernel*
is the whole difficulty: `IsIsogeny.finite_ker` gives finiteness only for a
NONZERO isogeny, and `F − [q] ≠ 0` is invisible to every counting fact in this
file — `#ker F = 1` (`natCard_ker_frobeniusPointEnd`) is perfectly consistent
with `F = [q]`, which is the supersingular case `E[q] = 0`.  The step is supplied
by the Weil-pairing determinant (`frobeniusPointEnd_ne_zsmul`), and once both
factors are known nonzero the finiteness bookkeeping is not needed at all: they
are then SURJECTIVE, so the composite is surjective and cannot be `0`.

THE CHECK THAT WOULD REFUTE this route: a `(M, N)` with `d ≠ 0` falling into
none of the three cases, or a proof that the third case fails to terminate.
Neither exists — the split is exhaustive and `|d|` is a strictly decreasing
`ℕ`-valued measure on the third branch.

## AUDIT 2026-07-30 — THE ROUTE ABOVE IS CIRCULAR IN A SECOND PLACE, AND THE
## WHOLE `ℤ[F]` AXIS IS CLOSED BY AN EXPLICIT COUNTER-MODEL

Two findings, checked against the file as it stands.  The second is decisive and
supersedes the ROUTE UPDATE above: **that re-cut cannot be carried out at all.**

**(1) The re-cut is circular twice over, not once.**  The route note records
that `natCard_ker_degreeFormEnd_of_not_dvd` is "currently proven FROM this leaf,
so the dependency would have to be reversed", and treats the `d = 0` analysis as
the only other missing piece.  There is a second cycle it does not mention:
bullet 1's engine `exists_natCard_ker_mul_pow` **itself calls
`natCard_ker_degreeFormEnd_of_not_dvd`** in its base case (the `q ∤ d` branch,
its last line), and that calls this leaf twice.  So the peeling machinery is not
independent of this leaf either, and "reverse the dependency" means, in full:
prove `natCard_ker_degreeFormEnd_of_not_dvd` outright.  Note also that
`natCard_ker_degreeFormEnd_of_dvd` reaches this leaf along BOTH paths — directly
in its `d = 0` branch and through `exists_natCard_ker_mul_pow` — so writing the
`d = 0` analysis alone frees nothing.

**(2) `#ker ψ = d` for `q ∤ d` is NOT a consequence of `hc`, so the reversal is
impossible.**  The counter-model is the one already recorded on
`exists_ne_zero_qTorsion` below, run at an INDEFINITE form; nobody had pointed
it at this leaf.  Take `q = 5`, `c = 7`, so `c² − 4q = 29 > 0` — Hasse FAILS —
and `q ∤ c`.  Let

    A = ⨁_{ℓ ≠ 5} (ℚ_ℓ/ℤ_ℓ)²,   F = the companion matrix  C = [[0, −5], [1, 7]]
                                     acting diagonally.

Every algebraic fact this module's `ℤ[F]` layer rests on holds in `A`:

* `A` is infinite and divisible, so `zsmul` is surjective on it — the role of
  `WeierstrassCurve.zsmul_surjective_algClosed` in `surjective_degreeFormEnd`;
* `det C = 5` is a unit in every `ℤ_ℓ` with `ℓ ≠ 5`, so `F` is BIJECTIVE and
  `#ker F = 1` (`injective_frobeniusPointEnd`, `surjective_frobeniusPointEnd`,
  `natCard_ker_frobeniusPointEnd`);
* `C² = 7·C − 5` is Cayley–Hamilton, i.e. **exactly `hc`** at `c = 7`;
* `A[n] ≅ (ℤ/n)²` has `n²` elements for every `5 ∤ n`
  (`TorsionCard.card_torsionBy`), and `A[5] = 0`, which is cyclic
  (`TorsionCharP.exists_zsmul_eq_of_charP`);
* for `d = m² − 7mn + 5n² ≠ 0` one has `#ker([m] − [n]F) = |d| / 5^{v₅(d)}`,
  because for a matrix `M` over `ℤ_ℓ` with `det M ≠ 0` the kernel of `M` on
  `(ℚ_ℓ/ℤ_ℓ)²` is `M⁻¹ℤ_ℓ² / ℤ_ℓ²`, of order `ℓ^(v_ℓ (det M))`.

Now take `(m, n) = (1, 1)`.  Then `d = 1 − 7 + 5 = −1`, so `5 ∤ d`, and
`I − C = [[1, 5], [−1, −6]]` has determinant `−1`, a unit at every `ℓ`.  Hence
`ker([1] − F) = 0` and `#ker([1] − F) = 1`, while this leaf's conclusion reads

    1 ≤ −1.

So the leaf is FALSE in `A`, hence not derivable from `hc` together with
divisibility, bijectivity of `F`, `#E[n] = n²` for `q ∤ n`, and cyclicity of
`E[q]`.  The same witness refutes `natCard_ker_degreeFormEnd_of_not_dvd` in `A`
(it reads `1 = −1`) and `degreeForm_nonneg`, and it is consistent with the
PROVEN `natCard_ker_mul_natCard_ker_conj`: the conjugate `(m − n·c, −n) =
(−6, −1)` has the same `d = −1` and the same count `1`, and `1 · 1 = (−1)²`.
The ONE statement of this module that `A` does not interpret is
`natCard_ker_one_sub_frobeniusPointEnd`, which identifies `ker([1] − F)` with
`Wbar(𝔽_q)` — a geometric identification, not an algebraic one; and it is not a
contradiction either, since `#ker([1] − F) = 1` in `A` and a curve is allowed one
rational point.  That `A` escapes exactly there is the finding, not a gap in it.

**A QUALIFICATION TO (2), added 2026-07-31 by the NINTH CUT, and it matters
because as written (2) steers a successor away from a route it does not
refute.**  What `A` refutes is `ℤ[F]`-only reasoning, and `A` itself survives the
NINTH CUT: its `F` is not a scalar and its discriminant `29` is not a square, so
`frobeniusPointEnd_ne_zsmul` and `degreeForm_ne_zero` both hold in `A`.  Two
consequences.  First, a Weil-pairing determinant is not useless here — it cannot
see the SIGN of `d`, which is what (2) is about, but it does decide that `F` is
not multiplication by an integer, and that is what the `d = 0` analysis needed.
Second, the property `A` FAILS is that its unit group is infinite: the companion
matrix generates an infinite group of invertible endomorphisms.  So an argument
that uses **finiteness of the invertible endomorphisms** escapes `A` by
construction, and the Pell route in the section header above
`exists_point_ne_zero` is exactly that argument, with the single atom "an isogeny
invertible in `WeierstrassCurve.End` has finite multiplicative order".  Read (2)
as "no `ℤ[F]`-internal rearrangement", not as "no route".

**What (2) settles.**  It is a proof of what the 2026-07-27 audit asserted
informally — "a sign is invisible to every p-adic argument, since a determinant
over `ℤ_ℓ` has none" — in the strong form: *no* rearrangement of the `ℤ[F]`
material in this file, and no `ℓ`-adic / Tate-module or Weil-pairing computation
(`WeilPairing.det_frobeniusTorsionEnd` included), can close this leaf or any
sub-leaf that implies it.  Those tools compute `|d|`; the leaf asks for `d`.
Concretely, and this is worth recording because it looks like progress and is
not: the Weil-pairing determinant together with
`WeierstrassCurve.n_torsion_dimension` (which does give
`E.nTorsion N ≃+ ZMod N × ZMod N` over a separably closed field in EVERY
characteristic — a docstring elsewhere denying that a rank-`2` torsion structure
is available is stale) yields `#ker ψ = |d|` for `q ∤ d` via Smith normal form on
`E[d²]`.  That is an EQUALITY, strictly more than this leaf asks for in that
case, and it STILL leaves exactly `0 ≤ d`, i.e. Hasse.

So the residual content of this leaf is precisely `0 ≤ m² − c·m·n + n²q`, which
is the inert positivity statement the 2026-07-27 audit already refused to hand
back — and (2) is *why* it is inert: it has no algebraic proof.  What it needs is
the archimedean input that `deg` is a nonnegative integer, i.e. the
function-field degree theory this development does not have (MACHINERY AUDIT
above).  **Do not re-cut this leaf along the `ℓ`-adic axis, and do not hand back
the positivity statement.  The refuting check for any proposed sub-leaf is the
model above: if the sub-leaf is TRUE in `A` at `q = 5, c = 7`, it cannot imply
this leaf.**

**(3) A stale claim, and the concurrent owner it was left for has since landed.**
The docstring of `sq_frobeniusPointEnd_qPrimary` used to end "Both want `F`
BIJECTIVE on `Wbar(𝔽̄_q)` …, which is not yet a declaration in this file".  This
audit declined to fix that in place because the leaf had a live concurrent owner
rewriting exactly those lines; that owner was `flt-lean-129`, whose SIXTH CUT is
precisely `bijective_frobeniusPointEnd`, PROVEN and UNCONDITIONALLY — which is
what the two characteristic-equation leaves needed, since they are upstream of
`hc` and the older `surjective_frobeniusPointEnd` derived surjectivity FROM `hc`.
So the clause is gone and the declaration exists.  Recorded here because the
sequence is the point: not fixing it in place was right, and the reason it was
right is that the owner was doing something strictly better than the fix.


A SECOND ROUTE, ANALYSED AND REJECTED 2026-07-30 — the WEIL-PAIRING one, recorded
so that nobody spends a cycle on it after seeing the composite-level determinant
become available.  Sketch (NOT machine-checked; it is written down only to be
refuted): let `N := d²` with `q ∤ d ≠ 0`, take `det(F | Wbar[N]) = q` (proven
downstream as `MazurTorsion.det_frobeniusTorsionEnd_of_coprime`; see the
relocation note on `exists_sq_frobeniusPointEnd_prime_to_char`) and
`tr(F | Wbar[N]) = c` (Cayley–Hamilton plus `hc`, since `q` is a unit mod `N`);
then `det(ψ | Wbar[N]) = m² − c·m·n + n²q = d`, and `ker ψ ⊆ Wbar[d] ⊆ Wbar[N]`,
so a Smith normal form `e₁ ∣ e₂ ∣ N` for `ψ` on `Wbar[N]` has
`#ker ψ = e₁·e₂` and `gcd(e₁e₂, N) = gcd(d, d²) = |d|`, forcing `e₁e₂ = |d|`.

**That gives `#ker ψ = |d|`, not `#ker ψ = d`, and the difference is the whole
leaf.**  A determinant over `ZMod N` is defined only up to a unit and a kernel
count cannot see a sign — this is verbatim the point `MazurTorsion.lean`'s own
audit of `det_one_sub_frobeniusTorsionEnd_eq_natCard_frobFixed` records ("for a
bare group endomorphism `#ker` and `det` agree only up to sign; positivity is not
group theory").  So the route reduces this leaf to `0 ≤ m² − c·m·n + n²q`, which
the 2026-07-27 audit in `MazurTorsion.lean` already showed is EQUIVALENT to
Hasse's bound, which is downstream of this leaf.  It is therefore circular, and
it stays circular however much composite-level pairing theory is imported.

What that leaves, stated so the leaf is not mistaken for a linear-algebra
exercise: the content here is the INSEPARABLE degree, i.e. that `#ker ψ`, which
is `deg_sep ψ`, is bounded by a quantity that is a cardinality by construction.
The tree has no scheme-theoretic `deg` (`Isogeny.degree` is `Nat.card (ker ·)`,
i.e. the separable degree — `frobIsog_degree = 1`, not `q`), and
`Isogeny.isRationalMap_dualHom_is_false` refutes the dual in characteristic `q`.
So a successor either builds a degree theory or finds the positivity elsewhere;
no rearrangement of what is already here will do it. -/
theorem natCard_ker_degreeFormEnd_le (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] {c : ℤ}
    (hc : frobeniusPointEnd q Wbar * frobeniusPointEnd q Wbar
      = c • frobeniusPointEnd q Wbar
        - (q : ℤ) • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)))
    (m n : ℤ) :
    (Nat.card (LinearMap.ker (degreeFormEnd q Wbar m n)) : ℤ)
      ≤ m ^ 2 - c * m * n + n ^ 2 * (q : ℤ) :=
  sorry

/-! ### The `q`-primary machinery: `F` peels off

Everything in this section exists to prove `natCard_ker_degreeFormEnd_of_dvd`
below, and it reduces that leaf — a two-parameter family — to the SINGLE
classical fact `natCard_ker_frobeniusConj`, `#ker([c] − F) = q` for `q ∤ c`,
which is in turn proven from `#E[q] = q` and so from the one surviving leaf
`exists_ne_zero_qTorsion`.

The mechanism is that `F` is BIJECTIVE on `Wbar(𝔽̄_q)`
(`bijective_frobeniusPointEnd`, proven far above — it moved up on 2026-07-30
because the ISOGENY section needs it, and that section is upstream of the
characteristic equation), so composing with it does not change a kernel count,
while it divides the value of the degree form by `q`.  Iterating that on the
conjugate `ψ'` — which is where the `q`s live, since `q ∣ d` with `q ∤ m` forces
`q ∣ m − n·c` — writes `ψ' = F^k ∘ β` with `β` prime to `q`, and the `q ∤ d`
case evaluates `#ker β`.
-/

/-- **`#ker F = 1`** (PROVEN): the Frobenius is purely inseparable, so its
kernel is trivial.  This is what makes peeling `F` off a composite free. -/
theorem natCard_ker_frobeniusPointEnd (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) :
    Nat.card (LinearMap.ker (frobeniusPointEnd q Wbar)) = 1 := by
  rw [LinearMap.ker_eq_bot.mpr (bijective_frobeniusPointEnd q Wbar).1]
  exact Nat.card_unique

/-- `[0] − [−1]∘F` is `F` (PROVEN, definitional): the conjugate of the
`(m, n) = (c, 1)` pair `[c] − F` is `F` itself, which is what makes
`F ∘ ([c] − F) = ([c] − F) ∘ F = [q]` an instance of
`degreeFormEnd_mul_conj`. -/
theorem degreeFormEnd_zero_neg_one (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) :
    degreeFormEnd q Wbar 0 (-1) = frobeniusPointEnd q Wbar := by
  simp [degreeFormEnd]

/-- **`([c] − F) ∘ F = [q]`** (PROVEN): the characteristic equation, read as
the factorisation of `[q]` through the Frobenius.  `[c] − F` is the
Verschiebung; here it is just `degreeFormEnd q Wbar c 1`, and this identity is
`degreeFormEnd_mul_conj` at `(m, n) = (c, 1)`, whose form value is
`c² − c·c + q = q`. -/
theorem frobeniusConj_mul_frobeniusPointEnd (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) {c : ℤ}
    (hc : frobeniusPointEnd q Wbar * frobeniusPointEnd q Wbar
      = c • frobeniusPointEnd q Wbar
        - (q : ℤ) • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point))) :
    degreeFormEnd q Wbar c 1 * frobeniusPointEnd q Wbar
      = (q : ℤ) • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)) := by
  have h := degreeFormEnd_mul_conj q Wbar hc c 1
  rw [show c - 1 * c = (0 : ℤ) by ring, degreeFormEnd_zero_neg_one,
    show c ^ 2 - c * c * 1 + 1 ^ 2 * (q : ℤ) = (q : ℤ) by ring] at h
  exact h

/-- **The ORDINARY criterion** (sorry leaf, opened 2026-07-29; Silverman *AEC*
V.3.1, Deuring): a curve whose Frobenius trace is prime to `q` has a NONZERO
`q`-torsion point over `𝔽̄_q`.

This is the last characteristic-`q` input of the degree theory, and the only
place the ordinary/supersingular dichotomy enters.  Everything `q`-primary is
proven from it: `natCard_ker_zsmul_q` (`#E[q] = q`), then
`natCard_ker_frobeniusConj` (`#ker([c] − F) = q`), then
`natCard_ker_degreeFormEnd_of_dvd` (the whole `q ∣ d` family).

`hqc` IS LOAD-BEARING and the statement is FALSE without it: a supersingular
curve has `E[q] = 0` outright.  Witness `y² = x³ + 1` over `𝔽₅`, where the
affine points are `(0, ±1)`, `(2, ±2)`, `(4, 0)` — so `#E(𝔽₅) = 6`, `c = 0`,
and `E[5] = 0`.  `hc` is load-bearing too, because it is what pins `c` to the
Frobenius trace rather than leaving it a free integer: `c` is UNIQUE given
`hc`, since two solutions differ by an integer annihilating `F`'s image, i.e.
all of `Wbar(𝔽̄_q)`, which has points of order `n` for every `q ∤ n`
(`TorsionCard.card_torsionBy`).

WHAT IS FREE HERE, AND A CORRECTION.  The note this leaf replaces claimed the
upper half `#ker([c] − F) ≤ q` was "already free" from
`natCard_ker_degreeFormEnd_le` at `(m, n) = (c, 1)`.  That is not free: that
declaration is itself an OPEN leaf.  The upper half is genuinely free, but from
`TorsionCharP.exists_zsmul_eq_of_charP` — the `q`-torsion in characteristic `q`
is CYCLIC, PROVEN 2026-07-25 out of the vanishing of `ΨSqₚ′` — which gives
`#E[q] ∣ q` outright.  `natCard_ker_zsmul_q` below now takes it from there, so
the `q`-primary count no longer depends on `natCard_ker_degreeFormEnd_le` at
all.  What is missing is exactly the LOWER bound `E[q] ≠ 0`, which is this
leaf, stated as the existence of ONE point rather than as a count.

IT IS NOT DERIVABLE FROM THE ALGEBRA IN THIS FILE, and that is worth recording
because several route notes have proposed rearranging the peeling to get it.
Take `A = ⨁_{ℓ ≠ q} (ℚ_ℓ/ℤ_ℓ)²` with `F` acting on each `T_ℓ = ℤ_ℓ²` by the
companion matrix of `X² − c·X + q`, for ANY `c` prime to `q`.  Then `F` is
bijective, `F² = c·F − q`, and `#ker([m] − [n]F) = |d| / q^{v_q(d)}` for every
`(m, n)` — so `#ker F = 1` and every `q ∤ d` count agrees with
`natCard_ker_degreeFormEnd_of_not_dvd` and with `degreeFormEnd_peel` — and yet
`A[q] = 0`.  Every algebraic identity this module proves holds in that model,
so any proof of this leaf must use the GEOMETRY of the curve, not `ℤ[F]`.

A SECOND ROUTE, AND A CORRECTION TO THE STEER BELOW (2026-07-30).  The note
below says "no invariant differentials", and that was written when this tree had
no invariant-differential machinery.  It now does:
`EllipticCurve/DifferentialCharacter.lean` defines `IsDiffChar φ c` ("`φ` pulls
the invariant differential `ω = dx/(2y + a₁x + a₃)` back to `c·ω`") and proves it
additive, multiplicative on composites, and equal to `n` on `[n]`.  That is
exactly the classical route's first half: `λ(F) = 0` because `d(x^q) = 0`, so
`λ([c] − F) = c`, and `hqc` says `c ≠ 0` in `𝔽_q` — i.e. the Verschiebung
`V = [c] − F` is SEPARABLE precisely when `q ∤ c`.  Note this half needs
`isIsogeny_frobeniusPointEnd`/`isRationalMap_frobeniusPointEnd` above to have a
certificate for `F` at all, which is new as of the EIGHTH CUT.

What that route still needs, and it is why it is recorded rather than taken:
"separable and non-constant ⟹ `#ker = deg > 1`".  The tree has no
scheme-theoretic `deg` (see the same discussion on
`natCard_ker_degreeFormEnd_le`), and `DifferentialCharacter`'s own injectivity
statement `eq_zero_of_isDiffChar_zero` carries `[CharZero F]` — necessarily, since
`F` itself has `λ(F) = 0` and `F ≠ 0`.  So the missing atom is a fibre-counting
statement for a separable rational map of curves, which is a real piece of work
but is a statement about ONE-VARIABLE POLYNOMIALS (the `x`-witness `A/B` and its
Wronskian `A′B − AB′`, both already handled in that file) rather than about
`𝔽_{q^n}`-point counts.  Weigh it against the character-sum route below.

THE FIRST ROUTE, and it is elementary: no invariant differentials, no dual
isogeny, no Cartier operator, no `E[q^∞]` structure theorem.  It is Deuring's
congruence, used twice.  For `q` odd write the curve as `y² = g(x)` with
`deg g = 3`, set `G = g^{(q−1)/2}` and let `H ∈ 𝔽_q` be the coefficient of
`x^{q−1}` in `G` (the Hasse invariant).

1. `#E(𝔽_{q^n}) ≡ 1 − Hₙ (mod q)`, where `Hₙ` is the coefficient of
   `x^{q^n − 1}` in `g^{(q^n − 1)/2}`.  Pure character sum:
   `#E(𝔽_{q^n}) = q^n + 1 + Σ_x χ(g(x))` with `χ(u) = u^{(q^n − 1)/2}`, and
   `Σ_{x ∈ 𝔽_{q^n}} x^k = −1` exactly when `k > 0` and `(q^n − 1) ∣ k`.
2. `Hₙ = H^n` in `𝔽_q`.  `g^{(q^n − 1)/2} = ∏_{i < n} G^{q^i}` and
   `G^{q^i} = Σ_j a_j^{q^i} x^{j·q^i}`, so the coefficient of `x^{q^n − 1}` is
   a sum over `Σ_i j_i q^i = q^n − 1` with `0 ≤ j_i ≤ deg G = 3(q−1)/2`.  Since
   `3(q−1)/2 < 2q − 1`, the congruence `j₀ ≡ −1 (mod q)` forces `j₀ = q − 1`,
   and induction forces every `j_i = q − 1`.  Hence
   `Hₙ = ∏_i H^{q^i} = H^{1 + q + ⋯ + q^{n−1}} = H^n`, using `H^q = H` for
   `H ∈ 𝔽_q`.
3. `n = 1` gives `c = q + 1 − #E(𝔽_q) ≡ H (mod q)`, so `hqc` says `H ≠ 0`;
   then `n = q − 1` gives `H^{q−1} = 1`, so `q ∣ #E(𝔽_{q^{q−1}})`, and Cauchy
   produces a point of order `q` over `𝔽_{q^{q−1}} ⊆ 𝔽̄_q`.

The cost of that route is not the argument but the INFRASTRUCTURE it needs:
point counting over `𝔽_{q^n}` (this module only ever counts over `𝔽_q`, in
`natCard_ker_one_sub_frobeniusPointEnd`) and the power-sum identity.  `q = 2`
is not covered by it — completing the square fails — but there the whole
statement is finite and explicit: in characteristic `2`,
`−(x, y) = (x, y + a₁x + a₃)`, so `P = −P` forces `a₁x = 0`; hence for `a₁ ≠ 0`
the point `(0, y)` with `y² + a₃y = a₆` is a nonzero `2`-torsion point, and
`a₁ = 0` is exactly the supersingular case over `𝔽₂` (where `2 ∣ c`), which
`hqc` excludes.

THE CHECK THAT WOULD REFUTE the claim that this is the minimal atom: a proof of
`E[q] ≠ 0` from the kernel counts alone.  The model above rules that out. -/
theorem exists_ne_zero_qTorsion (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] {c : ℤ}
    (hc : frobeniusPointEnd q Wbar * frobeniusPointEnd q Wbar
      = c • frobeniusPointEnd q Wbar
        - (q : ℤ) • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)))
    (hqc : ¬ ((q : ℤ) ∣ c)) :
    ∃ P : (Wbar⁄(AlgebraicClosure (ZMod q))).Point, P ≠ 0 ∧ (q : ℤ) • P = 0 :=
  sorry

/-- **`#E[q] = q` in the ordinary case** (PROVEN 2026-07-29 over
`exists_ne_zero_qTorsion` and `TorsionCharP.exists_zsmul_eq_of_charP`).

The two halves of the dichotomy meet here.  Cyclicity in characteristic `q`
says every `q`-torsion point is a multiple of any nonzero one, so `E[q]` is
either trivial or the cyclic group generated by one point of order `q`; the
leaf supplies a nonzero point, so it is the latter and the count is `q`.

Note the direction of the dependency, which is the reverse of the 2026-07-28
arrangement: `#E[q] = q` is now the primitive and `#ker([c] − F) = q` the
consequence, because the upper bound is available on `E[q]` (where it is
`TorsionCharP`'s cyclicity) and NOT on `ker([c] − F)` (where it would be the
open `natCard_ker_degreeFormEnd_le`). -/
theorem natCard_ker_zsmul_q (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] {c : ℤ}
    (hc : frobeniusPointEnd q Wbar * frobeniusPointEnd q Wbar
      = c • frobeniusPointEnd q Wbar
        - (q : ℤ) • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)))
    (hqc : ¬ ((q : ℤ) ∣ c)) :
    Nat.card (LinearMap.ker
      ((q : ℤ) • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)))) = q :=
  natCard_ker_zsmul_q_of_ordinary q Wbar (exists_ne_zero_qTorsion q Wbar hc hqc)

/-- **The `q`-torsion count of an ORDINARY curve** (PROVEN 2026-07-29 over
`natCard_ker_zsmul_q`): `#ker([c] − F) = q` when `q ∤ c`.

`[c] − F` is the Verschiebung `V`, and `V ∘ F = [q]`
(`frobeniusConj_mul_frobeniusPointEnd`) with `F` bijective, so
`#ker V = #ker V · #ker F = #E[q] = q`.

This is the `(m, n) = (c, 1)` instance of `natCard_ker_degreeFormEnd_of_dvd`
below, and the reduction there runs from the two-parameter family down to it —
so it must NOT be proven by citing that theorem or
`natCard_ker_degreeFormEnd_of_sq`.  It is not: the input is `#E[q] = q`, whose
own inputs are `TorsionCharP`'s cyclicity and the leaf
`exists_ne_zero_qTorsion`, neither of which is downstream of anything here. -/
theorem natCard_ker_frobeniusConj (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] {c : ℤ}
    (hc : frobeniusPointEnd q Wbar * frobeniusPointEnd q Wbar
      = c • frobeniusPointEnd q Wbar
        - (q : ℤ) • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)))
    (hqc : ¬ ((q : ℤ) ∣ c)) :
    Nat.card (LinearMap.ker (degreeFormEnd q Wbar c 1)) = q := by
  have h := natCard_ker_mul (degreeFormEnd q Wbar c 1) (frobeniusPointEnd q Wbar)
    (bijective_frobeniusPointEnd q Wbar).2
  rw [frobeniusConj_mul_frobeniusPointEnd q Wbar hc, natCard_ker_zsmul_q q Wbar hc hqc,
    natCard_ker_frobeniusPointEnd] at h
  simpa using h.symm

/-- **`#E[q^v] = q^v` in the ordinary case** (PROVEN over
`natCard_ker_zsmul_q`): `[q^v] = [q] ∘ [q^{v−1}]` and `[q^{v−1}]` is
surjective, so the counts multiply.  This is the only place the `q`-primary
part of `#E[d]` is evaluated, and it is where the `q ∤ c` hypothesis is
consumed. -/
theorem natCard_ker_zsmul_q_pow (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] {c : ℤ}
    (hc : frobeniusPointEnd q Wbar * frobeniusPointEnd q Wbar
      = c • frobeniusPointEnd q Wbar
        - (q : ℤ) • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)))
    (hqc : ¬ ((q : ℤ) ∣ c)) :
    ∀ v : ℕ, Nat.card (LinearMap.ker
      (((q : ℤ) ^ v) • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point))))
        = q ^ v :=
  natCard_ker_zsmul_q_pow_of_ordinary q Wbar (exists_ne_zero_qTorsion q Wbar hc hqc)

/-- **`#E[d] = d²` for `q ∤ d`, in `Module.End` form** (PROVEN): `ker_zsmul_one`
followed by `TorsionCard.card_torsionBy`, with the `|d|`-for-`d` normalisation
that `torsionBy` needs.  This is the block that
`natCard_ker_mul_natCard_ker_conj` runs inline; it is factored out here because
the `q ∣ d` argument needs it at a DIFFERENT integer (the prime-to-`q` part of
`d`) than the one the degree form supplies. -/
theorem natCard_ker_zsmul_one_of_not_dvd (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] {d : ℤ}
    (hd : ¬ ((q : ℤ) ∣ d)) :
    (Nat.card (LinearMap.ker
      (d • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)))) : ℤ) = d ^ 2 := by
  classical
  rw [ker_zsmul_one]
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
  rw [habs, hcard]
  push_cast
  exact sq_abs d

/-- **The `q ∤ d` case of the degree form** (PROVEN over
`natCard_ker_degreeFormEnd_le`): `#ker ψ = d` whenever `q ∤ d`, with NO
hypothesis on `m`.

This is the separation argument that `exists_natCard_ker_degreeFormEnd` runs
inline, factored out so that the `q ∣ d` case can call it at the prime-to-`q`
tail `β` of the peeling.  `#ker ψ · #ker ψ' = d²` and both factors are at most
`d` (the form is conjugation-invariant, `degreeForm_conj`), so both equal
`d`. -/
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

/-- **Peeling one `F` off** (PROVEN, pure ring algebra over the characteristic
equation): `[q·M₀] − [N]∘F = F ∘ ([c·M₀ − N] − [M₀]∘F)`.

Expanding the right-hand side and rewriting `F²` by `hc` gives
`(c·M₀ − N)·F − M₀·(c·F − q) = −N·F + q·M₀`, which is the left-hand side.
Since `F` is bijective this identity says that a degree form whose FIRST
coordinate is divisible by `q` has the same kernel count as one whose form
value is `q` times smaller. -/
theorem degreeFormEnd_peel (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) {c : ℤ}
    (hc : frobeniusPointEnd q Wbar * frobeniusPointEnd q Wbar
      = c • frobeniusPointEnd q Wbar
        - (q : ℤ) • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)))
    (M₀ N : ℤ) :
    degreeFormEnd q Wbar ((q : ℤ) * M₀) N
      = frobeniusPointEnd q Wbar * degreeFormEnd q Wbar (c * M₀ - N) M₀ := by
  simp only [degreeFormEnd, mul_sub, mul_smul_comm, mul_one, smul_smul, hc, smul_sub]
  module

/-- **The peeling, iterated** (PROVEN over `natCard_ker_degreeFormEnd_of_not_dvd`):
if the CONJUGATE invariant `M − c·N` is prime to `q`, then the kernel count of
`[M] − [N]∘F` is prime to `q` and the form value is that count times a power
of `q`.

WHY THE INVARIANT IS `M − c·N` AND WHY IT IS PRESERVED.  The recursion sends
`(M, N) ↦ (c·M/q − N, M/q)` when `q ∣ M`, and then the new invariant is
`(c·M/q − N) − c·(M/q) = −N`.  It is nonzero mod `q` because `q ∣ M` and
`q ∤ M − c·N` force `q ∤ c·N`.  So the invariant seeds itself, and the
recursion TERMINATES with `q ∤ d`: at a step with `q ∤ M`, the identity
`d ≡ M·(M − c·N) (mod q)` has both factors prime to `q`.  That is the whole
reason no `ℤ_q` unit-root analysis is needed here, and it is what replaces the
`v_q(d) = v_q(m − n·u)` computation the 2026-07-27 route note proposed.

The recursion is bounded by `|d|`, which drops by a factor of at least `2` at
each step, and `k` is that bound. -/
theorem exists_natCard_ker_mul_pow (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] {c : ℤ}
    (hc : frobeniusPointEnd q Wbar * frobeniusPointEnd q Wbar
      = c • frobeniusPointEnd q Wbar
        - (q : ℤ) • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point))) :
    ∀ (k : ℕ) (M N : ℤ), (M ^ 2 - c * M * N + N ^ 2 * (q : ℤ)).natAbs ≤ k →
      ¬ ((q : ℤ) ∣ M - c * N) → M ^ 2 - c * M * N + N ^ 2 * (q : ℤ) ≠ 0 →
      ∃ v : ℕ, ¬ ((q : ℤ) ∣ (Nat.card (LinearMap.ker (degreeFormEnd q Wbar M N)) : ℤ)) ∧
        M ^ 2 - c * M * N + N ^ 2 * (q : ℤ)
          = (Nat.card (LinearMap.ker (degreeFormEnd q Wbar M N)) : ℤ) * (q : ℤ) ^ v := by
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  have hqprime : Prime ((q : ℤ)) := Nat.prime_iff_prime_int.mp (Fact.out : q.Prime)
  intro k
  induction k with
  | zero =>
    intro M N hk _ hne
    exact absurd (Int.natAbs_eq_zero.mp (Nat.le_zero.mp hk)) hne
  | succ k ih =>
    intro M N hk hMN hne
    by_cases hdvd : ((q : ℤ) ∣ M ^ 2 - c * M * N + N ^ 2 * (q : ℤ))
    · -- `q ∣ d` forces `q ∣ M`, so one `F` peels off
      have hqM : (q : ℤ) ∣ M := by
        have hsplit : M ^ 2 - c * M * N + N ^ 2 * (q : ℤ)
            = M * (M - c * N) + N ^ 2 * (q : ℤ) := by ring
        rw [hsplit] at hdvd
        have hmul : (q : ℤ) ∣ M * (M - c * N) := by
          have h2 : (q : ℤ) ∣ N ^ 2 * (q : ℤ) := dvd_mul_left _ _
          simpa using dvd_sub hdvd h2
        rcases hqprime.dvd_mul.mp hmul with h | h
        · exact h
        · exact absurd h hMN
      obtain ⟨M₀, rfl⟩ := hqM
      have hqe : ((q : ℤ) * M₀) ^ 2 - c * ((q : ℤ) * M₀) * N + N ^ 2 * (q : ℤ)
          = (q : ℤ) * ((c * M₀ - N) ^ 2 - c * (c * M₀ - N) * M₀ + M₀ ^ 2 * (q : ℤ)) := by
        ring
      have hene : (c * M₀ - N) ^ 2 - c * (c * M₀ - N) * M₀ + M₀ ^ 2 * (q : ℤ) ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hqe
        exact hne hqe
      have hMN' : ¬ ((q : ℤ) ∣ (c * M₀ - N) - c * M₀) := by
        rw [show (c * M₀ - N) - c * M₀ = -N by ring]
        intro h
        exact hMN (dvd_sub (dvd_mul_right _ _) (((dvd_neg).mp h).mul_left c))
      have hk' : ((c * M₀ - N) ^ 2 - c * (c * M₀ - N) * M₀ + M₀ ^ 2 * (q : ℤ)).natAbs ≤ k := by
        have hnat := congrArg Int.natAbs hqe
        rw [Int.natAbs_mul, Int.natAbs_natCast] at hnat
        rw [hnat] at hk
        have hpos : ((c * M₀ - N) ^ 2 - c * (c * M₀ - N) * M₀ + M₀ ^ 2 * (q : ℤ)).natAbs ≠ 0 :=
          Int.natAbs_ne_zero.mpr hene
        have h3 : 2 * ((c * M₀ - N) ^ 2 - c * (c * M₀ - N) * M₀ + M₀ ^ 2 * (q : ℤ)).natAbs
            ≤ k + 1 := le_trans (Nat.mul_le_mul_right _ hq2) hk
        omega
      have hsurj : Function.Surjective (degreeFormEnd q Wbar (c * M₀ - N) M₀) :=
        (surjective_degreeFormEnd q Wbar hc (m := c * M₀ - N) (n := M₀) hene).1
      have hcard : Nat.card (LinearMap.ker (degreeFormEnd q Wbar ((q : ℤ) * M₀) N))
          = Nat.card (LinearMap.ker (degreeFormEnd q Wbar (c * M₀ - N) M₀)) := by
        rw [degreeFormEnd_peel q Wbar hc M₀ N, natCard_ker_mul _ _ hsurj,
          natCard_ker_frobeniusPointEnd, one_mul]
      obtain ⟨v, hnd, hval⟩ := ih (c * M₀ - N) M₀ hk' hMN' hene
      refine ⟨v + 1, ?_, ?_⟩
      · rw [hcard]; exact hnd
      · rw [hqe, hcard, hval, pow_succ]; ring
    · exact ⟨0, by rw [natCard_ker_degreeFormEnd_of_not_dvd q Wbar hc hdvd]; exact hdvd,
        by rw [natCard_ker_degreeFormEnd_of_not_dvd q Wbar hc hdvd, pow_zero, mul_one]⟩

/-- **The `q`-primary case** (PROVEN 2026-07-28 over
`natCard_ker_degreeFormEnd_le` and `natCard_ker_frobeniusConj`): when `q ∤ m`
but `q ∣ d = m² − c·m·n + n²q`, the kernel count is still the value of the
form.

WHY THIS CASE IS SEPARATE, and it is not an artefact of the proof.  The proven
`natCard_ker_mul_natCard_ker_conj` evaluates `#ker ψ · #ker ψ'` as `#E[d]`,
and `TorsionCard.card_torsionBy` computes `#E[d] = d²` only for `q ∤ d`.  For
`q ∣ d` that is FALSE: at `q = 5`, `c = 1`, `(m, n) = (1, 1)` one has `d = 5`,
and an ordinary curve over `𝔽₅` has `#E[5] = 5`, not `25`.  So the whole
`q ∤ d` argument is unavailable here and something new is needed.

THE PROOF, and it is the route note of 2026-07-28 carried out.  First, `q ∣ d`
and `q ∤ m` FORCE `q ∤ c`: modulo `q`, `d ≡ m·(m − c·n)`, so `q ∣ d` with
`q ∤ m` gives `m ≡ c·n`, which needs both `q ∤ c` and `q ∤ n`.  That is the
ORDINARY case; the supersingular case (`q ∣ c`) never reaches this leaf,
because there `d ≡ m² ≢ 0`.  This is the ONE place `q ∤ c` is produced, and it
is what licenses `natCard_ker_zsmul_q_pow`.

Then `F` is BIJECTIVE (`injective_frobeniusPointEnd`,
`surjective_frobeniusPointEnd`), so peeling it off a composite leaves the
kernel count alone while dividing the form value by `q`
(`degreeFormEnd_peel`).  Applying that to the CONJUGATE
`ψ' = [m − n·c] + [n]∘F` — which is where the `q`s are, since `q ∣ d` with
`q ∤ m` gives `q ∣ m − n·c` — writes `d = A·q^v` with `A = #ker ψ'` prime to
`q` (`exists_natCard_ker_mul_pow`).  Finally `ψ ∘ ψ' = [d]` gives

    #ker ψ · A  =  #E[d]  =  #E[A] · #E[q^v]  =  A² · q^v,

by `natCard_ker_zsmul_one_of_not_dvd` and `natCard_ker_zsmul_q_pow`, whence
`#ker ψ = A·q^v = d`.

WHAT THE PROOF ACTUALLY USES, and it is worth recording because it is LESS
than the statement offers.  `hd` is consumed only to produce `q ∤ c`; the
argument above never needs `q ∣ d` again, and it therefore proves the `q ∤ d`
case as well (there `v = 0` and `A = d`).  It does need `hm`, which seeds the
peeling invariant: the invariant of the conjugate pair `(m − n·c, −n)` is
`(m − n·c) − c·(−n) = m`.

The DEGENERATE case `d = 0` is discharged by
`natCard_ker_degreeFormEnd_le` alone: it gives `#ker ψ ≤ 0`, and a `Nat.card`
is nonnegative, so both sides are `0` — which is correct, the kernel being all
of the infinite `Wbar(𝔽̄_q)`.

WHAT SURVIVED.  The reduction bottoms out at `natCard_ker_frobeniusConj`,
`#ker([c] − F) = q` for `q ∤ c` — the ordinary `q`-torsion count, which is
exactly the `(m, n) = (c, 1)` INSTANCE of this theorem.  So this declaration
is a statement about a two-parameter family proven from a single instance of
itself.  That instance is now PROVEN too (2026-07-29), from `#E[q] = q`; the
leaf under it is `exists_ne_zero_qTorsion`, the bare existence of a nonzero
`q`-torsion point. -/
theorem natCard_ker_degreeFormEnd_of_dvd (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] {c : ℤ}
    (hc : frobeniusPointEnd q Wbar * frobeniusPointEnd q Wbar
      = c • frobeniusPointEnd q Wbar
        - (q : ℤ) • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)))
    {m n : ℤ} (hm : ¬ ((q : ℤ) ∣ m))
    (hd : (q : ℤ) ∣ m ^ 2 - c * m * n + n ^ 2 * (q : ℤ)) :
    (Nat.card (LinearMap.ker (degreeFormEnd q Wbar m n)) : ℤ)
      = m ^ 2 - c * m * n + n ^ 2 * (q : ℤ) := by
  classical
  have hqprime : Prime ((q : ℤ)) := Nat.prime_iff_prime_int.mp (Fact.out : q.Prime)
  rcases eq_or_ne (m ^ 2 - c * m * n + n ^ 2 * (q : ℤ)) 0 with hd0 | hd0
  · -- `d = 0` is IMPOSSIBLE off the origin (`degreeForm_ne_zero`, NINTH CUT), and
    -- `q ∤ m` puts us off the origin.  This branch used to cite the still-open
    -- `natCard_ker_degreeFormEnd_le`; it no longer does.
    exact absurd hd0 (degreeForm_ne_zero q Wbar hc (m := m) (n := n)
      (fun hmn => hm (by rw [hmn.1]; exact dvd_zero _)))
  -- `q ∣ d` and `q ∤ m` force `q ∣ m − c·n`, hence `q ∤ c`: the ORDINARY case
  have hmc : (q : ℤ) ∣ m - c * n := by
    have hsplit : m ^ 2 - c * m * n + n ^ 2 * (q : ℤ)
        = m * (m - c * n) + n ^ 2 * (q : ℤ) := by ring
    rw [hsplit] at hd
    have hmul : (q : ℤ) ∣ m * (m - c * n) := by
      have h2 : (q : ℤ) ∣ n ^ 2 * (q : ℤ) := dvd_mul_left _ _
      simpa using dvd_sub hd h2
    rcases hqprime.dvd_mul.mp hmul with h | h
    · exact absurd h hm
    · exact h
  have hqc : ¬ ((q : ℤ) ∣ c) := by
    intro h
    exact hm (by simpa using dvd_add hmc (h.mul_right n))
  -- peel the conjugate: `d = A · q^v` with `A = #ker ψ'` prime to `q`
  have hconj := degreeForm_conj c m n (q : ℤ)
  obtain ⟨v, hnd, hval⟩ := exists_natCard_ker_mul_pow q Wbar hc
    ((m - n * c) ^ 2 - c * (m - n * c) * (-n) + (-n) ^ 2 * (q : ℤ)).natAbs
    (m - n * c) (-n) le_rfl
    (by rw [show (m - n * c) - c * (-n) = m by ring]; exact hm)
    (by rw [hconj]; exact hd0)
  rw [hconj] at hval
  have hA0 : (Nat.card (LinearMap.ker (degreeFormEnd q Wbar (m - n * c) (-n))) : ℤ) ≠ 0 := by
    intro h0
    exact hnd (by rw [h0]; exact dvd_zero _)
  have hsurj' : Function.Surjective (degreeFormEnd q Wbar (m - n * c) (-n)) :=
    (surjective_degreeFormEnd q Wbar hc (m := m) (n := n) hd0).2
  have hprod := natCard_ker_mul (degreeFormEnd q Wbar m n)
    (degreeFormEnd q Wbar (m - n * c) (-n)) hsurj'
  rw [degreeFormEnd_mul_conj q Wbar hc m n] at hprod
  have hqv : ((q : ℤ) ^ v) ≠ 0 := by
    have : (0 : ℤ) < (q : ℤ) := by exact_mod_cast (Fact.out : q.Prime).pos
    positivity
  -- `#E[d] = A² · q^v`, the prime-to-`q` and `q`-primary parts separately
  have hsplit2 : (m ^ 2 - c * m * n + n ^ 2 * (q : ℤ))
        • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point))
      = ((Nat.card (LinearMap.ker (degreeFormEnd q Wbar (m - n * c) (-n))) : ℤ)
          • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)))
        * (((q : ℤ) ^ v)
          • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point))) := by
    rw [zsmul_one_mul_zsmul_one, hval]
  have htors : (Nat.card (LinearMap.ker ((m ^ 2 - c * m * n + n ^ 2 * (q : ℤ))
      • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)))) : ℤ)
      = (Nat.card (LinearMap.ker (degreeFormEnd q Wbar (m - n * c) (-n))) : ℤ) ^ 2
        * (q : ℤ) ^ v := by
    rw [hsplit2, natCard_ker_mul _ _ (surjective_zsmul_one q Wbar hqv),
      natCard_ker_zsmul_q_pow q Wbar hc hqc v]
    push_cast
    rw [natCard_ker_zsmul_one_of_not_dvd q Wbar hnd]
  have hprodZ : (Nat.card (LinearMap.ker ((m ^ 2 - c * m * n + n ^ 2 * (q : ℤ))
      • (1 : Module.End ℤ ((Wbar⁄(AlgebraicClosure (ZMod q))).Point)))) : ℤ)
      = (Nat.card (LinearMap.ker (degreeFormEnd q Wbar m n)) : ℤ)
        * (Nat.card (LinearMap.ker (degreeFormEnd q Wbar (m - n * c) (-n))) : ℤ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℤ)) hprod
  rw [htors] at hprodZ
  have hX : (Nat.card (LinearMap.ker (degreeFormEnd q Wbar m n)) : ℤ)
      = (Nat.card (LinearMap.ker (degreeFormEnd q Wbar (m - n * c) (-n))) : ℤ)
        * (q : ℤ) ^ v := by
    refine mul_right_cancel₀ hA0 ?_
    rw [← hprodZ]
    ring
  rw [hX]
  exact hval.symm

/-- **The degree of `[m] − [n]∘F` is a binary quadratic form of
discriminant `c² − 4q`, counted by its kernel** — opened as a sorry leaf
2026-07-27, **PROVEN since**, over exactly the four leaves this module still
carries: `exists_sq_frobeniusPointEnd_prime_to_char` and
`sq_frobeniusPointEnd_qPrimary` (through the proven umbrella
`exists_sq_frobeniusPointEnd`), `natCard_ker_degreeFormEnd_le`, and
`exists_ne_zero_qTorsion` (through `natCard_ker_degreeFormEnd_of_dvd`).  It is
still the ONLY input of Hasse's bound `hasse_bound_natCard_affine_point`, which
is why the route notes below are kept: they document the axes searched for
those leaves, not for this theorem.  For `q ∤ m` the endomorphism `[m] − [n]∘F` of
`Wbar(𝔽̄_q)` is separable, so its degree is the cardinality of its kernel, and
that degree is `m² − c·m·n + n²q` for a coefficient `c` independent of
`(m, n)`.

(The `(sorry leaf)` label this docstring carried until 2026-07-30 was stale:
the declaration below has had a real proof since 2026-07-27.  Such labels get
harvested into dispatch lists, so a stale one manufactures work at a proven
node — see CLAUDE.md.)

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
survives is exactly step 1 and step 4.  The three names below are the shape of
that cut; two of them have since been proven and pushed one level down, so read
each bullet's status annotation before dispatching at any of these names:

* `exists_sq_frobeniusPointEnd` — the Frobenius characteristic equation on
  points, `F² = c·F − q`.  Step 1.  **PROVEN 2026-07-28** over the
  torsion-primary split; the live leaves under it are
  `exists_sq_frobeniusPointEnd_prime_to_char` and
  `sq_frobeniusPointEnd_qPrimary`.
* `natCard_ker_degreeFormEnd_le` — separable degree ≤ degree, one-sided and
  with no hypothesis on `m`.  Half of step 4.
* `natCard_ker_degreeFormEnd_of_dvd` — the `q`-primary case `q ∣ d`.  The
  other half of step 4, and the only place the ordinary/supersingular
  dichotomy is used.  **PROVEN 2026-07-28** over the single instance
  `natCard_ker_frobeniusConj`, `#ker([c] − F) = q` for `q ∤ c`, which is
  **PROVEN 2026-07-29** in turn; what survives of the pair is the existence
  leaf `exists_ne_zero_qTorsion`.

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
